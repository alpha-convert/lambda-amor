(* Joseph Cutler, 2021 *)
open Syntax

module FMap = Map.Make(struct
    type t = string
    let compare = String.compare
  end)

let lift_key (x : string) : FMap.key = x

exception UnboundSourceName of string

(*
 * Mapping from source names to idents (source * fresh)
 *)
type fresh_env = {
  ident_env : la_ident FMap.t;
  idx_var_env : (la_idx_var * [`Alias | `Bound]) FMap.t;
  type_var_env : (la_type_var * [`Alias | `Bound]) FMap.t;
}

let empty_fresh_env = {ident_env = FMap.empty ; idx_var_env = FMap.empty; type_var_env = FMap.empty}

type 'a freshener = fresh_env -> 'a

let return (x : 'a) : 'a freshener =
  fun _ -> x

let (>>=) (m : 'a freshener) (f : 'a -> 'b freshener) : 'b freshener =
  fun env -> (f (m env)) env

let (let*) x f = x >>= f

let rec mapM (f : 'a -> 'b freshener) (xs : 'a list) : 'b list freshener =
  match xs with
    [] -> return []
  | y::ys -> let* b = f y in
             let* bs = mapM f ys in
             return @@ b :: bs

(*
 * Note: this should probably never hit the `Fresh case...
 *
 * Replace an unfreshened variable x with its freshened version.
 *)
let freshen_bound_ident (x : la_ident) : la_ident freshener =
  match x.ident_fresh_name with
    `TopLevel _ -> return x
  | _ -> fun env -> (match FMap.find_opt x.ident_source_name env.ident_env with
                                  None -> raise (UnboundSourceName x.ident_source_name)
                                | Some y -> y
                               )

(*
 * Generate a fresh name based on x, bind it, and run m. Then, return the
 * result of m, along with the new name.
 *)

let (|!:|) (x : la_ident_binder) (m : 'a freshener) : (la_ident_binder * 'a) freshener =
  match x with
    Wild -> let* v = m in return (x,v)
  | Name ({ident_fresh_name = `TopLevel _ ; _} as n) -> fun env -> (x,m {env with ident_env = FMap.add n.ident_source_name n env.ident_env})
  | Name x -> let fn = Fresh_var.gen_var () in
              let x' = {x with ident_fresh_name = `Fresh fn} in
              fun env -> let env' = {env with ident_env = FMap.add x.ident_source_name x' env.ident_env} in
              (Name x',m env')


(* could be a source of bugs *)
let freshen_bound_idx_var (i : la_idx_var) : la_idx_term freshener =
  match i.idx_fresh_name with
  | `Alias _ -> return (IAlias i)
  | _ -> fun env -> (match FMap.find_opt i.idx_source_name env.idx_var_env with
                       None -> raise (UnboundSourceName i.idx_source_name)
                     | Some(j,`Bound) -> IVar j
                     | Some(j,`Alias) -> IAlias j)

(*
let freshen_bound_idx_var_raw (i : la_idx_var) : la_idx_var freshener =
  match i.idx_fresh_name with
  | `Alias _ -> return i
  | _ -> fun env -> (match FMap.find_opt i.idx_source_name env.idx_var_env with
                                  None -> raise (UnboundSourceName i.idx_source_name)
                                | Some(j,`Bound) -> j
                                | Some(j,`Alias) -> j
                               )
*)

let (|!:::|) (i : la_idx_var_binder) (m : 'a freshener) : (la_idx_var_binder * 'a) freshener =
  match i with
    IWild -> let* v = m in return (i,v)
  | IName ({idx_fresh_name = `Alias _;_} as n) -> fun env -> (i, m {env with idx_var_env = FMap.add n.idx_source_name (n,`Alias) env.idx_var_env})
  | IName n -> let fn = Fresh_var.gen_var () in
               let n' = {n with idx_fresh_name = `Fresh fn} in
               fun env ->
               let env' = {env with idx_var_env = FMap.add n.idx_source_name (n',`Bound) env.idx_var_env} in
               (IName n',m env')

let freshen_bound_type_var (a : la_type_var) : la_type freshener =
  match a.type_fresh_name with
  | `Alias _ -> return @@ (Ne,TyAlias a)
  | _ -> fun env -> (match FMap.find_opt a.type_source_name env.type_var_env with
                       None -> raise (UnboundSourceName a.type_source_name)
                     | Some (a,`Bound) -> (Ne,TyVar a)
                     | Some (a,`Alias) -> (Ne,TyAlias a))

let (|!::::|) (a : la_type_var_binder) (m : 'a freshener) : (la_type_var_binder * 'a) freshener =
  match a with
    TWild -> let* v = m in return (a,v)
  | TName ({type_fresh_name = `Alias _;_} as n) ->fun env -> (a, m {env with type_var_env = FMap.add n.type_source_name (n,`Alias) env.type_var_env})
  | TName n -> let fn = Fresh_var.gen_var () in
               let n' = {n with type_fresh_name = `Fresh fn} in
               fun env ->
               let env' = {env with type_var_env = FMap.add n.type_source_name (n',`Bound) env.type_var_env} in
               (TName n',m env')

(*
let freshen_pvec_var {pot_source_name = s;_} =
  let idx_var_to_pvec_var {idx_source_name = s;idx_fresh_name = f} = {pot_source_name = s;pot_fresh_name=f} in
  fun env -> (match FMap.find_opt s env.idx_var_env with
                  None -> raise (UnboundSourceName s)
                | Some (i,`Bound) -> PVecVar (idx_var_to_pvec_var i)
                | Some (i,`Alias) -> PVecAlias (idx_var_to_pvec_var i))



let rec freshen_pvec (p : la_pot_vec) : la_pot_vec freshener =
  match p with
    (PVec _ | PVecAlias _) -> return p
  | PVecVar x -> freshen_pvec_var x
  | PVecPlus(p1,p2) -> let* p1' = freshen_pvec p1 in
                       let* p2' = freshen_pvec p2 in
                       return @@ PVecPlus(p1',p2')
  | PVecShift p -> let* p' = freshen_pvec p in return @@ PVecShift p'
  | PVecMinus(p1,p2) -> let* p1' = freshen_pvec p1 in
                        let* p2' = freshen_pvec p2 in
                        return @@ PVecMinus(p1',p2')
  | PConstVec(it) -> let* it' = freshen_iterm it in return @@ PConstVec it'
*)

let rec freshen_iterm (iterm : la_idx_term) : la_idx_term freshener =
  match iterm with
    (IConst _ | IAlias _) -> return iterm
  | IVar i -> let* it = freshen_bound_idx_var i in
              return it
  | IPlus(it1,it2) -> let* it1' = freshen_iterm it1 in
                      let* it2' = freshen_iterm it2 in
                      return @@ IPlus(it1',it2')
  | IMinus(it1,it2) -> let* it1' = freshen_iterm it1 in
                       let* it2' = freshen_iterm it2 in
                       return @@ IMinus(it1',it2')
  | IMult(ic,it) -> let* it' = freshen_iterm it in return @@ IMult(ic,it')
  | IShift(it) -> let* it' = freshen_iterm it in return @@ IShift it'
  | IFamLam(i,s,it) -> let* (i',it') = i |!:::| (freshen_iterm it) in
                       return @@ IFamLam(i',s,it')
  | IFamApp(it1,it2) -> let* it1' = freshen_iterm it1 in
                        let* it2' = freshen_iterm it2 in
                        return @@ IFamApp(it1',it2')
  | ISum(i,f,lb,ub) -> let* i',f' = i |!:::| (freshen_iterm f) in
                       let* lb' = freshen_iterm lb in
                       let* ub' = freshen_iterm ub in
                       return @@ ISum(i',f',lb',ub')
  | IConstVec(it) -> let* it' = freshen_iterm it in return @@ IConstVec it'
  | INtoR(it) -> let* it' = freshen_iterm it in return @@ INtoR it'

let rec freshen_constr (c : la_constr) : la_constr freshener =
  match c with
       (Top | Bot) -> return c
     | Conj(cs) -> let* cs' = mapM freshen_constr cs in return @@ Conj cs'
     | Imp(c1,c2) -> freshen_constr c1 >>= fun c1' ->
                     freshen_constr c2 >>= fun c2' ->
                     return @@ Imp(c1',c2')
     (* this is stupid... *)
     | Forall(iss,c) -> let f (i,s) m = (IName i) |!:::| m >>= fun (i',(is',c')) -> return ((i',s)::is',c') in
                        let m0 = freshen_constr c >>= fun c' -> return ([],c') in
                        List.fold_right f iss m0 >>= fun (iss',c') ->
                        return @@ forall iss' c'
     | Exists(iss,c) -> let f (i,s) m = (IName i) |!:::| m >>= fun (i',(is',c')) -> return ((i',s)::is',c') in
                        let m0 = freshen_constr c >>= fun c' -> return ([],c') in
                        List.fold_right f iss m0 >>= fun (iss',c') ->
                        return @@ exists iss' c'
     | Eq(it1,it2) -> let* it1' = freshen_iterm it1 in
                      let* it2' = freshen_iterm it2 in
                      return @@ Eq(it1',it2')
     | Leq(it1,it2) -> let* it1' = freshen_iterm it1 in
                       let* it2' = freshen_iterm it2 in
                       return @@ Leq(it1',it2')
     | Lt(it1,it2) -> let* it1' = freshen_iterm it1 in
                      let* it2' = freshen_iterm it2 in
                      return @@ Lt(it1',it2')
     | Comment(s,c) -> let* c' = freshen_constr c in return @@ Comment(s,c')

let rec freshen_type (t : la_type) : la_type freshener =
  match type_head t with
    (TyUnit | TyBool | TyNat | TyAlias _) -> return t
  | TyVar a -> freshen_bound_type_var a
  | TyArr(t1,t2) -> let* t1' = freshen_type t1 in
                    let* t2' = freshen_type t2 in
                    return @@ ty_arr t1' t2'
  | TyTensor(t1,t2) -> let* t1' = freshen_type t1 in
                       let* t2' = freshen_type t2 in
                       return @@ ty_tensor t1' t2'
  | TyWith(t1,t2) -> let* t1' = freshen_type t1 in
                     let* t2' = freshen_type t2 in
                     return @@ ty_with t1' t2'
  | TyBang(t) -> let* t' = freshen_type t in return @@ ty_bang t'
  | TySum(t1,t2) -> let* t1' = freshen_type t1 in
                    let* t2' = freshen_type t2 in
                    return @@ ty_sum t1' t2'
  | TyIForall(i,s,t) -> let* i',t' = i |!:::| (freshen_type t) in
                        return @@ ty_i_forall i' s t'
  | TyIExists(i,s,t) -> let* i',t' = i |!:::| (freshen_type t) in
                        return @@ ty_i_exists i' s t'
  | TyTForall(a,k,t) -> let* a',t' = a |!::::| (freshen_type t) in
                        return @@ ty_t_forall a' k t'
  | TyList(it,t) -> let* t' = (freshen_type t) in
                    let* it' = freshen_iterm it in
                    return @@ ty_list it' t'
  | TyImplies(c,t) -> let* c' = freshen_constr c in
                      let* t'= freshen_type t in
                      return @@ ty_implies c' t'
  | TyConj(c,t) -> let* c' = freshen_constr c in
                   let* t' = freshen_type t in
                   return @@ ty_conj c' t'
  | TyMonad(it,p,t) -> let* it' = freshen_iterm it in
                       let* p' = freshen_iterm p in
                       let* t' = freshen_type t in
                       return @@ ty_monad it' p' t'
  | TyPot(it,p,t) -> let* it' = freshen_iterm it in
                     let* p' = freshen_iterm p in
                     let* t' = freshen_type t in
                     return @@ ty_pot it' p' t'
  | TyConstPot(it,t) -> let* it' = freshen_iterm it in
                        let* t' = freshen_type t in
                        return @@ ty_const_pot it' t'
  | TyFamLam(i,s,t) -> let* i',t' = i |!:::| (freshen_type t) in
                       return @@ ty_fam_lam i' s t'
  | TyFamApp(t,it) -> let* it' = freshen_iterm it in
                      let* t' = freshen_type t in
                      return @@ ty_fam_app t' it'
                     

let rec freshen_exp (e : la_exp) : la_exp freshener =
  match e with
    (Const _ | Hole) -> return e
  | Var x -> let* x' = freshen_bound_ident x in return (Var x')
  | Binop(b,e1,e2) -> let* e1' = freshen_exp e1 in
                      let* e2' = freshen_exp e2 in
                      return @@ Binop(b,e1',e2')
  | Lam(x,e) -> let* x',e' = x |!:| (freshen_exp e) in
                return @@ Lam(x',e')
  | App(e1,e2) -> let* e1' = freshen_exp e1 in
                  let* e2' = freshen_exp e2 in
                  return @@ App(e1',e2')
  | Ann(e,t) -> let* e' = freshen_exp e in
                let* t' = freshen_type t in
                return @@ Ann(e',t')
  | PPair(e1,e2) -> let* e1' = freshen_exp e1 in
                    let* e2' = freshen_exp e2 in
                    return @@ PPair(e1',e2')
  | PLet(e1,x,y,e2) -> let* e1' = freshen_exp e1 in
                       let* (x',(y',e2')) = x |!:| (y |!:| (freshen_exp e2)) in
                       return @@ PLet(e1',x',y',e2')
  | NPair(e1,e2) -> let* e1' = freshen_exp e1 in
                    let* e2' = freshen_exp e2 in
                    return @@ NPair(e1',e2')
  | Fst e -> let* e' = freshen_exp e in return @@ Fst e'
  | Snd e -> let* e' = freshen_exp e in return @@ Snd e'
  | Bang e -> let* e' = freshen_exp e in return @@ Bang e'
  | LetBang(e1,x,e2) -> let* e1' = freshen_exp e1 in
                        let* x',e2' = x |!:| (freshen_exp e2) in
                        return @@ LetBang(e1',x',e2')
  | Inl e -> let* e' = freshen_exp e in return @@ Inl e'
  | Inr e -> let* e' = freshen_exp e in return @@ Inr e'
  | SCase(e,x,e1,y,e2) -> let* e' = freshen_exp e in
                          let* x',e1' = x |!:| (freshen_exp e1) in
                          let* y',e2' = y |!:| (freshen_exp e2) in
                          return @@ SCase(e',x',e1',y',e2')
  | NCase(e,e1,n,e2) -> let* e' = freshen_exp e in
                        let* e1' = freshen_exp e1 in
                        let* n',e2' = n |!:| (freshen_exp e2) in
                        return @@ NCase(e',e1',n',e2')
  | Fix(x,e) -> let* x',e' = x |!:| (freshen_exp e) in
                return (Fix(x',e'))
  | ILam(i,e) -> let* i',e' = i |!:::| (freshen_exp e) in
                 return @@ ILam(i',e')
  | IApp(e,it) -> let* e' = freshen_exp e in
                  let* it' = freshen_iterm it in
                  return @@ IApp(e',it')
  | TLam(a,e) -> let* a',e' = a |!::::| (freshen_exp e) in
                 return @@ TLam(a',e')
  | TApp(e,t) -> let* e' = freshen_exp e in
                 let* t' = freshen_type t in
                 return @@ TApp(e',t')
  | Nil -> return Nil
  | Cons(e1,e2) -> let* e1' = freshen_exp e1 in
                   let* e2' = freshen_exp e2 in
                   return @@ Cons(e1',e2')
  | LCase(e,e1,h,t,e2) -> let* e' = freshen_exp e in
                            let* e1' = freshen_exp e1 in
                            let* (h',(t',e2')) = h |!:| (t |!:| (freshen_exp e2)) in
                            return @@ LCase(e',e1',h',t',e2')
  | Pack(it,e) -> let* it' = freshen_iterm it in 
                  let* e' = freshen_exp e in
                  return @@ Pack (it',e')
  | Unpack(e,j,x,e1) -> let* e' = freshen_exp e in
                        let* (x',(j',e1')) = (x |!:| (j |!:::| (freshen_exp e1))) in
                        return @@ Unpack(e',j',x',e1')
  | CLam e -> let* e' = freshen_exp e in return @@ CLam e'
  | CApp e -> let* e' = freshen_exp e in return @@ CApp e'
  | CPair e -> let* e' = freshen_exp e in return @@ CPair e'
  | CLet(e,x,e1) -> let* e' = freshen_exp e in
                    let* x',e1' = x |!:| (freshen_exp e1) in
                    return @@ CLet(e',x',e1')
  | Ret e -> let* e' = freshen_exp e in return @@ Ret e'
  | Bind(e,x,e1) -> let* e' = freshen_exp e in
                    let* x',e1' = x |!:| (freshen_exp e1) in
                    return @@ Bind(e',x',e1')
  | Tick(it,p) -> let* it' = freshen_iterm it in
                  let* p' = freshen_iterm p in
                  return @@ Tick(it',p')
  | Store(it,p,e) -> let* e' = freshen_exp e in
                     let* p' = freshen_iterm p in
                     let* it' = freshen_iterm it in
                     return @@ Store(it',p',e')
  | StoreConst(it,e) -> let* it' = freshen_iterm it in
                        let* e' = freshen_exp e in
                        return @@ StoreConst(it',e')
  | Release(e,x,e1) -> let* e' = freshen_exp e in
                         let* x',e1' = x |!:| (freshen_exp e1) in
                       return @@ Release(e',x',e1')
  | Shift(e) -> let* e' = freshen_exp e in return @@ Shift(e')
  | Absurd -> return Absurd
  | Ite(e,e1,e2) -> let* e' = freshen_exp e in
                    let* e1' = freshen_exp e1 in
                    let* e2' = freshen_exp e2 in
                    return @@ Ite(e',e1',e2')
  | Let(e,x,e') -> let* e = freshen_exp e in
                   let* x,e' = x |!:| (freshen_exp e') in
                   return @@ Let(e,x,e')


let freshen_decl (d : la_decl) : la_decl freshener =
  match d with
    ValDec (x,e,t) -> let* e' = freshen_exp e in
                      let* t' = freshen_type t in
                      return @@ ValDec (x,e',t')
  | TyDec (a,t,k) -> let* t' = freshen_type t in return @@ TyDec(a,t',k)
  | IdxDec(j,it,s) -> let* it' = freshen_iterm it in return @@ IdxDec(j,it',s)
  | DoDec(x,it1,it2,t,e) -> let* it1' = freshen_iterm it1 in
                            let* it2' = freshen_iterm it2 in
                            let* t' = freshen_type t in
                            let* e' = freshen_exp e in
                            return @@ DoDec(x,it1',it2',t',e')

let with_toplevel_name (x : la_ident) (m : la_pgm freshener) : la_pgm freshener =
  fun env -> m ({env with ident_env = FMap.add x.ident_source_name x env.ident_env})

let with_alias_idx_name (i : la_idx_var) (m : la_pgm freshener) : la_pgm freshener =
  fun env -> m ({env with idx_var_env = FMap.add i.idx_source_name (i,`Alias) env.idx_var_env})

let with_alias_type_name (x : la_type_var) (m : la_pgm freshener) : la_pgm freshener =
  fun env -> m ({env with type_var_env = FMap.add x.type_source_name (x,`Alias) env.type_var_env})


let rec freshen_pgm (p : la_pgm) : la_pgm freshener =
  match p with
    [] -> return []
  | (ValDec (x,_,_) as d)::ds -> let* d' = freshen_decl d in
                                 let* ds' = with_toplevel_name x (freshen_pgm ds) in
                                 return (d'::ds')
  | (TyDec (a,_,_) as d)::ds -> let* d' = freshen_decl d in
                                let* ds' = with_alias_type_name a (freshen_pgm ds) in
                                return (d'::ds')
  | (IdxDec (i,_,_) as d)::ds -> let* d' = freshen_decl d in
                                 let* ds' = with_alias_idx_name i (freshen_pgm ds) in
                                 return (d'::ds')
  | (DoDec (x,_,_,_,_) as d) :: ds -> let* d' = freshen_decl d in
                                      let* ds' = with_toplevel_name x (freshen_pgm ds)
                                      in return (d' :: ds')
                                         

let do_freshen_pgm (p : la_pgm) : la_pgm =
  freshen_pgm p empty_fresh_env
