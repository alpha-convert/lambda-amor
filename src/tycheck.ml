(* Joseph Cutler, 2021 *)
open Syntax
open Tyerror


(**
 * state/error monad for type checking/inferring
 * Ctx.t corresponds to the Ψ ; Θ ; Δ ; Ω ; Γ
        context of the infer/check judgment- we carry this around.
        all but the Γ (aff_ctx_t) component only have the reader
        part of the state monad- since we only ever add variables to them,
        and don't thread them through the judgments. The output
        of an 'a checker includes an aff_ctx_t, which contains
        the affine variables not used by the monadic action, and
        can be threaded to further ones.
 * The Tyerror.t is for error handling and typed holes- see tyerror.ml
 * The Env.t is a set of bindings from type/index aliases to their values.
 *)
type 'a checker = Ctx.t * Env.t -> ('a * Ctx.aff_ctx_t) Tyerror.t
type 'a inferer = 'a checker


let return (x : 'a) : 'a checker =
  fun (ctx,_) -> Tyerror.return (x,ctx.aff_ctx)

let fail_with ex = fun _ -> Fail ex

(*
 * The bind for the checker. Given a checker, it runs it,
   constructs the subsequent checker using the continuation,
   and then modifies it by replacing the input affine context
   by the output of the first-- threading the state through.
*)
let (>>=) (x : 'a checker) (f : 'a -> 'b checker) : 'b checker = 
  fun (ctx,env) -> match x (ctx,env) with
                     Fail ex -> Fail ex
                   | Ok (y,aff_ctx) -> (f y) ({ctx with aff_ctx = aff_ctx},env)

let map f m = fun (ctx,env) ->
                match m (ctx,env) with
                  Fail ex -> Fail ex
                | Ok(a,ac) -> Ok(f a,ac)

let (let*) x f = x >>= f
let (let+) x f = map f x

let (>>) (m1 : unit checker) (m2 : 'a checker) : 'a checker =
  m1 >>= fun () -> m2

let rec mapM (f : 'a -> 'b checker) (xs : 'a list) : 'b list checker =
  match xs with
    [] -> return []
  | y::ys -> let* b = f y in
             let* bs = mapM f ys in
             return @@ b :: bs

(* Intercept the error output of m, replace it with a generic error *)
let handle (m : 'a checker) (s : Tyerror.error_elem -> string) : 'a checker =
  fun u -> match m u with
             Ok (a,_) -> (return a) u
           | Fail err -> Fail (Generic (s err))

let get_ctx : Ctx.t checker =
  fun (c,e) -> (return c) (c,e)
  
(* normalize_type t = return t', where t' is the normal form of t.*)
let normalize_type (t : la_type) : la_type checker =
  fun ce -> (return @@ Normalize.normalize_type ce t) ce

(* normalize t and ensure that its normal form is a base type.*)
let normalize_base_type (t : la_type) : la_type checker = 
  let rec is_base_type t =
    match type_head t with
      (TyUnit | TyNat | TyBool) -> return ()
    | (TyBang t | TyList (_,t)) -> is_base_type t
    | (TyTensor(t1,t2) | TySum(t1,t2)) -> (is_base_type t1) >> (is_base_type t2)
    | _ -> fail_with (DoDecUnobservable t)
  in
  let* t' = normalize_type t in
  let* _ =  is_base_type t' in
  return t'

let with_ctx (x : 'a checker) (f : Ctx.t -> Ctx.t) : 'a checker =
  fun (ctx,env) -> x (f ctx,env)

let with_env (x : 'a checker) (f : Env.t -> Env.t) : 'a checker =
  fun (ctx,env) -> x (ctx,f env)

(*
 * The checker which binds x : t, does m, and then unbinds x
   before the next checker.
 *)
let (|:|) (x : la_ident_binder) (t : la_type) (m : 'a checker) : 'a checker =
  match x with
    Wild -> m
  | Name x -> fun ctx -> match (with_ctx m (Ctx.aff_bind (x,t))) ctx with
               Fail ex -> Fail ex
             | Ok (a,aff_ctx) -> Ok (a, Ctx.aff_unbind x aff_ctx)

(*
 * Binds x : t as an exp variable, and runs m. Unlike the |:| function,
   we don't need to unbind, since exponential variables can be used
   multiple times!
 *)
let (|::|) (x : la_ident_binder) (t : la_type) (m : 'a checker) =
  match x with
    Wild -> m
  | Name x -> with_ctx m (Ctx.exp_bind (x,t))

let (|:::|) (i : la_idx_var_binder) (s : la_sort) (m : 'a checker) =
  match i with
    IWild -> m
  | IName i -> with_ctx m (Ctx.idx_bind (i,s))

let (|::::|) (c : la_constr) (m : 'a checker) =
  with_ctx m (Ctx.ctr_add c)

let (|:::::|) (a : la_type_var_binder) (k : la_kind) (m : 'a checker) =
  match a with
    TWild -> m
  | TName a -> with_ctx m (Ctx.type_bind (a,k))

(* Add a binding (i ↦ is) to the environment before running m.*)
let (<:::>) (i : la_idx_var) (is : la_idx_term * la_sort) (m : 'a checker) =
  match i.idx_fresh_name with
    `Alias j -> with_env m (Env.idx_bind (j,is))
  | _ -> fail_with (Generic "Attemmpted to bind a non-alias index.")

let (<:::::>) (a : la_type_var) (tk : la_type * la_kind) (m : 'a checker) =
  match a.type_fresh_name with
    `Alias x -> with_env m (Env.type_bind (x,tk))
  | _ -> fail_with (Generic "Attempted to bind non-alias type.")

(*
 Look up the type of x, mark it as used if it was affine.
 return the type, as well as the True constraint.

 Raises an affine reuse error if x was affine and already
 marked as used, an unbound variable error if the variable
 is not found.
*)
let var_infer x : (la_type * la_constr) inferer = 
  fun (ctx,_) -> (match Ctx.term_var_lookup ctx x with
                    `Aff t -> Tyerror.return ((t,Top), Ctx.aff_mark ctx.aff_ctx x)
                  | `Used -> raise (AffReuse x)
                  | `Exp t -> Tyerror.return ((t,Top), ctx.aff_ctx)
                  | `Missing -> raise (UnboundVar x))


(* Gets the type of a constant term *)
let ty_of_const = function
    BConst _ -> ty_bool
  | UConst -> ty_unit
  | NConst _ -> ty_nat

(*
 * Infer the type of constants
 *)
let const_infer c : (la_type * la_constr) inferer =
  fun (ctx,_) -> Ok ((ty_of_const c,Top),ctx.aff_ctx)

(*
 * Modify m so that the input affine context is passed through
   to the output: used when the premise of a rule zeroes out the
   affine context, and so the conclusion uses no affine variables.
 *)
let pass_ctx (m : 'a checker) : 'a checker =
  fun (ctx,env) -> match m (ctx,env) with
                     Fail ex -> Fail ex
                   | Ok(a,_) -> Ok(a,ctx.aff_ctx)

(*
 * Run the actions m1,m2 in "parallel" on the same input context-
 * used for shared-resource rules like the branches of a match
 * or intro for negative pairs.
*)
let parallel ((m1,m2) : ('a checker) * ('b checker)) : ('a * 'b) checker = 
   fun ctx -> match (m1 ctx, m2 ctx) with
                    (Fail ex,_) -> Fail ex
                  | (_,Fail ex) -> Fail ex
                  | (Ok(c1,g1),Ok(c2,g2)) -> Ok ((c1,c2),Ctx.intersect g1 g2)

let (>>&&=) ms f = (parallel ms) >>= f

(** sort_eq s s' = return () iff s = s'*)
let rec sort_eq s s' : unit checker = 
  match s, s' with
    (SoBase SoNat,SoBase SoNat) -> return ()
  | (SoBase SoPosReal,SoBase SoPosReal) -> return ()
  | (SoBase SoPotVec,SoBase SoPotVec) -> return ()
  | (SoArr(bs1,s2),SoArr(bs1',s2')) -> sort_eq (SoBase bs1) (SoBase bs1') >>
                                       sort_eq s2 s2'
  | _ -> fail_with (UnequalSorts (s,s'))

(* kind_eq k k' = return () iff k = k'*)
let rec kind_eq k k' : unit checker =
  match k, k' with
    KStar, KStar -> return ()
  | KArr(s,k),KArr(s',k') -> sort_eq s s' >> kind_eq k k'
  | _ -> fail_with (Generic "unequal kinds")

(* ivar_infer i = return (s,T) iff i : S ∈ Θ *)
let ivar_infer i : (la_sort * la_constr) inferer =
  fun (ctx,env) -> match Ctx.idx_var_lookup ctx i with
                     None -> Tyerror.raise (Generic ("infer... unbound index variable: source:" ^ i.idx_source_name ))
                   | Some s -> (return (s,Top)) (ctx,env)

(* check_ivar i s = return T iff i : s ∈ Θ *)
let check_ivar i s : la_constr checker =
  fun (ctx,env) -> match Ctx.idx_var_lookup ctx i with
                     None -> Tyerror.raise (Generic ("checking... unbound index variable: source:" ^ i.idx_source_name ))
                   | Some s' -> (handle (sort_eq s s') (fun _ -> "IVar " ^ i.idx_source_name ^ " has sort " ^ show_la_sort s' ^ " expected " ^ show_la_sort s) >> return Top) (ctx,env)

(* check_sort I s = return Φ iff Θ ; Δ ⊢ I : s => Φ *)
(* TODO: This isn't quite right as of 12/21/20. Consider m + (n - 1)) for m + n >= 1.*)
let rec check_sort iterm s : la_constr checker =
  match iterm, s with
    (IConst (ICNat _) , SoBase SoNat) -> return Top
  | (IConst (ICReal _) , SoBase SoPosReal) -> return Top
  | (IConst (ICPVec _) , SoBase SoPotVec) -> return Top
  | (IPlus (i1,i2),SoBase _) -> let* phi1 = check_sort i1 s in
                                let* phi2 = check_sort i2 s in
                                return (conj phi1 phi2)
  | (IMinus(i1,i2),SoBase _) -> let* phi1 = check_sort i1 s in
                                let* phi2 = check_sort i2 s in
                                let c = smart_leq(i2,i1) in
                                return @@ conj_list [phi1;phi2;c]
  | IMult(ic,it),SoBase (SoNat | SoPosReal) -> let* phi1 = check_sort (IConst ic) s in
                                               let* phi2 = check_sort it s in
                                               return @@ conj phi1 phi2
  | IMult(ic,it),SoBase SoPotVec -> let* phi1 = check_sort (IConst ic) (SoBase SoPosReal) in
                                    let* phi2 = check_sort it s in
                                    return @@ conj phi1 phi2
  | IShift it,_ -> sort_eq s (SoBase SoPotVec) >> check_sort it s
  | (IVar i | IAlias i),s -> check_ivar i s
  | IFamLam(i,s,it),SoArr(s',s'') -> let* phi = sort_eq (SoBase s) (SoBase s') >>
                                    (i |:::| (SoBase s)) (check_sort it s'') in
                                    return @@ forall [i,SoBase s] phi
  | IFamApp(it1,it2),s -> let* s',phi1 = infer_sort it1 in
                          (match s' with
                             SoArr(s1,s2) -> let* phi2 = check_sort it2 (SoBase s1) in
                                             sort_eq s2 s >>
                                             return @@ conj phi1 phi2
                           | _ -> fail_with (Generic "not of sort arrow!"))

  | ISum(IName i,f,lb,ub),s -> let nat = SoBase SoNat in
                               let i_bounds = conj (smart_leq(lb,idx_var i)) (Lt(idx_var i,ub)) in
                               let* phi1 = i_bounds |::::| (((IName i) |:::| nat) (check_sort f s)) in
                               (check_sort lb nat,check_sort ub nat) >>&&= fun (phi2,phi3) ->
                               return @@ conj_list [forall [IName i,SoBase SoNat] (imp i_bounds phi1);phi2;phi3]
  | ISum(IWild,f,lb,ub),s -> let nat = SoBase SoNat in
                             let* phi1 = (check_sort f s) in
                             (check_sort lb nat,check_sort ub nat) >>&&= fun (phi2,phi3) ->
                             return @@ conj_list [phi1;phi2;phi3]


  | IConstVec(it),SoBase SoPotVec -> check_sort it (SoBase SoPosReal)
  | INtoR it,SoBase SoPosReal -> check_sort it (SoBase SoNat)
               
  | _ -> fail_with (Generic (Printf.sprintf "sort failure: %s <- %s" (iterm_pp iterm) (la_sort_pp s)))

(* infer_sort I = return (s,Φ) iff Θ ; Δ ⊢ I : S ⇒ Φ *)
and infer_sort iterm : (la_sort * la_constr) inferer =
  match iterm with
    IConst (ICNat _) -> return @@ (SoBase SoNat,Top)
  | IConst (ICReal _) -> return @@ (SoBase SoPosReal,Top)
  | IConst (ICPVec _) -> return @@ (SoBase SoPotVec,Top)
  | IPlus(it1,it2) -> let* s,phi1 = infer_sort it1 in
                      let* phi2 = (check_sort it2 s) in
                      return (s,conj phi1 phi2)
  | IMinus(it1,it2) -> let* s,phi1 = infer_sort it1 in
                       let* phi2 = (check_sort it2 s) in
                       let pos = smart_leq(it2,it1) in
                       return (s,conj_list [phi1;phi2;pos])
  | IMult(ic,it) -> let scalar_sort s =
                      (match s with
                         SoBase SoNat -> return @@ SoBase SoNat
                       | SoBase SoPosReal -> return @@ SoBase SoPosReal
                       | SoBase SoPotVec -> return @@ SoBase SoPosReal
                       | _ -> fail_with (Generic "Cant multiply something of this sort."))
                    in let* s,phi1 = infer_sort it in
                       let* s' = scalar_sort s in
                       let* phi2 = check_sort (IConst ic) s' in
                       return (s,conj phi1 phi2)

  | IShift it -> let* phi = check_sort it (SoBase SoPotVec) in
                 return (SoBase SoPotVec,phi)
  | (IVar i | IAlias i) -> ivar_infer i
  | IFamLam(i,s,it) -> let* s',phi = (i |:::| (SoBase s)) (infer_sort it) in
                       return @@ (SoArr(s,s'),phi)
  | IFamApp(it1,it2) -> let* s,phi1 = infer_sort it1 in
                        (match s with
                           SoArr(s1,s2) -> let* phi2 = (check_sort it2 (SoBase s1)) in
                                           return (s2,conj phi1 phi2)
                         | _ -> fail_with (Generic "Not an index-level function!"))
  | ISum(i,f,lb,ub) -> let* s,phi1 = (i |:::| (SoBase SoNat)) (infer_sort f) in
                       let* phi2 = check_sort lb (SoBase SoNat) in
                       let* phi3 = check_sort ub (SoBase SoNat) in
                       return (s,conj_list [phi1;phi2;phi3])
  | IConstVec(it) -> let* phi = check_sort it (SoBase SoPosReal) in
                     return (SoBase SoPotVec,phi)
  | INtoR it -> let* phi = check_sort it (SoBase SoNat) in
                return (SoBase SoPosReal,phi)



(* The constraint is well-formed (all inequalties have matching sorts)*)
(* check_wf_constr c = return Φ iff Θ ; Δ ⊢ c wf ⇒ Φ *)
let rec check_wf_constr (c : la_constr) : la_constr checker =
  match c with
    (Top | Bot) -> return Top
  | Conj(cs) -> let* cs' = mapM check_wf_constr cs in return (conj_list cs')
  | Imp(c1,c2) -> let* phi1 = check_wf_constr c1 in
                  let* phi2 = c1 |::::| (check_wf_constr c2) in
                  return (conj phi1 (imp c1 phi2))
  
  | Forall(iss,c) -> let* phi = List.fold_right (fun (i,s) m -> (IName i |:::| s) m) iss (check_wf_constr c) in return @@ Forall(iss,phi)
  | Exists(iss,c) -> let* phi = List.fold_right (fun (i,s) m -> (IName i |:::| s) m) iss (check_wf_constr c) in
                     return @@ Forall(iss,Imp(c,phi))
  | (Eq(it1,it2) | Leq(it1,it2) | Lt(it1,it2)) -> let* s,phi1 = infer_sort it1 in
                                                  let* phi2 = check_sort it2 s in
                                                  return (conj phi1 phi2)
  | Comment(_,_) -> fail_with (Generic "Should not be comments in user constraints")
 
let tvar_check a k =
  fun (ctx,env) ->  match Ctx.type_var_lookup ctx a with
                      None -> Tyerror.raise (Generic "unbound type var")
                    | Some k' -> (kind_eq k k' >> return Top) (ctx,env)

(* Returns the type to which a is bound. *)
let alias_get_type a : la_type checker =
  match a.type_fresh_name with
    `Alias x -> fun (ctx,env) -> (match Env.type_var_lookup env x with
                                      None -> Tyerror.raise (Generic "type alias has no binding")
                                    | Some (t,_) -> (return t) (ctx,env))
  | _ -> fail_with (Generic "not a type alias.")

let tvar_infer a =
  fun (ctx,env) -> match Ctx.type_var_lookup ctx a with
                      None -> Tyerror.raise (Generic "unbound type var")
                    | Some k' -> (return k') (ctx,env)


let rec check_kind (t : la_type) (k : la_kind) : la_constr checker =
  match type_head t,k with
    (TyUnit | TyBool | TyNat),KStar -> return Top
  | (TyVar a | TyAlias a),_ -> tvar_check a k
  | (TyArr(t1,t2) | TyTensor(t1,t2)
     | TyWith(t1,t2) | TySum(t1,t2)),_ -> let* phi1 = check_kind t1 k in
                                          let* phi2 = check_kind t2 k in
                                          return @@ conj phi1 phi2
  | TyBang t,_ -> check_kind t k
  | (TyIForall(i,s,t) | TyIExists(i,s,t)),_ -> let* phi = (i |:::| s) (check_kind t k) in
                                               return @@ forall [i,s] phi
  | TyTForall(a,k',t),_ -> (a |:::::| k') (check_kind t k)
  | TyList(it,t),_ -> let* phi1 = check_sort it (SoBase SoNat) in
                      let* phi2 = check_kind t k in
                      return @@ conj phi1 phi2
  | (TyConj(c,t)),_ -> let* phi1 = check_kind t k in
                       let* phi2 = check_wf_constr c in
                       return @@ conj phi1 phi2
  | (TyImplies(c,t)),_ -> let* phi1 = check_kind t k in
                          let* phi2 = check_wf_constr c in
                          return @@ conj (imp c phi1) phi2
  | (TyMonad(it,p,t) | TyPot(it,p,t)),_ -> let* phi1 = check_sort it (SoBase SoNat) in
                                           let* phi2 = check_kind t k in
                                           let* phi3 = check_sort p (SoBase SoPotVec) in
                                           return @@ conj_list[phi1;phi2;phi3]
  | TyConstPot(it,t),_ -> let* phi1 = check_sort it (SoBase SoPosReal) in
                          let* phi2 = check_kind t k in
                          return @@ conj phi1 phi2
  | TyFamLam(i,s,t), KArr(s',k) -> let* _ = sort_eq s s' in
                                   let* phi = (i |:::| s) (check_kind t k) in
                                   return @@ forall [i,s] phi
  | TyFamApp(t,it),k -> let* (k',phi1) = infer_kind t in
                        (match k' with
                           KArr(s,k') -> let* phi2 = check_sort it s in
                                         let* _ = kind_eq k k' in
                                         return (conj phi1 phi2)
                          | _ -> fail_with (Generic "not an indexed type!"))
                        
  | _ -> fail_with (Generic "Kind checking failed.")

and infer_kind (t : la_type) : (la_kind * la_constr) inferer =
  match type_head t with
    (TyUnit | TyBool | TyNat) -> return (KStar,Top)
  | TyVar a -> let* k = tvar_infer a in return (k,Top)
  | TyAlias a -> let* k = tvar_infer a in return (k,Top)
  | (TyArr(t1,t2)
  | TyTensor(t1,t2)
  | TyWith(t1,t2)
  | TySum(t1,t2)) -> let* phi1 = check_kind t1 KStar in
                     let* phi2 = check_kind t2 KStar in
                     return (KStar,conj phi1 phi2)
  | TyBang t -> let* phi = check_kind t KStar in return (KStar,phi)
  | (TyIForall(i,s,t)
  | TyIExists(i,s,t)) -> let* phi = ((i |:::| s) (check_kind t KStar)) in
                         return(KStar,phi)
  | TyTForall(a,k,t) -> let* phi = ((a |:::::| k) (check_kind t KStar)) in
                        return (KStar,phi)
  | TyList(it,t) -> let* phi1 = check_sort it (SoBase SoNat) in
                    let* phi2 = check_kind t KStar in
                    return (KStar,conj phi1 phi2)
  | (TyImplies(c,t)
  | TyConj(c,t)) -> let* phi1 = check_wf_constr c in
                    let* phi2 = check_kind t KStar in
                    return (KStar,conj phi1 phi2)
  | (TyPot(it,p,t)
  | TyMonad(it,p,t)) -> let* phi1 = check_sort it (SoBase SoNat) in
                        let* phi2 = check_sort p (SoBase SoPotVec) in
                        let* phi3 = check_kind t KStar in
                        return (KStar, conj_list [phi1;phi2;phi3])
  | TyConstPot(it,t) -> let* phi1 = check_sort it (SoBase SoPosReal) in
                         let* phi2 = check_kind t KStar in
                         return(KStar, conj phi1 phi2)
  | TyFamApp(t,it) -> let* k,phi1 = infer_kind t in
                      (match k with
                         KArr(s,k') -> let* phi2 = check_sort it s in
                                       return (k',conj phi1 phi2)
                       | _ -> fail_with (Generic "not an indexed type!"))
  | TyFamLam(i,s,t) -> let* k,phi = (i |:::| s) (infer_kind t) in
                       return (KArr(s,k),phi)

(*
 * TODO: subPotArrow, subPotZero
 * subty t t' = return Φ iff Ψ ; Θ ; Δ ⊢ t <: t' : K ⇒ Φ
 *)
let subty t t' : la_constr checker =
   let rec subty' t t' : la_constr checker =
     match type_head t, type_head t' with
       (TyUnit,TyUnit) -> return Top
     | (TyBool,TyBool) -> return Top
     | (TyNat,TyNat) -> return Top
     | (TyVar a,TyVar b) -> if a.type_fresh_name = b.type_fresh_name
                            then return Top
                            else fail_with (Generic "Incomparable type vars")
     | (TyArr(t1,t2),TyArr(t1',t2')) -> let* phi1 = subty' t1' t1 in
                                        let* phi2 = subty' t2 t2' in
                                        return (conj phi1 phi2)
     | (TyTensor(t1,t2),TyTensor(t1',t2')) -> let* phi1 = subty' t1 t1' in
                                              let* phi2 = subty' t2 t2' in
                                              return (conj phi1 phi2)
     | (TyWith(t1,t2),TyWith(t1',t2')) -> let* phi1 = subty' t1 t1' in
                                          let* phi2 = subty' t2 t2' in
                                          return (conj phi1 phi2)
     | (TyBang t, TyBang t') -> subty' t t'
     | (TySum(t1,t2),TySum(t1',t2')) -> let* phi1 = subty' t1 t1' in
                                        let* phi2 = subty' t2 t2' in
                                        return (conj phi1 phi2)
     | TyIForall(IName i,s,t),TyIForall(IName j,s',t') -> let* _ = sort_eq s s' in
                                              let* phi = (IName i |:::| s) (subty' t (type_idx_subst (idx_var i) j t')) in
                                              return (forall [IName i,s] phi)
     | TyIForall(IWild,s,t),TyIForall(IName j,s',t') -> let* _ = sort_eq s s' in
                                                        let* phi = (IName j |:::| s') (subty' t t') in
                                                        return (forall [IName j,s] phi)
     | TyIForall(IName i,s,t),TyIForall(IWild,s',t') -> let* _ = sort_eq s s' in
                                                        let* phi = (IName i |:::| s) (subty' t t') in
                                                        return (forall [IName i,s] phi)
     | TyIForall(IWild,s,t),TyIForall(IWild,s',t') -> let* _ = sort_eq s s' in subty' t t'
     | TyIExists(IName i,s,t),TyIExists(IName j,s',t') -> let* _ = sort_eq s s' in
                                                          let* phi = (IName i |:::| s) (subty' t (type_idx_subst (idx_var i) j t')) in
                                                         return (forall [IName i,s] phi)
     | TyIExists(IWild,s,t),TyIExists(IName j,s',t') -> let* _ = sort_eq s s' in
                                                        let* phi = (IName j |:::| s') (subty' t t') in
                                                        return (forall [IName j,s] phi)
     | TyIExists(IName i,s,t),TyIExists(IWild,s',t') -> let* _ = sort_eq s s' in
                                                        let* phi = (IName i |:::| s) (subty' t t') in
                                                        return (forall [IName i,s] phi)
     | TyIExists(IWild,s,t),TyIExists(IWild,s',t') -> let* _ = sort_eq s s' in subty' t t'

     | TyTForall(TName a,k,t),TyTForall(TName b,k',t') -> let* _ = kind_eq k k' in (TName a |:::::| k) (subty' t (type_type_subst (ty_var a) b t'))
     | TyTForall(TName a,k,t),TyTForall(TWild,k',t') -> let* _ = kind_eq k k' in (TName a |:::::| k) (subty' t t')
     | TyTForall(TWild,k,t),TyTForall(TName b,k',t') -> let* _ = kind_eq k k' in (TName b |:::::| k) (subty' t t')
     | TyTForall(TWild,k,t),TyTForall(TWild,k',t') -> let* _ = kind_eq k k' in (subty' t t')
         
     | (TyList(it1,t),TyList(it2,t')) -> let* phi = subty' t t' in
                                         return (conj phi (smart_eq (it1,it2)))

     | (TyConj(c,t),TyConj(c',t')) -> let* phi = subty' t t' in
                                      return (conj phi (imp c c'))
     | (TyImplies(c,t),TyImplies(c',t')) -> let* phi = subty' t t' in
                                            return (conj phi (imp c' c))
     | (TyMonad(it1,q,t),TyMonad(it2,p,t')) -> let* phi = subty' t t' in
                                               return (conj_list [phi;smart_eq(it1,it2);smart_leq(q, p)])

     | (TyPot(it1,q,t),TyPot(it2,p,t')) -> let* phi = subty' t t' in
                                           return (conj_list [phi;smart_eq(it1,it2);smart_leq(p, q)])
     | TyConstPot(it,t),TyConstPot(it',t') -> let* phi = subty' t t' in
                                              let c = smart_leq(it',it) in
                                              return @@ conj phi c
     | TyFamLam(IName i,s,t),TyFamLam(IName j,s',t') -> let* _ = sort_eq s s' in
                                                        let* phi = (IName i |:::| s) (subty' t (type_idx_subst (idx_var i) j t')) in
                                                        return (forall [IName i,s] phi)
     | TyFamLam(IWild,s,t),TyFamLam(IName j,s',t') -> let* _ = sort_eq s s' in
                                                      let* phi = (IName j |:::| s) (subty' t t') in
                                                      return (forall [IName j,s] phi)
     | TyFamLam(IName i,s,t),TyFamLam(IWild,s',t') -> let* _ = sort_eq s s' in
                                                      let* phi = (IName i |:::| s) (subty' t t') in
                                                      return (forall [IName i,s] phi)
     | TyFamLam(IWild,s,t),TyFamLam(IWild,s',t') -> let* _ = sort_eq s s' in subty' t t'

     | TyFamApp(t1,j1),TyFamApp(t2,j2) -> let* phi = subty' t1 t2 in
                                          let c = smart_eq(j1,j2) in
                                          return @@ conj c phi
    (*
      cases should be impossible after normalization.
     | TyFamApp(TyFamLam(i,s,t),it),t' -> let* phi1 = check_sort it s in
                                          let tsubst = type_idx_subst it i t in
                                          let* phi2 = subty' tsubst t' in
                                          return @@ conj phi1 phi2
     | t,TyFamApp(TyFamLam(i,s,t'),it) -> let* phi1 = check_sort it s in
                                          let tsubst' = type_idx_subst it i t' in
                                          let* phi2 = subty' t tsubst' in
                                          return @@ conj phi1 phi2
     *)

     | _ -> fail_with (SubtyFail (t,t'))
   in let* t = normalize_type t
   in let* t' = normalize_type t'
   in subty' t t'


let check_hole t : la_constr checker =
  fun (ctx,_) -> raise (CheckHole (t,ctx))

let infer_hole : (la_type * la_constr) inferer =
  fun (ctx,_) -> raise (InferHole ctx)


(*
 * check e t = return Φ iff Ψ ; Θ ; Δ ; Ω ; Γ ⊢ e : t ⇒ Φ, Γ'
*)
let rec check  (e : la_exp) (t : la_type) : la_constr checker =
  let rec check' (e : la_exp) (t : la_type) : la_constr checker =
    match e,type_head t with
    (* FIXME: this is a hack. *)
    (*
    | _,TyAlias a -> let* t = alias_get_type a in check e t
    | _,TyFamApp((_,TyAlias a),j) -> let* t' = alias_get_type a in check e (ty_fam_app t' j)
    *)
  (*  | _,TyFamApp(TyFamLam(i,_,t),j) -> check e (Syntax.type_idx_subst j i t)*)
    | (Binop(b,e1,e2),_) -> check_binop b e1 e2 t
    (* T-lam *)
    | (Lam (x,e),TyArr(t1,t2)) -> (x |:| t1) (check' e t2)

    (* T-tensorI *)
    | (PPair(e1,e2),TyTensor(t1,t2)) -> let* phi1 = check' e1 t1 in
                                        let* phi2 = check' e2 t2 in
                                        return (conj phi1 phi2)
    (* T-tensorE *)
    | (PLet(e,x,y,e'),_) -> let* t',phi1 = infer e in
                            (match type_head t' with
                              TyTensor(t1,t2) -> let* phi2 = (x |:| t1) ((y |:| t2) (check' e' t)) in
                                                  return (conj phi1 phi2)
                            | _ -> fail_with @@ WrongType(e,t',"t1 * t2"))
    (* T-withI *)
    | (NPair(e1,e2),TyWith(t1,t2)) -> (check' e1 t1, check' e2 t2) >>&&= fun (phi1,phi2) ->
                                      return (conj phi1 phi2)
    (* T-expI *)
    | (Bang e,TyBang t) -> pass_ctx (with_ctx (check' e t) Ctx.erase_aff)

    (* T-expE *)
    | (LetBang(e,x,e'),_) -> let* t',phi1 = infer e in
                            (match type_head t' with
                                TyBang t' -> let* phi2 = (x |::| t') (check' e' t) in
                                            return (conj phi1 phi2)
                              | _ -> fail_with @@ WrongType(e,t',"!t"))
    (* T-inl *)
    | (Inl e,TySum(t1,_)) -> check' e t1
    (* T-inr *)
    | (Inr e,TySum(_,t2)) -> check' e t2
    (* T-case *)
    | (SCase(e,x,e1,y,e2),_) -> let* t',phi1 = infer e in
                                (match type_head t' with
                                  TySum(t1,t2) ->
                                    let m1 = (x |:| t1) (check' e1 t) in
                                    let m2 = (y |:| t2) (check' e2 t) in
                                    (m1,m2) >>&&= fun (phi2,phi3) ->
                                    return (conj_list [phi1 ; phi2 ; phi3])
                                | _ -> fail_with @@ WrongType(e,t',"t1 + t2"))
    (* T-fix *)
    | (Fix(x,e),_) -> pass_ctx (with_ctx ((x |::| t) (check' e t)) Ctx.erase_aff)

    (* T-IAbs *)
    | (ILam(IName j,e),TyIForall(IName i,s,t)) -> let* phi = (IName j |:::| s) (check' e (Syntax.type_idx_subst (idx_var j) i t)) in
                                                  return (forall [(IName j,s)] phi)
    (* TODO: which of these binders do we need? *)
    | (ILam(IWild,e),TyIForall(IName i,s,t)) -> let* phi = (IName i |:::| s) (check' e t) in
                                                return (forall [(IName i,s)] phi)
    | (ILam(IName j,e),TyIForall(IWild,s,t)) -> let* phi = (IName j |:::| s) (check' e t) in
                                                return (forall [(IName j,s)] phi)
    | (ILam(IWild,e),TyIForall(IWild,_,t)) -> check' e t
    (* T-TAbs *)
    | (TLam(TName b,e),TyTForall(TName a,k,t)) -> (TName b |:::::| k) (check' e (Syntax.type_type_subst (ty_var b) a t))
    | (TLam(TName b,e),TyTForall(TWild,k,t)) -> (TName b |:::::| k) (check' e t)
    | (TLam(TWild,e),TyTForall(TName a,k,t)) -> (TName a |:::::| k) (check' e t)
    | (TLam(TWild,e),TyTForall(TWild,_,t)) -> check' e t

    (* T-nil *)
    | (Nil,TyList(it,_)) -> let* phi = check_sort it (SoBase SoNat) in
                            return (conj phi (smart_eq(it,IConst (ICNat 0))))
    (* T-cons *)
    | (Cons(e1,e2),TyList(n,t)) -> let* phi1 = check' e1 t in
                                  let  predn = IMinus(n,IConst(ICNat 1)) in
                                  (* TODO: smart constructors for types with nf-status*)
                                  let* phi2 =  check' e2 (type_status t,TyList(predn,t)) in
                                  return (conj_list [(smart_leq(IConst (ICNat 1),n));phi1;phi2])

    (* T-match *)
    | (LCase(e,e1,h,tl,e2),_) -> let* t',phi1 = infer e in
                                (match type_head t' with
                                    TyList(n,t') -> let m1 = check' e1 t in
                                                  let m2 = (h |:| t') (
                                                            (tl |:| (ty_list (IMinus(n,IConst (ICNat 1))) t'))
                                                            (check' e2 t)) in
                                                  let zero = IConst (ICNat 0) in
                                                  let n_eq_zero = smart_eq(n,zero) in
                                                  let n_geq_one = smart_leq(IConst (ICNat 1),n) in
                                                  (n_eq_zero |::::| m1,n_geq_one |::::| m2) >>&&= fun (phi2,phi3) ->
                                                  let phi2' = imp n_eq_zero phi2 in
                                                  let phi3' = imp n_geq_one phi3 in
                                                  return @@ conj_list [phi1 ; phi2' ; phi3']
                                  | _ -> fail_with @@ WrongType(e,t',"List(i,t)"))
    | (NCase(e,e1,n,e2),_) -> let* phi1 = check' e ty_nat in
                              (check' e1 t, (n |:| ty_nat) (check' e2 t)) >>&&= fun (phi2,phi3) ->
                              return (conj_list[phi1;phi2;phi3])
    (* T-existI *)
    (* FIXME *)
    | (Pack(it,e),TyIExists(IName i,s,t)) -> let* phi1 = check_sort it s in
                                      let* phi2 = check' e (Syntax.type_idx_subst it i t) in
                                      return (conj phi1 phi2)
    | (Pack(it,e),TyIExists(IWild,s,t)) -> let* phi1 = check_sort it s in
                                          let* phi2 = check' e t in 
                                          return (conj phi1 phi2)
                                
    | (Pack _,_) -> fail_with @@ WrongType(e,t,"exists t")

    (* T-ExistE*)
    | (Unpack(e,IName j,x,e'),_) -> let* t',phi1 = infer e in
                                    (match type_head t' with
                                        TyIExists(i,s,t') -> let* phi2 = (x |:| Syntax.type_idx_binder_subst (idx_var j) i t') ((IName j |:::| s) (check e' t)) in
                                                            return @@ conj phi1 (forall [(IName j,s)] phi2)
                                      | _ -> fail_with @@ WrongType(e,t,"exists"))
    | (Unpack(e,IWild,x,e'),_) -> let* t',phi1 = infer e in
                            (match type_head t with
                                TyIExists(i,s,t') -> let* phi2 = (x |:| t') (check' e' t) in
                                                    return @@ conj phi1 (forall [(i,s)] phi2)
                            | _ -> fail_with @@ WrongType(e,t',"exists"))

    (* T-CI *)
    | (CLam(e),TyImplies(c,t)) -> let* phi1 = check_wf_constr c in
                                  let* phi2 = c |::::| check' e t in
                                  return @@ conj phi1 (imp c phi2)

    (* T-CandI *)
    | (CPair(e),TyConj(c,t)) -> let* phi1 = check_wf_constr c in
                                let* phi2 = check' e t in
                                return @@ conj_list [c;phi1;phi2]

    | (CPair _,_) -> fail_with @@ WrongType(e,t,"<c,t>")

    (* T-CandE *)
    | (CLet(e,x,e'),_) -> let* t',phi1 = infer e in
                          (match type_head t' with
                              TyConj(c,t') -> let* phi2 = c |::::| ((x |:| t') (check' e' t)) in
                                            return @@ conj phi1 (imp c phi2)
                            | _ -> fail_with @@ WrongType(e,t',"<c,t>"))

    (*T-ret*)
    | (Ret e,TyMonad(it,q,t)) -> let* phi1 = check_sort it (SoBase SoNat) in
                                let* phi2 = check_sort q (SoBase SoPotVec) in
                                let* phi3 = check' e t in
                                return (conj_list [phi1;phi2;phi3])

    (* T-bind *)
    | (Bind(e,x,e'),TyMonad(it1,q,t2)) -> let* t,phi1 = infer e in
                          (match type_head t with
                              TyMonad(it2,p,t1) -> let* phi2 = check_sort q (SoBase SoPotVec) in
                                                  let* phi3 = (x |:| t1) ((check' e' (ty_monad it1 (IMinus(q,p)) t2))) in
                                                  let eq_it12 = smart_eq(it1,it2) in
                                                  let leq = smart_leq(p,q) in
                                                  return (conj_list [eq_it12;leq;phi1;phi2;phi3])
                            | _ -> fail_with @@ WrongType(e,t,"M (i|p) t"))


    (* ERR *)
    | (Bind _,_) -> fail_with (Generic "Cannot bind into non monad")
    (* T-store *)
    | (Store (k,w,e),TyMonad(i,q,(_,TyPot(j,p,t)))) -> 
                                                  let* phi3 = check_sort k (SoBase SoNat) in
                                                  let* phi6 = check_sort w (SoBase SoPotVec) in
                                                  let* phi7 = check' e t in
                                                  let  c1 = smart_leq (p,w) in
                                                  let  c2 = smart_leq (w,q) in
                                                  let  c3 = smart_eq(i,j) in
                                                  let  c4 = smart_eq(j,k) in
                                                  return (conj_list [c1;c2;c3;c4;phi3;phi6;phi7])
    | StoreConst(it,e),TyMonad(_,q,(_,TyConstPot(it',t))) -> let* phi1 = check_sort it (SoBase SoPosReal) in
                                                        let* phi4 = check' e t in
                                                        let c1 = smart_leq(it',it) in
                                                        let c2 = smart_leq(IConstVec it,q) in
                                                        return @@ conj_list [phi1;phi4;c1;c2]

    (* ERR *)
    | (Store _,_) -> fail_with (Generic "cannot store into something other than monad o pot")
    | (StoreConst _,_) -> fail_with (Generic "cannot store into something other than monad o pot")

    (* T-release *)
    | (Release(e,x,e'),TyMonad(i,q,t2)) -> let* t1,phi1 = infer e in
                                              (match type_head t1 with
                                                TyPot(j,p,t1) -> (*let* phi2 = check_sort q (SoBase SoPotVec) in*)
                                                                  let t2' = ty_monad i (IPlus(p,q)) t2 in
                                                                  let* phi3 = (x |:| t1) (check' e' t2') in
                                                                  return @@ conj_list [smart_eq(i,j);phi1;(*phi2;*)phi3]
                                              | TyConstPot(it,t1) -> let* phi2 = check_sort it (SoBase SoPosReal) in
                                                                      let t2' = ty_monad i (IPlus(q,IConstVec it)) t2 in
                                                                      let* phi3 = (x |:| t1) (check' e' t2') in
                                                                      return @@ conj_list[phi1;phi2;phi3]
                                              | _ -> fail_with (Generic "not a potential."))
    (* ERR *)
    | (Release _,_) -> fail_with (Generic "cannot release into non-monad")

    (* TODO: CHECK ME, if correct, re-write declarative rule. *)
    | (Shift (e),TyMonad(it,q,t)) -> let p_it = IMinus(it,IConst (ICNat 1)) in
                                    let t' = ty_monad p_it (IShift q) t in
                                    let* phi1 = check' e t' in
                                    (*let* phi2 = check_sort q (SoBase SoPotVec) in*)
                                    let inotzero = smart_leq(IConst (ICNat 1),it) in
                                    return (conj_list [inotzero;phi1(*;phi2*)])
                                    
    | (Absurd,_) -> return Bot
    | (Ite(e,e1,e2),_) -> let* phi1 = check' e ty_bool in
                          (check' e1 t,check' e2 t) >>&&= fun (phi2,phi3) -> 
                          return (conj_list [phi1;phi2;phi3])
    | Let(e,x,e'),_ -> let* t',phi1 = infer e in
                      let* phi2 = (x |:| t') (check' e' t) in
                      return @@ conj phi1 phi2
    | Hole,_ -> check_hole t


    (* T-sub *)
    | _ -> let* t',phi1 = infer e in
          let* phi2 = subty t' t in
          return @@ (conj phi1 phi2)
  in let* t = normalize_type t in
  check' e t
         

and infer (e : la_exp) : (la_type * la_constr) inferer =
  let infer' (e : la_exp) : (la_type * la_constr) inferer =
          match e with
          (* T-const *)
            Const c -> const_infer c
          (* T-var *)
          | Var x -> var_infer x
          (* T-app *)
          | App(e1,e2) -> let* t,phi1 = infer e1 in
                          (match type_head t with
                            TyArr(t1,t2) -> let* phi2 = (check e2 t1) in
                                            return (t2,conj phi1 phi2)
                          | _ -> fail_with (WrongType(e1,t,"a -> b")))
           (* T-fst *)
          | Fst e -> let* t,phi = infer e in
                     (match type_head t with
                       TyWith(t1,_) -> return (t1,phi)
                     | _ -> fail_with (Generic "Not with type!"))

          (* T-snd *)
          | Snd e -> let* t,phi = infer e in
                     (match type_head t with
                       TyWith(_,t2) -> return (t2,phi)
                     | _ -> fail_with (Generic "Not with type!"))

          (* T-iapp *)
          | IApp (e,it) -> let* t,phi1 = infer e in
                          (match type_head t with
                             TyIForall(i,s,t) -> let* phi2 = check_sort it s in
                             return (type_idx_binder_subst it i t,conj phi1 phi2)
                           | _ -> fail_with (Generic "not a forall"))

          (* T-tapp *)
          | TApp(e,t) -> let* t',phi1 = infer e in
                         (match type_head t' with
                            TyTForall(a,k,t') -> let* phi2 = check_kind t k in
                                                 return (type_type_binder_subst t a t',conj phi1 phi2)
                          | _ -> fail_with (Generic ("not a type forall, instead: " ^ show_la_type t')))

          (* T-CE *)
          | CApp e -> let* t,phi = infer e in
                      (match type_head t with
                         TyImplies(c,t) -> return (t,conj c phi)
                       | _ -> fail_with (Generic "not a forall!"))

          (* T-tick *)
          | Tick (it,p) -> let* phi1 = check_sort it (SoBase SoNat) in
                           let* phi2 = check_sort p (SoBase SoPotVec) in
                           return (ty_monad it p ty_unit,conj phi1 phi2)

          | Store (it,q,e) -> let* t,phi = infer e in
                              let t' = ty_monad it q (ty_pot it q t) in
                              return (t',phi)
          (* T-ann *)
          | Ann (e,t) -> let* phi = check e t in return (t,phi)
          | Hole -> infer_hole
          | _ -> fail_with (InferFail e)

  in let* (t,c) = infer' e in
     let* t' = normalize_type t in
     return (t',c)
     

and check_binop b e1 e2 t =
  match b,type_head t with
    (BopPlus,TyNat) -> let* phi1 = check e1 t in
                       let* phi2 = check e2 t in
                       return (conj_list [phi1;phi2])
  | _ -> fail_with (Generic "Binop fail")

(*
 * Declarations (e,t) are all implicitly typed as box(e) <= !t,
 * and then bound in the ! context.
 *)
let check_decl (d : la_decl) : la_constr checker =
  match d with
    ValDec (_,e,t) -> let* t' = normalize_type t in
                      let* phi1 = with_ctx (check e t') Ctx.erase_aff in
                      let* phi2 = check_kind t KStar in
                      return @@ conj phi1 phi2
  | TyDec (_,t,k) -> check_kind t k
  | IdxDec(_,it,s) -> check_sort it s
  | DoDec(_,it1,it2,t,e) -> let* phi1 = with_ctx (check_sort it1 (SoBase SoNat)) Ctx.erase_idx in
                            let* phi2 = with_ctx (check_sort it2 (SoBase SoPotVec)) Ctx.erase_idx in
                            let* phi3 = check_kind t KStar in
                            let* t = normalize_base_type t in
                            let t' = ty_monad it1 it2 t in
                            let* phi4 = with_ctx (check e t') Ctx.erase_aff in
                            return @@ conj_list [phi1;phi2;phi3;phi4]


let rec check_pgm (p : la_pgm) : (la_constr list) checker =
  match p with
    [] -> return []
  | (ValDec (x,_,t) as d)::ds -> let* c = check_decl d in
                                 let* cs = (Name x |::| t) (check_pgm ds) in
                                 return (c :: cs)
  | (TyDec (a,t,k) as d)::ds -> let* c = check_decl d in
                                let* cs = (TName a |:::::| k) ((a <:::::> (t,k)) (check_pgm ds)) in
                                return (c :: cs)
  | (IdxDec (i,it,s) as d)::ds -> let* c = check_decl d in
                                  let* cs = (IName i |:::| s) ((i <:::> (it,s)) (check_pgm ds)) in
                                  return (c :: cs)
  | (DoDec (x,_,_,t,_) as d) :: ds -> let* c = check_decl d in
                                      let* cs = (Name x |:| t) (check_pgm ds) in
                                      return (c :: cs)