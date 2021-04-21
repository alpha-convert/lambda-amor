(* Joseph Cutler, 2021 *)
open Syntax

module IMap = Map.Make(struct
                        type t = la_idx_var
                        let compare = compare
                      end)


(*
 * ctx: for sort/kind inference.
 * alias_env: maps type/idx aliases to their types
 * idx_env: bound idx vars for nbe
 *)
type eval_env = {ctx : Ctx.t ; alias_env : Env.t}

and 'a eval = eval_env -> 'a

and nf_type = SUnit | SBool | SNat
              | SArr of nf_type * nf_type
              | STensor of nf_type * nf_type
              | SWith of nf_type * nf_type
              | SBang of nf_type
              | SSum of nf_type * nf_type
              | SIForall of la_idx_var_binder * la_sort * nf_type
              | SIExists of la_idx_var_binder * la_sort * nf_type
              | STForall of la_type_var_binder * la_kind * nf_type
              | SList of la_idx_term * nf_type
              | SImplies of la_constr * nf_type
              | SConj of la_constr * nf_type
              | SMonad of la_idx_term * la_idx_term * nf_type
              | SConstPot of la_idx_term * nf_type
              | SPot of la_idx_term * la_idx_term * nf_type
              | SFamLam of la_idx_var_binder * la_sort * nf_type
              | SNe of ne_type
and ne_type = SVar of la_type_var
            | SFamApp of ne_type * la_idx_term


let (let*) (x : 'a eval) (f : 'a -> 'b eval) : 'b eval = fun env -> f (x env) @@ env
let return (x : 'a) : 'a eval = fun _ -> x

exception NormalizeFreshenFail of string

let refreshen_type (t : la_type) : la_type eval =
  (* eval env to fresh env *)
  let ee_to_fe (e : eval_env) : Freshen.fresh_env =
    let affs = List.map (fun (x,_) -> (x.ident_source_name,x)) @@ Ctx.VMap.bindings e.ctx.aff_ctx in
    let exps = List.map (fun (x,_) -> (x.ident_source_name,x)) @@ Ctx.VMap.bindings e.ctx.exp_ctx in
    let idents = affs @ exps in
    let ident_env : la_ident Freshen.FMap.t = List.fold_right (fun (x,x') c -> Freshen.FMap.add (Freshen.lift_key x) x' c) idents Freshen.FMap.empty in
    let idx_tag i =
      match i.idx_fresh_name with
        `Alias _ -> `Alias
      | `Fresh _ -> `Bound
      | `Unfreshened  -> raise (NormalizeFreshenFail "Attepted to refreshen an unfreshened type var")
    in
    (* these are all inherited, I think *)
    let idxs_from_ctx : (string * (la_idx_var * [`Alias | `Bound])) list = List.map (fun (x,_) -> (x.idx_source_name,(x,idx_tag x))) @@ Ctx.IMap.bindings e.ctx.idx_ctx in
    let idxs_from_env : (string * (la_idx_var * [`Alias | `Bound])) list = List.map (fun (x,_) -> (Env.from_key x,({idx_fresh_name = `Alias (Env.from_key x);idx_source_name=(Env.from_key x)},`Alias))) @@ Env.TMap.bindings e.alias_env.idx_env in
    let idxs = idxs_from_ctx @ idxs_from_env in
    let idx_var_env : (la_idx_var * [`Alias | `Bound]) Freshen.FMap.t = List.fold_right (fun (x,x') c -> Freshen.FMap.add (Freshen.lift_key x) x' c) idxs Freshen.FMap.empty in
    let type_tag i =
      match i.type_fresh_name with
        `Alias _ -> `Alias
      | `Fresh _ -> `Bound
      | `Unfreshened  -> raise (NormalizeFreshenFail "Attepted to refreshen an unfreshened type var")
    in
    let typs_from_ctx : (string * (la_type_var * [`Alias | `Bound])) list = List.map (fun (x,_) -> (x.type_source_name,(x,type_tag x))) @@ Ctx.TMap.bindings e.ctx.typ_ctx in
    let typs_from_env : (string * (la_type_var * [`Alias | `Bound])) list = List.map (fun (x,_) -> (Env.from_key x,({type_fresh_name = `Alias (Env.from_key x);type_source_name=(Env.from_key x)},`Alias))) @@ Env.TMap.bindings e.alias_env.typ_env in
    let typs = typs_from_ctx @ typs_from_env in
    let type_var_env : (la_type_var * [`Alias | `Bound]) Freshen.FMap.t = List.fold_right (fun (x,x') c -> Freshen.FMap.add (Freshen.lift_key
     x) x' c) typs Freshen.FMap.empty in
    {ident_env = ident_env; idx_var_env = idx_var_env;type_var_env=type_var_env}
  in fun e -> Freshen.freshen_type t (ee_to_fe e)


(*
let bind_idx_var i s it env =
  {env with idx_env = IMap.add i it env.idx_env; ctx = Ctx.idx_bind (i,s) env.ctx}

let (|:::|) i s m =
  fun env -> m @@ {env with ctx = Ctx.idx_bind (i,s) env.ctx}

let (|:::::|) a k m =
  fun env -> m @@ {env with ctx = Ctx.type_bind (a,k) env.ctx}
  *)

(*
exception Unimplemented
exception Fail of string
*)

exception Impossible


let rec s_type_idx_subst (it : la_idx_term) (i : la_idx_var) (st : nf_type) : nf_type =
  match (st : nf_type) with
| SUnit -> SUnit
| SBool -> SBool
| SNat -> SNat
| SArr (s1,s2) -> SArr(s_type_idx_subst it i s1,s_type_idx_subst it i s2)
| STensor(s1,s2) -> STensor(s_type_idx_subst it i s1,s_type_idx_subst it i s2)
| SWith(s1,s2) -> SWith(s_type_idx_subst it i s1,s_type_idx_subst it i s2)
| SBang s -> SBang(s_type_idx_subst it i s)
| SSum(s1,s2) -> SSum(s_type_idx_subst it i s1,s_type_idx_subst it i s2)
| SIForall (j,s,st) -> SIForall(j,s,s_type_idx_subst it i st)
| SIExists(j,s,st) -> SIExists(j,s,s_type_idx_subst it i st)
| STForall (a,k,s) -> STForall(a,k,s_type_idx_subst it i s)
| SList (it',s) -> SList(idx_idx_subst it i it',s_type_idx_subst it i s)
| SImplies (c,s) -> SImplies(constr_idx_subst it i c,s_type_idx_subst it i s)
| SConj (c,s) -> SImplies(constr_idx_subst it i c,s_type_idx_subst it i s)
| SMonad (it1,it2,s) -> SMonad(idx_idx_subst it i it1, idx_idx_subst it i it2,s_type_idx_subst it i s)
| SConstPot (it',s) -> SConstPot(idx_idx_subst it i it',s_type_idx_subst it i s)
| SPot (it1,it2,s) -> SPot(idx_idx_subst it i it1, idx_idx_subst it i it2,s_type_idx_subst it i s)
| SFamLam(j,s',st) -> SFamLam(j,s',s_type_idx_subst it i st)
| SNe (s) -> SNe(s_ne_type_idx_subst it i s)
and s_ne_type_idx_subst it i st =
  match st with
    SVar x -> SVar x
  | SFamApp(st,it') -> SFamApp(s_ne_type_idx_subst it i st, idx_idx_subst it i it')

let s_type_idx_binder_subst it i st =
  match i with
    IWild -> st
  | IName i -> s_type_idx_subst it i st

exception NormalizeUnboundTypeAlias of la_type_var
let lookup_ty_alias (a : la_type_var) : (la_type * la_kind) eval =
  fun env -> match Env.type_var_lookup env.alias_env a.type_source_name with
               Some(t,k) -> (t,k)
            | _ -> raise (NormalizeUnboundTypeAlias a)
  

let rec eval_type (t : la_type) : nf_type eval =
  match type_head t with
    TyUnit -> return SUnit
  | TyBool -> return SBool
  | TyNat -> return SNat
  | TyVar x -> return (SNe (SVar x))
  | TyAlias a -> let* (t',_) = lookup_ty_alias a in
                 let* t'' = refreshen_type t' in
                 eval_type t''
  | TyArr(t1,t2) -> let* t1' = eval_type t1 in
                    let* t2' = eval_type t2 in
                    return @@ SArr(t1',t2')
  | TyTensor(t1,t2) -> let* t1' = eval_type t1 in
                      let* t2' = eval_type t2 in
                      return @@ STensor(t1',t2')
  | TyWith(t1,t2) -> let* t1' = eval_type t1 in
                     let* t2' = eval_type t2 in
                     return @@ SWith(t1',t2')
  | TyBang(t) -> let* t' = eval_type t in return @@ SBang t'
  | TySum(t1,t2) -> let* t1' = eval_type t1 in
                     let* t2' = eval_type t2 in
                    return @@ SSum(t1',t2')
  | TyIForall(i,s,t) -> let* t' = eval_type t in return @@ SIForall(i,s,t')
  | TyIExists(i,s,t) -> let* t' = eval_type t in return @@ SIExists(i,s,t')
  | TyTForall(a,k,t) -> let* t' = eval_type t in return @@ STForall(a,k,t')
  | TyList(it,t) -> let* t' = eval_type t in return @@ SList(it,t')
  | TyImplies(c,t) -> let* t' = eval_type t in return @@ SImplies(c,t')
  | TyConj(c,t) -> let* t' = eval_type t in return @@ SConj(c,t')
  | TyMonad(it1,it2,t) -> let* t' = eval_type t in return @@ SMonad(it1,it2,t')
  | TyPot(it1,it2,t) -> let* t' = eval_type t in return @@ SPot(it1,it2,t')
  | TyConstPot(it,t) -> let* t' = eval_type t in return @@ SConstPot(it,t')
  | TyFamLam(i,s,t) -> let* t' = eval_type t in return @@ SFamLam(i,s,t')
  | TyFamApp(t,it) -> let* t' = eval_type t in
                      (match t' with
                        SFamLam(i,_,t) -> return @@ s_type_idx_binder_subst it i t
                      | SNe(t') -> return @@ SNe (SFamApp(t',it))
                      | _ -> raise Impossible)  

let rec read_back_nf_type (st : nf_type) : la_type =
  match st with
| SUnit -> (Nf,TyUnit)
| SBool -> (Nf,TyBool)
| SNat -> (Nf,TyNat)
| SArr (st1,st2) -> (Nf,TyArr(read_back_nf_type st1,read_back_nf_type st2))
| STensor(st1,st2) -> (Nf,TyTensor(read_back_nf_type st1,read_back_nf_type st2))
| SWith(st1,st2) -> (Nf,TyWith(read_back_nf_type st1,read_back_nf_type st2))
| SSum(st1,st2) -> (Nf,TySum(read_back_nf_type st1,read_back_nf_type st2))
| SBang st -> (Nf,TyBang(read_back_nf_type st))
| SIForall(i,s,st) -> (Nf,TyIForall(i,s,read_back_nf_type st))
| SIExists(i,s,st) -> (Nf,TyIExists(i,s,read_back_nf_type st))
| STForall(a,k,st) -> (Nf,TyTForall(a,k,read_back_nf_type st))
| SList (it,st) -> (Nf,TyList(it,read_back_nf_type st))
| SImplies(c,st) -> (Nf,TyImplies(c,read_back_nf_type st))
| SConj(c,st) -> (Nf,TyConj(c,read_back_nf_type st))
| SMonad(it1,it2,st) -> (Nf,TyMonad(it1,it2,read_back_nf_type st))
| SConstPot(it,st) -> (Nf,TyConstPot(it,read_back_nf_type st))
| SPot(it1,it2,st) -> (Nf,TyPot(it1,it2,read_back_nf_type st))
| SFamLam(i,s,st) -> (Nf,TyFamLam(i,s,read_back_nf_type st))
| SNe st -> read_back_ne_type st

and read_back_ne_type st =
  match st with
    SVar x -> (Ne,TyVar x)
  | SFamApp(st,it) -> (Ne,TyFamApp(read_back_ne_type st, it))
let from_tycheck (ctx,env) = {alias_env = env; (*idx_env = IMap.empty;*) ctx = ctx}

let normalize_type ((c,e) : Ctx.t * Env.t) (t : la_type) : la_type =
  let st = eval_type t (from_tycheck (c,e)) in read_back_nf_type st