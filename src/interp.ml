(* Joseph Cutler, 2021 *)
open Syntax

(* Both maps keyed by fresh names *)
module VMap = Map.Make(struct
                        type t = string
                        let compare = compare
                      end)

module IMap = Map.Make(struct
                        type t = string
                        let compare = compare
                      end)


type env = {thunk_env : thunk VMap.t ; idx_env : idx_thunk IMap.t}
and thunk = Thunk of env * la_exp | Value of value


and value = VNat of int | VBool of bool | VUnit | VNil
          | VCons of value * value
          | VLamClos of env * la_ident_binder * la_exp
          | VPPair of value * value
          | VNPair of value * value
          | VInl of value
          | VInr of value
          | VBangClos of env * la_exp
          | VILamClos of env * la_idx_var_binder * la_exp
          | VTLamClos of env * la_exp
          (* Need to make a choice here- existential packages are lazy and not observable *)
          | VPackClos of env * la_idx_term * la_exp
          | VCLamClos of env * la_exp
          (* So are constraint types *)
          | VConjClos of env * la_exp

          | VMonadic of env * maction
and maction = MRet of la_exp
            | MBind of la_exp * la_ident_binder * la_exp
            | MTick of la_idx_term * la_idx_term
            | MStore of la_idx_term * la_idx_term * la_exp
            | MStoreConst of la_idx_term * la_exp
            | MRelease of la_exp * la_ident_binder * la_exp
            | MShift of la_exp
and cost = float

and 'a interp = env -> 'a
and 'a withcost = cost * 'a

and idx_pvec_value = float list
and idx_nat_value = int
and idx_real_value = float

and idx_value = IVPVec of idx_pvec_value | IVNat of idx_nat_value | IVReal of idx_real_value
              | IVLamClos of env * la_idx_var_binder * la_idx_term
and idx_thunk = IThunk of env * la_idx_term | IValue of idx_value

let empty = {thunk_env = VMap.empty ; idx_env = IMap.empty}

let pp_env {thunk_env = te; idx_env = ie} =
  let fst (x,_) = x in
  let pp xs = "[" ^ String.concat "," xs ^ "]" in
  let tel = List.map fst @@ VMap.bindings te in
  let iel = List.map fst @@ IMap.bindings ie in
  (pp tel) ^ (pp iel)


let (let*) (m : 'a interp) (f : 'a -> 'b interp) : 'b interp =
  fun env -> f (m env) env

let return (x : 'a) : 'a interp = fun _ -> x

let cur_env : env interp =
  fun e -> e

let with_env (rho : env) (m : 'a interp) : 'a interp =
  fun _ -> m rho

exception Fail
exception UnfreshenedVarExn of [`Id of la_ident | `Idx of la_idx_var]
exception VarNotFound of la_ident
exception IdxVarNotFound of la_idx_var

let lookup_thunk (x : la_ident) : thunk interp =
  match x.ident_fresh_name with
    (`Fresh s | `TopLevel s) ->
      fun env -> (match VMap.find_opt s env.thunk_env with
                None -> raise (VarNotFound x)
              | Some t -> t)
  | _ -> raise (UnfreshenedVarExn (`Id x))

let lookup_idx_thunk (x : la_idx_var) : idx_thunk interp =
  match x.idx_fresh_name with
    (`Fresh s | `Alias s) ->
      fun env -> (match IMap.find_opt s env.idx_env with
                None -> raise (IdxVarNotFound x)
              | Some t -> t)
  | _ -> raise (UnfreshenedVarExn (`Idx x))


let (>->) (i : la_idx_var_binder) (vit : idx_value) (m : 'a interp) : 'a interp =
  match i with
    IWild -> m
  | IName{idx_fresh_name = (`Fresh s | `Alias s) ; _} ->
      fun env ->
      let ienv = IMap.add s (IValue vit) env.idx_env in
      m {env with idx_env = ienv}
  | IName i -> raise (UnfreshenedVarExn (`Idx i))

let (|>->) (i : la_idx_var_binder) ((rho,it) : env * la_idx_term) (m : 'a interp) : 'a interp =
  match i with
    IWild -> m
  | IName {idx_fresh_name = (`Fresh s | `Alias s) ;_} -> 
      fun env ->
      let ienv = IMap.add s (IThunk (rho,it)) env.idx_env in
      m {env with idx_env = ienv}
  | IName i -> raise (UnfreshenedVarExn (`Idx i))


let (|->) (x : la_ident_binder) (v : value) (m : 'a interp) : 'a interp =
  match x with
    Wild -> m
  | Name {ident_fresh_name = (`Fresh s | `TopLevel s);_} ->
      fun env ->
      let tenv = VMap.add s (Value v) env.thunk_env in
      m {env with thunk_env = tenv}
 | Name x -> raise (UnfreshenedVarExn (`Id x))

let (||->) (x : la_ident_binder) ((rho,e) : env * la_exp) (m : 'a interp) : 'a interp =
  match x with
    Wild -> m
  | Name {ident_fresh_name = (`Fresh s | `TopLevel s);_} ->
      fun env ->
      let tenv = VMap.add s (Thunk (rho,e)) env.thunk_env in
      m {env with thunk_env = tenv}
  | Name x -> raise (UnfreshenedVarExn (`Id x))




exception HitAbsurd
exception HitHole
exception RuntimeTyError
exception SumUmplemented
exception Unimplemented

let rec eval_pure (e : la_exp) : value interp =
  match e with
| Const (NConst n) -> return @@ VNat n
| Const (BConst b) -> return @@ VBool b
| Const (UConst) -> return VUnit
| Var x -> let* t = lookup_thunk x in eval_thunk t
| Binop (BopPlus, e1, e2) -> let* v1 = eval_pure e1 in
                             let* v2 = eval_pure e2 in
                             return @@ value_plus v1 v2
| Lam (x,e) -> let* env = cur_env in 
               return @@ VLamClos(env,x,e)
| App (e1,e2) -> let* v = eval_pure e1 in value_apply v e2
| Ann (e,_) -> eval_pure e
| PPair (e1,e2) -> let* v1 = eval_pure e1 in
                   let* v2 = eval_pure e2 in
                  return @@ VPPair(v1,v2)
| PLet (e, x, y, e') -> let* v1,v2 = eval_ppair e in
                        (x |-> v1) ((y |-> v2) (eval_pure e'))
(* Negative pairs are evaluated because this is pure evaluation
   which incurs no cost *)
| NPair (e1,e2) -> let* v1 = eval_pure e1 in
                   let* v2 = eval_pure e2 in
                  return @@ VNPair(v1,v2)
| Fst e -> let* (v,_) = eval_npair e in return v
| Snd e -> let* (_,v) = eval_npair e in return v
| Bang e -> let* env = cur_env in return @@ VBangClos(env,e)
| LetBang (e,x,e') -> let* th = eval_bang e in
                      (x ||-> th) (eval_pure e')
| Inl e -> let* v = eval_pure e in return @@ VInl v
| Inr e -> let* v = eval_pure e in return @@ VInr v
| SCase (e, x, e1, y, e2) -> let* sv = eval_sum e in
                             (match sv with
                                `Inl v -> (x |-> v) (eval_pure e1)
                              | `Inr v -> (y |-> v) (eval_pure e2))
| NCase (e, e1, n, e2) -> let* v = eval_nat e in
                          (match v with
                             `Zero -> eval_pure e1
                            | `Succ v -> (n |-> v) (eval_pure e2)
                          )
| Fix (x,e') -> let* env = cur_env in (x ||-> (env,e)) (eval_pure e')
| ILam (i,e) -> let* env = cur_env in return @@  VILamClos(env,i,e)
| IApp (e1,it) -> let* v = eval_pure e1 in
                  value_iapply v it
| TLam (_,e) -> let* env = cur_env in return @@ VTLamClos(env,e)
| TApp (e, _) -> let* v = eval_pure e in value_tapply v
| Nil -> return VNil
| Cons (e1,e2) -> let* v1 = eval_pure e1 in
                  let* v2 = eval_pure e2 in
                  return @@ VCons(v1,v2)
| LCase (e, e1, h, t, e2) -> let* vl = eval_list e in
                             (match vl with
                                `Nil -> eval_pure e1
                              | `Cons(vh,vt) -> (h |-> vh) ((t |-> vt) (eval_pure e2))
                             )
| Pack (iterm,e) -> let* env = cur_env in return @@ VPackClos(env,iterm,e)
| Unpack (e, i, x, e') -> let* (it_th,th) = eval_package e in
                          (i |>-> it_th) ((x ||-> th) (eval_pure e'))
| CLam e -> let* env = cur_env in return @@ VCLamClos (env,e)
| CApp e -> let* v = eval_pure e in value_capply v
| CPair e -> let* env = cur_env in return @@ VConjClos(env,e)
| CLet (e, x, e') -> let* th = eval_conj e in
                     (x ||-> th) (eval_pure e')
| Ret e -> let* env = cur_env in return @@ VMonadic (env,MRet e)
| Bind (e, x, e') -> let* env = cur_env in return @@ VMonadic(env,MBind(e,x,e'))
| Tick (it1,it2) -> let* env = cur_env in return @@ VMonadic(env,MTick(it1,it2))
| Store (it1,it2,e) -> let* env = cur_env in return @@ VMonadic(env,MStore(it1,it2,e))
| StoreConst (it,e) -> let* env = cur_env in return @@ VMonadic(env,MStoreConst(it,e))
| Release (e,x,e') -> let* env = cur_env in return @@ VMonadic(env,MRelease(e,x,e'))
| Shift e -> let* env = cur_env in return @@ VMonadic(env,MShift(e))
| Absurd -> raise HitAbsurd
| Ite (e, e1, e2) -> let* b = eval_bool e in
                     if b then eval_pure e1 else eval_pure e2
| Let (e, x, e') -> let* env = cur_env in
                    (x ||-> (env,e)) (eval_pure e')
| Hole -> raise HitHole

and value_plus (e1 : value) (e2 : value) : value =
  match e1,e2 with
    VNat n1,VNat n2 -> VNat (n1 + n2)
  | _ -> raise Unimplemented

(* Destruct v and then continue*)
(*
*
* FIXME FIXME FIXME
* Huge possible error here- order of with_env and binding seems wonky.
*
*
*
*
*)
and value_apply (v : value) (e' : la_exp) : value interp =
  match v with
    VLamClos(env,x,e) -> let* env' = cur_env in
                         (with_env env ((x ||-> (env',e')) (eval_pure e)))
  | _ -> raise RuntimeTyError

and value_iapply (v : value) (it : la_idx_term) : value interp =
  match v with
    VILamClos(env,i,e) -> let* env' = cur_env in
                           (with_env env ( (i |>-> (env',it)) (eval_pure e)))
  | _ -> raise RuntimeTyError

and value_tapply (v : value) : value interp =
  match v with
    VTLamClos(env,e) -> with_env env (eval_pure e)
  | _ -> raise RuntimeTyError

and value_capply (v : value) : value interp =
  match v with
    VCLamClos(env,e) -> with_env env (eval_pure e)
  | _ -> raise RuntimeTyError

(* Run a value just recieved from a variable lookup.*)
and eval_thunk = function
  Thunk(env,e) -> with_env env (eval_pure e)
| Value v -> return v

(* eval_* functions run the term and then peel off the desired constructor *)
and eval_ppair (e : la_exp) : (value * value) interp =
  let* v = eval_pure e in
  match v with
    VPPair(v1,v2) -> return (v1,v2)
  | _ -> raise RuntimeTyError

and eval_npair (e : la_exp) : (value * value) interp =
  let* v = eval_pure e in
  match v with
    VNPair(v1,v2) -> return (v1,v2)
  | _ -> raise RuntimeTyError

and eval_bang (e : la_exp) : (env * la_exp) interp =
  let* v = eval_pure e in 
  match v with
    VBangClos(rho,e) -> return (rho,e)
  | _ -> raise RuntimeTyError

and eval_sum (e : la_exp) : [`Inl of value | `Inr of value] interp =
  let* v = eval_pure e in
  match v with
    VInl(v) -> return @@ `Inl v
  | VInr(v) -> return @@ `Inr v
  | _ -> raise RuntimeTyError

and eval_nat (e : la_exp) : [`Zero | `Succ of value] interp =
  let* v = eval_pure e in
  match v with
    VNat 0 -> return `Zero
  | VNat n -> return @@ `Succ (VNat (n-1))
  | _ -> raise RuntimeTyError

and eval_list (e : la_exp) : [`Nil | `Cons of value * value] interp =
  let* v = eval_pure e in
  match v with
    VNil -> return `Nil
  | VCons(v1,v2) -> return @@ `Cons(v1,v2)
  | _ -> raise RuntimeTyError

and eval_package (e : la_exp) : ((env * la_idx_term) * (env * la_exp)) interp =
  let* v = eval_pure e in
  match v with
    VPackClos(rho,it,e) -> return ((rho,it),(rho,e))
  | _ -> raise RuntimeTyError

and eval_conj (e : la_exp) : (env * la_exp) interp =
  let* v = eval_pure e in
  match v with
    VConjClos(rho,e) -> return (rho,e)
  | _ -> raise RuntimeTyError

and eval_bool (e : la_exp) : bool interp =
  let* v = eval_pure e in
  match v with
    VBool b -> return b
  | _ -> raise RuntimeTyError

let eval_monad (e : la_exp) : (env * maction) interp =
  let* v = eval_pure e in
  match v with
    VMonadic(env,m) -> return (env,m)
  | _ -> raise RuntimeTyError


let rec eval_idx_term (it : la_idx_term) : idx_value interp =
  match it with
  IConst (ICNat n) -> return @@ IVNat n
| IConst (ICReal r) -> return @@ IVReal r
| IConst (ICPVec rs) -> return @@ IVPVec rs
| (IVar x | IAlias x) -> let* it_th = lookup_idx_thunk x in eval_idx_thunk it_th
| IPlus (it1,it2) -> let* v1 = eval_idx_term it1 in
                     let* v2 = eval_idx_term it2 in
                     idx_value_add v1 v2
| IMinus (it1, it2) -> let* v1 = eval_idx_term it1 in
                       let* v2 = eval_idx_term it2 in
                       idx_value_sub v1 v2
| IMult (ic, it) -> let* v = eval_idx_term it in
                    idx_value_mult ic v
| IShift it -> let* v = eval_idx_term it in idx_value_shift v
| IFamLam (i, _, t) -> let* env = cur_env in return @@ IVLamClos (env,i,t)
| IFamApp (it1, it2) -> let* vit1 = eval_idx_term it1 in
                        let* vit2 = eval_idx_term it2 in
                         idx_value_apply vit1 vit2
(* SUM unimplemented *)
| ISum (i,f,lb,ub) -> let* nlb = eval_idx_nat lb in
                      let* nub = eval_idx_nat ub in
                      eval_idx_sum i f nlb nub
| IConstVec it -> let* v = eval_idx_term it in
                  idx_value_constvec v
| INtoR _ -> raise Unimplemented

and zip_extend xs ys =
    match xs,ys with
      [],[] -> []
    | [],ys -> List.map (fun y -> (0.0,y)) ys
    | xs,[]-> List.map (fun x -> (x,0.0)) xs
    | x::xs,y::ys -> (x,y) :: (zip_extend xs ys)

and add_pvecs ps1 ps2 =
  List.map (fun (x,y) -> x -. y) (zip_extend ps1 ps2)

and sub_pvecs ps1 ps2 =
  List.map (fun (x,y) -> x +. y) (zip_extend ps1 ps2)
  
and idx_value_add v1 v2 =
  match v1,v2 with
    IVNat n1, IVNat n2 -> return @@ IVNat (n1 + n2)
  | IVReal r1, IVReal r2 -> return @@ IVReal (r1 +. r2)
  | IVPVec ps1, IVPVec ps2 -> return @@ IVPVec (add_pvecs ps1 ps2)
  | _ -> raise RuntimeTyError

and idx_value_sub v1 v2 =
  match v1,v2 with
    IVNat n1, IVNat n2 -> return @@ IVNat (n1 - n2)
  | IVReal r1, IVReal r2 -> return @@ IVReal (r1 -. r2)
  | IVPVec ps1, IVPVec ps2 -> return @@ IVPVec (sub_pvecs ps1 ps2)
  | _ -> raise RuntimeTyError

and idx_value_mult ic v =
  match ic,v with
    ICNat n1, IVNat n2 -> return @@ IVNat (n1 * n2)
  | ICReal r1, IVReal r2 -> return @@ IVReal (r1 *. r2)
  | ICReal r, IVPVec ps -> return @@ IVPVec (List.map (fun p -> r *. p) ps)
  | _ -> raise RuntimeTyError

and idx_value_shift _ =
 raise Unimplemented

and idx_value_constvec v =
  match v with
    IVReal r -> return @@ IVPVec [r]
  | _ -> raise RuntimeTyError

and idx_value_apply v vit =
  match v with
    (* TODO: check this... order of with_env and binding*)
    IVLamClos(env,i,it) -> (i >-> vit) (with_env env (eval_idx_term it))
  | _ -> raise RuntimeTyError


and eval_idx_thunk = function
  IThunk(env,it) -> with_env env (eval_idx_term it)
| IValue v -> return v

and eval_idx_nat (e : la_idx_term) : idx_nat_value interp =
  let* v = eval_idx_term e in
  match v with
    IVNat n -> return n
  | _ -> raise RuntimeTyError

and eval_idx_real (e : la_idx_term) : idx_real_value interp =
  let* v = eval_idx_term e in
  match v with
    IVReal r -> return r
  | _ -> raise RuntimeTyError

and eval_idx_pvec (e : la_idx_term) : idx_pvec_value interp =
  let* v = eval_idx_term e in
  match v with
    IVPVec ps -> return @@ ps
  | _ -> raise RuntimeTyError

and eval_idx_sum _ _ (_ : int) (_ : int) =
  raise SumUmplemented

(* TODO *)
let rec binomial n k = if n = k then 1 else ((binomial (n-1) k) * n) / (n-k)

let compute_cost (n : idx_nat_value) (ps : idx_pvec_value) : cost =
  List.fold_right (fun x y -> x +. y)
  (List.mapi (fun i r -> r *. (Int.to_float @@ binomial n i)) ps)
  0.0

let rec run_monad (m : maction) : value withcost interp =
  match m with
    MRet e -> let* v = eval_pure e in return (0.0,v)
  | MBind (e, x, e') -> let* (env,m) = eval_monad e in
                        let* (c1,v1) = with_env env (run_monad m) in
                        let* (env',m') = (x |-> v1) (eval_monad e') in
                        let* (c2,v2) = with_env env' (run_monad m') in
                        return (c1 +. c2,v2)
  | MTick (it1,it2) -> let* n = eval_idx_nat it1 in
                       let* p = eval_idx_pvec it2 in
                       return (compute_cost n p,VUnit)
  | MStore (_, _, e) -> let* v = eval_pure e in return (0.0,v)
  | MStoreConst (_, e) -> let* v = eval_pure e in return (0.0,v)
  | MRelease (e,x,e') -> let* v = eval_pure e in
                         let* (env,m) = (x |-> v) (eval_monad e') in
                         with_env env (run_monad m)
  | MShift e -> let* (env,m) = eval_monad e in with_env env (run_monad m)

type dodec_result = {name : la_ident; 
                     return_val : value;
                     actual_cost : cost; 
                     static_cost : cost}

let rec run_pgm (p : la_pgm) : (dodec_result list) interp =
  match p with
    [] -> return []
  | ValDec (x, e, _) :: ds -> let* env = cur_env in (Name x ||-> (env,e)) (run_pgm ds)
  | TyDec (_, _, _) :: ds -> run_pgm ds
  | IdxDec (i, it, _) :: ds -> let* env = cur_env in (IName i |>-> (env,it)) (run_pgm ds)
  | DoDec (x, it1, it2, _, e) :: ds -> let* (env,m) = eval_monad e in
                                       let* (c,v) = with_env env (run_monad m) in
                                       let* n = eval_idx_nat it1 in
                                       let* p = eval_idx_pvec it2 in
                                       let c' = compute_cost n p in
                                       let* l = run_pgm ds in
                                       let r = {name = x; 
                                                return_val = v;
                                                actual_cost = c;
                                                static_cost = c'} in
                                       return (r :: l)

let run (p : la_pgm) = run_pgm p empty

let rec pp_value (v : value) : string =
  match v with
| VNat n -> Int.to_string n
| VBool b -> Bool.to_string b
| VUnit -> "()"
| VNil -> "[]"
| VCons (v,vs) -> pp_value v ^ " :: " ^ pp_value vs
| VLamClos (_, _, _) -> "<closure>"
| VPPair (v1,v2) -> "<<" ^ pp_value v1 ^ "," ^ pp_value v2 ^ ">>"
| VNPair (v1,v2) -> "(" ^ pp_value v1 ^ "," ^ pp_value v2 ^ ")"
| VInl v -> "inl(" ^ pp_value v ^ ")"
| VInr v -> "inr(" ^ pp_value v ^ ")"
| VBangClos (_, _) -> "<closure>"
| VILamClos (_, _, _) -> "<closure>"
| VTLamClos (_, _) -> "<closure>"
| VPackClos (_, _, _) -> "<closure>"
| VCLamClos (_, _) -> "<closure>"
| VConjClos (_, _) -> "<closure>"
| VMonadic (_, _) -> "<monadic action>"