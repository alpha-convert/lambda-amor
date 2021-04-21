(* Joseph Cutler, 2021 *)
open Syntax

type elab_idx_var = string

let ivar_to_elab_var {idx_fresh_name = x; idx_source_name = y} =
  match x with
    `Fresh x -> x
  | `Alias x -> x
  | `Unfreshened -> raise (UnfreshenedVarExn y)

type elab_base_sort = ESoNat | ESoPosReal
type elab_sort = ESoBase of elab_base_sort | ESoArr of elab_base_sort * elab_sort

type elab_idx_const = ENat of int | EReal of float

type elab_idx_term = EConst of elab_idx_const | EVar of elab_idx_var
                   | EPlusNat of elab_idx_term * elab_idx_term
                   | EPlusReal of elab_idx_term * elab_idx_term
                   | EMinusNat of elab_idx_term * elab_idx_term
                   | EMinusReal of elab_idx_term * elab_idx_term
                   | EMultNat of int * elab_idx_term
                   | EMultReal of float * elab_idx_term
                   | EFamLam of elab_idx_var * elab_base_sort * elab_idx_term
                   | EFamApp of elab_idx_term * elab_idx_term
                   | ESumReal of elab_idx_var * elab_idx_term * elab_idx_term * elab_idx_term
                   | ESumNat of elab_idx_var * elab_idx_term * elab_idx_term * elab_idx_term
                   | ENtoR of elab_idx_term

(*
 * Elaborated constraints-- desugar into linear equations.
 *)
type elab_constr = ETop | EBot | EConj of elab_constr list
                 | EImp of elab_constr * elab_constr
                 | EForall of elab_idx_var * elab_sort * elab_constr
                 | EExists of elab_idx_var * elab_sort * elab_constr
                 | EEqNat of elab_idx_term * elab_idx_term
                 | ELeqNat of elab_idx_term * elab_idx_term
                 | ELtNat of elab_idx_term * elab_idx_term
                 | EEqReal of elab_idx_term * elab_idx_term
                 | ELeqReal of elab_idx_term * elab_idx_term
                 | ELtReal of elab_idx_term * elab_idx_term

module IMap  = Map.Make(struct
                          type t = la_idx_var
                          let compare = compare
                        end)

(*
 * TODO: If need be, factor this into another error monad.
 *)
type 'a elab = (la_sort IMap.t) * (la_idx_term IMap.t) -> [`Ok of 'a | `Fail of string]

let return (x : 'a) : 'a elab =
  fun _ -> `Ok x

let fail_with s = fun _ -> `Fail s

let (>>=) (x : 'a elab) (f : 'a -> 'b elab) : 'b elab =
  fun ctx -> match (x ctx) with
               `Ok y -> (f y) ctx
             | `Fail s -> (fail_with s) ctx

let (let*) x f = x >>= f

let (|:::|) x s m = 
  match x with
    IWild -> m
  | IName x -> fun (ctx,e) -> m (IMap.add x s ctx,e)

let (|->) (i : la_idx_var) (eit : la_idx_term) (m : 'a elab) : 'a elab = 
  fun (c,env) -> m (c,IMap.add i eit env)

(*
 * Constraint elab phases:
 * 1. Extend potential vectors to length k (degree k - 1)
 *    (extend_pvecs)
 * 2. Elaborate pvec terms
 *    (elab_pvecs)
 * 3. Unfold quantifiers
 *    (unfold binders)
 * 4. Turn to elab type
 *    (transform_to_elab)
 *)

(*
 * Invariant: k >= max size of a pvec literal in c.
 *)

let sort_of_var x = 
  fun (ctx,_) -> (match IMap.find_opt x ctx with
                            Some s -> `Ok s
                          | None -> `Fail ("Index " ^ x.idx_source_name ^ " has unknown sort. Probably a compiler error."))

let get_alias x =
  fun (_,env) -> (match IMap.find_opt x env with
                            Some it -> `Ok it
                          | None -> `Fail ("Alias " ^ x.idx_source_name ^ " unbound. Probably a compiler error."))


exception Invariant of string

let rec mapM (f : 'a -> 'b elab) (xs : 'a list) : 'b list elab =
  match xs with
    [] -> return []
  | y::ys -> let* b = f y in
             let* bs = mapM f ys in
             return @@ b :: bs

let rec subst_aliases (c : la_constr) : la_constr elab =
  let rec sa_iterm (it : la_idx_term) : la_idx_term elab =
    match it with
      (IConst _ | IVar _) -> return it
    | IAlias x -> get_alias x
    | IPlus(it1,it2) -> let* it1' = sa_iterm it1 in
                        let* it2' = sa_iterm it2 in
                        return @@ IPlus(it1',it2')
    | IMinus(it1,it2) -> let* it1' = sa_iterm it1 in
                         let* it2' = sa_iterm it2 in
                         return @@ IMinus(it1',it2')
    | IMult(c,it) -> let* it' = sa_iterm it in
                      return @@ IMult(c,it')
    | IShift(it) -> let* it' = sa_iterm it in return (IShift it')
    | IFamLam(i,s,it) -> let* it' = sa_iterm it in return @@ IFamLam(i,s,it')
    | IFamApp(it1,it2) -> let* it1' = sa_iterm it1 in
                          let* it2' = sa_iterm it2 in
                          return @@ IFamApp(it1',it2')
    | ISum(i,it,lb,ub) -> let* it' = sa_iterm it in
                          let* lb' = sa_iterm lb in
                          let* ub' = sa_iterm ub in
                          return @@ ISum(i,it',lb',ub')
    | IConstVec(it) -> let* it' = sa_iterm it in return (IConstVec it')
    | INtoR (it) -> let* it' = sa_iterm it in return (INtoR it')
  in match c with
       (Top | Bot) -> return c
  | Conj(cs) -> let* cs' = mapM subst_aliases cs in return @@ Conj(cs')
  | Imp(c1,c2) -> let* c1' = subst_aliases c1 in
                  let* c2' = subst_aliases c2 in
                  return @@ Imp(c1',c2')
  | Forall(xss,c) -> let* c' = subst_aliases c in return @@ Forall(xss,c')
  | Exists(xss,c) -> let* c' = subst_aliases c in return @@ Exists(xss,c')
  | Eq(it1,it2) -> let* it1' = sa_iterm it1 in
                   let* it2' = sa_iterm it2 in
                   return @@ Eq(it1',it2')
  | Leq(it1,it2) -> let* it1' = sa_iterm it1 in
                    let* it2' = sa_iterm it2 in
                    return @@ Leq(it1',it2')
  | Lt(it1,it2) -> let* it1' = sa_iterm it1 in
                   let* it2' = sa_iterm it2 in
                   return @@ Lt(it1',it2')
  | Comment(s,c) -> let* c' = subst_aliases c in return @@ Comment(s,c')

let rec iterm_extend_pvecs (k : int) (iterm : la_idx_term) : la_idx_term =
  let rec dup n u =
  match n with
    0 -> []
  | _ -> u :: (dup (n-1) u)

  in match iterm with
    IConst (ICPVec p) -> let n = List.length p in
                         if n > k then raise (Invariant "k not length of largest pvec")
                         else let r = k - n in
                              let zs = dup r 0. in
                              IConst (ICPVec (p @ zs))
  | (IConst _ | IVar _ | IAlias _) -> iterm
  | IPlus(it1,it2) -> IPlus(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | IMinus(it1,it2) -> IMinus(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | IMult(ic,it) -> IMult(ic,iterm_extend_pvecs k it)
  | IShift(it) -> IShift(iterm_extend_pvecs k it)
  | IFamLam(i,s,it) -> IFamLam(i,s,iterm_extend_pvecs k it)
  | IFamApp(it1,it2) -> IFamApp(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | ISum(i,f,lb,ub) -> ISum(i,iterm_extend_pvecs k f,iterm_extend_pvecs k lb, iterm_extend_pvecs k ub)
    (* TODO: currently, these get extended in the "elab pvecs" phase-- do it here
     *       instead, somehow *)
  | IConstVec(it) -> IConstVec(iterm_extend_pvecs k it)
  | INtoR(it) -> INtoR(iterm_extend_pvecs k it)

let rec extend_pvecs (k : int) (c : la_constr) : la_constr =
  match c with
    (Top | Bot) -> c
  | Conj(cs) -> Conj(List.map (extend_pvecs k) cs)
  | Imp(c1,c2) -> Imp(extend_pvecs k c1,extend_pvecs k c2)
  | Forall(xs,c) -> Forall(xs,extend_pvecs k c)
  | Exists(xs,c) -> Exists(xs,extend_pvecs k c)
  | Eq(it1,it2) -> Eq(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | Leq(it1,it2) -> Leq(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | Lt(it1,it2) -> Lt(iterm_extend_pvecs k it1,iterm_extend_pvecs k it2)
  | Comment(s,c) -> Comment(s,extend_pvecs k c)

(* Infer the sort of an (unelaborated) index term
   * INVARIANT: iterm is sort-correct.*)
let rec so_infer iterm : la_sort elab =
  match iterm with
    IConst (ICNat _) -> return @@ SoBase SoNat
  | IConst (ICReal _) -> return @@ SoBase SoPosReal
  | IConst (ICPVec _) -> return @@ SoBase SoPotVec
  | IPlus(it1,_) -> so_infer it1
  | IMinus(it1,_) -> so_infer it1
  | IMult(_,it) -> so_infer it
  | IShift _ -> return @@ SoBase SoPotVec
  | (IVar x | IAlias x) -> fun (ctx,_) -> (match IMap.find_opt x ctx with
                            Some s -> `Ok s
                          | None -> `Fail ("Inference fail. Index " ^ x.idx_source_name ^ " unbound. Probably a compiler error."))
  | IFamLam(i,s,it) -> let* s' = (i |:::| (SoBase s)) (so_infer it) in
                       return @@ SoArr(s,s')
  | IFamApp(it,_) -> let* s = so_infer it in
                     (match s with
                        SoArr(_,s) -> return s
                      | _ -> fail_with "Not an index-level function!")
  | ISum(i,f,_,_) -> (i |:::| (SoBase SoNat)) (so_infer f)
  | IConstVec _ -> return @@ SoBase SoPotVec
  | INtoR _ -> return @@ SoBase SoPosReal

(*
 * monadic action binds un-elaborated types as it goes, to  know
 * which variables to unroll in to real k-tuples.
 *
 * INVARIANT: k > 1 (at least linear constraints)
 *)
exception Fail
let rec elab_pvecs (k : int) (c : la_constr) : la_constr elab =

  (* Extends an ivar to length k *)
  let extend_ivar {idx_fresh_name = x;idx_source_name = y} : (la_idx_var list) elab =
       match x with
         `Fresh x -> let freshs = List.init k (fun n -> `Fresh (x ^ "_" ^ (Int.to_string n))) in
                     let sources = List.init k (fun n -> y ^ "_" ^ (Int.to_string n)) in
                     let ivs = List.map (fun (s,f) -> {idx_source_name = s;idx_fresh_name = f}) (List.combine sources freshs) in
                     return ivs
       | _ -> raise (UnfreshenedVarExn y)
  in let extend_ivar_binder i =
    match i with
      IWild -> let i = Fresh_var.gen_var() in
               let* is = extend_ivar {idx_fresh_name = `Fresh i; idx_source_name = i} in
               return @@ List.map (fun i -> IName i) is
    | IName i -> let* is = extend_ivar i in
                 return @@ List.map (fun i -> IName i) is

  in let rec extend_sort (s : la_sort) : la_sort list =
      (*
      TODO: SO the idea is that:
        \vec{\R} |-> \R^k
        a -> \vec R |-> (a -> \R)^k
        \vec R -> a |-> R -> R -> ... -> a

        anything of sort \vec R becomes a k-list of terms of length k.
        could REALLY use some refinement types here.
      *)
       let extend_base_negative (bs : la_base_sort) : la_sort -> la_sort =
         fun s ->
           match bs with
             (SoPosReal | SoNat) -> SoArr(bs,s)
           | SoPotVec -> let rs = List.init k (fun _ -> SoPosReal) in
                         List.fold_right (fun real s -> SoArr(real,s)) rs s
       in match s with
            SoBase (SoNat | SoPosReal) -> [s]
          | SoBase SoPotVec -> List.init k (fun _ -> SoBase (SoPosReal))
          | SoArr(bs1,s2) -> let s2s = extend_sort s2 in
                             List.map (extend_base_negative bs1) s2s



  in let elab_binder connective (xs : (la_idx_var * la_sort) list) c : la_constr elab =
    let rec mFlatmap (f : 'a -> ('b list) elab) (xs : 'a list) : ('b list) elab = 
      match xs with
        [] -> return []
      | x::xs -> let* y = f x in
                 let* ys = mFlatmap f xs in
                 return (y @ ys)
    in let m = List.fold_right (fun (x,s) m -> (IName x |:::| s) m) xs (elab_pvecs k c) in

    let unroll_binding (x,s) : ((la_idx_var * la_sort) list) elab = 
      (* ss should either be length k or length 1 *)
      let ss = extend_sort s in
      let n = List.length ss in
      (*FIXME Some things are speical cased to n = 1- if k = 1 this breaks stuff *)
      if n == k then
         let* xs = extend_ivar x in
         return @@ List.combine xs ss
      else if n == 1 then
        return @@ List.combine [x] ss
      else fail_with "Elab error: unmatched lengths"

    in let* xs' = mFlatmap unroll_binding xs in
       let* c' = m in return (connective xs' c')

 (* smart constructor to deal with base case *)
  in let plus x y = match x,y with
                      (IConst (ICReal 0.)),_ -> y
                    | _,(IConst (ICReal 0.)) -> x
                    | _ -> IPlus(x,y)

  (*
   * Elaborate the name of an index level function variable,
   * f : s
   *
   * TODO: fold this in with the SoPotVec case of IVar in elab_pvec_iterm
   *)
  in let extend_ifun_name (f : la_idx_var) (s  : la_sort) : (la_idx_var list) elab =
       let ss = extend_sort s in
       let n = List.length ss in
       if n == k then extend_ivar f 
      (*FIXME CAN'T USE N=1 FOR when to extend ivar! *)
       else if n == 1 then return [f]
       else fail_with "Elab error: unmatched lengths"

  (* Given an index term of sort SoPotVec, return a list of the iterms of sort SoPosReal
   * which represent the k components of the pvec represented by the input
   * INVARIANT: iterm has already been k-expanded, all pvecs have length k.
   *
   * TODO: better name for this function
   * *)
  in let rec elab_pvec_iterm iterm : (la_idx_term list) elab =
    match iterm with
      IConst (ICPVec fs) -> return (List.map (fun f -> IConst (ICReal f)) fs)
    | IConst c -> return [IConst c]
    | IVar x -> let* s = sort_of_var x in
                (match s with
                  SoBase (SoNat | SoPosReal) -> return @@ [IVar x]
                | SoBase SoPotVec -> extend_ivar x >>= fun xs -> return @@ List.map (fun x' -> IVar x') xs
                | SoArr(_,_) -> extend_ifun_name x s >>= fun xs -> return @@ List.map (fun x' -> IVar x') xs)
    | IAlias _ -> fail_with "Shouldn't be aliases anymore"
    | IPlus (it1,it2) -> let* it1s = elab_pvec_iterm it1 in
                         let* it2s = elab_pvec_iterm it2 in
                         return (List.map (fun (x,y) -> plus x y) (List.combine it1s it2s))
    | IMinus(it1,it2) -> let* it1s = elab_pvec_iterm it1 in
                         let* it2s = elab_pvec_iterm it2 in
                         return (List.map (fun (x,y) -> IMinus(x,y)) (List.combine it1s it2s))
    | IMult(ic,it) -> let* its = elab_pvec_iterm it in return @@ List.map (fun it' -> IMult(ic,it')) its
    | IShift it -> let* its = elab_pvec_iterm it in
                   let zero = IConst (ICReal 0.) in
                   let f x (y,zs) = (x,(plus x y)::zs) in
                   let _,r = List.fold_right f its (zero,[]) in
                   return r
    | IFamLam(i,SoPotVec,it) -> let* its = (i |:::| (SoBase SoPotVec)) (elab_pvec_iterm it) in
                                let* is = extend_ivar_binder i in
                                (* If this doesn't work, sorry- I wrote
                                 * this at 12:41am... *)
                                let term_for it' = List.fold_right (fun i it -> IFamLam(i,SoPosReal,it)) is it' in
                                return @@ List.map term_for its
    | IFamLam(i,s,it) -> let* its = (i |:::| (SoBase s)) (elab_pvec_iterm it) in
                         return @@ List.map (fun it' -> IFamLam(i,s,it')) its
    | IFamApp(it1,it2) -> let* it1s = elab_pvec_iterm it1 in
                          let* it2s = elab_pvec_iterm it2 in
                          let f it1' = List.fold_right (fun it2' it -> IFamApp(it,it2')) (List.rev it2s) it1' in
                          return @@ List.map f it1s
    | ISum(i,f,lb,ub) -> let* lbs = elab_pvec_iterm lb in
                         let* ubs = elab_pvec_iterm ub in
                         let n1,n2 = (List.length lbs,List.length ubs) in
                         if n1 <> n2 || n1 <> 1 || n2 <> 1 then fail_with "Bound elab fails- should be singleton nats."
                         else let lb',ub' = (List.nth lbs 0,List.nth ubs 0) in
                              let* fs = (i |:::| (SoBase SoNat)) (elab_pvec_iterm f) in
                              return @@ List.map (fun f' -> ISum(i,f',lb',ub')) fs
    | IConstVec(it) -> let* its = elab_pvec_iterm it in
                       if List.length its <> 1 then fail_with "Const vector elab'd to length != 1" 
                       else let it' = List.nth its 0 in
                            let zeros = List.init (k-1) (fun _ -> IConst (ICReal 0.)) in
                            return @@ it' :: zeros
    | INtoR it -> let* its = elab_pvec_iterm it in
                  if List.length its <> 1 then fail_with "Nat elab'd to length != 1" 
                  else let it' = List.nth its 0 in
                  return [INtoR it']
                 
       
  (* invariant: it1, it2 are sort-correct and have the same sort
   * NOTE: iterms should only include terms of one type...
   *)
  in let elab_ineq ineq it1 it2 : la_constr elab =
      let* it1s = elab_pvec_iterm it1 in
      let* it2s = elab_pvec_iterm it2 in
      let its = List.map ineq (List.combine it1s it2s) in
      return (conj_list its)

  in match c with
    (Top | Bot) -> return c
  | Conj(cs) -> let* cs' = mapM (elab_pvecs k) cs in return @@ Conj(cs')
  | Imp(c1,c2) -> let* c1' = elab_pvecs k c1 in
                  let* c2' = elab_pvecs k c2 in
                  return (Imp(c1',c2'))
  | Forall(xs,c) -> elab_binder (fun xs c -> Forall(xs,c)) xs c
  | Exists(xs,c) -> elab_binder (fun xs c -> Exists(xs,c)) xs c
  | Eq(it1,it2) -> elab_ineq (fun (a,b) -> Eq (a,b)) it1 it2
  | Leq(it1,it2) -> elab_ineq (fun (a,b) -> Leq (a,b)) it1 it2
  | Lt(it1,it2) -> elab_ineq (fun (a,b) -> Lt (a,b)) it1 it2
  | Comment(s,c) -> let* c' = elab_pvecs k c in return @@ Comment(s,c')


(* TODO: remove this pass... *)
let rec unfold_binders (c : la_constr) : la_constr =
  match c with
    (Top | Bot) -> c
  | (Eq _ | Leq _ | Lt _) -> c
  | Conj(cs) -> Conj(List.map unfold_binders cs)
  | Imp(c1,c2) -> Imp(unfold_binders c1,unfold_binders c2)
  | Forall(xs,c) -> List.fold_right (fun (x,s) c' -> Forall([x,s],c')) xs (unfold_binders c)
  | Exists(xs,c) -> List.fold_right (fun (x,s) c' -> Exists([x,s],c')) xs (unfold_binders c)
  | Comment(s,c) -> Comment(s,unfold_binders c)

(*
 * Simply transforms constructors- no pvec elaboration here.
 *)
let to_elab_base_sort (bs : la_base_sort) : elab_base_sort elab =
  match bs with
    SoPosReal -> return ESoPosReal
  | SoNat -> return ESoNat
  | _ -> fail_with "Elab error: pvec sort found after flattening"

let rec to_elab_sort (s : la_sort) : elab_sort elab =
  match s with
    SoBase bs -> let* bs' = to_elab_base_sort bs in return @@ ESoBase bs'
  | SoArr(bs1,s2) -> let* bs1' = to_elab_base_sort bs1 in
                     let* s2' = to_elab_sort s2 in
                     return @@ ESoArr(bs1',s2')

let rec elab_iterm (iterm : la_idx_term) : elab_idx_term elab =
  match iterm with
    IConst(ICNat n) -> return (EConst (ENat n))
  | IConst(ICReal r) -> return (EConst (EReal r))
  | IConst(_) -> fail_with "Elab error: pvec const in index term after elaboration"
  | IVar {idx_fresh_name = `Fresh x;_} -> return (EVar x)
  | IVar {idx_fresh_name = `Alias x;_} -> fail_with @@ "Ivar" ^ x ^ "found with alias tag"
  | IVar {idx_source_name = y;_} -> raise (UnfreshenedVarExn y)
  | IAlias _ -> fail_with "Aliases should have been rm'd by now"
  | IPlus(it1,it2) -> let* it1' = elab_iterm it1 in
                      let* it2' = elab_iterm it2 in
                      let* s = so_infer it1 in
                      (match s with
                         SoBase SoNat -> return (EPlusNat(it1',it2'))
                       | SoBase SoPosReal -> return (EPlusReal(it1',it2'))
                       | _ -> fail_with "Elab error: pvec sort found after pvec elab")
  | IMinus(it1,it2) -> let* it1' = elab_iterm it1 in
                       let* it2' = elab_iterm it2 in
                       let* s = so_infer it1 in
                       (match s with
                          SoBase SoNat -> return (EMinusNat(it1',it2'))
                        | SoBase SoPosReal -> return (EMinusReal(it1',it2'))
                        | _ -> fail_with "Elab error: pvec sort found after pvec elab")
  | IMult(ic,it) -> let* it' = elab_iterm it in
                    let* s = so_infer it in
                    (match s,ic with
                       SoBase SoNat,ICNat n -> return @@ EMultNat(n,it')
                     | SoBase SoPosReal,ICReal r -> return @@ EMultReal(r,it')
                     | _ -> fail_with "Impossible case")

  | IShift _ -> fail_with "Elab error: shift in index term after elaboration"
  | IFamLam(IName {idx_fresh_name = `Fresh i;_},s,it) -> let* it' = elab_iterm it in
                                                         let* s' = to_elab_base_sort s in
                                                        return @@ EFamLam(i,s',it')
  | IFamLam(IWild,s,it) -> let* it' = elab_iterm it in
                           let* s' = to_elab_base_sort s in
                           return @@ EFamLam(Fresh_var.gen_var(),s',it')
  | IFamLam(IName {idx_fresh_name = `Unfreshened;_},_,_) -> fail_with "Elab error: unfreshened name"
  | IFamLam(IName {idx_fresh_name = `Alias _;_},_,_) -> fail_with "Elab error: binder has alias name"
  | IFamApp(it1,it2) -> let* it1' = elab_iterm it1 in
                        let* it2' = elab_iterm it2 in
                        return @@ EFamApp(it1',it2')
  | ISum(IName {idx_fresh_name = `Fresh x;_} as i,f,lb,ub) -> let* f' = (i |:::| (SoBase SoNat)) (elab_iterm f) in
                                                        let* lb' = elab_iterm lb in
                                                        let* ub' = elab_iterm ub in
                                                        let* s = (i |:::| (SoBase SoNat)) (so_infer f) in
                                                        (match s with
                                                           SoBase SoNat -> return @@ ESumNat(x,f',lb',ub')
                                                         | SoBase SoPosReal -> return @@ ESumReal(x,f',lb',ub')
                                                         | _ -> fail_with "Elab error: pvec sort found after pvec elab")
  | ISum(IWild,f,lb,ub) -> let* f' = elab_iterm f in
                           let* lb' = elab_iterm lb in
                           let* ub' = elab_iterm ub in
                           let* s = so_infer f in
                           let x = Fresh_var.gen_var() in
                           (match s with
                               SoBase SoNat -> return @@ ESumNat(x,f',lb',ub')
                             | SoBase SoPosReal -> return @@ ESumReal(x,f',lb',ub')
                             | _ -> fail_with "Elab error: pvec sort found after pvec elab")

  | ISum(IName {idx_source_name = i;_},_,_,_) -> raise (UnfreshenedVarExn i)
  | IConstVec _ -> fail_with "Elab error: const vec in index term after elaboration"
  | INtoR it -> let* it' = elab_iterm it in return @@ ENtoR it'


let rec elab_constr (c : la_constr) : elab_constr elab =
  match c with
    Top -> return ETop
  | Bot -> return EBot
  | Conj(cs) -> let* cs' = mapM elab_constr cs in return (EConj cs')
  | Imp(c1,c2) -> let* c1' = elab_constr c1 in
                  let* c2' = elab_constr c2 in
                  return (EImp (c1',c2'))
  | Forall([{idx_fresh_name = `Fresh f;_} as x,s],c) -> let* c' = (IName x |:::| s) (elab_constr c) in
                                                        let* s' = to_elab_sort s in
                                                        return (EForall(f,s',c'))
  | Forall([_,_],_) -> fail_with "Elab error: unfresh binder"
  | Forall(_,_) -> fail_with "Elab error: nonsingleton universal binder."
  | Exists([{idx_fresh_name = `Fresh f;_} as x,s],c) -> let* c' = (IName x |:::| s) (elab_constr c) in
                                                        let* s' = to_elab_sort s in
                                                        return (EExists(f,s',c'))
  | Exists([_,_],_) -> fail_with "Elab error: unfresh binder"
  | Exists(_,_) -> fail_with "Elab error: nonsingleton existential binder."
  | Eq(it1,it2) -> let* it1' = elab_iterm it1 in
                   let* it2' = elab_iterm it2 in
                   let* s = so_infer it1 in
                   (match s with
                      SoBase SoNat -> return (EEqNat(it1',it2'))
                    | SoBase SoPosReal -> return (EEqReal(it1',it2'))
                    | SoBase _ -> fail_with "Elab error: pvec sort found after pvec elab"
                    | SoArr(_,_) -> fail_with "Elab error: equation between arrow sorts")
  | Leq(it1,it2) -> let* it1' = elab_iterm it1 in
                    let* it2' = elab_iterm it2 in
                    let* s = so_infer it1 in
                    (match s with
                       SoBase SoNat -> return (ELeqNat(it1',it2'))
                     | SoBase SoPosReal -> return (ELeqReal(it1',it2'))
                     | SoBase _ -> fail_with  "Elab error: pvec sort found after pvec elab"
                     | SoArr(_,_) -> fail_with "Elab error: equation between arrow sorts")
  | Lt(it1,it2) -> let* it1' = elab_iterm it1 in
                   let* it2' = elab_iterm it2 in
                   let* s = so_infer it1 in
                   (match s with
                      SoBase SoNat -> return (ELtNat(it1',it2'))
                    | SoBase SoPosReal -> return (ELtReal(it1',it2'))
                    | SoBase _ -> fail_with  "Elab error: pvec sort found after pvec elab"
                    | SoArr(_,_) -> fail_with "Elab error: equation between arrow sorts")
  | Comment(_,c) -> elab_constr c

let elab k (c : la_constr) : elab_constr elab = 
  let* c = subst_aliases c in
  let  c = extend_pvecs k c in
  let* c = elab_pvecs k c in
  let  c = unfold_binders c in
  elab_constr c

let rec elab_decs k (ds : [`IdxDec of la_idx_var*la_idx_term*la_sort*la_constr 
                          | `OtherDec of la_constr] list) : (elab_constr list) elab =
  match ds with
    [] -> return []
  | (`IdxDec(i,it,s,c)) :: ds -> let* ec = elab k c in
                               let* ecs = (i |-> it) ((IName i |:::| s) (elab_decs k ds)) in
                               return @@ ec :: ecs
  | (`OtherDec c) :: ds -> let* ec = elab k c in
                           let* ecs = elab_decs k ds in
                           return @@ ec :: ecs


let rec elab_sort_pp (s : elab_sort) : string =
  match s with
    ESoBase ESoNat -> "Nat"
  | ESoBase ESoPosReal -> "Real"
  | ESoArr(bs1,s2) -> "(" ^ elab_sort_pp (ESoBase bs1) ^ ") -> (" ^ elab_sort_pp s2 ^ ")"

let rec elab_iterm_pp iterm =
  match iterm with
    EConst (ENat n) -> Int.to_string n
  | EConst (EReal r) -> Float.to_string r
  | EVar i -> i
  | EPlusNat(i1,i2) -> "(" ^ (elab_iterm_pp i1)  ^ " + " ^ (elab_iterm_pp i2) ^ ")"
  | EPlusReal(i1,i2) -> "(" ^ (elab_iterm_pp i1)  ^ " +. " ^ (elab_iterm_pp i2) ^ ")"
  | EMinusNat(i1,i2) -> "(" ^ (elab_iterm_pp i1)  ^ " - " ^ (elab_iterm_pp i2) ^ ")"
  | EMinusReal(i1,i2) -> "(" ^ (elab_iterm_pp i1)  ^ " -. " ^ (elab_iterm_pp i2) ^ ")"
  | EMultNat(n,it) -> "(" ^ Int.to_string n  ^ " * " ^ (elab_iterm_pp it) ^ ")"
  | EMultReal(r,it) -> "(" ^ Float.to_string r  ^ " *. " ^ (elab_iterm_pp it) ^ ")"
  | EFamLam(i,s,it) -> "\\" ^ i ^ ":" ^ (elab_sort_pp (ESoBase s)) ^ ".(" ^ (elab_iterm_pp it)^ ")"
  | EFamApp(i1,i2) -> "(" ^ (elab_iterm_pp i1)  ^ ")  (" ^ (elab_iterm_pp i2) ^ ")"
  | ESumReal(i,f,lb,ub) -> "sum(" ^ i ^ "." ^ elab_iterm_pp f ^ ",{" ^ elab_iterm_pp lb ^ "," ^ elab_iterm_pp ub ^ "})"
  | ESumNat(i,f,lb,ub) -> "sum(" ^ i ^ "." ^ elab_iterm_pp f ^ ",{" ^ elab_iterm_pp lb ^ "," ^ elab_iterm_pp ub ^ "})"
  | ENtoR it -> "real(" ^ elab_iterm_pp it ^ ")"


let rec elab_constr_pp ec : string =
  match ec with
    ETop -> "tt"
  | EBot -> "ff"
  | EConj([]) -> "()"
  | EConj(cs) -> "(" ^ (String.concat " /\\ " (List.map elab_constr_pp cs)) ^ ")"
  | EImp(c1,c2) -> "(" ^ (elab_constr_pp c1) ^ " -> " ^ (elab_constr_pp c2) ^ ")"
  | EEqNat(i1,i2) -> (elab_iterm_pp i1) ^ " = " ^ (elab_iterm_pp i2)
  | ELeqNat(i1,i2) -> (elab_iterm_pp i1) ^ " <= " ^ (elab_iterm_pp i2)
  | ELtNat(i1,i2) -> (elab_iterm_pp i1) ^ " < " ^ (elab_iterm_pp i2)
  | EEqReal(i1,i2) -> (elab_iterm_pp i1) ^ " =. " ^ (elab_iterm_pp i2)
  | ELeqReal(i1,i2) -> (elab_iterm_pp i1) ^ " <=. " ^ (elab_iterm_pp i2)
  | ELtReal(i1,i2) -> (elab_iterm_pp i1) ^ " <. " ^ (elab_iterm_pp i2)
  | EForall(x,s,c) -> "forall (" ^ x ^ ":" ^ elab_sort_pp s ^ ").(" ^ (elab_constr_pp c) ^ ")"
  | EExists(x,s,c) -> "exists (" ^ x ^ ":" ^ elab_sort_pp s ^ ").(" ^ (elab_constr_pp c) ^ ")"