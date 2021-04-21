(* Joseph Cutler, 2021 *)
open Syntax

(* Pass 1: remove comments. *)
(* Pass 2: flatten constraints. *)

let rec remove_comments (c : la_constr) : la_constr =
  match (c : la_constr) with
| Top -> c
| Bot -> c
| Conj cs -> conj_list (List.map remove_comments cs)
| Imp (c1,c2) -> Imp(remove_comments c1,remove_comments c2)
| Forall (iss,c) -> Forall(iss,remove_comments c)
| Exists (iss,c) -> Exists (iss,remove_comments c)
| Eq (_, _) -> c
| Leq (_, _) -> c
| Lt (_, _) -> c
| Comment (_, c) -> c

type flat_constr = FConj of flat_nconj_constr list
                      | FNotConj of flat_nconj_constr
and flat_nconj_constr = FTop | FBot | FImp of flat_constr * flat_constr
                      | FForall of ((la_idx_var * la_sort) list) * flat_constr
                      | FExists of ((la_idx_var * la_sort) list) * flat_constr
                      | FEq of la_idx_term * la_idx_term
                      | FLeq of la_idx_term * la_idx_term
                      | FLt of la_idx_term * la_idx_term

let rec flatten_constr (c : la_constr) : flat_constr =
  match c with
| Top -> FNotConj FTop
| Bot -> FNotConj FBot
| Conj cs -> let cs' = List.map flatten_constr cs in
             let cs'' : flat_nconj_constr list = Core.List.fold_right cs' ~init:[] ~f:(
               fun fc fncs -> match fc with
                                FConj(fncs') -> fncs' @ fncs
                              | FNotConj(fnc) -> fnc :: fncs
             ) in
             FConj(cs'')
| Imp (c1,c2) -> FNotConj (FImp(flatten_constr c1,flatten_constr c2))
| Forall (iss, c) -> FNotConj(FForall(iss,flatten_constr c))
| Exists (iss, c) -> FNotConj(FExists(iss,flatten_constr c))
| Eq (it1,it2) -> FNotConj(FEq(it1,it2))
| Leq (it1,it2) -> FNotConj(FLeq(it1,it2))
| Lt (it1,it2) -> FNotConj(FLt(it1,it2))
(* Probably should be gone if the comment rm pass is on *)
| Comment (_, c) -> flatten_constr c

let rec read_back_nconj_constr (fc : flat_nconj_constr) : la_constr =
  match fc with
    FTop -> Top
  | FBot -> Bot
  | FImp(fc1,fc2) -> Imp(read_back_constr fc1,read_back_constr fc2)
  | FForall(iss,fcc) -> Forall(iss,read_back_constr fcc)
  | FExists(iss,fcc) -> Exists(iss,read_back_constr fcc)
  | FEq(it1,it2) -> Eq(it1,it2)
  | FLeq(it1,it2) -> Leq(it1,it2)
  | FLt(it1,it2) -> Lt(it1,it2)
and read_back_constr (fc : flat_constr) : la_constr = 
  match fc with
    FConj(fcs) -> Conj(List.map read_back_nconj_constr fcs)
  | FNotConj(fc) -> read_back_nconj_constr fc

let rec dedup xs =
  match xs with
    [] -> []
  | y::ys -> let ys' = dedup ys in
             if List.mem y ys' then ys' else y::ys'

let rec dedup_conj (c : la_constr) : la_constr =
  match c with
| Top -> c
| Bot -> c
| Conj cs -> let cs' = List.map dedup_conj cs in
             Conj(dedup cs')
| Imp (c1,c2) -> Imp(dedup_conj c1,dedup_conj c2)
| Forall (iss,c) -> Forall(iss,dedup_conj c)
| Exists (iss,c) -> Exists(iss,dedup_conj c)
| (Eq (_, _)
| Leq (_, _)
| Lt (_, _)) -> c
| Comment (_, c) -> dedup_conj c

let do_optimize (c : la_constr) : la_constr =
  let _ = remove_comments c in
  let _ = read_back_constr (flatten_constr c) in
  let _ = dedup_conj c in
  c