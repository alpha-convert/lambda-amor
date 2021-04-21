(* Joseph Cutler, 2021 *)
open Syntax

module VMap = Map.Make(struct
                       type t = la_ident
                       let compare = compare
                     end)

module IMap = Map.Make(struct
                        type t = la_idx_var
                        let compare  = compare
                      end)

module TMap = Map.Make(struct
                        type t = la_type_var
                        let compare = compare
                      end)


type aff_ctx_t = (la_type * [`Used | `Unused]) VMap.t
type exp_ctx_t = la_type VMap.t 
type idx_ctx_t = la_sort IMap.t 
type typ_ctx_t = la_kind TMap.t 
type ctr_ctx_t = la_constr list

type t = {
  aff_ctx : aff_ctx_t; (* affine term context Gamma*)
  exp_ctx : exp_ctx_t; (* Exponential term context Omega*)
  idx_ctx : idx_ctx_t; (* Index variable conetxt Theta *)
  ctr_ctx : ctr_ctx_t;
  typ_ctx : typ_ctx_t; (* Type context Sigma *)
}

let pp ctx =
  let f (x,(t,use)) = match use with
                        `Used -> None
                      | _ -> Some (x,t) in
  let affs = String.concat "\n" @@ List.map (fun (x,t) -> x.ident_source_name ^ " : " ^ la_type_pp t) @@ List.filter_map f @@ VMap.bindings ctx.aff_ctx in
  let exps = String.concat "\n" @@ List.map (fun (x,t) -> x.ident_source_name ^ " :: " ^ la_type_pp t) @@ VMap.bindings ctx.exp_ctx in
  let idxs = String.concat "\n" @@ List.map (fun (i,s) -> i.idx_source_name ^ " ::: " ^ la_sort_pp s) @@ IMap.bindings ctx.idx_ctx in
  let ctrs = String.concat "\n" @@ List.map constr_pp ctx.ctr_ctx in
  let typs = String.concat "\n" @@ List.map (fun (a,k) -> a.type_source_name ^ " ::::: " ^ la_kind_pp k) @@ TMap.bindings ctx.typ_ctx in
  String.concat "\n" @@ List.filter (fun s -> s != "") [affs;exps;idxs;ctrs;typs]
  


let empty = {aff_ctx = VMap.empty; exp_ctx = VMap.empty; idx_ctx = IMap.empty; typ_ctx = TMap.empty; ctr_ctx = []}

(*
 * Search through the affine and exponential contexts, and find the term variable x
 *)
let term_var_lookup (ctx : t) (x : la_ident) : [`Aff of la_type | `Used | `Exp of la_type | `Missing] =
  match x.ident_fresh_name with
    (`Fresh _ | `TopLevel _) ->
      (match (VMap.find_opt x ctx.aff_ctx) with
        (Some (_,`Used)) -> `Used
      | (Some (t,`Unused)) -> `Aff t
      | None -> match VMap.find_opt x ctx.exp_ctx with
                  Some t -> `Exp t
                | None -> `Missing)
  | `Unfreshened -> raise (UnfreshenedVarExn x.ident_source_name)

let idx_var_lookup (ctx : t) (i : la_idx_var) : la_sort option =
  match i.idx_fresh_name with
    (`Fresh _ | `Alias _) -> IMap.find_opt i ctx.idx_ctx
  | `Unfreshened -> raise (UnfreshenedVarExn i.idx_source_name)

let type_var_lookup (ctx : t) (a : la_type_var) : la_kind option =
  match a.type_fresh_name with
    (`Fresh _ | `Alias _) -> TMap.find_opt a ctx.typ_ctx
  | `Unfreshened -> raise (UnfreshenedVarExn a.type_source_name)


(*
 * Mark an affine variable as "used"
 *)
let aff_mark (gamma : aff_ctx_t) (x : la_ident) : aff_ctx_t =
  let f = function
    | Some (x,`Unused) -> Some (x,`Used)
    | x -> x
  in match x.ident_fresh_name with
       `Fresh _ -> VMap.update x f gamma
     | `TopLevel _ -> gamma
     | `Unfreshened -> raise (UnfreshenedVarExn x.ident_source_name)

(*
 * Bind x : t as an affine variable
 *)
(*
 * TODO: do we want to error out if a toplevel name gets bound as affine?
 *)
let aff_bind ((x,t) : la_ident * la_type) (ctx : t) : t =
  match x.ident_fresh_name with
    (`Fresh _ | `TopLevel _) -> {ctx with aff_ctx = VMap.add x (t,`Unused) ctx.aff_ctx}
  | `Unfreshened -> raise (UnfreshenedVarExn x.ident_source_name)

let aff_unbind (x : la_ident) (aff_ctx : aff_ctx_t) : aff_ctx_t =
  match x.ident_fresh_name with
    (`Fresh _ | `TopLevel _) -> VMap.remove x aff_ctx
  | `Unfreshened -> raise (UnfreshenedVarExn x.ident_source_name)

(*
 * Bind x : t as an exponential variable
 *)
let exp_bind ((x,t) : la_ident * la_type) (ctx : t) : t =
  match x.ident_fresh_name with
    (`Fresh _ | `TopLevel _) -> {ctx with exp_ctx = VMap.add x t ctx.exp_ctx}
  | `Unfreshened -> raise (UnfreshenedVarExn x.ident_source_name)

(*
 * Bind i : s as an index variable
 *)
let idx_bind ((i,s) : la_idx_var * la_sort ) (ctx : t) : t =
  {ctx with idx_ctx = IMap.add i s ctx.idx_ctx}

let ctr_add c ctx =
  {ctx with ctr_ctx = c :: ctx.ctr_ctx}

let type_bind (a,k) (ctx : t) : t =
  {ctx with typ_ctx = TMap.add a k ctx.typ_ctx}

(*
 * Intersect the affine contexts of ctx1, ctx2
 * x : t is unused in intersect ct1,ctx2 iff it's unused in both.
 *)
let intersect (ctx1 : aff_ctx_t) (ctx2 : aff_ctx_t) : aff_ctx_t =
  let f = fun _ u v ->
    match u,v with
      (None,_) -> None
    | (_,None) -> None
    | (Some (t,`Used),_) -> Some (t,`Used)
    | (_,Some(t,`Used)) -> Some (t,`Used)
    | (Some (t,`Unused),Some (_,`Unused)) -> Some (t,`Unused)
  in VMap.merge f ctx1 ctx2

(*
 * Zero out the affine context of ctx
 *)
let erase_aff (ctx : t) : t =
  {ctx with aff_ctx = VMap.empty}

let erase_idx (ctx : t) : t =
  {ctx with idx_ctx = IMap.empty}

(*
 * Adjoin two index contexts
 *)
exception Impossible

let idx_adjoin ic1 ic2 = 
  let f = fun _ u v ->
    match u,v with
      (None,_) -> v
    | (_,None) -> u
    | _ -> raise Impossible
  in IMap.merge f ic1 ic2
