(* Joseph Cutler, 2021 *)
open Syntax

(*
 * Maps toplevel type aliases to their types
 *)
module TMap = Map.Make(struct
                        type t = string
                        let compare = compare
                      end)

type typ_env_t = (la_type * la_kind) TMap.t 
type idx_env_t = (la_idx_term * la_sort) TMap.t 

type t = {
  idx_env : idx_env_t;
  typ_env : typ_env_t;
}

let from_key x = x
let to_key x = x

let empty : t = {typ_env = TMap.empty; idx_env = TMap.empty}

let type_bind (a,t) (env : t) : t =
  {env with typ_env = TMap.add a t env.typ_env}

let type_var_lookup env a =
  TMap.find_opt a env.typ_env

let idx_bind (i,s) env =
  {env with idx_env = TMap.add i s env.idx_env}

let idx_var_lookup env i =
  TMap.find_opt i env.idx_env
