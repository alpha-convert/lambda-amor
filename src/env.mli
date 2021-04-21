(* Joseph Cutler, 2021 *)
module TMap : Map.S

val to_key : string -> TMap.key
val from_key : TMap.key -> string

type typ_env_t = (Syntax.la_type * Syntax.la_kind) TMap.t 
type idx_env_t = (Syntax.la_idx_term * Syntax.la_sort) TMap.t 

type t = {
  idx_env : idx_env_t;
  typ_env : typ_env_t;
}

val empty : t
 
val type_bind : Syntax.la_type_fresh_name * (Syntax.la_type * Syntax.la_kind) -> t -> t

val type_var_lookup : t -> Syntax.la_type_fresh_name -> (Syntax.la_type * Syntax.la_kind) option

val idx_bind : Syntax.la_idx_fresh_name * (Syntax.la_idx_term * Syntax.la_sort) -> t -> t

val idx_var_lookup : t -> Syntax.la_idx_fresh_name -> (Syntax.la_idx_term * Syntax.la_sort) option