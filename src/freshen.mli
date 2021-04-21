(* Joseph Cutler, 2021 *)
module FMap : Map.S

(* this is immensely stupid, do this the right way. *)
val lift_key : string -> FMap.key

type fresh_env = {
  ident_env : Syntax.la_ident FMap.t;
  idx_var_env : (Syntax.la_idx_var * [`Alias | `Bound]) FMap.t;
  type_var_env : (Syntax.la_type_var * [`Alias | `Bound]) FMap.t;
}

type 'a freshener = fresh_env -> 'a

val freshen_type : Syntax.la_type -> Syntax.la_type freshener

val do_freshen_pgm : Syntax.la_pgm -> Syntax.la_pgm