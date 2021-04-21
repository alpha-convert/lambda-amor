(* Joseph Cutler, 2021 *)
open Syntax
    
type error_elem = AffReuse of la_ident (* Affine variable used multiple times *)
                   | UnboundVar of la_ident (* Use of an unbound variable *)
                   | AnnCheck of la_exp * la_type (* Check failed *)
                   | InferFail of la_exp (* Coouldn't infer the type of expression *)
                   | SubtyFail of la_type * la_type (* t <: t' could not be proved*)
                   | WrongType of la_exp * la_type * string (* e has type t, expected something of the form s *)
                   | UnequalSorts of la_sort * la_sort
                   | DoDecUnobservable of la_type
                   | Generic of string
                   | CheckHole of la_type * Ctx.t
                   | InferHole of Ctx.t

type 'a t = Ok of 'a | Fail of error_elem

let raise ex = Fail ex
let return a = Ok a

let (>>=) e f =
  match e with
    Ok a -> f a
  | Fail ex -> Fail ex

let pp err =
  match err with
    AffReuse x -> "Used variable " ^ x.ident_source_name ^ " twice."
  | UnboundVar x -> "Use of unbound variable " ^ x.ident_source_name ^ "."
  | AnnCheck(e,t) -> "Annotation check failed. " ^ show_la_exp e ^ " does not have type " ^ la_type_pp t
  | InferFail e -> "Could not infer the type of expression: " ^ show_la_exp e
  | SubtyFail(t,t') -> "Unable to prove subtyping relation: " ^ la_type_pp t ^ " <: " ^ la_type_pp t'
  | WrongType(e,t,s) -> "Expression " ^ show_la_exp e ^ " found to have type " ^ show_la_type t ^ ". Expected something of the form " ^ s
  | UnequalSorts(s,s') -> "Unequal sorts, " ^ show_la_sort s ^ " != " ^ show_la_sort s'
  | DoDecUnobservable(t) -> "Attempted do-dec with unobservable type " ^ la_type_pp t
  | Generic s -> s
  | CheckHole(t,ctx) -> "Hit a (checking) hole!\nHave:\n" ^ Ctx.pp ctx ^ "\nWant: " ^ la_type_pp t
  | InferHole ctx -> "Hit an (inferring) hole!\nHave:\n" ^ Ctx.pp ctx
