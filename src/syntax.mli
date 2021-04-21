(* Joseph Cutler, 2021 *)

(** The type of base sorts for lambda-amor *)
type la_base_sort = SoNat | SoPosReal | SoPotVec
[@@deriving show]
type la_sort = SoBase of la_base_sort | SoArr of la_base_sort * la_sort

[@@deriving show]
val la_sort_pp : la_sort -> string

type la_idx_fresh_name = string
[@@deriving show]

type la_idx_var = {idx_source_name : string; idx_fresh_name : [`Unfreshened | `Fresh of la_idx_fresh_name | `Alias of string]}
[@@deriving show]
type la_idx_var_binder = IWild | IName of la_idx_var
[@@deriving show]

type la_pot_vec_lit =  float list
[@@deriving show]

type la_idx_const = ICNat of int | ICReal of float | ICPVec of la_pot_vec_lit
[@@deriving show]

type la_idx_term = IConst of la_idx_const | IVar of la_idx_var
                 | IAlias of la_idx_var
                 | IPlus of la_idx_term * la_idx_term
                 | IMinus of la_idx_term * la_idx_term
                 | IMult of la_idx_const * la_idx_term
                 | IShift of la_idx_term
                 | IFamLam of la_idx_var_binder * la_base_sort * la_idx_term
                 | IFamApp of la_idx_term * la_idx_term
                 | ISum of la_idx_var_binder * la_idx_term * la_idx_term * la_idx_term
                 | IConstVec of la_idx_term
                 | INtoR of la_idx_term
[@@deriving show]

type la_constr = Top | Bot | Conj of la_constr list | Imp of la_constr * la_constr
       | Forall of ((la_idx_var * la_sort) list) * la_constr
       | Exists of ((la_idx_var * la_sort) list) * la_constr
       | Eq of la_idx_term * la_idx_term
       | Leq of la_idx_term * la_idx_term
       | Lt of la_idx_term * la_idx_term
       | Comment of string * la_constr
[@@deriving show]

val ivar_pp : la_idx_var -> string
val pvec_pp : la_pot_vec_lit -> string
 
val iterm_pp : la_idx_term -> string
val constr_pp : la_constr -> string

exception UnfreshenedVarExn of string
 
type la_ident_fresh_name = string
type la_ident = {ident_source_name : string; ident_fresh_name : [`Unfreshened | `TopLevel of la_ident_fresh_name | `Fresh of la_ident_fresh_name]}
[@@deriving show]
type la_ident_binder = Wild | Name of la_ident
[@@deriving show]

type la_constant = NConst of int | BConst of bool | UConst
[@@deriving show]

type la_type_fresh_name = string
[@@deriving show]

type la_type_var = {type_source_name : string; type_fresh_name : [`Unfreshened | `Alias of string | `Fresh of string]}
[@@deriving show]
type la_type_var_binder = TWild | TName of la_type_var
[@@deriving show]

type la_kind = KStar | KArr of la_sort * la_kind
[@@deriving show]
val la_kind_pp : la_kind -> string


type nf_status = Nf | Ne | Unknown
[@@deriving show]

type la_type_t = TyUnit | TyBool | TyNat
             | TyVar of la_type_var
             (* These aren't parsed- they get added by the freshen phase *)
             | TyAlias of la_type_var
             | TyArr of la_type * la_type
             | TyTensor of la_type * la_type
             | TyWith of la_type * la_type
             | TyBang of la_type
             | TySum of la_type * la_type
             | TyIForall of la_idx_var_binder * la_sort * la_type
             | TyIExists of la_idx_var_binder * la_sort * la_type
             | TyTForall of la_type_var_binder * la_kind * la_type
             | TyList of la_idx_term * la_type
             | TyImplies of la_constr * la_type
             | TyConj of la_constr * la_type
             | TyMonad of la_idx_term * la_idx_term * la_type
             (* TODO: chagnge me to TyPolyPot *)
             | TyPot of la_idx_term * la_idx_term * la_type
             | TyConstPot of la_idx_term * la_type
             | TyFamLam of la_idx_var_binder * la_sort * la_type
             | TyFamApp of la_type * la_idx_term
[@@deriving show]

and la_type = nf_status * la_type_t
[@@deriving show]

val type_head : la_type -> la_type_t
val type_status : la_type -> nf_status

val ty_var : la_type_var -> la_type
val ty_alias: la_type_var -> la_type
val ty_unit : la_type
val ty_bool : la_type
val ty_nat : la_type
val ty_arr : la_type -> la_type -> la_type
val ty_tensor : la_type -> la_type -> la_type
val ty_with : la_type -> la_type -> la_type
val ty_bang : la_type -> la_type
val ty_sum : la_type -> la_type -> la_type
val ty_i_forall : la_idx_var_binder -> la_sort -> la_type -> la_type
val ty_i_exists : la_idx_var_binder -> la_sort -> la_type -> la_type
val ty_t_forall : la_type_var_binder -> la_kind -> la_type -> la_type
val ty_implies : la_constr -> la_type -> la_type
val ty_conj : la_constr -> la_type -> la_type
val ty_list : la_idx_term -> la_type -> la_type
val ty_monad : la_idx_term -> la_idx_term -> la_type -> la_type
val ty_pot : la_idx_term -> la_idx_term -> la_type -> la_type
val ty_const_pot : la_idx_term -> la_type -> la_type
val ty_fam_lam : la_idx_var_binder -> la_sort -> la_type -> la_type
val ty_fam_app : la_type -> la_idx_term -> la_type


val la_type_pp : la_type -> string

type la_binop = BopPlus

type la_exp =  Const of la_constant | Var of la_ident
            | Binop of la_binop * la_exp * la_exp
            | Lam of la_ident_binder * la_exp | App of la_exp * la_exp
            | Ann of la_exp * la_type
            | PPair of la_exp * la_exp | PLet of la_exp * la_ident_binder * la_ident_binder * la_exp
            | NPair of la_exp * la_exp | Fst of la_exp | Snd of la_exp
            | Bang of la_exp | LetBang of la_exp * la_ident_binder * la_exp
            | Inl of la_exp | Inr of la_exp
            | SCase of la_exp * la_ident_binder * la_exp * la_ident_binder * la_exp
            | NCase of la_exp * la_exp * la_ident_binder * la_exp
            | Fix of la_ident_binder * la_exp
            | ILam of la_idx_var_binder * la_exp
            | IApp of la_exp * la_idx_term
            | TLam of la_type_var_binder * la_exp
            | TApp of la_exp * la_type
            | Nil | Cons of la_exp * la_exp
            | LCase of la_exp * la_exp * la_ident_binder * la_ident_binder * la_exp
            | Pack of la_idx_term * la_exp
            | Unpack of la_exp * la_idx_var_binder * la_ident_binder * la_exp
            | CLam of la_exp | CApp of la_exp
            | CPair of la_exp | CLet of la_exp * la_ident_binder * la_exp
            | Ret of la_exp | Bind of la_exp * la_ident_binder * la_exp
            | Tick of la_idx_term * la_idx_term
            | Store of la_idx_term * la_idx_term * la_exp
            | StoreConst of la_idx_term * la_exp
            | Release of la_exp * la_ident_binder * la_exp
            | Shift of la_exp
            | Absurd
            | Ite of la_exp * la_exp * la_exp
            | Let of la_exp * la_ident_binder * la_exp
            | Hole
[@@deriving show]

type la_decl = ValDec of la_ident * la_exp * la_type
            | TyDec of la_type_var * la_type * la_kind
            | IdxDec of la_idx_var * la_idx_term * la_sort
            | DoDec of la_ident * la_idx_term * la_idx_term * la_type * la_exp
[@@deriving show]

type la_pgm = la_decl list

val conj : la_constr -> la_constr -> la_constr
val imp : la_constr -> la_constr -> la_constr
val conj_list : la_constr list -> la_constr

val exists : (la_idx_var_binder * la_sort) list -> la_constr -> la_constr
val forall : (la_idx_var_binder * la_sort) list -> la_constr -> la_constr

val smart_eq : la_idx_term * la_idx_term -> la_constr
val smart_leq : la_idx_term * la_idx_term -> la_constr


val idx_var : la_idx_var -> la_idx_term

(*
 * iterm[j/i]
 *)
val idx_idx_subst : la_idx_term -> la_idx_var ->la_idx_term -> la_idx_term

(* 
 * c[j/i]
 *)
val constr_idx_subst : la_idx_term -> la_idx_var -> la_constr -> la_constr

(*
 * t[j/i]
 *)
val type_idx_subst : la_idx_term -> la_idx_var ->la_type -> la_type
val type_idx_binder_subst : la_idx_term -> la_idx_var_binder ->la_type -> la_type

(*t[t'/a]*)
val type_type_subst : la_type -> la_type_var -> la_type -> la_type
val type_type_binder_subst : la_type -> la_type_var_binder -> la_type -> la_type

(* e[t'/a] *)
val exp_type_subst : la_type -> la_type_var -> la_exp -> la_exp