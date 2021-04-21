(* Joseph Cutler, 2021 *)
type la_base_sort = SoNat | SoPosReal | SoPotVec
[@@deriving show]

type la_sort = SoBase of la_base_sort | SoArr of la_base_sort * la_sort
[@@deriving show]

let rec la_sort_pp s =
  match s with
    SoBase SoNat -> "Nat"
  | SoBase SoPosReal -> "Real"
  | SoBase SoPotVec -> "PVec"
  | SoArr(bs1,s2) -> (la_sort_pp @@ SoBase bs1) ^ " -> (" ^ (la_sort_pp s2) ^ ")"


type la_idx_fresh_name = string
[@@deriving show]

type la_idx_var = {idx_source_name : string; idx_fresh_name : [`Unfreshened | `Fresh of la_idx_fresh_name | `Alias of string]}
[@@deriving show]

type la_idx_var_binder = IWild | IName of la_idx_var
[@@deriving show]


type la_pot_vec_lit = float list
[@@deriving show]

type la_idx_const = ICNat of int | ICReal of float | ICPVec of la_pot_vec_lit
[@@deriving show]

(* General index terms - can appear in terms*)
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


(*
 * TODO: ensure that index db vars always line up with binders
 *)
type la_constr = Top | Bot | Conj of la_constr list | Imp of la_constr * la_constr
       | Forall of ((la_idx_var * la_sort) list) * la_constr
       | Exists of ((la_idx_var * la_sort) list) * la_constr
       | Eq of la_idx_term * la_idx_term
       | Leq of la_idx_term * la_idx_term
       | Lt of la_idx_term * la_idx_term
       | Comment of string * la_constr
[@@deriving show]

let ivar_pp i =
  match i.idx_fresh_name with
    (`Fresh _ | `Alias _)  ->  i.idx_source_name (*^ "#" ^ j*)
  | _ -> "U(" ^ i.idx_source_name ^ ")"

  let ibinder_pp = function
    IWild -> "_"
  | IName i -> ivar_pp i

let show_bindings (bs : (la_idx_var * la_sort) list) : string =
  String.concat "," (List.map (fun (i,s) -> ivar_pp i ^ " : "^ (la_sort_pp s)) bs)

let pvec_pp pot =
  String.concat "," (List.map Float.to_string pot)

let rec iterm_pp iterm =
  match iterm with
    IConst (ICNat n) -> Int.to_string n
  | IConst (ICReal r) -> Float.to_string r
  | IConst (ICPVec p) -> "[" ^  pvec_pp p ^ "]"
  | (IVar i | IAlias i) -> ivar_pp i
  | IPlus(i1,i2) -> "(" ^ (iterm_pp i1)  ^ " + " ^ (iterm_pp i2) ^ ")"
  | IMinus(i1,i2) -> "(" ^ (iterm_pp i1)  ^ " - " ^ (iterm_pp i2) ^ ")"
  | IMult(ic,it) -> iterm_pp (IConst ic) ^ " * " ^ iterm_pp it
  | IShift i -> "<| " ^ (iterm_pp i)
  | IFamLam(i,s,it) -> "\\" ^ (ibinder_pp i) ^ ":" ^ (la_sort_pp (SoBase s)) ^ "." ^ "(" ^ iterm_pp it ^ ")"
  | IFamApp(it1,it2) -> "(" ^ (iterm_pp it1) ^ ") (" ^ (iterm_pp it2) ^ ")"
  | ISum(i,f,lb,ub) -> "sum(" ^ ibinder_pp i ^ "." ^ iterm_pp f ^ ",{" ^ iterm_pp lb ^ "," ^ iterm_pp ub ^ "})"
  | IConstVec(it) -> "[" ^ iterm_pp it ^ "]"
  | INtoR it -> "real(" ^ iterm_pp it ^ ")"


let rec constr_pp(c : la_constr) : string =
  match c with
    Top -> "tt"
  | Bot -> "ff"
  | Conj([]) -> "()"
  | Conj(cs) -> "/\\[" ^ (String.concat " /\\ " (List.map constr_pp cs)) ^ "]"
  | Imp(c1,c2) -> "(" ^ (constr_pp c1) ^ " -> " ^ (constr_pp c2) ^ ")"
  | Eq(i1,i2) -> (iterm_pp i1) ^ " = " ^ (iterm_pp i2)
  | Leq(i1,i2) -> (iterm_pp i1) ^ " <= " ^ (iterm_pp i2)
  | Lt(i1,i2) -> (iterm_pp i1) ^ " < " ^ (iterm_pp i2)
  | Forall(iss,c) -> "forall (" ^ (show_bindings iss) ^ ").(" ^ (constr_pp c) ^ ")"
  | Exists(iss,c) -> "exists (" ^ (show_bindings iss) ^ ").(" ^ (constr_pp c) ^ ")"
  | Comment(s,c) -> "(//" ^ s ^ " ; " ^ (constr_pp c) ^ ")"


exception UnfreshenedVarExn of string
type la_ident_fresh_name = string
[@@deriving show]

type la_ident = {ident_source_name : string; ident_fresh_name : [`Unfreshened | `TopLevel of la_ident_fresh_name | `Fresh of la_ident_fresh_name]}
[@@deriving show]

type la_ident_binder = Wild | Name of la_ident
[@@deriving show]

type la_constant = NConst of int | BConst of bool | UConst
[@@deriving show]

type la_type_fresh_name = string
[@@deriving show]

type la_type_var = {type_source_name : string; type_fresh_name : [`Unfreshened | `Alias of la_type_fresh_name | `Fresh of la_type_fresh_name]}
[@@deriving show]

type la_type_var_binder = TWild | TName of la_type_var
[@@deriving show]

type la_kind = KStar | KArr of la_sort * la_kind
[@@deriving show]

let rec la_kind_pp k =
  match k with
    KStar -> "*"
  | KArr(s,k) -> "(" ^ la_sort_pp s ^ ") => (" ^ la_kind_pp k ^ ")"

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

let type_head (_,t) = t
let type_status (s,_) = s


let ty_var a = (Ne,TyVar a)
let ty_alias a = (Ne,TyAlias a)
let ty_nat = (Nf,TyNat)
let ty_bool = (Nf,TyBool)
let ty_unit = (Nf,TyUnit)

let bin_join st1 st2 =
  match st1,st2 with
    Unknown,_ -> Unknown
  | _,Unknown -> Unknown
  | Nf,Nf -> Nf
  | Ne,_ -> Nf
  | _,Ne -> Nf

let promote_or_unknown s =
  match s with
    (Nf | Ne) -> Nf
  | Unknown -> Unknown


let ty_arr t1 t2 = (bin_join (type_status t1) (type_status t2), TyArr (t1,t2))
let ty_tensor t1 t2 = (bin_join (type_status t1) (type_status t2), TyTensor(t1,t2))
let ty_with t1 t2 = (bin_join (type_status t1) (type_status t2), TyWith (t1,t2))
let ty_bang t = (promote_or_unknown @@ type_status t,TyBang t)
let ty_sum t1 t2 = (bin_join (type_status t1) (type_status t2), TySum (t1,t2))

let ty_i_forall i s t = (promote_or_unknown @@ type_status t,TyIForall(i,s,t))
let ty_i_exists i s t = (promote_or_unknown @@ type_status t,TyIExists(i,s,t))
let ty_t_forall a k t = (promote_or_unknown @@ type_status t,TyTForall(a,k,t))

let ty_conj c t = (promote_or_unknown @@ type_status t,TyConj(c,t))
let ty_implies c t = (promote_or_unknown @@ type_status t,TyImplies(c,t))

let ty_list it t = (promote_or_unknown @@ type_status t, TyList(it,t))
let ty_monad it1 it2 t = (promote_or_unknown @@ type_status t, TyMonad(it1,it2,t))
let ty_pot it1 it2 t = (promote_or_unknown @@ type_status t, TyPot(it1,it2,t))
let ty_const_pot it t = (promote_or_unknown @@ type_status t, TyConstPot(it,t))
let ty_fam_lam i s t = (promote_or_unknown @@ type_status t, TyFamLam(i,s,t))

let ty_fam_app t it =
  match type_status t with
    (Nf | Unknown) -> (Unknown, TyFamApp(t,it))
  | Ne -> (Ne, TyFamApp(t,it))

let tvar_pp a = a.type_source_name

let tbinder_pp = function
  TWild -> "_"
| TName a -> tvar_pp a

let rec la_type_pp t =
  match type_head t with
    TyUnit -> "unit"
  | TyBool -> "bool"
  | TyNat -> "nat"
  | TyVar a -> a.type_source_name
  | TyAlias a -> a.type_source_name
  | TyArr(t1,t2) -> "(" ^ la_type_pp t1 ^ " -> " ^ la_type_pp t2 ^ ")"
  | TyTensor(t1,t2) -> "(" ^ la_type_pp t1 ^ " * " ^ la_type_pp t2 ^ ")"
  | TyWith(t1,t2) -> "(" ^ la_type_pp t1 ^ " & " ^ la_type_pp t2 ^ ")"
  | TySum(t1,t2) -> "(" ^ la_type_pp t1 ^ " + " ^ la_type_pp t2 ^ ")"
  | TyBang(t) -> "!" ^ la_type_pp t
  | TyIForall(i,s,t) -> "Iforall " ^ ibinder_pp i ^ " : " ^ la_sort_pp s ^ ". " ^ la_type_pp t
  | TyIExists(i,s,t) -> "Iexists " ^ ibinder_pp i ^ " : " ^ la_sort_pp s ^ ". " ^ la_type_pp t
  | TyTForall(a,k,t) -> "Tforall " ^ tbinder_pp a ^ " : " ^ la_kind_pp k ^ ". " ^ la_type_pp t
  | TyList(it,t) -> "List(" ^ iterm_pp it ^ "," ^ la_type_pp t ^ ")"
  | TyImplies(c,t) -> "<" ^ constr_pp c ^ "> => (" ^ la_type_pp t ^ ")"
  | TyConj(c,t) -> "<" ^ constr_pp c ^ "," ^ la_type_pp t ^ ">"
  | TyMonad(it,p,t) -> "M (" ^ iterm_pp it ^ "," ^ iterm_pp p ^ ")" ^ la_type_pp t
  | TyPot(it,p,t) -> "[" ^ iterm_pp it ^ "," ^ iterm_pp p ^ "]" ^ la_type_pp t
  | TyConstPot(it,t) -> "[" ^ iterm_pp it ^ "]" ^ la_type_pp t
  | TyFamLam(i,s,t) -> "(ILam " ^ ibinder_pp i ^ " : " ^ la_sort_pp s ^ ". " ^ la_type_pp t ^ ")"
  | TyFamApp(t,it) -> "(" ^ la_type_pp t ^ " " ^ iterm_pp it ^ ")"

type la_binop = BopPlus
[@@deriving show]

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

let conj_list xs = 
  match (List.filter (fun c -> c <> Top) xs) with
    [] -> Top
  | cs' -> Conj cs'

let conj x y =
  (*if x = y then x else*) conj_list [x;y]

let imp x y =
  match x,y with
    (Top,_) -> y
  | (_,Top) -> Top
  | (Bot,_) -> Top
  | _ -> if x = y then Top else Imp(x,y)


let exists xs phi =
  match (xs,phi) with
    (_,Top) -> Top
  | (_,Bot) -> Bot
  | ([],phi) -> phi
  | _ -> Exists (List.filter_map (function (IName x,s) -> Some (x,s) | _ -> None) xs,phi)

let forall xs phi = 
  match (xs,phi) with
    (_,Top) -> Top
  | (_,Bot) -> Bot
  | ([],_) -> phi
  | _ -> Forall (List.filter_map (function (IName x,s) -> Some (x,s) | _ -> None) xs,phi)

let smart_eq (it1,it2) =
  if it1 = it2 then Top else Eq(it1,it2)

let smart_leq (it1,it2) =
  (*Leq(it1,it2)*)
  if it1 = it2 then Top else Leq(it1,it2)

let idx_var ({idx_source_name=js;idx_fresh_name=jf} as j) =
  match jf with
    `Alias _ -> IAlias j
  | `Fresh _ -> IVar j
  | _ -> raise (UnfreshenedVarExn js)

(*
 * iterm[j/i]
 *)
let rec idx_idx_subst (j : la_idx_term) (i : la_idx_var) (iterm : la_idx_term) : la_idx_term =
  match iterm with
    (IConst _ | IAlias _) -> iterm
  | IVar k -> if i.idx_fresh_name = k.idx_fresh_name then j
              else IVar k
  | IPlus(it1,it2) -> IPlus(idx_idx_subst j i it1, idx_idx_subst j i it2)
  | IMinus(it1,it2) -> IMinus(idx_idx_subst j i it1, idx_idx_subst j i it2)
  | IMult(ic,it) -> IMult(ic, idx_idx_subst j i it)
  | IShift iterm -> IShift (idx_idx_subst j i iterm)
  | IFamLam(k,s,it) -> IFamLam(k,s,idx_idx_subst j i it)
  | IFamApp(it1,it2) -> IFamApp(idx_idx_subst j i it1, idx_idx_subst j i it2)
  | ISum(k,f,lb,ub) -> ISum(k,idx_idx_subst j i f,idx_idx_subst j i lb, idx_idx_subst j i ub)
  | IConstVec(it) -> IConstVec(idx_idx_subst j i it)
  | INtoR(it) -> INtoR(idx_idx_subst j i it)

(* 
 * c[j/i]
 *)
let rec constr_idx_subst (j : la_idx_term) (i : la_idx_var) (c : la_constr) : la_constr =
  match c with
    Top -> Top
  | Bot -> Bot
  | Conj(cs) -> Conj(List.map (constr_idx_subst j i) cs)
  | Imp(c1,c2) -> Imp(constr_idx_subst j i c1, constr_idx_subst j i c2)
  | Eq(i1,i2) -> Eq(idx_idx_subst j i i1, idx_idx_subst j i i2)
  | Leq(i1,i2) -> Leq(idx_idx_subst j i i1, idx_idx_subst j i i2)
  | Lt(i1,i2) -> Lt(idx_idx_subst j i i1, idx_idx_subst j i i2)
  | Forall(xis,c) -> Forall(xis,constr_idx_subst j i c)
  | Exists(xis,c) -> Exists(xis,constr_idx_subst j i c)
  | Comment(s,c) -> Comment(s,constr_idx_subst j i c)


(*
 * t[j/i]
 *)
let rec type_idx_subst (j : la_idx_term) (i : la_idx_var) (t : la_type) : la_type =
  (type_status t,
   match type_head t with
    (TyUnit | TyBool | TyNat | TyVar _ | TyAlias _) -> type_head t
  | TyArr(t1,t2) -> TyArr(type_idx_subst j i t1,type_idx_subst j i t2)
  | TyTensor(t1,t2) -> TyTensor(type_idx_subst j i t1,type_idx_subst j i t2)
  | TyWith(t1,t2) -> TyWith(type_idx_subst j i t1,type_idx_subst j i t2)
  | TyBang(t) -> TyBang(type_idx_subst j i t)
  | TySum(t1,t2) -> TySum(type_idx_subst j i t1,type_idx_subst j i t2)
  | TyIForall(x,s,t) -> TyIForall(x,s,type_idx_subst j i t)
  | TyIExists(x,s,t) -> TyIExists(x,s,type_idx_subst j i t)
  | TyTForall(a,k,t) -> TyTForall(a,k,type_idx_subst j i t)
  | TyList(it,t) -> TyList(idx_idx_subst j i it,type_idx_subst j i t)
  | TyImplies(c,t) -> TyImplies(constr_idx_subst j i c, type_idx_subst j i t)
  | TyConj(c,t) -> TyConj(constr_idx_subst j i c, type_idx_subst j i t)
  | TyMonad(it',q,t) -> let t' = type_idx_subst j i t in
                        let q' = idx_idx_subst j i q in
                        TyMonad(idx_idx_subst j i it',q',t')
  | TyPot(it',q,t) -> let t' = type_idx_subst j i t in
                      let q' = idx_idx_subst j i q in
                      TyPot(idx_idx_subst j i it',q',t')
  | TyConstPot(it',t) -> TyConstPot(idx_idx_subst j i it',type_idx_subst j i t)
  | TyFamLam(k,s,t) -> TyFamLam(k,s,type_idx_subst j i t)
  | TyFamApp(t,it') -> TyFamApp(type_idx_subst j i t ,idx_idx_subst j i it')
  )
                    
let type_idx_binder_subst (j : la_idx_term) (i : la_idx_var_binder) (t : la_type) : la_type =
  match i with
    IWild -> t
  | IName i -> type_idx_subst j i t

(*t[t'/a]*)
let rec type_type_subst t' a t =
  (Unknown,
   match type_head t with
    (TyUnit | TyBool | TyNat | TyAlias _) -> type_head t
  | TyVar c -> if c.type_fresh_name = a.type_fresh_name
               then type_head t'
               else type_head t
  | TyArr(t1,t2) -> TyArr(type_type_subst t' a t1,type_type_subst t' a t2)
  | TyTensor(t1,t2) -> TyTensor(type_type_subst t' a t1,type_type_subst t' a t2)
  | TyWith(t1,t2) -> TyWith(type_type_subst t' a t1,type_type_subst t' a t2)
  | TyBang(t) -> TyBang(type_type_subst t' a t)
  | TySum(t1,t2) -> TySum(type_type_subst t' a t1,type_type_subst t' a t2)
  | TyIForall(x,s,t) -> TyIForall(x,s,type_type_subst t' a t)
  | TyIExists(x,s,t) -> TyIExists(x,s,type_type_subst t' a t)
  | TyTForall(b,k,t) -> TyTForall(b,k,type_type_subst t' a t)
  | TyList(x,t) -> TyList(x,type_type_subst t' a t)
  | TyImplies(c,t) -> TyImplies(c,type_type_subst t' a t)
  | TyConj(c,t) -> TyConj(c,type_type_subst t' a t)
  | TyMonad(k,q,t) -> TyMonad(k,q,type_type_subst t' a t)
  | TyPot(k,q,t) -> TyPot(k,q,type_type_subst t' a t)
  | TyConstPot(it,t) -> TyConstPot(it,type_type_subst t' a t)
  | TyFamLam(i,s,t) -> TyFamLam (i,s,type_type_subst t' a t)
  | TyFamApp(t,i) -> TyFamApp(type_type_subst t' a t,i)
  )

let type_type_binder_subst t' a t =
  match a with
    TWild -> t
  | TName a -> type_type_subst t' a t

(* e[t'/a] *)
let rec exp_type_subst t' a e =
  match e with
    (Const _ | Var _ | Nil | Absurd | Tick _ | Hole) -> e
  | Binop(b,e1,e2) -> Binop(b,exp_type_subst t' a e1,exp_type_subst t' a e2)
  | Lam(x,e) -> Lam(x,exp_type_subst t' a e)
  | App(e1,e2) -> App(exp_type_subst t' a e1,exp_type_subst t' a e2)
  | Ann(e,t) -> Ann(exp_type_subst t' a e,type_type_subst t' a t)
  | PPair(e1,e2) -> PPair(exp_type_subst t' a e1,exp_type_subst t' a e2)
  | PLet(e,x,y,e') -> PLet(exp_type_subst t' a e,x,y,exp_type_subst t' a e')
  | NPair(e1,e2) -> NPair(exp_type_subst t' a e1,exp_type_subst t' a e2)
  | Fst e -> Fst (exp_type_subst t' a e)
  | Snd e -> Snd (exp_type_subst t' a e)
  | Bang e -> Bang (exp_type_subst t' a e)
  | LetBang(e,x,e') -> LetBang(exp_type_subst t' a e,x,exp_type_subst t' a e')
  | Inl e -> Inl (exp_type_subst t' a e)
  | Inr e -> Inr (exp_type_subst t' a e)
  | SCase(e,x,e1,y,e2) -> SCase(exp_type_subst t' a e,x,exp_type_subst t' a e1,y,exp_type_subst t' a e2)
  | NCase(e,e1,n,e2) -> NCase(exp_type_subst t' a e,exp_type_subst t' a e1,n,exp_type_subst t' a e2)
  | Fix(x,e) -> Fix(x,exp_type_subst t' a e)
  | ILam(i,e) -> ILam(i,exp_type_subst t' a e)
  | IApp(e,i) -> IApp(exp_type_subst t' a e,i)
  | TLam(b,e) -> TLam(b,exp_type_subst t' a e)
  | TApp(e,t) -> TApp(exp_type_subst t' a e,t)
  | Cons(e1,e2) -> Cons(exp_type_subst t' a e1,exp_type_subst t' a e2)
  | LCase(e,e1,h,t,e2) -> LCase(exp_type_subst t' a e,exp_type_subst t' a e1,h,t,exp_type_subst t' a e2)
  | Pack (j,e) -> Pack (j,exp_type_subst t' a e)
  | Unpack(e,i,x,e') -> Unpack(exp_type_subst t' a e,i,x,exp_type_subst t' a e')
  | CLam e -> CLam (exp_type_subst t' a e)
  | CApp e -> CApp (exp_type_subst t' a e)
  | CPair e -> CPair (exp_type_subst t' a e)
  | CLet(e,x,e') -> CLet(exp_type_subst t' a e,x,exp_type_subst t' a e')
  | Ret e -> Ret (exp_type_subst t' a e)
  | Bind(e,x,e') -> Bind(exp_type_subst t' a e,x,exp_type_subst t' a e')
  | Store(i,q,e) -> Store(i,q,exp_type_subst t' a e)
  | StoreConst(it,e) -> StoreConst(it,exp_type_subst t' a e)
  | Release(e,x,e') -> Release(exp_type_subst t' a e,x,exp_type_subst t' a e')
  | Shift(e) -> Shift(exp_type_subst t' a e)
  | Ite(e,e1,e2) -> Ite(exp_type_subst t' a e,exp_type_subst t' a e1,exp_type_subst t' a e2)
  | Let(e,x,e') -> Let(exp_type_subst t' a e,x,exp_type_subst t' a e')

(*
(* d[t'/a] *)
let dec_type_subst t' a d =
  match d with
    TyDec(a,t,k) -> TyDec(a, type_type_subst t' a t, k)
  | ValDec(x,e,t) -> ValDec(x, exp_type_subst t' a e, type_type_subst t' a t)

(* p[t'/a] *)
let rec pgm_type_subst t' a p =
  match p with
    [] -> []
  | d::ds -> (dec_type_subst t' a d) :: (pgm_type_subst t' a ds)
*)