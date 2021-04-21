(* Joseph Cutler, 2021 *)
open Constr_elab
open Why3

module type WHY_3_DATA = sig
  val config : Whyconf.config
  val main : Whyconf.main
  val env : Env.env

  val prover_config : Whyconf.config_prover
  val prover_driver : Driver.driver

  val sum_real_theory : Theory.theory
  val sum_nat_theory : Theory.theory
end

module MakeTranslator(Why3Data : WHY_3_DATA) = struct
  exception TransError of string

  let env = Why3Data.env

  let int_theory : Theory.theory = Env.read_theory env ["int"] "Int"
  let real_theory : Theory.theory = Env.read_theory env ["real"] "RealInfix"
  let int_to_real_theory : Theory.theory = Env.read_theory env ["real"] "FromInt"

  let plus_int_symbol : Term.lsymbol =
    Theory.ns_find_ls int_theory.Theory.th_export ["infix +"]

  let plus_real_symbol : Term.lsymbol =
    Theory.ns_find_ls real_theory.Theory.th_export ["infix +."]

  let minus_int_symbol : Term.lsymbol =
    Theory.ns_find_ls int_theory.Theory.th_export ["infix -"]

  let minus_real_symbol : Term.lsymbol =
    Theory.ns_find_ls real_theory.Theory.th_export ["infix -."]

  let mult_int_symbol : Term.lsymbol =
    Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]

  let mult_real_symbol : Term.lsymbol =
    Theory.ns_find_ls real_theory.Theory.th_export ["infix *."]

  let leq_int_symbol : Term.lsymbol =
    Theory.ns_find_ls int_theory.Theory.th_export ["infix <="]

  let leq_real_symbol : Term.lsymbol =
    Theory.ns_find_ls real_theory.Theory.th_export ["infix <=."]

  let lt_int_symbol : Term.lsymbol =
    Theory.ns_find_ls int_theory.Theory.th_export ["infix <"]

  let lt_real_symbol : Term.lsymbol =
    Theory.ns_find_ls real_theory.Theory.th_export ["infix <."]


  let sum_real_symbol : Term.lsymbol =
    Theory.ns_find_ls Why3Data.sum_real_theory.Theory.th_export ["sum"]

  let sum_nat_symbol : Term.lsymbol =
    Theory.ns_find_ls Why3Data.sum_nat_theory.Theory.th_export ["sum"]

  let int_to_real_symbol : Term.lsymbol =
    Theory.ns_find_ls int_to_real_theory.Theory.th_export ["from_int"]

  let why3_posreal f =
    let (f,i) = modf f in
    let is = Printf.sprintf "%.0f" i in
    let fs = String.sub (Printf.sprintf "%.3f" f) 2 3 in
    Term.t_const (Why3.Constant.ConstReal (Why3.Number.real_literal ~radix:10 ~neg:false ~int:is ~frac:fs ~exp:None)) Ty.ty_real
    
    


  module Map = Map.Make(struct type t = string let compare = String.compare end)
  type vmap_t = Term.vsymbol Map.t


  let base_sort_to_ty (s : elab_base_sort) : Ty.ty =
    match s with
      ESoNat -> Ty.ty_int
    | ESoPosReal -> Ty.ty_real

  let rec sort_to_ty (s : elab_sort) : Ty.ty =
    match s with
      ESoBase bs -> base_sort_to_ty bs
    | ESoArr(bs1,s2) -> Ty.ty_func (base_sort_to_ty bs1) (sort_to_ty s2)

  (*
   * Conditions to restrict quantifier domains, since Nat is translated to Int, and PosReal
   * to Real.
   *)
  let rec ty_refinement_term (x : Term.vsymbol) (s : elab_sort) : Term.term =
    let rec arg_sorts s : elab_base_sort list =
      match s with
        ESoBase _ -> []
      | ESoArr(bs1,s) -> bs1 :: (arg_sorts s)

    (* Get return sort of function *)
    in let rec ret_sort s =
         match s with
           ESoBase b -> b
         | ESoArr(_,s) -> ret_sort s

    in match s with
      ESoBase ESoNat -> let zero = Term.t_nat_const 0 in
                        Term.t_app_infer leq_int_symbol [zero;Term.t_var x]
    (* Positive reals are reals that... are positive *)
    | ESoBase ESoPosReal -> let zero = Term.t_real_const BigInt.zero (* ??? *) in
                           Term.t_app_infer leq_real_symbol [zero;Term.t_var x]
    (* Any fully saturated application of x, with arguments of the right type, lands in the right type *)
    | ESoArr(_,s') -> let ss = arg_sorts s in
                      let s_ret = ret_sort s' in
                      let xs = List.map (fun s -> Term.create_vsymbol (Ident.id_fresh "x") (base_sort_to_ty s)) ss in
                      let xs_terms : Term.term list = List.map Term.t_var xs in
                      let xs_refinements = List.map (fun (x,s) -> ty_refinement_term x (ESoBase s)) (List.combine xs ss) in
                      let args_refined = List.fold_right Term.t_and xs_refinements Term.t_true in
                      let x_saturated : Term.term = List.fold_right (fun x f -> Term.t_func_app f x) (List.rev xs_terms) (Term.t_var x) in
                      let t = match s_ret with
                                ESoNat -> let zero = Term.t_nat_const 0 in
                                          Term.t_app_infer leq_int_symbol [zero;x_saturated]
                              | ESoPosReal -> let zero = Term.t_real_const BigInt.zero in
                                              Term.t_app_infer leq_real_symbol [zero;x_saturated]
                      in Term.t_forall_close xs [] (Term.t_implies args_refined t)

  let rec iterm_to_term (env : vmap_t) (it : elab_idx_term) : Term.term =
    match it with
      EConst(ENat n) -> Term.t_nat_const n
    | EConst(EReal r) -> why3_posreal r
    | EVar x -> (match Map.find_opt x env with
                   Some sym_x -> Term.t_var sym_x
                 | None -> raise (TransError ("Variable " ^ x ^ " not yet created.")))
    | EPlusNat(it1,it2) -> let t1 = iterm_to_term env it1 in
                           let t2 = iterm_to_term env it2 in
                           Term.t_app_infer plus_int_symbol [t1;t2]
    | EPlusReal(it1,it2) -> let t1 = iterm_to_term env it1 in
                            let t2 = iterm_to_term env it2 in
                            Term.t_app_infer plus_real_symbol [t1;t2]
    | EMinusNat(it1,it2) -> let t1 = iterm_to_term env it1 in
                            let t2 = iterm_to_term env it2 in
                            Term.t_app_infer minus_int_symbol [t1;t2]
    | EMinusReal(it1,it2) -> let t1 = iterm_to_term env it1 in
                             let t2 = iterm_to_term env it2 in
                             Term.t_app_infer minus_real_symbol [t1;t2]
    | EMultNat(n,it) -> let t1 = iterm_to_term env it in
                        let t2 = Term.t_nat_const n in
                        Term.t_app_infer mult_int_symbol [t1;t2]
    | EMultReal(r,it) -> let t1 = iterm_to_term env it in
                         let t2 = why3_posreal r in
                         Term.t_app_infer mult_real_symbol [t1;t2]
    | EFamLam(i,s,it) -> let sym_i = Term.create_vsymbol (Ident.id_fresh i) (base_sort_to_ty s) in
                         let env = Map.add i sym_i env in
                         let it' = iterm_to_term env it in
                         Term.t_lambda [sym_i] [] it'
    | EFamApp(it1,it2) -> let t1 = iterm_to_term env it1 in
                          let t2 = iterm_to_term env it2 in
                          Term.t_func_app t1 t2
    | ESumReal(i,f,lb,ub) -> let sym_i = Term.create_vsymbol (Ident.id_fresh i) Ty.ty_int in
                             let env = Map.add i sym_i env in
                             let f' = iterm_to_term env f in
                             let lb' = iterm_to_term env lb in
                             let ub' = iterm_to_term env ub in
                             let func = Term.t_lambda [sym_i] [] f' in
                             Term.t_app_infer sum_real_symbol [lb';ub';func]
    | ESumNat(i,f,lb,ub) -> let sym_i = Term.create_vsymbol (Ident.id_fresh i) Ty.ty_int in
                            let env = Map.add i sym_i env in
                            let f' = iterm_to_term env f in
                            let lb' = iterm_to_term env lb in
                            let ub' = iterm_to_term env ub in
                            let func = Term.t_lambda [sym_i] [] f' in
                            Term.t_app_infer sum_nat_symbol [lb';ub';func]
    | ENtoR it -> let t = iterm_to_term env it in
                  Term.t_app_infer int_to_real_symbol [t]
  let rec constr_to_term (env : vmap_t) (c : elab_constr) : Term.term =
    match c with
      ETop -> Term.t_true
    | EBot -> Term.t_false
    | EConj(cs) -> Term.t_and_simp_l (List.map (constr_to_term env) cs)
    (*| EConj([]) -> Term.t_true*)
    (*( EConj(c::cs) -> List.fold_lleftTerm.t_and (cconstr_to_term env c) (ist.map (constr_to_term env) cs) *)
    | EImp(c1,c2) -> Term.t_implies (constr_to_term env c1) (constr_to_term env c2)
    | EForall(x,s,c) -> let sym_x = Term.create_vsymbol (Ident.id_fresh x) (sort_to_ty s) in
                        let t = constr_to_term (Map.add x sym_x env) c in
                        let t' = Term.t_implies (ty_refinement_term sym_x s) t in
                        Term.t_forall_close [sym_x] [] t'
    | EExists(x,s,c) -> let sym_x = Term.create_vsymbol (Ident.id_fresh x) (sort_to_ty s) in
                        let t = constr_to_term (Map.add x sym_x env) c in
                        let t' = Term.t_and (ty_refinement_term sym_x s) t in
                        Term.t_exists_close [sym_x] [] t'
    | EEqNat(it1,it2) -> Term.t_equ (iterm_to_term env it1) (iterm_to_term env it2)
    | EEqReal(it1,it2) -> Term.t_equ (iterm_to_term env it1) (iterm_to_term env it2)
    | ELeqNat(it1,it2) -> let t1' = iterm_to_term env it1 in
                          let t2' = iterm_to_term env it2 in
                          Term.t_app_infer leq_int_symbol [t1';t2']
    | ELtNat(it1,it2) -> let t1' = iterm_to_term env it1 in
                         let t2' = iterm_to_term env it2 in
                         Term.t_app_infer lt_int_symbol [t1';t2']
    | ELeqReal(it1,it2) -> let t1' = iterm_to_term env it1 in
                           let t2' = iterm_to_term env it2 in
                           Term.t_app_infer leq_real_symbol [t1';t2']
    | ELtReal(it1,it2) -> let t1' = iterm_to_term env it1 in
                          let t2' = iterm_to_term env it2 in
                          Term.t_app_infer lt_real_symbol [t1';t2']

  let do_translate (c : elab_constr) : Term.term = 
    constr_to_term Map.empty c
end
