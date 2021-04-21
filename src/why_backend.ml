(* Joseph Cutler, 2021 *)
open Why3


module type INSTANCE_DATA = sig
  val prover_name : string
  val time_limit : int
end

module type SOLVER_INTERFACE = sig
    val solve : Constr_elab.elab_constr list -> string list -> unit
end

module MakeSolver(D : INSTANCE_DATA) (Debug : Support.DEBUG_OUTPUT) : SOLVER_INTERFACE = struct
  let config : Whyconf.config = Whyconf.read_config None
  let main : Whyconf.main = Whyconf.get_main config

  (*let provers : Whyconf.config_prover Whyconf.Mprover.t = Whyconf.get_provers config*)
  let env : Env.env = Env.create_env @@ (Whyconf.loadpath main) @ ["./"]

  let prover_config : Whyconf.config_prover =
    let fp = Whyconf.parse_filter_prover D.prover_name in
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      Printf.eprintf "Prover %s not installed or not configured\n" D.prover_name;
      exit 0
    end else
      snd (Whyconf.Mprover.max_binding provers)

  let prover_driver : Driver.driver =
    Whyconf.load_driver main env prover_config.Whyconf.driver []

  let sum_real_theory : Theory.theory = Env.read_theory env ["la"] "SumReal"
  let sum_nat_theory : Theory.theory = Env.read_theory env ["la"] "SumNat"

  module WhyTrans = Why_trans.MakeTranslator(struct
      let config = config
      let main = main
      let env = env
      let prover_config = prover_config
      let prover_driver = prover_driver
      let sum_real_theory = sum_real_theory
      let sum_nat_theory = sum_nat_theory
  end)

  let rec zip3 xs ys zs =
    match xs, ys, zs with
      [], _, _ -> []
    | _, [], _ -> []
    | _, _, [] -> []
    | x::xs, y::ys, z::zs -> (x,y,z) :: (zip3 xs ys zs)

  open Format
  let solve ecs goal_names =
    let terms : Term.term list = List.map WhyTrans.do_translate ecs in

    let tasks = List.map (fun _ -> None) terms in
    let tasks = List.map (fun t -> Task.use_export t WhyTrans.int_theory) tasks in
    let tasks = List.map (fun t -> Task.use_export t WhyTrans.real_theory) tasks in
    let tasks = List.map (fun t -> Task.use_export t WhyTrans.int_to_real_theory) tasks in
    (* Without this, arrow types don't work!! *)
    let tasks = List.map (fun t -> Task.use_export t Theory.highord_theory) tasks in
    let tasks = List.map (fun t -> Task.use_export t sum_real_theory) tasks in
    let tasks = List.map (fun t -> Task.use_export t sum_nat_theory) tasks in

    let goal_ids = List.map (fun x -> Decl.create_prsymbol (Ident.id_fresh x)) goal_names in

    let tasks = List.map (fun(id,task,term) -> Task.add_prop_decl task Decl.Pgoal id term)
                (zip3 goal_ids tasks terms) in

    let () = Debug.full_dump(fun () ->  List.iter (fun t -> printf "@[task is:@\n%a@]@.\n" Pretty.print_task t) tasks) in

    Printf.printf "Starting solver";
    let start_solve = Unix.gettimeofday() in

    let results = List.map (fun task -> Call_provers.wait_on_call (Driver.prove_task ~limit:{Call_provers.empty_limit with limit_time = D.time_limit}
                                                  ~command:prover_config.Whyconf.command
                                                  prover_driver task)) 
                  tasks in

    let end_solve = Unix.gettimeofday() in

    List.iter (fun (x,r) -> printf "@[For %s, prover %s answers %a@."
      x D.prover_name (Call_provers.print_prover_result ~json_model:true) r) (List.combine goal_names results);

    Printf.printf "Solving time: %f\n" (end_solve -. start_solve)

end