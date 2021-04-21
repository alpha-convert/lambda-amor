(* Joseph Cutler, 2021 *)

let infile : string ref = ref ""
let outfile : string option ref = ref None
let prover_name : string ref = ref "z3"
let time_limit : int ref = ref 10
let verbosity_level : int ref = ref 0
let potvec_length : int ref = ref 3


module DebugOutput = Support.DebugOutput(struct
  let verbosity_level = verbosity_level
end)

let at_verbosity n f = if !verbosity_level >= n then f () else ()

let arg_options = [
  "-p", Arg.Set_string prover_name, "Prover: set by default to z3.";
  "-o", Arg.String (fun s -> outfile := Some s), "Dump verbose output to file (TODO)";
  "-t", Arg.Set_int time_limit, "Set time limit for constraint solving to n (by defalt 10s per goal)";
  "-v", Arg.Set_int verbosity_level, "Set verbosity level to n (0: Default, 1: Phase Information, 2: Full Debug)";
  "-k", Arg.Set_int potvec_length, "Set potential vector elaboration length. (by default 3) "
]

let parse_args () =
  Arg.parse arg_options (fun s ->
     infile := s
  ) "Usage: lambda-amor [options] infile "

let parse_from_file () : Syntax.la_pgm * string list =
  let ic = open_in !infile in
  let lexbuf = Lexing.from_channel ic in
  let p = Parser.pgm Lexer.main lexbuf in
  let fun_names = List.filter_map (fun dec ->
                    match dec with
                      Syntax.ValDec (x,_,_) -> Some (x.ident_source_name)
                    | Syntax.TyDec (a,_,_) -> Some (a.type_source_name)
                    | Syntax.IdxDec (i,_,_) -> Some (i.idx_source_name)
                    | Syntax.DoDec (x,_,_,_,_) -> Some (x.ident_source_name)
                  ) p in
  (p,fun_names)

let print_dec d =
  DebugOutput.full_dump(fun () ->
    match d with
      Syntax.ValDec (x,e,t) -> Printf.printf "let %s : %s = %s\n" x.ident_source_name  (Syntax.show_la_type t) (Syntax.show_la_exp e)
    | Syntax.TyDec (a,t,k) -> Printf.printf "type %s : %s = %s\n" a.type_source_name (Syntax.show_la_kind k) (Syntax.show_la_type t)
    | Syntax.IdxDec (j,it,s) -> Printf.printf "idx %s : %s = %s\n" j.idx_source_name (Syntax.show_la_sort s) (Syntax.show_la_idx_term it)
    | Syntax.DoDec(x,it1,it2,t,e) -> Printf.printf "do %s : M(%s,%s) (%s) <- %s" x.ident_source_name (Syntax.show_la_idx_term it1) (Syntax.show_la_idx_term it2) (Syntax.show_la_type t) (Syntax.show_la_exp e)
  )

let tycheck_pgm p =
  (* Checking phase *)
  let res = Tycheck.check_pgm p (Ctx.empty,Env.empty) in
  let cs = match res with
           Ok (cs,_) -> cs
         | Fail z -> Printf.printf "%s" (Tyerror.pp z) ; exit 1 in
  List.iter (fun c ->
    DebugOutput.full_dump (fun () -> Printf.printf "Constraint generated: %s\n" (Syntax.constr_pp c))
    ) cs ;
  (* Optimize phase *)
  let ocs = List.map Constr_optimize.do_optimize cs in
  let formatted_cs = List.map(fun (d,c) ->
    match d with
      Syntax.IdxDec(i,it,s) -> `IdxDec(i,it,s,c)
    | _ -> `OtherDec c
  ) (List.combine p ocs) in
  let ecs = 
    let emp = Constr_elab.IMap.empty in
    match (Constr_elab.elab_decs !potvec_length formatted_cs) (emp,emp) with
      `Ok ecs -> ecs
    | `Fail s -> Printf.printf "Failed: %s" s ; exit 1
  in ecs

let solve_constraints ecs goal_names =
  let module Solver = Why_backend.MakeSolver(struct
    let prover_name = !prover_name
    let time_limit = !time_limit
  end) (DebugOutput) in
  (*actually count only this step- don't worry about the setup*)
  Solver.solve ecs goal_names

let run_pgm p =
  let print_result (r : Interp.dodec_result) =
    DebugOutput.default (fun () -> Printf.printf "Result of %s: %s\nActual Cost: %F, Static Cost: %F\n" (r.name.ident_source_name) (Interp.pp_value @@ r.return_val) (r.actual_cost) (r.static_cost))
  in
  let results = Interp.run p in
  let _ = List.map print_result results in ()

let main () =
  let start = Unix.gettimeofday() in
  parse_args();
  (* Parse phase *)
  let (p,goal_names) = parse_from_file () in
  (* Freshen phase*)
  let p = Freshen.do_freshen_pgm p in
  DebugOutput.full_dump (fun () -> List.iter print_dec p) ;
  let ecs = tycheck_pgm p in
  let constr_gend = Unix.gettimeofday() in
  solve_constraints ecs goal_names;
  (* Only do this if the pgm typechecks, lol. *)
  run_pgm p ;
  let pgm_end = Unix.gettimeofday() in
  DebugOutput.default(fun () ->
    Printf.printf "Tycheck Time: %f\nTotal time: %f\n" (constr_gend -. start) (pgm_end -. start)
  )

let _ = main()