(* Joseph Cutler, 2021 *)
module type INSTANCE_DATA = sig
    val prover_name : string
    val time_limit : int
end

module type SOLVER_INTERFACE = sig
    val solve : Constr_elab.elab_constr list -> string list -> unit
end

module MakeSolver(Data : INSTANCE_DATA) (Debug : Support.DEBUG_OUTPUT) : SOLVER_INTERFACE