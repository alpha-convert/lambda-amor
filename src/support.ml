(* Joseph Cutler, 2021 *)
module CodeLoc = struct
  (* file name, line number, column number*)
  type t = Loc of string * int * int | Generated

  let loc s l c = Loc(s,l,c)
end

module type DEBUG_INFO = sig
  val verbosity_level : int ref
end

module type DEBUG_OUTPUT = sig
  val at_verbosity : int -> (unit -> unit) -> unit

  val default : (unit -> unit) -> unit
  val phase_info : (unit -> unit) -> unit
  val full_dump : (unit -> unit) -> unit
end

module DebugOutput(D : DEBUG_INFO) : DEBUG_OUTPUT = struct
  let at_verbosity n f = if !(D.verbosity_level) >= n then f() else ()

  let default f = at_verbosity 0 f

  let phase_info f = at_verbosity 1 f

  let full_dump f = at_verbosity 2 f
end