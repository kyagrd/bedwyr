module Make : functor (I : Interpreter.Interpreter) ->
sig
  val interpret : unit -> unit
end
