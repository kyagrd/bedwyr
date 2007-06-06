(**********************************************************************
*Interface:
* This functor contructs a toplevel interface using the given
* interpreter.  The interface implements the toplevel loop, reading
* input and passing it to the interpreter for processing.
**********************************************************************)
module type Interface =
sig
  (********************************************************************
  *interpret:
  * This is the toplevel loop.  It returns only when the interpreter
  * exits.
  ********************************************************************)
  val interpret : unit -> unit
end
module Make : functor (I : Interpreter.Interpreter) -> Interface
