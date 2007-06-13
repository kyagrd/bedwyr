(**********************************************************************
*Interpreter:
* This functor builds an interpreter that uses the given output for
* writing and the given logic for reasoning.
**********************************************************************)
module type Interpreter =
sig
  type session
  exception Exit of session
  exception Logic of string
  
  val onStart : unit -> session
  val onEnd : session -> unit
  val onPrompt : session -> session
  val onInput : session -> session 
end
module Make : functor (O : Output.Output) -> functor (L : Logic.Logic) -> Interpreter
