module type Interpreter =
sig
  type session
  exception Exit of session
  
  val onStart : unit -> session
  val onEnd : session -> unit
  val onPrompt : session -> session
  val onInput : string -> session -> session 
end

module Make : functor (O : Output.Output) -> functor (L : Logic.Logic) -> Interpreter
