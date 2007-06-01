module Table : Map.S with type key = String.t
type 'a table = 'a Table.t

(**********************************************************************
*Logic:
*
**********************************************************************)
type 'a tactic = 'a -> ('a list -> unit) -> unit
type 'a tactical = 'a Absyn.tactical list -> 'a
module type Logic =
sig
  val name : string
  val info : string
  val start : string
  
  type session
  val incl : string list -> session -> session
  val reset : unit -> session
  val operator : string -> string -> int -> session -> session
  val prove : string -> string -> session -> session
  val definition : string -> session -> session
  
  type sequent
  val validSequent : session -> bool
  val sequent : session -> (sequent * session) option
  val sequents : session -> sequent list
  val string_of_sequents : session -> string
  val updateSequents : sequent list -> session -> session
  
  val tacticals : (sequent tactic) tactical table
end

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module type LogicSig =
sig
  type logic_sequent
end

module GenericTacticals : functor (L : LogicSig) -> functor (O : Output.Output) ->
sig
  type logic_tactic = (L.logic_sequent tactic)
  type logic_tactical = logic_tactic tactical

  val invalidArguments : string -> logic_tactic
  val failureTactical : logic_tactic
  val idTactical : logic_tactic
  val applyTactical : logic_tactic -> logic_tactic
  val orElseTactical : logic_tactic -> logic_tactic -> logic_tactic
  val thenTactical : logic_tactic -> logic_tactic -> logic_tactic
  val repeatTactical : logic_tactic -> logic_tactic
  val tryTactical : logic_tactic -> logic_tactic
  val completeTactical : logic_tactic -> logic_tactic
  val tacticals : logic_tactical table
end