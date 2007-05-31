module Table : Map.S with type key = String.t
type 'a table = 'a Table.t

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
  
  type tactic = sequent -> (sequent list -> unit) -> unit
  type tactical = string -> tactic

  val tacticals : tactical table
end

module type LogicSig =
sig
  type sequent
  type tactic = sequent -> (sequent list -> unit) -> unit
end

module GenericTacticals : functor (L : LogicSig) ->
sig
  val failureTactical : L.tactic
  val idTactical : L.tactic
  val applyTactical : L.tactic -> L.tactic
  val orTactical : L.tactic -> L.tactic -> L.tactic
  val thenTactical : L.tactic -> L.tactic -> L.tactic
  val repeatTactical : L.tactic -> L.tactic
end
