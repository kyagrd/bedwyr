module Table : Map.S with type key = String.t
type 'a table = 'a Table.t
val contains : string -> 'a Table.t -> bool
val find : string -> 'a Table.t -> 'a option

(**********************************************************************
*Tactics and Tacticals:
* The type of a sequent is abstracted from the types of tactics and
* and tacticals so that a logic cannot redefine the types of tactics
* and tacticals, and need not copy the types' definitions into its
* body.  It is assumed that, in the following types, the type variable
* 'a will only ever be of type L.sequent where L is a module of type
* Logic, and the type variable 'b will only ever be of type L.proof
* with similar constraints.
**********************************************************************)
(*  Continuations *)
type continue = unit -> unit
type failure = unit -> unit

(*  Pre Tactics *)
type ('a, 'b) pretactic =
  'a -> ('a list -> ('b list -> 'b) -> continue -> unit) -> failure -> unit

(*  Tactics *)
type 'a proofbuilder = 'a list -> 'a list
type ('a, 'b) success = 'a list -> 'a list -> 'b proofbuilder -> continue -> unit
type ('a, 'b) tactic = 'a list -> ('a, 'b) success -> failure -> unit

(*  Tacticals *)
type ('a, 'b) tactical = 'a -> 'b Absyn.tactical list -> 'b

val composeProofBuilders : 'a proofbuilder -> 'a proofbuilder -> 'a proofbuilder
val idProofBuilder : 'a proofbuilder

(**********************************************************************
*Logic:
* This module signature provides an interface for all logics.
**********************************************************************)
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
  val definitions : string list -> session -> session
  val undo : session -> session
  val redo : session -> session
  
  type sequent
  val validSequent : session -> bool
  val sequents : session -> sequent list
  val string_of_sequents : sequent list -> string
    
  type proof
  val proof : session -> proof proofbuilder
  val string_of_proofs : proof list -> string
  
  val update : sequent list -> proof proofbuilder -> session -> session

  val tacticals : session -> (session, (sequent, proof) tactic) tactical table
  val defineTactical : string -> (session, (sequent, proof) tactic) tactical -> session -> session
end

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module type LogicSig =
sig
  type logic_session
  type logic_sequent
  type logic_proof
end

module GenericTacticals : functor (L : LogicSig) -> functor (O : Output.Output) ->
sig
  type logic_pretactic = (L.logic_sequent, L.logic_proof) pretactic
  type logic_tactic = (L.logic_sequent, L.logic_proof) tactic
  type logic_tactical = (L.logic_session, logic_tactic) tactical

  val makeTactical : logic_pretactic -> logic_tactic
  val invalidArguments : string -> logic_tactic
  val failureTactical : logic_tactic
  val idTactical : logic_tactic
  val applyTactical : logic_tactic -> logic_tactic
  val orElseTactical : logic_tactic -> logic_tactic -> logic_tactic
  val orElseListTactical : logic_tactic list -> logic_tactic
  val thenTactical : logic_tactic -> logic_tactic -> logic_tactic
  val repeatTactical : logic_tactic -> logic_tactic
  val iterateTactical : logic_tactic -> logic_tactic
  val tryTactical : logic_tactic -> logic_tactic
  val completeTactical : logic_tactic -> logic_tactic
  val tacticals : logic_tactical table
end