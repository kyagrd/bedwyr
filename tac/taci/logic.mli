(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
(**********************************************************************
* Logic
***********************************************************************
* This module contains the signature Logic that every logic must
* implement in order to be able to be used by Taci.  This signature is
* explained in detain in /tac/taci/README.  Additionally a functor that
* creates a module with a set of generic tacticals (tacticals that any
* logic will be able to use provided it implements the Logic signature)
* is included.
**********************************************************************)
exception Interrupt

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
type ('a, 'b) success =
  'a list -> 'a list -> 'b proofbuilder -> continue -> unit
type ('a, 'b) tactic = 'a list -> ('a, 'b) success -> failure -> unit

(*  Tacticals *)
type ('a, 'b) tactical = 'a -> 'b Absyn.tactical list -> 'b

val composeProofBuilders : 'a proofbuilder -> 'a proofbuilder -> 'a proofbuilder
val idProofBuilder : 'a proofbuilder

(**********************************************************************
*Logic:
* This module signature provides an interface for all logics.  For more
* information regarding the assumptions made about the types and functions
* contained in this signature, see tac/taci/README.
**********************************************************************)
module type Logic =
sig
  val name : string
  val info : string
  val start : string

  type session
  val incl : string list -> session -> session
  val reset : unit -> session
  val lemma : string -> string -> session -> session
  val theorem : string -> string -> session -> session
  val proved : session -> session
  val lemmas : session -> session
  val definitions : string list -> session -> session
  val undo : session -> session
  val redo : session -> session
  val logicDefined : string -> string list -> session -> session
  
  type sequent
  val validSequent : session -> bool
  val sequents : session -> sequent list
  val string_of_sequents : session -> string

  val theoremName : session -> string

  type proof
  val proof : session -> proof proofbuilder
  val string_of_proofs : session -> string

  val update : sequent list -> proof proofbuilder -> session -> session

  val tacticals : session -> (session, (sequent, proof) tactic) tactical table
  val defineTactical :
   string -> (session, (sequent, proof) tactic) tactical -> session -> session
end

(**********************************************************************
*LogicSig:
* Due to the way O'Caml deals with recursive modules (or rather, the
* way it more or less doesn't) a logic can only make use of the
* generic tacticals defined in the GenericTacticals functor by creating
* a structure implementing the below signature and then applying the
* functor to it.  A better way should really be found.
*
* In general, to do so a logic will have lines similar to the following,
* assuming it has already defined the required types session, sequent,
* and proof:
*
*   module Sig =
*   struct
*     type logic_session = session
*     type logic_sequent = sequent
*     type logic_proof = proof
*   end
*   module G = Logic.GenericTacticals
*
**********************************************************************)
module type LogicSig =
sig
  type logic_session
  type logic_sequent
  type logic_proof
end

(**********************************************************************
*GenericTacticals:
* A number of tacticals that are logic independent.
**********************************************************************)
module GenericTacticals : functor (L : LogicSig) -> functor (O : Output.Output) ->
sig
  type logic_pretactic = (L.logic_sequent, L.logic_proof) pretactic
  type logic_tactic = (L.logic_sequent, L.logic_proof) tactic
  type logic_tactical = (L.logic_session, logic_tactic) tactical

  val makeTactical : logic_pretactic -> logic_tactic
  val invalidArguments : string -> logic_tactic
  val failureTactical : logic_tactic
  val idTactical : logic_tactic
  val admitTactical : (L.logic_sequent -> L.logic_proof) -> logic_tactic
  val orElseTactical : logic_tactic -> logic_tactic -> logic_tactic
  val orElseListTactical : logic_tactic list -> logic_tactic
  val cutThenTactical : (unit -> unit -> unit) -> logic_tactic -> logic_tactic -> logic_tactic
  val thenTactical : logic_tactic -> logic_tactic -> logic_tactic
  val andThenTactical : logic_tactic -> logic_tactic list -> logic_tactic
  val repeatTactical : logic_tactic -> logic_tactic
  val cutRepeatTactical : (unit -> unit -> unit) -> logic_tactic -> logic_tactic
  val firstTactical : logic_tactic -> logic_tactic
  val iterateTactical : logic_tactic -> logic_tactic
  val tryTactical : logic_tactic -> logic_tactic
  val completeTactical : logic_tactic -> logic_tactic
  val tacticals : logic_tactical table
end
