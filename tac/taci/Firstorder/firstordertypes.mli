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
*ParamSig:
* Acts as a parameter to Firstorder in order to change properties of
* the logic generated by Firstorder.
**********************************************************************)
module type ParamSig =
sig
  (** The print name of the logic. *)
  val name : string

  (** Determines whether or not strict nabla comparisons are used in the
    * axiom rule. *)
  val strictNabla : bool
  
  (** Indicates whether the logic is intuitionistic instead of classical. *)
  val intuitionistic : bool
end

(**********************************************************************
*TypesSig:
* Contains information about logic types, and useful operations on
* them.
**********************************************************************)
module type TypesSig =
sig
  (********************************************************************
  *formula:
  * Represent formulae in sequents.  Formulae consist of a local
  * context level and an abstract syntax formula.
  ********************************************************************)
  type formula_annotation = { context : int ; progressing_bound : int option }
  type formula =
    Formula of (formula_annotation * (Firstorderabsyn.annotation Firstorderabsyn.polarized))


  (********************************************************************
  *sequent:
  * A sequent has a left and right side, each a list of formulas, along
  * with an index approximating its signature (set of eigenvariables).
  * Additionally, there are three bounds: bound is the maximum number
  * of synchronous stages to do, and lemma_bound
  * is the number of times to introduce lemmas.
  ********************************************************************)
  type sequent = {
    lvl : int ;
    lhs : formula list ;
    rhs : formula list ;
    bound : int option ;
    lemma_bound : int option ;
  }

  (********************************************************************
  *proof:
  * rule: the name of the rule applied
  * formula: the formula on which the rule was applied
  * sequent: the sequent on which the rule was applied
  * params: the parameters (their names and their values); these are
  *   rule-specific
  * bindings:
  * subs: sub-proofs
  ********************************************************************)
  type proof = {
    rule : string;
    formula : formula option;
    sequent : sequent;
    params : (string * string) list;
    bindings : Term.term list;
    subs : proof list
  }

  (********************************************************************
  *lemmas:
  ********************************************************************)
  type lemma = string * Firstorderabsyn.annotation Firstorderabsyn.polarized * proof

  (********************************************************************
  *session:
  * A session is:
  *   tactical table
  *   definition table
  *   sequents
  *   proof builder
  *   undo info
  *   redo info
  *   lemmas
  ********************************************************************)  
  type session = {
    tactics :
      (session, (sequent, proof) Logic.tactic) Logic.tactical Logic.table ;
    definitions : (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table ;
    sequents : sequent list ; (* current goals *)
    builder : proof Logic.proofbuilder ;
    state : Term.state ;
    diff : Term.subst ;
    initial_namespace : Term.namespace ;
    proof_namespace   : Term.namespace ;
    theorem_name : string option ;
    theorem : (Firstorderabsyn.annotation Firstorderabsyn.polarized) option ;
    lemmas : lemma list
  }

  val annotateFormula : Firstorderabsyn.annotation -> string -> string
  val string_of_formula : formula -> string
  val string_of_formula_ast : formula -> string
  val xml_of_formula : formula -> string

  val parsePattern : string -> Firstorderabsyn.pattern_annotation Firstorderabsyn.polarized_pattern option
  val parseInvariant :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.abstraction option
  val parseFormula :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.polarized option
  val parseDefinition :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.definition option

  val parseTerm : string -> Term.term option

  val updateBound : int option -> int option
  val outOfBound  : int option -> bool
  
  val makeExistentialVar : string -> int -> int -> (int * Term.term)
  val makeUniversalVar : string -> int -> int -> (int * Term.term)
  val makeNablaVar : int -> int -> (int * int * Term.term)
  
  val modifyFormulaAnnotations :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    Firstorderabsyn.annotation Firstorderabsyn.polarized ->
    Firstorderabsyn.annotation Firstorderabsyn.polarized
  val modifySequentAnnotations :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    sequent ->
    sequent
  
  val composeModifiers :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)

  val freezeModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val unfreezeModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val unfocusModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val idModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  
  val focusFormula : formula -> formula
  val freezeFormula : formula -> formula
  
  val makeFormula :
    Firstorderabsyn.annotation Firstorderabsyn.polarized -> formula
  
  val stringToIntDefault : string -> int -> int 
end

(**********************************************************************
*Types:
* Constructs a TypesSig.  The functor takes an output module because
* some of the operations need to report an error to the user.
**********************************************************************)
module Types : functor (O : Output.Output) -> TypesSig
