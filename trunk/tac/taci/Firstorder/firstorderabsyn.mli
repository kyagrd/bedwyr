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
* Firstorderabsyn
***********************************************************************
* This module defines the abstract syntax of formulas for the logics
* defined in Firstorder (see firstorder.mli).  Terms within formulas
* are represented using the ndcore library (see ndcore/term.mli).
**********************************************************************)
exception SyntaxError of string
exception SemanticError of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * string list * formula
  | NuFormula of string * string list * formula
  
  | AbstractionFormula of string * formula
  | ApplicationFormula of formula * term list
  
  | AtomicFormula of string * term list
  | DBFormula of int * string * int (* lifts, name, index *)
  
type fixpoint =
    Inductive
  | CoInductive

type predefinition =
  PreDefinition of (string * string list * formula * fixpoint)

type definition =
  Definition of (string * int * formula * fixpoint)

type state
type unifyresult =
    UnifyFailed
  | UnifySucceeded of state
  | UnifyError of string

val makeAnonymousFormula : unit -> formula
val makeAnonymousTerm : unit -> term
val isAnonymousTerm : term -> bool
val isAnonymousFormula : formula -> bool

val mapFormula : (formula -> formula) -> (term -> term) -> formula -> formula
val abstract : string -> formula -> formula
val abstractDummyWithoutLambdas : formula -> formula
val abstractVar : term -> formula -> formula
val abstractVarWithoutLambdas : term -> formula -> formula
val apply : term list -> formula -> formula option
val applyFixpoint : formula -> formula -> formula option
val string_of_definition : definition -> string
val string_of_formula : generic:string list -> formula -> string
val string_of_formula_ast : generic:string list -> formula -> string

val eliminateNablas : term list -> formula -> formula

val undoUnify : state -> unit
val rightUnify : term -> term -> unifyresult
val leftUnify : term -> term -> unifyresult
val unifyList : (term -> term -> unifyresult) -> term list -> term list -> unifyresult
val matchFormula : formula -> formula -> bool

val getDefinitionArity : definition -> int
val getDefinitionBody : definition -> formula

val getTermHeadAndArgs : term -> (string * term list) option
