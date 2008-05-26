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

type fixpoint =
    Inductive
  | CoInductive
(*
type polarity =
    Synchronous
  | Asynchronous
*)
type quantifier =
    Pi
  | Sigma
  | Nabla

type connective =
    And
  | Or 
  | Imp

type 'a polarized = ('a * 'a formula)

and 'a predicate = 
    FixpointFormula of (fixpoint * (string * string list * 'a abstraction))
  | DBFormula of int * string * int
  | AtomicFormula of string

and 'a abstraction = 
    AbstractionFormula of (string * 'a abstraction)
  | AbstractionBody of 'a polarized

and 'a formula =
    BinaryFormula of (connective * 'a polarized * 'a polarized)
  | EqualityFormula of (term * term)
  | QuantifiedFormula of (quantifier * 'a abstraction)
  | ApplicationFormula of ('a predicate * term list)

type 'a predefinition =
  PreDefinition of (string * string list * 'a polarized * fixpoint)

type 'a definition =
  Definition of (string * int * 'a polarized * fixpoint)


type ('a,'b,'c,'d,'e) mapf = {polf : 'a polarized -> 'b ; predf : 'a predicate -> 'c ; abstf : 'a abstraction -> 'd ; formf : 'a formula -> 'e}

type state
type unifyresult =
    UnifyFailed
  | UnifySucceeded of state
  | UnifyError of string

(*val makeAnonymousFormula : unit -> 'a weak
val isAnonymousFormula : formula -> bool *)

val isAnonymousTerm : term -> bool 
val makeAnonymousTerm : unit -> term

val mapFormula : (unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) mapf) -> (term -> term) -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) mapf
val terms_polarized : 'a polarized -> term list
val abstract : string -> ('a, 'a abstraction, unit, 'a abstraction, unit) mapf
val abstractDummyWithoutLambdas : unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) mapf
val abstractVar : term -> ('a, 'a abstraction, unit, 'a abstraction, unit) mapf 
val abstractVarWithoutLambdas : term -> unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) mapf

val apply : term list -> 'a abstraction -> 'a abstraction option
val eliminateNablas : term list -> ('a, 'a polarized, term list -> 'a formula, 'a abstraction, 'a formula) mapf

val applyFixpoint : 'a abstraction -> ('a, 'a polarized option, 'a predicate option, 'a abstraction option, 'a formula option) mapf

val string_of_definition : 'a definition -> string
val string_of_formula : generic:string list -> (* names:string list -> *) ('a,string,string,string,string) mapf
val string_of_formula_ast : generic:string list -> ('a,string,string,string,string) mapf


val undoUnify : state -> unit
val rightUnify : term -> term -> unifyresult
val leftUnify : term -> term -> unifyresult
val unifyList : (term -> term -> unifyresult) -> term list -> term list -> unifyresult
(* val matchFormula : 'a w_polarized -> 'a polarized -> bool *)

val getDefinitionArity : 'a definition -> int
val getDefinitionBody : 'a definition -> 'a polarized

val getTermHeadAndArgs : term -> (string * term list) option

