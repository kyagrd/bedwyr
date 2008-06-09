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

type progress =
    Progressing
  | Unknown

type fixpoint =
    Inductive
  | CoInductive

type quantifier =
    Pi
  | Sigma
  | Nabla

type connective =
    And
  | Or
  | Imp

(*  Annotations *)
type polarity = Positive | Negative
type freezing = Frozen | Unfrozen
type control  = Normal | Focused | Delayed
type junk     = Clean | Dirty of (unit -> unit)
type annotation = {
  polarity : polarity ;
  freezing : freezing ;
  control  : control ;
  junk     : junk
}
val defaultAnnotation : annotation

(*  Formulas  *)
type 'a polarized = ('a * 'a formula)

and 'a predicate = 
    FixpointFormula of fixpoint * string * (string * progress) list * 'a abstraction
  | DBFormula of int * string * int
  | AtomicFormula of string

and 'a formula =
    BinaryFormula of (connective * 'a polarized * 'a polarized)
  | EqualityFormula of (term * term)
  | QuantifiedFormula of (quantifier * 'a abstraction)
  | ApplicationFormula of ('a predicate * term list)

and 'a abstraction =
    AbstractionFormula of string * 'a abstraction
  | AbstractionBody of 'a polarized

(*  Patterns  *)
type pattern_annotation = {
  polarity_pattern : polarity option ;
  freezing_pattern : freezing option ;
  control_pattern  : control option ;
  junk_pattern     : junk option
}
val defaultPatternAnnotation : pattern_annotation

type fixpoint_pattern =
    InductivePattern
  | CoinductivePattern
  | AnonymousFixpoint

type 'a polarized_pattern = 'a * 'a formula_pattern

and 'a predicate_pattern =
    AtomicPattern of string
  | AnonymousPredicate
  | AnonymousMu
  | AnonymousNu

and 'a formula_pattern =
    BinaryPattern of connective * 'a polarized_pattern * 'a polarized_pattern
  | EqualityPattern of term * term
  | QuantifiedPattern of quantifier * 'a abstraction_pattern
  | ApplicationPattern of 'a predicate_pattern * term list

and 'a abstraction_pattern =
    AbstractionPattern of string * 'a abstraction_pattern
  | AbstractionBodyPattern of 'a polarized_pattern
  | AnonymousAbstraction

val anonymousBinder : string

type 'a predefinition =
  PreDefinition of (string * (string * progress) list * 'a abstraction_pattern * fixpoint)

type 'a definition =
  Definition of (string * (string * progress) list * 'a abstraction * fixpoint)

type state

type unifyresult =
    UnifyFailed
  | UnifySucceeded of state
  | UnifyError of string

(*  map_formula: mapping over formulas.  *)
type ('a,'b,'c,'d,'e) map_formula =
  {polf : 'a polarized -> 'b ;
  predf : 'a predicate -> 'c ;
  abstf : 'a abstraction -> 'd ;
  formf : 'a formula -> 'e}

(*  mappattern: mapping over formulas.  *)
type ('a,'b,'c,'d,'e) map_pattern =
  {polp : 'a polarized_pattern -> 'b ;
  predp : 'a predicate_pattern -> 'c ;
  abstp : 'a abstraction_pattern -> 'd ;
  formp : 'a formula_pattern -> 'e}

val string_of_freezing : freezing -> string
val string_of_polarity : polarity -> string
val string_of_control : control -> string

val string_of_pattern : pattern_annotation polarized_pattern -> string
val string_of_pattern_ast : pattern_annotation polarized_pattern -> string
val patternAnnotationToFormulaAnnotation :
      polarity -> pattern_annotation -> annotation

val isAnonymousTerm : term -> bool 
val makeAnonymousTerm : unit -> term

val mapFormula :
  (unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) map_formula) ->
    (term -> term) -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) map_formula

val mapFormula2 :
 (string -> 'a -> 'a) -> (connective -> 'a -> 'a * 'a) -> 
 ('a -> ('b, 'b polarized, term list -> 'b formula, 'b abstraction, 'b formula) map_formula)
 -> (term -> term) -> 'a -> ('b, 'b polarized, term list -> 'b formula, 'b abstraction, 'b formula) map_formula

val mapPattern :
  (unit ->
    (pattern_annotation,
      pattern_annotation polarized_pattern,
      pattern_annotation predicate_pattern,
      pattern_annotation abstraction_pattern,
      pattern_annotation formula_pattern) map_pattern) ->
    (term -> term) ->
    (pattern_annotation,
      pattern_annotation polarized_pattern,
      pattern_annotation predicate_pattern,
      pattern_annotation abstraction_pattern,
      pattern_annotation formula_pattern) map_pattern

val termsPolarized : 'a polarized -> term list
val abstract : string -> ('a, 'a abstraction, unit, 'a abstraction, unit) map_formula
val abstractPattern : string -> ('a, 'a abstraction_pattern, unit, 'a abstraction_pattern, unit) map_pattern
val abstractDummyWithoutLambdas : unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) map_formula
val abstractVar : term -> ('a, 'a abstraction, unit, 'a abstraction, unit) map_formula 
val abstractVarWithoutLambdas : term -> unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) map_formula
val abstractWithoutLambdas : string -> unit -> ('a,'a polarized,'a predicate,'a abstraction,'a formula) map_formula

val apply : term list -> 'a abstraction -> 'a abstraction option
val fullApply : term list -> 'a abstraction -> 'a polarized option
val eliminateNablas : term list -> ('a, 'a polarized, term list -> 'a formula, 'a abstraction, 'a formula) map_formula

val applyFixpoint : 'a abstraction -> ('a, 'a polarized option, 'a predicate option, 'a abstraction option, 'a formula option) map_formula

val string_of_definition : 'a definition -> string
val string_of_formula : generic:string list -> (* names:string list -> *) ('a,string,string,string,string) map_formula
val string_of_formula_ast : generic:string list -> ('a,string,string,string,string) map_formula

val undoUnify : state -> unit
val rightUnify : term -> term -> unifyresult
val leftUnify : term -> term -> unifyresult
val unifyList : (term -> term -> unifyresult) -> term list -> term list -> unifyresult

val matchPattern : pattern_annotation polarized_pattern -> pattern_annotation polarized_pattern -> bool
val matchFormula : pattern_annotation polarized_pattern -> annotation polarized -> bool

val getDefinitionArity : 'a definition -> int
val getDefinitionBody : 'a definition -> 'a abstraction
val predicateofDefinition : 'a definition -> 'a predicate

val getTermHeadAndArgs : term -> (string * term list) option

val negativeFormula : annotation formula -> annotation polarized
val positiveFormula : annotation formula -> annotation polarized

val freeze : annotation -> annotation
val thaw : annotation -> annotation
val focus : annotation -> annotation
val delay : annotation -> annotation
val changeAnnotation : (annotation -> annotation) -> annotation polarized -> annotation polarized
