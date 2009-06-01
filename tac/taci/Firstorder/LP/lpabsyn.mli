(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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
exception Error of string

type constant = Constant of string * int * progress list option * clause list

and clause = Clause of term * term option

and definition =
    ClauseDefinition of term * term option
  | ProgressDefinition of string * progress list

and progress =
    Progressing
  | NonProgressing

and term =
    AtomicTerm of string
  | VariableTerm of string
  | ApplicationTerm of term * term list
  | ConjunctionTerm of term * term
  | DisjunctionTerm of term * term
  | ImplicationTerm of term * term
  | AbstractionTerm of string * term
  | EqualityTerm of term * term
  | PiTerm of term
  | SigmaTerm of term
  | NablaTerm of term
  

val getConstantName : constant -> string
val getConstantArity : constant -> int
val getConstantProgress : constant -> progress list option
val getConstantClauses : constant -> clause list

val getClauseHead : clause -> term
val getClauseBody : clause -> term option

val substitute : term -> string -> term -> term
val string_of_term : term -> string

val getTermFVS : term -> string list
val getAtomName : term -> string
val getApplicationHead : term -> term
val getApplicationArguments : term -> term list
val getVariableName : term -> string

val defaultProgress : progress list option -> int -> progress list
