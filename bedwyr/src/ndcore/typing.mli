(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012 Quentin Heath                                         *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

(** Pre-terms and kind/type checking. *)

(** Position information during parsing. For error messages only. *)
type pos = Lexing.position * Lexing.position

(** Pre-term with type and position information,
  * but without substitutions and sharing. *)
type preterm

(** {6 Creating pre-terms} *)
(** [change_pos (p1,_) t (_,p2)] replaces the position by [(p1,p2)] in [t]. *)
val change_pos :
  pos -> preterm -> pos -> preterm

val pre_qstring : pos -> string -> preterm

val pre_nat : pos -> int -> preterm

val pre_freeid : pos -> string -> preterm

val pre_predconstid : pos -> string -> preterm

val pre_internid : pos -> string -> preterm

val pre_true : pos -> preterm

val pre_false : pos -> preterm

val pre_eq : pos -> preterm -> preterm -> preterm

val pre_and : pos -> preterm -> preterm -> preterm

val pre_or : pos -> preterm -> preterm -> preterm

val pre_arrow : pos -> preterm -> preterm -> preterm

val pre_binder :
  pos ->
  Term.binder -> (pos * string * Type.simple_type) list -> preterm -> preterm

val pre_lambda : pos -> (pos * string * Type.simple_type) list -> preterm -> preterm

val pre_app : pos -> preterm -> preterm list -> preterm

(** {6 Kind checking} *)

(** Kind checking error. *)
exception Type_kinding_error of pos * Type.simple_kind * Type.simple_kind

(** [kind_check ty expected_kind atomic_kind] checks that type [ty]
  * is of the kind [expected_kind] (usually [TKind]).
  * In the current implementation, types are simple types,
  * so it always succeeds (except when given a non-existing type).
  *
  * [atomic_kind] is a function returning the kind of an atomic type,
  * and the returned value is [(flex,hollow,hogher_order,propositional)],
  * describing whether the type is an unassigned type variable,
  * contains unassigned type variables, contains [TProp]
  * and ends with [TProp]. *)
val kind_check :
  Type.simple_type ->
  Type.simple_kind ->
  (pos * string -> Type.simple_kind) ->
  bool * bool * bool * bool

(** {6 Type unifying} *)
(** Type unifier type.
  * Used as an environment for the type variables
  * (a binding [k,v] symbolizes the substitution [(TVar k) -> v]). *)
type type_unifier

(** Apply a function on each substitution of a unifier. *)
val iter : (int -> Type.simple_type -> unit) -> type_unifier -> unit

(** Display a type in its {i ground form}, ie a unique form with regards to the
  * unifier. *)
val ty_norm : ?unifier:type_unifier -> Type.simple_type -> Type.simple_type

(** {6 Type checking} *)

(** Type checking error on a term. *)
exception Term_typing_error of pos * Type.simple_type * Type.simple_type *
            type_unifier

(** Type checking error on a free or bound variable. *)
exception Var_typing_error of string option * pos * Type.simple_type

(** Find which arguments of an application are free variables. *)
val pure_args : preterm -> string list

(** [atomic_kind pt ty fv nt dv iv bv i pa] checks that the pre-term [pt]
  * build by the parser has the type [ty] (usually [TProp]),
  * and either translates it to the corresponding term
  * and realizes the type unification as side effect,
  * or raises an exception to indicate nonunifiability
  * or to signal a case outside of the authorized types.
  *
  * Whether it succeeds or not, a lot of fresh type variables are created
  * that aren't needed after this stage, and nothing is done to clean up
  * the global type unifier at present, so this function has a memory leak.
  *
  * [fv], [dv], [iv] and [bv] are functions returning the type (and,
  * depending on the case, the corresponding term) of a free, declared,
  * intern or bound variable.
  * [nt] maps a provided function on a set of types once the type unification
  * is done and before the corresponding unifier is lost
  * (ie when [i] is false).
  * [i] states whether the result of the inference is to be kept in the
  * global type unifier or not, and
  * [pa] are the names of free variables used as argument of a top-level
  * (wrt a definition) application, ie which will be abstracted on,
  * and whose type can therefore contain [TProp].
  * @return a type-checked Term.term and its type
  * @raise Var_typing_error if a free variable of type [prop] is found
  * @raise Term_typing_error if the pre-tem isn't well typed *)
val type_check_and_translate :
  preterm ->
  Type.simple_type ->
  (pos * string -> Term.term * Type.simple_type) ->
  ((Term.var -> Type.simple_type -> Type.simple_type) -> unit) ->
  (pos * string -> Term.term * Type.simple_type) ->
  (pos * string -> Term.term * Type.simple_type) ->
  (pos * string * Type.simple_type -> Type.simple_type) ->
  bool -> string list ->
  Term.term * Type.simple_type
