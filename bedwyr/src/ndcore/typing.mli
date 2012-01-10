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

(** Position information. For error messages only. *)
type pos = Lexing.position * Lexing.position

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
exception Type_kinding_error of pos * Type.simple_kind * Type.simple_kind

val kind_check :
  Type.simple_type ->
  Type.simple_kind ->
  (pos * string -> Type.simple_kind) ->
  bool * bool * bool * bool

(** {6 Type unifying} *)
(** Type unifier type.
  * A binding [k,v] symbolizes the substitution [(TVar k) -> v]. *)
type type_unifier

(** Apply a function on each substitution of a unifier. *)
val iter : (int -> Type.simple_type -> unit) -> type_unifier -> unit

(** Display a type in its {i ground form}, ie a unique form with regards to the
  * unifier. *)
val ty_norm : ?unifier:type_unifier -> Type.simple_type -> Type.simple_type

(** {6 Type checking} *)

exception Term_typing_error of pos * Type.simple_type * Type.simple_type *
            type_unifier
exception Var_typing_error of pos

(** Type-check and translate a pre-term.
  * Either succeeds and realizes the type unification as side effect,
  * or raises an exception to indicate nonunifiability
  * or to signal a case outside of the authorized types.
  *
  * In any case, a lot of fresh type variables are created that aren't needed
  * after this stage. Nothing is done to clean up the global type unifier
  * at present.
  * @param pre_term a pre-term built by the parser
  * @param expected_type the simple type the term is supposed to have (usually
  * TProp)
  * @param typed_free_var a function returning a type and a term when given the
  * name of a free variable
  * @param typed_declared_var a function returning a type and a term when given
  * the name of a declared constant or a predicate
  * @param typed_intern_var a function returning a type and a term when given
  * the name of a pre-defined constant or predicate
  * @param bound_var_type a function returning the type of a bound variable
  * @param infer whether the result of the inference is to be kept in the
  * global type unifier or not
  * @return a type-checked Term.term and its type
  * @raise Var_typing_error if a free variable of type [prop] is found
  * @raise Term_typing_error if the pre-tem isn't well typed *)
val type_check_and_translate :
  preterm ->
  Type.simple_type ->
  (pos * string -> Term.term * Type.simple_type) ->
  (pos * string -> Term.term * Type.simple_type) ->
  (pos * string -> Term.term * Type.simple_type) ->
  (pos * string * Type.simple_type -> Type.simple_type) -> bool ->
  Term.term * Type.simple_type
