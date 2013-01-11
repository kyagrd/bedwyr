(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012-2013 Quentin Heath, Alwen Tiu                         *)
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
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

(** Kinds, types; checking and pretty-printing. *)

(** Input signature of the functor {!Typing.Make}. *)
module type INPUT = sig
  (** Type of some additional information. *)
  type pos

  (** Dummy information. *)
  val dummy_pos : pos
end

(** Output signature of the functor {!Typing.Make}. *)
module type S = sig
  type pos
  val dummy_pos : pos

  (** {6 Kinds} *)

  (** Kind (of type operators). *)
  type ki
  val ktype : ki
  val ki_arrow : ki list -> ki -> ki

  (** Print a kind. *)
  val pp_kind : Format.formatter -> ki -> unit
  val kind_to_string : ki ->string

  (** {6 Types} *)

  (** First-order parametricly polymorphic types (of sort [*]),
    * including some predefined monomorphic ones. *)
  type ty

  (** User-defined base type. *)
  val tconst : string -> ty list -> ty
  val tprop : ty
  val tstring : ty
  val tnat : ty

  (** Type parameters (for polymorphism). *)
  val tparam : int -> ty

  (** Type variables (for type inference). *)
  val tvar : int -> ty

  (** Type composition. *)
  val ty_arrow : ty list -> ty -> ty
  val fresh_typaram : unit -> ty

  (** Map type names to parametric types. *)
  val get_typaram : string -> ty
  val fresh_tyvar : unit -> ty

  (** Create a fresh instance of a polymorphic type.
    * All type parameters are replaced with fresh type variables. *)
  val fresh_tyinst : ty -> ty
  val build_abstraction_types : int -> ty list * ty

  (** Print a type. *)
  val pp_type : Format.formatter -> ty -> unit
  val type_to_string : ty -> string

  (** {6 Kind checking} *)

  (** Kind checking error. *)
  exception Type_kinding_error of string * pos option * ki * ki

  (** [kind_check ty atomic_kind] checks that type [ty] and all its subtypes
    * are of the kind [TKind].
    *
    * @param atomic_kind function returning the kind of a type constructor
    * @return [(arity,flex_head,hollow,propositional,higher_order)]
    * (describing whether the type has an unresolved type parameter as target,
    * contains unresolved type parameters, ends with [TProp]
    * or contains [TProp] somewhere else than as target) *)
  val kind_check :
    ?p:pos ->
    ty ->
    atomic_kind:(pos * string -> ki) ->
    int * bool * bool * bool * bool

  (** {6 Type unifying} *)

  (** Type unifier type.
    * Used as an environment for the type variables
    * (a binding [k,v] symbolizes the substitution [(TVar k) -> v]). *)
  type type_unifier

  (** Apply a function on each substitution of a unifier. *)
  val iter : (int -> ty -> unit) -> type_unifier -> unit

  val global_unifier : type_unifier ref

  (** Clear the global unifier. *)
  val clear : unit -> unit

  (** Display a type in its {i ground form}, ie a unique form with regards to the
    * unifier. *)
  val ty_norm : ?unifier:type_unifier -> ty -> ty

  (** Print a type in a more unique way. *)
  val pp_type_norm :
    ?unifier:type_unifier -> Format.formatter -> ty -> unit
  val type_to_string_norm :
    ?unifier:type_unifier -> ty -> string

  (** Type incompletely inferred. *)
  exception Hollow_type of string

  (** Type unification impossible. *)
  exception Type_unification_error of ty * ty * type_unifier

  (** Refines the provided unifier accordingly to a pair of types. *)
  val unify_constraint : type_unifier -> ty -> ty -> type_unifier
  (* TODO Does this unification procedure have a name?*)
end

(** Functor building an implementation of the typing structure,
  * given a position type. *)
module Make (I : INPUT) : S with type pos = I.pos
