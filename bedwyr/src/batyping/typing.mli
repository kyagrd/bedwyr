(****************************************************************************)
(* Prenex polymorphic typing                                                *)
(* Copyright (C) 2011-2015 Quentin Heath                                    *)
(* Copyright (C) 2013 Alwen Tiu                                             *)
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
  (** Some additional information. *)
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

  (** Kind of proper types ([*]). *)
  val ktype : ki

  (** Kind of type operators ([... -> *]). *)
  val ki_arrow : ki list -> ki -> ki

  (** Print a kind. *)
  val pp_kind : Format.formatter -> ki -> unit
  val kind_to_string : ki ->string

  (** {6 Types} *)

  (** First-order parametricly polymorphic types (of sort [*]),
    * including some predefined monomorphic ones. *)
  type ty

  (** User-declared types and type operators. *)
  val tconst : string -> ty list -> ty
  (** The (zero or more) arguments of the operator are given backwards. *)

  (** Runtime-declared product types. *)
  val ttuple : ty -> ty -> ty list -> ty
  (** The (zero or more) last components (after the two first ones) are
    * given in reverse order. *)

  (** return type of predicates ([prop]). *)
  val tprop : ty

  (** Type of quoted strings ([string]). *)
  val tstring : ty

  (** Type of integers ([nat]). *)
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
  val get_fresh_tyinst : unit -> ty -> ty
  (** The mapping from type parameters to type variables will be kept across
    * calls for a given [get_fresh_tyinst ()]. *)

  val fresh_tyvars : int -> ty list

  (** {6 Kind checking} *)

  (** Kind checking error. *)
  exception Type_kinding_error of string * pos * ki * ki

  (** Polymorphism error. *)
  exception Undefinite_type of string * pos * ty * int list

  (** "Style" of an object and its name, if relevant. *)
  type obj =
    | Predicate of string
    | Constant of string
    | QuantVar of string option
    | AbsVar

  (** [kind_check ~obj ~p ty ~atomic_kind] checks that type [ty] of a
    * [obj]-style object and all its subtypes are of the kind [TKind].
    *
    * @param atomic_kind function returning the kind of a type
    * constructor
    * @return [arity] *)
  val kind_check :
    obj:obj ->
    p:pos ->
    ty ->
    atomic_kind:(pos * string -> ki) ->
    int

  (** {6 Typing} *)

  (** Higher-order variable (free or quantified). *)
  exception Type_order_error of string option * pos * ty

  (** Un-propositional predicate. *)
  exception Invalid_pred_declaration of string * pos * ty

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

  (** Type unification impossible. *)
  exception Type_unification_error of ty * ty * type_unifier

  (** Refines the provided unifier accordingly to a pair of types. *)
  val unify_constraint : type_unifier -> ty -> ty -> type_unifier
  (* TODO Does this unification procedure have a name?*)

  (** {6 Output} *)

  (** Print a type. *)
  val get_pp_type :
    ?unifier:type_unifier -> unit -> Format.formatter -> ty -> unit
  (** [get_pp_type ()] builds a formatting function which will always
    * use the same representation for a given type parameter
    * or variable. It can be used to display the types of multiple
    * formulae with consistency. *)

  (** Convert a type to a string. *)
  val get_type_to_string :
    ?unifier:type_unifier -> unit -> ty -> string
  (** [get_type_to_string ()] works like [get_pp_type ()]. *)
end

(** Functor building an implementation of the typing structure,
  * given a position type. *)
module Make (I : INPUT) : S with type pos = I.pos
