(****************************************************************************)
(* Bedwyr -- prenex polymorphic typing                                      *)
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
module type POSITION = sig
  (** Position information. *)
  type t

  (** Dummy position information. *)
  val dummy : t

  (** Position information pretty-printing. *)
  val pp : Format.formatter -> t -> unit
end

(** Output signature of the functor {!Typing.Make}. *)
module type S = sig
  (** Position information. *)
  type pos

  (** {6 Kinds} *)
  module Kind : sig
    (** Kind (of type operators). *)
    type t

    (** Kind of proper types ([*]). *)
    val ktype : t

    (** Kind of type operators ([... -> *]). *)
    val arrow : t list -> t -> t

    (** Print a kind. *)
    val pp : Format.formatter -> t -> unit
    val to_string : t -> string
  end

  (** {6 Types} *)
  module Type : sig
    (** First-order parametricly polymorphic types (of sort [*]),
      * including some predefined monomorphic ones. *)
    type t

    (** User-declared types and type operators. *)
    val const : pos -> string -> t list -> t
    (** The (zero or more) arguments of the operator are given backwards. *)

    (** Runtime-declared product types. *)
    val tuple : t -> t -> t list -> t
    (** The (zero or more) last components (after the two first ones) are
      * given in reverse order. *)

    (** return type of predicates ([prop]). *)
    val prop : t

    (** Type of quoted strings ([string]). *)
    val string : t

    (** Type of integers ([nat]). *)
    val nat : t

    (** Type parameters (for polymorphism). *)
    val param : int -> t

    (** Type variables (for type inference). *)
    val var : int -> t

    (** Type composition. *)
    val arrow : t list -> t -> t
    val fresh_param : unit -> t

    (** Map type names to parametric types. *)
    val get_param : string -> t
    val fresh_var : unit -> t

    (** Create a fresh instance of a polymorphic type.
      * All type parameters are replaced with fresh type variables. *)
    val instantiate_params : unit -> t -> t
    (** The mapping from type parameters to type variables will be kept across
      * calls for a given [instantiate_params ()]. *)

    val fresh_vars : int -> t list

    (** Position-agnostic comparison. *)
    val compare : t -> t -> int

    module Unifier : sig
      (** Type unifier.
        * Used as an environment for the type variables
        * (a binding [k,v] symbolizes the substitution [(TVar k) -> v]). *)
      type u

      (** Apply a function on each substitution of a unifier. *)
      val iter : (int -> t -> unit) -> u -> unit

      val global_unifier : u ref

      (** Clear the global unifier. *)
      val clear : unit -> unit

      (** Type unification impossible. *)
      exception Type_unification_error of t * t * u

      (** Refines the provided unifier accordingly to a pair of types. *)
      val refine : u -> t -> t -> u
      (* TODO Does this unification procedure have a name?*)

      (** Display a type in its {i ground form},
        * ie a unique form with regards to the unifier. *)
      val norm : ?unifier:u -> t -> t
    end

    (** Print a type. *)
    val get_pp :
      ?unifier:Unifier.u -> unit -> Format.formatter -> t -> unit
    (** [get_pp ()] builds a formatting function which will always
      * use the same representation for a given type parameter
      * or variable. It can be used to display the types of multiple
      * formulae with consistency. *)

    val pp : Format.formatter -> t -> unit

    (** Convert a type to a string. *)
    val get_to_string :
      ?unifier:Unifier.u -> unit -> t -> string
    (** [get_to_string ()] works like [get_pp ()]. *)

    val to_string : t -> string
  end

  (** {6 Kind checking} *)

  (** Kind checking error. *)
  exception Type_kinding_error of string * pos * Kind.t * Kind.t

  (** Un-propositional predicate. *)
  exception Invalid_pred_declaration of string * pos * Type.t

  (** Polymorphism error. *)
  exception Undefinite_type of string * pos * Type.t * int list

  (** Higher-order variable (free or quantified). *)
  exception Type_order_error of string option * pos * Type.t

  (** "Style" of an object and its name, if relevant. *)
  type obj =
    | Predicate of string
    | Constant of string
    | QuantVar of string option
    | AbsVar

  (** [kind_check ~obj ~p ty ~get_kind] checks that type [ty] of a
    * [obj]-style object and all its subtypes are of the kind [TKind].
    *
    * @param get_kind function returning the kind of a type
    * constructor
    * @return [arity] *)
  val kind_check :
    obj:obj ->
    p:pos ->
    Type.t ->
    get_kind:(pos * string -> Kind.t) ->
    int
end

(** Functor building an implementation of the typing structure,
  * given a position type. *)
module Make (Pos : POSITION) : S with type pos = Pos.t
