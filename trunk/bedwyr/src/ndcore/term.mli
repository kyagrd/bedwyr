(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler               *)
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

(** Representation of higher-order terms. *)

type tag = Eigen | Constant | Logic | String
type var = private { id : int ; tag : tag; ts : int; lts : int; }

type binder = Forall | Exists | Nabla
type term
type ptr
type envitem = Dum of int | Binding of term * int
type env = envitem list
type rawterm =
  | Var of var
  | DB of int
  | NB of int
  | True
  | False
  | Eq of term * term
  | And of term * term
  | Or of term * term
  | Arrow of term * term
  | Binder of binder * term
  | Lam of int * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr

val eq : term -> term -> bool
val eqvt : term -> term -> bool
val observe : term -> rawterm
val deref : term -> term

(** Binding a variable to a term in a destructive way,
  * saving and restoring previous states of the terms. *)

type state

val save_state : unit -> state
val restore_state : state -> unit

val bind : term -> term -> unit

type subst
type unsubst

val get_subst   : state -> subst
val apply_subst : subst -> unsubst
val undo_subst  : unsubst -> unit
val eq_subst    : subst -> subst -> bool

(** Creating terms. *)

val lambda : int -> term -> term
val string : string -> term
val op_true : term
val op_false : term
val op_eq : term -> term -> term
val op_and : term -> term -> term
val op_or : term -> term -> term
val op_arrow : term -> term -> term
val op_binder : binder -> term -> term
val mk_binder : binder -> term -> 'a list -> ('a -> term -> term) -> term
val ex_close : term -> term list -> term
val binop : string -> term -> term -> term
val db : int -> term
val nabla : int -> term
val app : term -> term list -> term
val susp : term -> int -> int -> env -> term

(** Creating variables, handling variable names. *)

type namespace

val save_namespace : unit -> namespace
val restore_namespace : namespace -> unit

val fresh : ?name:string -> lts:int -> ts:int -> tag -> term
val fresh_name : string -> string
val get_var_by_name : tag:tag -> ts:int -> lts:int -> string -> term
val atom : string -> term

val get_name : term -> string
val get_hint : term -> string

val get_dummy_name  : ?start:int -> string -> string
val get_dummy_names : ?start:int -> int -> string -> string list

val free    : string -> unit
val is_free : string -> bool


(** Other common manipulations. *)

exception NonNormalTerm

val abstract : term -> term -> term
val abstract_flex : term -> term -> term

val get_nablas : term -> int list

val get_vars : (var -> bool) -> term list -> term list
val logic_vars : term list -> term list
val eigen_vars : term list -> term list

val get_var : term -> var
val get_var_ts : var -> int
val get_var_lts : var -> int

(** Return an eigenvar copier.
  * When passive is passed to the copier,
  * it only propagates what's been copied when active,
  * but doesn't copy newly encountered variables. *)
val copy_eigen : unit -> (?passive:bool -> term -> term)
val simple_copy : term -> term
val shared_copy : term -> term

module Notations :
  sig
    (** Equality *)
    val ( %= ) : term -> term -> bool
    (** Observation *)
    val ( !! ) : term -> rawterm
    (** Abstraction *)
    val ( // ) : int -> term -> term
    (** Application *)
    val ( ^^ ) : term -> term list -> term
  end
