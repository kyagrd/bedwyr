(****************************************************************************)
(* Bedwyr -- concrete syntax tree to abstract syntax tree                   *)
(* Copyright (C) 2012-2015 Quentin Heath                                    *)
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

(* Pre-terms (CST) construction, checking, and translation to AST. *)

(** Position information during parsing. For error messages only. *)
module Pos : sig
  (** Position information. *)
  type t

  (** Dummy position information. *)
  val dummy : t

  (** Current position (lexing). *)
  val of_lexbuf : Lexing.lexbuf -> unit -> t

  (** Current position (parsing). *)
  val of_token : int -> t

  (** Offset pair. *)
  val to_pair : t -> int * int

  (** Position information pretty-printing. *)
  val pp : Format.formatter -> t -> unit
end

(** Wrapper around End_of_file in definition mode. *)
exception Empty_command

(** Wrapper around End_of_file in the toplevel. *)
exception Empty_term

(** Wrapper around some [Parsing.Parse_error]. *)
exception Parse_error of Pos.t * string * string

module Typing : Typing.S with type pos = Pos.t

(** Pre-term with type and position information,
  * but without substitutions or sharing. *)
type preterm

(** {6 Pre-terms creation} *)

(** Quoted string. *)
val pre_qstring : Pos.t -> string -> preterm

(** (Non-negative) natural number. *)
val pre_nat : Pos.t -> int -> preterm

(** Free variable or bound variable id. *)
val pre_freeid : Pos.t -> string -> preterm

(** Declared object (predicate or constant) or bound variable id. *)
val pre_predconstid : ?infix:bool -> Pos.t -> string -> preterm

(** Internal predicate id. *)
val pre_internid : Pos.t -> string -> preterm
(** It is not possible to define such a predicate;
  * those are predefined and usually experimental. *)

(** True. *)
val pre_true : Pos.t -> preterm

(** False. *)
val pre_false : Pos.t -> preterm

(** Term equality. *)
val pre_eq : Pos.t -> preterm -> preterm -> preterm

(** Formula binary conjunction. *)
val pre_and : Pos.t -> preterm -> preterm -> preterm

(** Formula binary disjunction. *)
val pre_or : Pos.t -> preterm -> preterm -> preterm

(** Formula implication. *)
val pre_arrow : Pos.t -> preterm -> preterm -> preterm

(** Quantification. *)
val pre_binder :
  Pos.t ->
  Term.binder -> (Pos.t * string * Typing.ty) list -> preterm -> preterm
(** The type [Term.binder] is used here, since the structure
  * is that of a [Term.term], and this module depends on [Term] either way. *)

(** Abstraction. *)
val pre_lambda : Pos.t -> (Pos.t * string * Typing.ty) list -> preterm -> preterm

(** Application. *)
val pre_app : Pos.t -> preterm -> preterm list -> preterm
(** The (zero or more) arguments of the application are given backwards. *)

(** Term tuple. *)
val pre_tuple : Pos.t -> preterm -> preterm -> preterm list -> preterm
(** The (zero or more) last components (after the two first ones) are
  * given in reverse order. *)

(** {6 Pre-terms manipulation} *)

(** Find which arguments of an application are free variables. *)
val free_args : preterm -> string list

(** {6 Input AST} *)

(** "Qed" command used outside of proof mode.
  * It should be the first command to appear after a "Theorem". *)
exception Qed_error of Pos.t

(** Flavouring keyword, prefixing a predicate declaration. *)
type flavour =
  | Normal (** no keyword *)
  | Inductive (** {b inductive} *)
  | CoInductive (** {b coinductive} *)

(** Command AST. *)
module Command : sig
  type t =
    | Kind    of (Pos.t * string) list * Typing.ki
    (** type declaration *)
    | Type    of (Pos.t * string) list * Typing.ty
    (** constant declaration *)
    | Def     of (flavour * Pos.t * string * Typing.ty) list *
                 (Pos.t * preterm * preterm) list
    (** predicate declaration and definition *)
    | Theorem of (Pos.t * string * preterm)
    (** theorem (imported from Abella) *)
    | Qed     of Pos.t
    (** end of proof (imported from Abella, ignored by Bedwyr) *)
end

(** Meta-command AST (mostly designed for the toplevel but also
  * available in input files). *)
module MetaCommand : sig
  type t =
    | Exit
    (** [#exit.] close all files and exit *)
    | Help
    (** [#help.] display a short help message *)
    | Include of string list
    (** [#include "f1.def" "f2.def".] load a list of files *)
    | Reload
    (** [#reload.] reload the current session *)
    | Session of string list
    (** [#session "f1.def" "f2.def".] load these files as the current session *)
    | Debug of string option
    (** [#debug on.] turn debugging on/off (default off) *)
    | Time of string option
    (** [#time on.] turn timing on/off (default off) *)
    | Equivariant of string option
    (** [#equivariant on.] turn equivariant tabling on/off (default on) *)
    | Freezing of int
    (** [#freezing 42.] set the freezing-point to a non-negative value or -1 (default 0) *)
    | Saturation of int
    (** [#saturation 42.] set the saturation pressure to a non-negative value or -1 (default 0) *)
    | Env
    (** [#env.] call {!System.print_env} *)
    | Type_of of preterm
    (** [#type_of t.] call {!System.print_type_of} *)
    | Show_def of Pos.t * string
    (** [#show_def p.] call {!System.show_def} *)
    | Show_table of Pos.t * string
    (** [#show_table p.] call {!System.show_table} *)
    | Clear_tables
    (** [#clear_tables.] call {!System.clear_tables} *)
    | Clear_table of Pos.t * string
    (** [#clear_table p.] call {!System.clear_table} *)
    | Save_table of Pos.t * string * string
    (** [#save_table p "p-table.def".] call {!System.save_table} *)
    | Export of string
    (** [#export "skeleton.xml".] call {!System.export} *)
    | Assert of preterm
    (** [#assert t.] check whether a query succeeds *)
    | Assert_not of preterm
    (** [#assert_not t.] check whether a query fails *)
    | Assert_raise of preterm
    (** [#assert_raise t.] check whether a query crashes *)
end

type definition_mode =
  [
  | `Command            of Command.t
  | `MetaCommand        of MetaCommand.t
  ]

type toplevel =
  [
  | `Term               of Pos.t * preterm
  | `MetaCommand        of MetaCommand.t
  ]

type term_mode =
  [
  | `Term               of Pos.t * preterm
  ]

(** {6 Pre-terms' type checking} *)

(** Type checking error. *)
exception Term_typing_error of Pos.t * Typing.ty * Typing.ty *
            Typing.type_unifier

(** [type_check_and_translate pt ty (fv,do,ip,ak)] checks that the
  * pre-term [pt] built by the parser has the type [ty] (usually
  * [TProp]), and either translates it to the corresponding term and
  * realizes the type unification as side effect, or raises an exception
  * to indicate non-unifiability or to signal a case outside of the
  * authorized types.
  *
  * The algorithm is certainly close to {e Algorithm W}, with
  * [Typing.unify_constraint] being the {e Var} rule.
  *
  * {e FIXME}
  * Whether it succeeds or not, a lot of fresh type variables are created
  * that aren't needed after this stage, and nothing is done to clean up
  * the global type unifier at present, so this function has a memory leak.
  *
  * [fv], [do] and [ip] are functions returning the type (and, depending
  * on the case, the corresponding term) of a free variable, declared
  * object (constant or predicate) or intern predicate.
  * [ak] returns the kind of a type constant.
  * @param stratum stratum of the predicate where this term belongs
  * @param head whether the term is the head of a clause (in which case
  * the type of its head must not be instantiated)
  * @param free_args names of the free variables used as argument of a
  * top-level (wrt a definition) application, ie which will be
  * abstracted on, and whose type can allowed to contain [TProp]
  * @param fold_free_types function that folds a provided action on a
  * set of types once the type unification is done
  * @param fresh_tyinst polymorphic type instantier
  * @return a list of singleton variables and a type-checked Term.term
  * @raise Invalid_pred_declaration if the target type of a predicate is
  * not [prop]
  * @raise Type_order_error if the type of a quantified or free variable
  * contains [prop]
  * @raise Undefinite_type if some type parameters are not transparant
  * @raise Type_kinding_error if a type constructor is applied on the
  * wrong number of arguments
  * @raise Term_typing_error if the pre-tem isn't well typed *)
val type_check_and_translate :
  ?stratum:int ->
  head:bool ->
  free_args:string list ->
  fold_free_types:((Term.var -> Typing.ty * Pos.t option ->
                    (Pos.t * string) list ->
                    (Pos.t * string) list) ->
                   (Pos.t * string) list ->
                   (Pos.t * string) list) ->
  fresh_tyinst:(Typing.ty -> Typing.ty) ->
  preterm ->
  Typing.ty ->
  ((Pos.t * string -> Term.term * Typing.ty) *
   (instantiate_type:bool -> ?forbidden_stratum:int -> Pos.t * string ->
    Term.term * Typing.ty) *
   (Pos.t * string -> Term.term * Typing.ty) *
   (obj:Typing.obj -> p:Pos.t -> Typing.ty -> int)) ->
  (Pos.t * string) list * Term.term
