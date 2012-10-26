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
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

(** Pre-terms and pre-AST, translation to terms and checking. *)

(** Type of the position information during parsing. For error messages only. *)
type pos = Lexing.position * Lexing.position

(** Dummy position for post-parsing errors. *)
val dummy_pos : pos

(** No valid token could be parsed from the input.
  * It might contain a valid prefix, though,
  * and in particular the provided byte could be a valid character,
  * but it often is the first byte of a multibyte unicode character. *)
exception Illegal_string of char

(** A "/*" or a "*/" was found in a quoted string.
  * In order to allow commenting a block of valid code without breaking the whole file,
  * those must be escaped (for instance "/\*" and "*\/").
  * Note that "\*"^"/" and "\/"^"*" still raise this exception. *)
exception Illegal_string_comment

(** Some characters that are only allowed in prefix names
  * were used next to some that are only allowed in infix names.
  * This happens to be forbidden for compatibility reasons;
  * a separating sequence (spaces, tabs, carriage returns, line feeds),
  * a comment or a quoted string is needed between two such names. *)
exception Illegal_token of string * string

(** The hash character was misused, or a meta-command was misspelled. *)
exception Unknown_command of string

(** Wrapper around some [Parsing.Parse_error]. *)
exception Parse_error of pos * string * string

module Typing : Typing.S with type pos = pos

(** Pre-term with type and position information,
  * but without substitutions or sharing. *)
type preterm

(** {6 Pre-terms creation} *)

(** Quoted string. *)
val pre_qstring : pos -> string -> preterm

(** (Non-negative) natural number. *)
val pre_nat : pos -> int -> preterm

(** Free variable or bound variable id. *)
val pre_freeid : pos -> string -> preterm

(** Declared object (predicate or constant) or bound variable id. *)
val pre_predconstid : pos -> string -> preterm

(** Internal predicate id. *)
val pre_internid : pos -> string -> preterm
(** It is not possible to define such a predicate;
  * those are predefined and usually experimental. *)

(** True. *)
val pre_true : pos -> preterm

(** False. *)
val pre_false : pos -> preterm

(** Term equality. *)
val pre_eq : pos -> preterm -> preterm -> preterm

(** Formula binary conjunction. *)
val pre_and : pos -> preterm -> preterm -> preterm

(** Formula binary disjunction. *)
val pre_or : pos -> preterm -> preterm -> preterm

(** Formula implication. *)
val pre_arrow : pos -> preterm -> preterm -> preterm

(** Quantification. *)
val pre_binder :
  pos ->
  Term.binder -> (pos * string * Typing.ty) list -> preterm -> preterm
(** The type [Term.binder] is used here, since the structure
  * is that of a [Term.term], and this module depends on [Term] either way. *)

(** Abstraction. *)
val pre_lambda : pos -> (pos * string * Typing.ty) list -> preterm -> preterm

(** Application. *)
val pre_app : pos -> preterm -> preterm list -> preterm

(** {6 Pre-terms manipulation} *)

(** [change_pos (p1,_) t (_,p2)] replaces the position by [(p1,p2)] in [t]. *)
val change_pos :
  pos -> preterm -> pos -> preterm

(** Find which arguments of an application are free variables. *)
val free_args : preterm -> string list

(** {6 Input AST ({e .def} file or toplevel)} *)

(** Flavouring keyword, prefixing a predicate declaration. *)
type flavour =
    Normal (** no keyword *)
  | Inductive (** {b inductive} *)
  | CoInductive (** {b coinductive} *)

(** "Hash-command" (meta-commands, mostly designed for the toplevel
  * but also available in input files). *)
type command =
    Exit
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
  (** [#type_of.] call {!System.print_type_of} *)
  | Show_def of pos * string
  (** [#show_def.] call {!System.show_def} *)
  | Show_table of pos * string
  (** [#show_table.] call {!System.show_table} *)
  | Clear_tables
  (** [#clear_tables.] call {!System.clear_tables} *)
  | Clear_table of pos * string
  (** [#clear_table.] call {!System.clear_table} *)
  | Save_table of pos * string * string
  (** [#save_table.] call {!System.save_table} *)
  | Assert of preterm
  (** [#assert.] check whether a query succeeds *)
  | Assert_not of preterm
  (** [#assert_not.] check whether a query fails *)
  | Assert_raise of preterm
  (** [#assert_raise.] check whether a query crashes *)

(** Global AST for any input (file or toplevel). *)
type input =
    KKind of (pos * string) list * Typing.ki
  (** type declaration *)
  | TType of (pos * string) list * Typing.ty
  (** constant declaration *)
  | Def of (flavour * pos * string * Typing.ty) list *
      (pos * preterm * preterm) list
  (** predicate declaration and definition *)
  | Query of preterm
  (** query (interactive mode) *)
  | Command of command
  (** meta-command (any mode) *)
  | Theorem of (pos * string * preterm)
  (** theorem (imported from Abella) *)

(** {6 Pre-terms' type checking} *)

(** Type checking error on a term. *)
exception Term_typing_error of pos * Typing.ty * Typing.ty *
            Typing.type_unifier

(** Type checking error on a free or bound variable. *)
exception Var_typing_error of string option * pos * Typing.ty

(** [type_check_and_translate pt ty (fv,dv,iv,bv)] checks that the pre-term [pt]
  * build by the parser has the type [ty] (usually [TProp]),
  * and either translates it to the corresponding term
  * and realizes the type unification as side effect,
  * or raises an exception to indicate nonunifiability
  * or to signal a case outside of the authorized types.
  *
  * {e FIXME}
  * Whether it succeeds or not, a lot of fresh type variables are created
  * that aren't needed after this stage, and nothing is done to clean up
  * the global type unifier at present, so this function has a memory leak.
  *
  * [fv], [dv], [iv] and [bv] are functions returning the type (and,
  * depending on the case, the corresponding term) of a free, declared,
  * intern or bound variable.
  * @param stratum stratum of the predicate this term defines
  * @param infer whether the result of the inference is to be kept in the
  * global type unifier or not
  * @param iter_free_types function that maps a provided action
  * on a set of types once the type unification is done
  * (and before the corresponding unifier is lost, if [infer] is false)
  * @param free_args names of the free variables used as argument of a top-level
  * (wrt a definition) application, ie which will be abstracted on,
  * and whose type are therefore allowed to contain [TProp]
  * @return a type-checked Term.term and its type
  * @raise Var_typing_error if a free variable of type [prop] is found
  * @raise Term_typing_error if the pre-tem isn't well typed *)
val type_check_and_translate :
  ?stratum:int ->
  ?infer:bool ->
  ?iter_free_types:((Term.var -> Typing.ty -> Typing.ty) -> unit) ->
  ?free_args:string list ->
  preterm ->
  Typing.ty ->
  ((pos * string -> Term.term * Typing.ty) *
   (?stratum:int -> pos * string -> Term.term * Typing.ty) *
   (pos * string -> Term.term * Typing.ty) *
   (pos * string * Typing.ty -> Typing.ty)) ->
  Term.term * Typing.ty
