(****************************************************************************)
(* Bedwyr -- high-level functions                                           *)
(* Copyright (C) 2005-2015 Baelde, Tiu, Ziegler, Heath                      *)
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

(** Predefined predicates, definitions bulding and handling. *)

open Parsetree.Preterm.Typing

(** Provide a term during the processing of a request.
  * Expected to ask the term interactivelly to the user. *)
val read_term : (unit -> Ndcore.Term.term option) ref

(** Provide a term during the processing of a request.
  * Expected to ask the term interactivelly to the user. *)
val fread_term : (Lexing.lexbuf -> unit -> Ndcore.Term.term option) ref

(** Enables the display of computation times. *)
val time : bool ref

(** Root of the tree of tabled atoms. *)
val root_atoms : Table.son list ref

(** Enables the use of {!Table.filter}. *)
val use_filter : bool ref

(** Guaranties that no table was cleared by {!System.clear_table}
  * without the others being also cleared, so that {!System.export} can
  * be used safely. *)
val clean_tables : bool ref


(** {6 Clauses and queries construction} *)

(** Translate a pre-term, with typing and position information,
  * into a term, with variable sharing.
  * Type checking (or rather type inference) is done on the fly,
  * and no type information is kept in the terms from this point.
  * If the term isn't well typed, or has a type that isn't [prop],
  * an exception is raised and the global type unifier isn't updated. *)
val translate_query :
  Parsetree.Preterm.preterm ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var,(Type.t*IO.Pos.t option)) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  Ndcore.Term.term option


(** {6 Predicates definitions} *)

exception Inconsistent_definition of string * IO.Pos.t * string

(** For each [(p,h,b)] of [c],
  * [add_clauses s c] adds the clause [h := b] to a definition,
  * as long as the var of the corresponding predicate has stratum [s].
  *
  * @return the list of singleton variables of the clause *)
val add_clauses :
  int -> (IO.Pos.t * Parsetree.Preterm.preterm * Parsetree.Preterm.preterm) list ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var,(Type.t*IO.Pos.t option)) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  (IO.Pos.t * string) list option


(** {6 Theorem definitions} *)

exception Inconsistent_theorem of string * IO.Pos.t * string

(** If possible, add the theorem to the tabling extended rules. *)
val add_theorem :
  (IO.Pos.t * string * Parsetree.Preterm.preterm) ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var,(Type.t*IO.Pos.t option)) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  unit option


(** {6 Predicates accessors} *)

exception Missing_definition of string * IO.Pos.t option
exception Missing_table of string * IO.Pos.t option

(** Get a predicate's tabling information and definition.
  * @raise Missing_declaration if [head_tm] is not an existing predicate
  *)
val get_flav_def : Ndcore.Term.term -> Environment.flavour * Ndcore.Term.term

(** Remove all tables. *)
val clear_tables : unit -> unit

(** Remove a table. *)
val clear_table : IO.Pos.t * Ndcore.Term.term -> unit


(** {6 Misc I/O} *)

(** Display all type and objects declarations. *)
val print_env : unit -> unit

(** Perform type checking on a pre-term and display the inferred type.
  * This can be used from the REPL to check the validity of a term
  * without messing with the future inference,
  * so the global type unifier is left unchanged
  * even if the term is well typed and of type [prop]. *)
val print_type_of :
  Parsetree.Preterm.preterm ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var,(Type.t*IO.Pos.t option)) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  unit option
(* TODO rewrite this comment once the new type system is merged *)

(** Display the body of a definition. *)
val show_def : IO.Pos.t * Ndcore.Term.term -> unit

(** Display the content of a table. *)
val show_table : IO.Pos.t * Ndcore.Term.term -> unit

(** Save the content of a table to a file.
  * The proved and disproved entries are stored as arguments
  * to the predicates [proved] and [disproved], respectively. *)
val save_table : IO.Pos.t * Ndcore.Term.term -> string -> string -> unit

(** Raised when a global table export was attempted after some tables
  * had been individually cleared, as opposed to all of them cleared. *)
exception Uncleared_tables

(** Export the current tables in an XML file.
  * Doesn't work between a call to [#clear_table] and the following call
  * to [#clear_tables]. *)
val export : string -> unit

(** Translate a pre-term into a term.
  * Similar to {!translate_query}, but with no assumption on the type. *)
val translate_term :
  Parsetree.Preterm.preterm ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var,(Type.t*IO.Pos.t option)) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  Ndcore.Term.term option

(** Deactivates I/O predicates.
  * They always return "true" (or "None" for {!read} and {!fread}),
  * but have no side effect. *)
val deactivate_io : unit -> unit

(** Reactivates I/O predicates. *)
val reactivate_io : unit -> unit

(** {7 Input predicates (stdin and file)} *)

(** Read from the standard input. *)
val read : (unit -> Ndcore.Term.term option) -> Ndcore.Term.term list -> Ndcore.Term.term option

(** Open a file for reading. The list should contain exactly one term,
  * the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was already open.
  * @raise File_error if the file exists or cannot be created *)
val fopen_in : Ndcore.Term.term list -> bool

(** Read from a file. The list should contain exactly two terms,
  * the first one being the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file wasn't opened for reading. *)
val fread :
  (Lexing.lexbuf -> unit -> Ndcore.Term.term option) -> Ndcore.Term.term list -> Ndcore.Term.term option

(** Close an open file. The list should contain exactly one term,
  * the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was not open for reading.
  * @raise File_error if the file cannot be closed *)
val fclose_in : Ndcore.Term.term list -> bool

(** {7 Output predicates (stdout and file)} *)

(** Write on the standard output. The list should contain exactly one term. *)
val print : (Ndcore.Term.term -> bool) -> Ndcore.Term.term list -> bool

(** Open a file for writing. The list should contain exactly one term,
  * the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was already open.
  * @raise File_error if the file exists or cannot be created *)
val fopen_out : Ndcore.Term.term list -> bool

(** Write in a file. The list should contain exactly two terms,
  * the first one being the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file wasn't opened for writing. *)
val fprint :
  (Format.formatter -> Ndcore.Term.term -> bool) -> Ndcore.Term.term list -> bool

(** Close an open file. The list should contain exactly one term,
  * the name of the file (an actual [Ndcore.Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was not open for writing.
  * @raise File_error if the file cannot be closed *)
val fclose_out : Ndcore.Term.term list -> bool


(** {6 Misc} *)

(** User interruption. *)
exception Interrupt

(** Raised when aborting search. *)
exception Abort_search

(** Failure of a "#assert*" meta-command. *)
exception Assertion_failed

(** Invalid meta-command, or wrong arguments. *)
exception Invalid_command

(** Remember the current included files, declared and defined objects,
  * so as to get back to this point with the second invocation. *)
val get_reset : unit -> unit -> unit

(** Forget all included files, declared and defined objects. *)
val reset : unit -> unit

(** @return [true] if a user interruption was detected since the last call to
  * {!check_interrupt}, [false] otherwise. *)
val check_interrupt : unit -> bool

(** Ensure that the second argument is called, while propagating the
  * exceptions raised by the first argument. *)
val sanitize : (unit -> unit) -> (unit -> unit) -> unit

(** Exit status. *)
module Status : sig
  val exit_with : unit -> 'a
  val exit_if : unit -> unit

  val input : unit -> unit
  val def : unit -> unit
  val ndcore : unit -> unit
  val solver : unit -> unit
  val bedwyr : unit -> unit
end

(** Limit on include-depth allowing for assertions. *)
val initial_test_limit  : int option ref

(** Increase the maximal include-depth allowing for assertions. *)
val incr_test_limit : unit -> unit

(** Remove the limit on include-depth allowing for assertions. *)
val remove_test_limit : unit -> unit

(** List of files to be included on startup. *)
val session     : string list ref

(** List of commands to be executed on startup, after file inclusions. *)
val definitions : string list ref

(** List of queries to be ran on startup, after commands execution. *)
val queries     : string list ref
