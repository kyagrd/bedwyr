(****************************************************************************)
(* Bedwyr -- file input/output                                              *)
(* Copyright (C) 2012-2013 Quentin Heath                                    *)
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

(** I/O utilities. *)

(** Wrapper around some [Sys_error]. *)
exception File_error of string * string * string


(** List of open files used for user I/O. *)

(** Close all open files.
  * Raises no exception on system errors. *)
val close_io_files : unit -> unit

(** Deactivates I/O predicates.
  * They always return "true" (or "None" for {!read} and {!fread}),
  * but have no effect. *)
val deactivate_io : unit -> unit

(** Reactivates I/O predicates. *)
val reactivate_io : unit -> unit


(** {6 Sanity wrappers} *)

val run_in : (in_channel -> 'a) -> string -> 'a

val run_out : (out_channel -> 'a) -> string -> 'a

val chdir : string -> unit

(** {6 Term input (stdin and file)} *)

(** Read from the standard input. *)
val read : (unit -> Term.term option) -> Term.term list -> Term.term option

(** Open a file for reading. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was already open.
  * @raise File_error if the file exists or cannot be created *)
val fopen_in : Term.term list -> bool

(** Read from a file. The list should contain exactly two terms,
  * the first one being the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file wasn't opened for reading. *)
val fread :
  (Lexing.lexbuf -> unit -> Term.term option) -> Term.term list -> Term.term option

(** Close an open file. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was not open for reading.
  * @raise File_error if the file cannot be closed *)
val fclose_in : Term.term list -> bool


(** {6 Term output (stdout and file)} *)

(** Write on the standard output. The list should contain exactly one term. *)
val print : (Term.term -> bool) -> Term.term list -> bool

(** Open a file for writing. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was already open.
  * @raise File_error if the file exists or cannot be created *)
val fopen_out : Term.term list -> bool

(** Write in a file. The list should contain exactly two terms,
  * the first one being the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file wasn't opened for writing. *)
val fprint :
  (Format.formatter -> Term.term -> bool) -> Term.term list -> bool

(** Close an open file. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was not open for writing.
  * @raise File_error if the file cannot be closed *)
val fclose_out : Term.term list -> bool