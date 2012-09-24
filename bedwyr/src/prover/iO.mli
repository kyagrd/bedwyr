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

(** Wrapper around some [Sys_error]. *)
exception File_error of string * string * string

(** {6 Sanity wrappers} *)

val open_in : string -> in_channel

val close_in : string -> in_channel -> unit

val open_out : string -> out_channel

val close_out : string -> out_channel -> unit

(** {6 stdout and file term output} *)

(** Write on the standard output. The list should contain exactly one term. *)
val print :
  (Term.term -> bool) -> Term.term list -> bool

(** Open a file for writing. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was already open.
  * @raise File_error if the file exists or cannot be created *)
val open_user_file : Term.term list -> bool

(** Write in a file. The list should contain exactly two terms,
  * the first one being the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file wasn't opened with [open_user_file]. *)
val fprint :
  (Format.formatter -> Term.term -> bool) -> Term.term list -> bool

(** Close an open file. The list should contain exactly one term,
  * the name of the file (an actual [Term.QString]).
  * Fails if the name is an unbound variable or a constant,
  * or if the file was not open.
  * @raise File_error if the file cannot be closed *)
val close_user_file : Term.term list -> bool

(** Close all open files.
  * Raises no exception if on system errors. *)
val close_user_files : unit -> unit
