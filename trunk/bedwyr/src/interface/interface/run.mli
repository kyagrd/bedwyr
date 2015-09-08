(****************************************************************************)
(* Bedwyr -- interface                                                      *)
(* Copyright (C) 2015 Quentin Heath                                         *)
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

(** Entry points for bedwyr's libraries. *)

(** (Re)load the session (i.e. the list of included definitions files). *)
val reload : ?session:(string list) -> unit -> unit

(** Solve a query (or execute a meta-command) read in a string.
  * @return [None] if any error was met,
  *         [Some ()] otherwise. *)
val query_string : string -> unit option

(** Solve (or execute) each of a stream of queries (and meta-commands)
  * read from a channel.
  * Returns when the channel is empty. *)
val queries_channel : in_channel -> unit

(** Execute a command (or a meta-command) read in a string.
  * @return [None] if the input is empty,
  *         [Some None] if the input is non-empty but is not a valid
  *         command (or meta-command),
  *         [Some (Some None)] if the input is correctly parsed as a
  *         command (or non-assertion meta-command),
  *         [Some (Some (Some term))] if the input is correctly parsed
  *         as an meta-command asserting something about the query
  *         [term]. *)
val definition_string : string -> Ndcore.Term.term option option option

(** Execute a stream of commands (and meta-commands) read in a string.
  * @return a list of the assertions that were met (no distinction is
  * made between those introduced by {e #assert}, {e #assert_not} or
  * {e #assert_raise}). *)
val definitions_string : ?fname:string -> string -> Ndcore.Term.term list option
