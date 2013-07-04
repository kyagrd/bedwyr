(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2013 Baelde, Tiu, Ziegler, Gacek, Heath               *)
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

(** Bedwyr's main loop. *)

(** Read a *.def file. *)
val include_file : ?test:bool -> string -> unit

(** Read the REPL or a script.
  * @param interactive intended for the REPL,
  * gives additional error messages *)
val input_queries : test:bool -> ?interactive:bool -> Lexing.lexbuf -> unit
