(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2011 Baelde, Tiu, Ziegler, Gacek, Heath               *)
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

(** Bedwyr's exceptions handling. *)

exception Invalid_command
exception Assertion_failed

(** Read a *.def file. *)
val input_defs : Lexing.lexbuf -> unit

(** Read the REPL or a script.
  * @param interactive intended for the REPL,
  * gives additional error messages *)
val input_queries : ?interactive:bool -> Lexing.lexbuf -> unit

(** Execute meta-commands ([#debug.], etc).
  * @raise Invalid_command if an argument is unexpected
  * (especially if a boolean flag is given something other than
  * "", "true", "on", "false" or "off")
  * @raise Assertion_failed if [#assert formula.], [#assert_not formula.]
  * or [#assert_raise formula.] fails *)
val command : System.command -> (unit -> unit) -> unit
