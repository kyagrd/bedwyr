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

module Status : sig
  val exit_with : unit -> unit
  val exit_if : unit -> unit
end

val reload : (?session:(string list) -> unit -> unit) ref
val include_file : (test_limit:int option -> string -> unit) ref

module Catch : sig
  val io : ?p:Preterm.Pos.t -> exn -> unit option
end

val defs :
  ?incremental:bool -> test_limit:int option -> Lexing.lexbuf ->
  unit option option

val defl :
  ?incremental:bool -> test_limit:int option -> Lexing.lexbuf ->
  unit option

val reps :
  ?concise:bool -> test_limit:int option -> Lexing.lexbuf ->
  unit option

val repl :
  ?concise:bool -> test_limit:int option -> Lexing.lexbuf ->
  unit
