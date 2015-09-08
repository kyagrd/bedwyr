(****************************************************************************)
(* Bedwyr -- input                                                          *)
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

(** {6 General purpose input facilities} *)

val apply_on_lexbuf :
  (Lexing.lexbuf -> 'a) -> Lexing.lexbuf ->
  'a option

val apply_on_string :
  (Lexing.lexbuf -> 'a) -> ?fname:string -> string ->
  'a

val apply_on_channel :
  (Lexing.lexbuf -> 'a) -> ?fname:string -> in_channel ->
  'a
