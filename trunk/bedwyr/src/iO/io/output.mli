(****************************************************************************)
(* Bedwyr -- message output                                                 *)
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

(** {6 General purpose message output facilities} *)

type colours = [`Error | `Warning | `Debug | `Clear]

val set_colours : int -> unit

val set_width : Format.formatter -> int -> unit

val fprintf :
  ?colour:colours ->
  ?tag:string ->
  ?p:Pos.t ->
  ?nl:bool ->
  formatter:Format.formatter ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

(*
val pp_spaced_string : Format.formatter -> string -> unit
 *)

(** {6 Wrappers for normal output} *)

val std_out : Format.formatter ref

val printf :
  ?nl:bool ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

val sprintf :
  ?tag:string ->
  ?p:Pos.t ->
  ('a, Format.formatter, unit, string) format4 -> 'a

(** {6 Wrappers for abnormal output} *)

val std_err : Format.formatter ref

val std_dbg : Format.formatter ref

(** Simple debug flag, can be set dynamically from the logic program. *)
val debug : bool ref

val err_poss : (int * int) list ref
val war_poss : (int * int) list ref

val wprintf :
  ?p:Pos.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

val eprintf :
  ?p:Pos.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a

val dprintf :
  ?p:Pos.t ->
  ('a, Format.formatter, unit, unit) format4 -> 'a
