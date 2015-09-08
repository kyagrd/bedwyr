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


val incr_test_limit : unit -> unit
val remove_test_limit : unit -> unit

val session     : string list ref
val definitions : string list ref
val queries     : string list ref
val test_limit  : int option ref

val reload : ?session:(string list) -> unit -> unit
val run_query_string : string -> unit option
val run_definitions_string : ?fname:string -> string -> unit option
val run_queries_channel : in_channel -> unit
