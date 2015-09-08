(****************************************************************************)
(* Bedwyr -- toplevel eval                                                  *)
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

(** Evaluation functions (to be used in a read-eval-print way).
  *
  * Most of the printing is actually already done by these same
  * functions.*)

val definition :
  include_file:(?test_limit:(int option) -> string -> Ndcore.Term.term list option) ->
  reload:(?session:(string list) -> unit -> unit) ->
  test_limit:(int option) ->
  print:('a -> unit) -> Parsetree.Preterm.definition_mode -> p:IO.Pos.t ->
  Ndcore.Term.term option option
val toplevel : concise:bool ->
  include_file:(?test_limit:(int option) -> string -> Ndcore.Term.term list option) ->
  reload:(?session:(string list) -> unit -> unit) ->
  test_limit:(int option) ->
  print:('a -> unit) -> Parsetree.Preterm.toplevel -> p:IO.Pos.t ->
  unit option
val term :
  print:('a -> unit) -> Parsetree.Preterm.term_mode -> p:IO.Pos.t ->
  Ndcore.Term.term option
