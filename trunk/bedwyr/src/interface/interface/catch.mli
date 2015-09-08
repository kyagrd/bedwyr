(****************************************************************************)
(* Bedwyr -- toplevel exception catching                                    *)
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

(** Catch some selected exceptions, replace them by an error message and
  * return [None]. *)

(** Catch exceptions commonly raised by query solving (from the unifier
  * or the prover). *)
val solve : p:IO.Pos.t -> exn -> 'a option

(** Catch exceptions commonly raised by meta-command execution (from
  * assertion, or actions that espect their arguments to be in an
  * appropriate state). *)
val meta_command : p:IO.Pos.t -> exn -> 'a option

(** Catch exceptions commonly raised by file I/O. *)
val io : ?p:IO.Pos.t -> exn -> 'a option

(** Catch all exceptions otherwise not handled. *)
val all : p:IO.Pos.t -> exn -> 'a option
