(****************************************************************************)
(* Bedwyr -- lexing position information                                    *)
(* Copyright (C) 2012-2015 Quentin Heath                                    *)
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

(** Position information during parsing. For error messages only. *)

(** Position information. *)
type t

(** Dummy position information. *)
val dummy : t

(** Current position (lexing). *)
val of_lexbuf : Lexing.lexbuf -> unit -> t

(** Current position (parsing). *)
val of_token : int -> t

(** Offset pair. *)
val to_pair : t -> int * int

(** Position information pretty-printing. *)
val pp : Format.formatter -> t -> unit
