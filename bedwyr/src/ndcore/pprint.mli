(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler               *)
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

val debug : bool ref

type assoc = Left | Right | Both | Nonassoc
val set_infix : (string * assoc) list -> unit

val term_to_string_full_debug :
  generic:string list -> bound:string list -> bool -> Term.term -> string

val term_to_string_full :
  generic:string list -> bound:string list -> Term.term -> string

val term_to_string : ?bound:string list -> Term.term -> string

val print_term : ?bound:string list -> Term.term -> unit

val pp_term : Format.formatter -> Term.term -> unit

val pp_preabstracted :
  generic:string list -> bound:string list ->
  Format.formatter -> Term.term -> unit

val term_to_string_preabstracted :
  generic:string list -> bound:string list -> Term.term -> string
