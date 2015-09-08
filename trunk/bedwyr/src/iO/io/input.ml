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

(* General purpose input facilities *)

let apply_on_lexbuf f lexbuf =
  try Some (f lexbuf)
  with Sys_error e ->
    Output.eprintf "Couldn't parse %S:@ %s."
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_fname) e ;
    None

let apply_on_string f ?(fname="") str =
  let lexbuf = Lexing.from_string str in
  let lexbuf = Lexing.({
    lexbuf with lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = fname }
  }) in
  f lexbuf

let apply_on_channel f ?(fname="") channel =
  let lexbuf = Lexing.from_channel channel in
  let lexbuf = Lexing.({
    lexbuf with lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = fname } ;
  }) in
  f lexbuf
