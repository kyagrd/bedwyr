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

type t = Lexing.position * Lexing.position

let dummy =
  Lexing.dummy_pos,Lexing.dummy_pos

let of_lexbuf lexbuf =
  let start = lexbuf.Lexing.lex_start_p in
  fun () -> start,lexbuf.Lexing.lex_curr_p

let of_token i =
  if i > 0
  then (Parsing.rhs_start_pos i,Parsing.rhs_end_pos i)
  else (Parsing.symbol_start_pos (),Parsing.symbol_end_pos ())

let to_pair (start,curr) =
  start.Lexing.pos_cnum,curr.Lexing.pos_cnum

let pp fmt (start,curr) =
  let pos_to_string (start,curr) =
    let l1 = start.Lexing.pos_lnum in
    let l2 = curr.Lexing.pos_lnum in
    let c1 = start.Lexing.pos_cnum - start.Lexing.pos_bol + 1 in
    let c2 = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if l1 < l2 then
      Printf.sprintf "line %d, byte %d - line %d, byte %d" l1 c1 l2 c2
    else if c1 < c2  then
      Printf.sprintf "line %d, bytes %d-%d" l2 c1 c2
    else
      Printf.sprintf "line %d, byte %d" l2 c2
  in
  let name = curr.Lexing.pos_fname in
  if name = "" then
    (* lexbuf line information is rarely accurate at the toplevel,
     * but character information still is! *)
    Format.fprintf fmt "At %s" (pos_to_string (start,curr))
  else
    Format.fprintf fmt "In file %S, at %s" name (pos_to_string (start,curr))
