(****************************************************************************)
(* Bedwyr prover                                                            *)
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

let get_keys table =
  Hashtbl.fold (fun k _ accum -> k::accum) table []

let print_list = function
  | [] -> ()
  | h :: t ->
      Format.printf "@;<1 0>@[<hov 2>" ;
      Format.printf "%s" h ;
      List.iter (fun k -> Format.printf "@ %s" k) t ;
      Format.printf "@]@;<1 0>"

let print_keys table =
  print_list (get_keys table)

let () =
  Format.printf "@[<v 0>" ;
  print_list (List.map (fun s -> "#"^s) (get_keys Lexer.command_table)) ;
  print_keys Lexer.ub_keyword_t ;
  print_keys Lexer.lb_keyword_t ;
  print_keys Lexer.lb_primitive_t ;
  print_keys Lexer.ib_primitive_t ;
  (* TODO get the following dynamically from Bedwyr *)
  print_list [
    "list" ;
    "nil" ;
    "::" ;
    "member" ;
  ] ;
  (* TODO get the following dynamically from Environment *)
  print_list [
    "read" ;
    "fread" ;
    "fopen_in" ;
    "fclose_in" ;
    "print" ;
    "println" ;
    "printstr" ;
    "fprint" ;
    "fprintln" ;
    "fprintstr" ;
    "fopen_out" ;
    "fclose_out" ;
  ] ;
  Format.printf "@]"
