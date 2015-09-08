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

let print_keys f table =
  print_list (List.map f (get_keys table))

let accum_names var _ accum =
  let n = Ndcore.Term.get_var_name var in
  let m = Str.replace_first (Str.regexp "^(\\(.+\\))$") "\\1" n in
  if m=n then n::accum else n::m::accum

let () =
  Format.printf "@[<v 0>" ;

  let open Parsetree.Lexer in
  print_keys (fun s -> "#"^s) command_table ;
  print_keys (fun x -> x) ub_keyword_t ;
  print_keys (fun x -> x) lb_keyword_t ;
  print_keys (fun x -> x) lb_primitive_t ;
  print_keys (fun x -> x) ib_primitive_t ;

  Interface.Run.reload () ;
  let open Prover.Environment in
  print_list (Types.fold accum_names []) ;
  print_list (Objects.fold accum_names accum_names []) ;
  print_keys Ndcore.Term.get_var_name Logic.builtins_t ;

  Format.printf "@]"
