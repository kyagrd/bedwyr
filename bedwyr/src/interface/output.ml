(****************************************************************************)
(* Bedwyr -- prover output                                                  *)
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

(* General purpose output facilities *)

let set_width formatter term_width =
  Format.pp_set_margin formatter term_width ;
  Format.pp_set_max_indent formatter
    ((Format.pp_get_margin formatter () * 4) / 5)

let kfprintf ~k ~prefix ~formatter f =
  if prefix="" then
    Format.kfprintf k formatter
      ("@[" ^^ f ^^ "@]")
  else
    Format.kfprintf k formatter
      ("@[<hov>%s@;<0 1>@[" ^^ f ^^ "@]@]")
      prefix

let prefix ~tag ?p () =
  let pos = match p with
    | Some p ->
        Format.fprintf Format.str_formatter "%a: " Preterm.Pos.pp p ;
        Format.flush_str_formatter ()
    | None -> ""
  in
  (tag^pos)

let fprintf ?(tag="") ?p ?(nl=false) ~formatter f =
  let k fmt =
    if nl
    then Format.pp_print_newline fmt ()
    else Format.pp_print_flush fmt ()
  in
  kfprintf ~k ~prefix:(prefix ~tag ?p ()) ~formatter f

(* Wrappers for normal output *)

let std_out = ref Format.std_formatter

let printf ?nl f =
  fprintf ?nl ~formatter:!std_out f

let sprintf ?(tag="") ?p f =
  let buffer = Buffer.create 80 in
  let return formatter =
    Format.pp_print_flush formatter () ;
    Buffer.contents buffer
  in
  let formatter = Format.formatter_of_buffer buffer in
  kfprintf ~k:return ~prefix:(prefix ~tag ?p ()) ~formatter f

(* Wrappers for abnormal output *)

let std_err = ref Format.err_formatter

let err_poss = ref []
let war_poss = ref []

let eprintf ?p f =
  begin match p with
    | Some pos -> err_poss := (Preterm.Pos.to_pair pos) :: !err_poss
    | None -> ()
  end ;
  fprintf ?p ~nl:true ~formatter:!std_err f

let wprintf ?p f =
  begin match p with
    | Some pos -> war_poss := (Preterm.Pos.to_pair pos) :: !war_poss
    | None -> ()
  end ;
  fprintf ~tag:"Warning: " ?p ~nl:true ~formatter:!std_err f

let std_dbg = ref Format.err_formatter

let debug = ref false

let dprintf ?p f =
  if !debug
  then fprintf ~tag:"[DEBUG] " ?p ~nl:true ~formatter:!std_dbg f
  else Format.ifprintf !std_dbg f
