(****************************************************************************)
(* Bedwyr -- message output                                                 *)
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

(* General purpose message output facilities *)

type colours = [`Error | `Warning | `Debug | `Clear]

let clear_ansi_code = "\027[0m"

let ansi_code,set_colours =
  let nb_colours =
    try ref (int_of_string (Sys.getenv "COLORS"))
    with Failure ("int_of_string") | Not_found -> ref 0
  in
  let ansi_code c = match !nb_colours with
    | 256 ->
        let rgb_to_256 r g b =
          "38;5;"^(string_of_int (16 + 6 * (6 * r + g) + b))
        in
        begin match c with
          | Some `Error -> Some ("\027[" ^ (rgb_to_256 5 1 1) ^ "m")
          | Some `Warning -> Some ("\027[" ^ (rgb_to_256 4 3 0) ^ "m")
          | Some `Debug -> Some ("\027[" ^ (rgb_to_256 4 1 5) ^ "m")
          | Some `Clear -> Some clear_ansi_code
          | None -> None
        end
    | 8 ->
        let rgb_to_8 r g b =
          (string_of_int (30 + 2 * (2 * b + g) + r))
        in
        begin match c with
          | Some `Error -> Some ("\027[" ^ (rgb_to_8 1 0 0) ^ "m")
          | Some `Warning -> Some ("\027[" ^ (rgb_to_8 1 1 0) ^ "m")
          | Some `Debug -> Some ("\027[" ^ (rgb_to_8 1 0 1) ^ "m")
          | Some `Clear -> Some clear_ansi_code
          | None -> None
        end
    | _ -> None
  and set_colours = fun n -> nb_colours := n in
  ansi_code,set_colours

let set_width formatter term_width =
  Format.pp_set_margin formatter term_width ;
  Format.pp_set_max_indent formatter
    ((Format.pp_get_margin formatter () * 4) / 5)

let cfprintf c fmt f =
  let k fmt = Format.fprintf fmt "@<0>%s" clear_ansi_code in
  Format.fprintf fmt "@<0>%s" c ;
  Format.kfprintf k fmt f

let pp_prefix fmt = function
  | Some p,Some c,_ -> cfprintf c fmt "%a: " Pos.pp p
  | Some p,None,tag -> Format.fprintf fmt "%s%a: " tag Pos.pp p
  | None,_,"" -> Format.fprintf fmt ("@]" ^^ "@[")
  | None,Some c,tag -> cfprintf c fmt "%s" tag
  | None,None,tag -> Format.fprintf fmt "%s" tag

let kfprintf ~k ?colour ~tag ?p ~formatter f =
  Format.kfprintf k formatter
    ("@[<hov 2>%a@," ^^ f ^^ "@]")
    pp_prefix (p,colour,tag)

let fprintf ?colour ?(tag="") ?p ?(nl=false) ~formatter f =
  let k fmt =
    if nl
    then Format.pp_print_newline fmt ()
    else Format.pp_print_flush fmt ()
  in
  kfprintf ~k ?colour:(ansi_code colour) ~tag ?p ~formatter f

(*
let pp_spaced_string fmt s =
  match Str.split_delim (Str.regexp "\n") s with
    | [] -> ()
    | h::t ->
        Format.pp_print_string fmt h ;
        List.iter
          Format.(fun s -> pp_print_space fmt () ; pp_print_string fmt s)
          t
 *)

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
  kfprintf ~k:return ~tag ?p ~formatter f

(* Wrappers for abnormal output *)

let std_err = ref Format.err_formatter

let err_poss = ref []
let war_poss = ref []

let eprintf ?p f =
  begin match p with
    | Some pos -> err_poss := (Pos.to_pair pos) :: !err_poss
    | None -> ()
  end ;
  fprintf ~colour:`Error ~tag:"[Error] " ?p ~nl:true ~formatter:!std_err f

let wprintf ?p f =
  begin match p with
    | Some pos -> war_poss := (Pos.to_pair pos) :: !war_poss
    | None -> ()
  end ;
  fprintf ~colour:`Warning ~tag:"[Warning] " ?p ~nl:true ~formatter:!std_err f

let std_dbg = ref Format.err_formatter

let debug = ref false

let dprintf ?p f =
  if !debug
  then fprintf ~colour:`Debug ~tag:"[Debug] " ?p ~nl:true ~formatter:!std_dbg f
  else Format.ifprintf !std_dbg f
