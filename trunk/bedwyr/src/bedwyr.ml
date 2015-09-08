(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005 David Baelde, Alwen Tiu, Axelle Ziegler               *)
(* Copyright (C) 2006 Andrew Gacek                                          *)
(* Copyright (C) 2006,2007,2009,2011 David Baelde                           *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2011-2013 Quentin Heath                                    *)
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

let () =
  let term_width =
    try int_of_string (Sys.getenv "COLUMNS")
    with Failure ("int_of_string") | Not_found -> 72
  in
  List.iter
    (fun fref -> Output.set_width !fref term_width)
    [Output.std_out;Output.std_err;Output.std_dbg]

let welcome_msg =
  Printf.sprintf
    "%s %s%s welcomes you.\n\
    \n\
    For a little help, type \"#help.\"\n"
    Config.package_name
    Config.package_version
    (if Config.build="v"^Config.package_version || Config.build="" then ""
     else " (revision " ^ Config.build ^ ")")

let version_msg =
  Printf.sprintf
    "%s prover %s, Copyright (C) 2005-2015 Slimmer project.\n\
    This is free software, distributed under the GNU General Public License\n\
    version 2.  There is NO WARRANTY, not even SOUNDNESS nor COMPLETENESS.\n\
    %s (built with OCaml %s on the %s).\n\
    Features (+/-):%s\n"
    Config.package_name
    Config.package_version
    (if Config.build="" then "Unknown revision"
     else "Rev. " ^ Config.build ^ "")
    Config.ocaml_version
    Config.build_date
    (String.concat ""
       (List.flatten
          (List.map
             (fun (s1,s2) ->
                [(match s2 with "" -> "\n - " | _ -> "\n + ") ; s1])
             Config.features)))

let print_version () =
  Output.printf ~nl:true "%s" version_msg ;
  exit 0

let usage_msg =
  Printf.sprintf
    "Usage: bedwyr [filename | option]*\n"

let batch       = ref false

(* Bedwyr's working directory *)
let () = IO.bwd := Sys.getcwd ()
module InclFiles =
  Set.Make (struct type t = string let compare = compare end)
let inclfiles = ref (InclFiles.empty)

let _ =
  Arg.parse
    (Arg.align
       [ "-I", Arg.Set batch,
           " Do not enter interactive mode" ;
         "-t", Arg.Unit Interface.incr_test_limit,
           " Run tests (use as many times as the #include-depth)" ;
         "-T", Arg.Unit Interface.remove_test_limit,
           " Run tests (use as many times as the #include-depth)" ;
         "--filter", Arg.Set System.use_filter,
           "Use tabling with variables" ;
         "-d", Arg.String (fun s -> Interface.definitions := s::!Interface.definitions),
           "<s> Add definition" ;
         "-e", Arg.String (fun s -> Interface.queries := s::!Interface.queries),
           "<s> Execute query" ;
         "--freezing", Arg.Set_int Prover.freezing_point,
           "<n> Enable backward chaining and set its limit" ;
         "--saturation", Arg.Set_int Prover.saturation_pressure,
           "<n> Enable forward chaining and set its limit" ;
         "--version", Arg.Unit print_version,
           " Display version info and exit" ;
         "-D", Arg.Set Output.debug,
           " Print debugging information" ;
         "--colours", Arg.Int (fun n -> Output.set_colours n),
          " Number of supported colours (256 or 8; 0 do disable)" ;
       ])
    (fun f -> Interface.session := f::!Interface.session)
    usage_msg ;
  Interface.session := List.rev (!Interface.session) ;
  Interface.definitions := List.rev (!Interface.definitions) ;
  Interface.queries := List.rev (!Interface.queries)

let _ =
  Interface.reload () ;
  Interface.Status.exit_if () ;
  List.iter
    (function query -> ignore (Interface.run_query_string query))
    !Interface.queries ;
  if !batch then Interface.Status.exit_with ()
  else begin
    Output.printf ~nl:true "%s" welcome_msg ;
    Interface.run_queries_channel stdin
  end
