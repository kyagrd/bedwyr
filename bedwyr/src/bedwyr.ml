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
    (fun fref -> IO.Output.set_width !fref term_width)
    [IO.Output.std_out;IO.Output.std_err;IO.Output.std_dbg]

let welcome_msg =
  let open Interface.Config in
  Printf.sprintf
    "%s %s%s welcomes you.\n\
    \n\
    For a little help, type \"#help.\"\n"
    package_name
    package_version
    (if build="v"^package_version || build="" then ""
     else " (revision " ^ build ^ ")")

let plugins = ref []

let add_plugin_dir,add_plugin =
  let plugin_dirs =
    ref [
      Findlib.package_directory Interface.Config.project_tarname ;
    ]
  in
  let add_plugin_dir dir = plugin_dirs := dir :: !plugin_dirs
  and add_plugin (plugin,desc) =
    let open Dynlink in
    let rec aux = function
      | [] -> ()
      | dir::dirs ->
          try
            loadfile (adapt_filename (Filename.concat dir plugin ^ ".cma")) ;
            plugins := desc :: !plugins
          with Error e -> aux dirs
    in
    aux !plugin_dirs
  in
  add_plugin_dir,add_plugin

let () =
  List.iter add_plugin [
    "tableXmlExport","XML export of proofs" ;
  ]

let version_msg =
  let open Interface.Config in
  Printf.sprintf
    "%s prover %s, Copyright (C) 2005-2015 Slimmer project.\n\
    This is free software, distributed under the GNU General Public License\n\
    version 2.  There is NO WARRANTY, not even SOUNDNESS nor COMPLETENESS.\n\
    Rev. %s (built with OCaml %s on the %s).\n\
    Features (+/-):%s\n\
    Plugins (+/-):%s\n"
    package_name
    package_version
    (if build="" then "unknown" else build)
    ocaml_version
    build_date
    (let get (s1,s2) = [(match s2 with "" -> "\n - " | _ -> "\n + ") ; s1] in
     String.concat "" (List.flatten (List.map get features)))
    (let get s = [("\n + ") ; s] in
     String.concat "" (List.flatten (List.map get !plugins)))

let print_version () =
  IO.Output.printf ~nl:true "%s" version_msg ;
  exit 0

let usage_msg =
  Printf.sprintf
    "Usage: bedwyr [filename | option]*\n"

let batch       = ref false

(* Bedwyr's working directory *)
let () = IO.Files.bwd := Sys.getcwd ()
module InclFiles =
  Set.Make (struct type t = string let compare = compare end)
let inclfiles = ref (InclFiles.empty)

let _ =
  Prover.System.(
    Arg.parse
      (Arg.align
         [ "-I", Arg.Set batch,
             " Do not enter interactive mode" ;
           "-t", Arg.Unit incr_test_limit,
             " Run tests (use as many times as the #include-depth)" ;
           "-T", Arg.Unit remove_test_limit,
             " Run tests (use as many times as the #include-depth)" ;
           "--filter", Arg.Set use_filter,
             "Use tabling with variables" ;
           "-d", Arg.String (fun s -> definitions := s::!definitions),
             "<s> Add definition" ;
           "-e", Arg.String (fun s -> queries := s::!queries),
             "<s> Execute query" ;
           "--freezing", Arg.Set_int Prover.Proofsearch.freezing_point,
             "<n> Enable backward chaining and set its limit" ;
           "--saturation", Arg.Set_int Prover.Proofsearch.saturation_pressure,
             "<n> Enable forward chaining and set its limit" ;
           "--version", Arg.Unit print_version,
             " Display version info and exit" ;
           "-D", Arg.Set IO.Output.debug,
             " Print debugging information" ;
           "--colours", Arg.Int (fun n -> IO.Output.set_colours n),
            "<n> Number of supported colours (256 or 8; 0 do disable)" ;
         ])
      (fun f -> session := f::!session)
      usage_msg ;
    session := List.rev (!session) ;
    definitions := List.rev (!definitions) ;
    queries := List.rev (!queries))

let _ =
  Interface.Run.reload () ;
  Prover.System.Status.exit_if () ;
  List.iter
    (function query -> ignore (Interface.Run.query_string query))
    !Prover.System.queries ;
  if !batch then Prover.System.Status.exit_with ()
  else begin
    IO.Output.printf ~nl:true "%s" welcome_msg ;
    Interface.Run.queries_channel stdin
  end
