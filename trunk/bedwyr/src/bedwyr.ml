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

let stdlib = "\
Kind    list    type -> type.

Type    nil     list _.
Type    ::      A -> list A -> list A.

Define member : A -> list A -> prop by
  member X (X :: _) ;
  member X (_ :: L) := member X L.

Kind    option  type -> type.
Type    opnone  option A.
Type    opsome  A -> option A.
"

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
let test_limit  = ref (Some 0)
let session     = ref []
let definitions = ref []
let queries     = ref []
let inclfiles   = ref []

let incr_test_limit () =
  test_limit := match !test_limit with
    | Some n -> Some (n+1)
    | None -> None
let remove_test_limit () =
  test_limit := None
let decr_test_limit = function
  | Some n when n > 0 -> Some (n-1)
  | Some _ -> Some 0
  | None -> None

let _ =
  Arg.parse
    (Arg.align
       [ "-I", Arg.Set batch,
           " Do not enter interactive mode" ;
         "-t", Arg.Unit incr_test_limit,
           " Run tests (use as many times as the #include-depth)" ;
         "-T", Arg.Unit remove_test_limit,
           " Run tests (use as many times as the #include-depth)" ;
         "--filter", Arg.Set System.use_filter,
           "Use tabling with variables" ;
         "-d", Arg.String (fun s -> definitions := s::!definitions),
           "<s> Add definition" ;
         "-e", Arg.String (fun s -> queries := s::!queries),
           "<s> Execute query" ;
         "--freezing", Arg.Set_int Prover.freezing_point,
           "<n> Enable backward chaining and set its limit" ;
         "--saturation", Arg.Set_int Prover.saturation_pressure,
           "<n> Enable forward chaining and set its limit" ;
         "--version", Arg.Unit print_version,
           " Display version info and exit" ;
         "-D", Arg.Set Output.debug,
           " Print debugging information"
       ])
    (fun f -> session := f::!session)
    usage_msg ;
  session := List.rev (!session) ;
  definitions := List.rev (!definitions) ;
  queries := List.rev (!queries)

let run_on_string ~strict f ?fname str =
  Read.apply_on_string
    (fun lexbuf -> ignore (f lexbuf)) ?fname str ;
  if strict then Interface.Status.exit_if ()

let run_on_file ~strict f fpath =
  let cwd = Sys.getcwd () in
  let fpath =
    if (Filename.is_relative fpath &&
        not (String.length fpath > 2 && fpath.[0]='~' && fpath.[1]='/'))
    then Filename.concat cwd fpath
    else fpath
  in
  if (List.mem fpath !inclfiles) then
    Output.wprintf "File %S already included, skipping." fpath
  else begin
    Output.wprintf "Now including %S." fpath ;
    inclfiles := fpath :: !inclfiles ;
    try
      IO.chdir (Filename.dirname fpath) ;
      let fname = Filename.basename fpath in
      IO.run_in
        (fun channel ->
           Read.apply_on_channel
             (fun lexbuf -> ignore (f lexbuf)) ~fname channel)
        fname ;
      IO.chdir cwd
    with e -> ignore (Interface.Catch.io e)
  end ;
  if strict then Interface.Status.exit_if ()

let _ =
  let test_limit = !test_limit in
  let reload ~strict ?(session=(!session)) () =
    System.reset_decls () ;
    Preterm.Typing.clear () ;
    run_on_string ~strict (Interface.defl ~test_limit) ~fname:"Bedwyr::stdlib" stdlib ;
    inclfiles := [] ;
    List.iter (run_on_file ~strict (Interface.defl ~test_limit)) session ;
    List.iter (run_on_string ~strict (Interface.defs ~test_limit)) !definitions
  in
  Interface.reload := reload ~strict:false ;
  Interface.include_file := (fun ~test_limit ->
    run_on_file ~strict:false (Interface.defl ~test_limit:(decr_test_limit test_limit))) ;
  reload ~strict:true () ;
  List.iter (run_on_string ~strict:true (Interface.reps ~test_limit)) !queries ;
  if !batch
  then Interface.Status.exit_with ()
  else begin
    Output.printf ~nl:true "%s" welcome_msg ;
    Interface.repl ~test_limit (Lexing.from_channel stdin)
  end
