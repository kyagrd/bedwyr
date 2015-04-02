(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2015 Baelde, Tiu, Ziegler, Gacek, Heath               *)
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
"

let welcome_msg =
  Printf.sprintf
    "%s %s%s welcomes you.\n\
    \n\
    For a little help, type \"#help.\"\n"
    Config.package_name
    Config.package_version
    (if Config.build="v"^Config.package_version || Config.build="" then ""
     else " (revision " ^ Config.build ^ ")")

let print_version () : unit =
  Printf.printf
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
       (List.map
          (fun (s1,s2) -> (match s2 with "" -> "\n - " | _ -> "\n + ") ^ s1)
          Config.features)) ;
  exit 0

let usage_msg =
  Printf.sprintf
    "Usage: bedwyr [filename | option]*\n"

let batch       = ref false
let session     = ref []
let definitions = ref []
let queries     = ref []
let inclfiles   = ref []

let incr_test_limit () =
  Interface.test_limit := match !Interface.test_limit with
    | Some n -> Some (n+1)
    | None -> None
let remove_test_limit () =
  Interface.test_limit := None

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
         "-D", Arg.Set System.debug,
           " Print debugging information"
       ])
    (fun f -> session := f::!session)
    usage_msg ;
  session := List.rev (!session) ;
  definitions := List.rev (!definitions) ;
  queries := List.rev (!queries)

let run_on_string ~strict f ?(fname="") str =
  let lexbuf = Lexing.from_string str in
  let lexbuf = Lexing.({
    lexbuf with lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = fname }
  }) in
  f lexbuf ;
  if strict then Interface.exit_if_status ()

let run_on_file ~strict f fpath =
  let cwd = Sys.getcwd () in
  let fpath =
    if (Filename.is_relative fpath &&
        not (String.length fpath > 2 && fpath.[0]='~' && fpath.[1]='/'))
    then Filename.concat cwd fpath
    else fpath
  in
  if (List.mem fpath !inclfiles) then
    Format.eprintf "File %S already included, skipping.@." fpath
  else begin
    Format.eprintf "Now including %S.@." fpath ;
    inclfiles := fpath :: !inclfiles ;
    try
      IO.chdir (Filename.dirname fpath) ;
      let fname = Filename.basename fpath in
      let aux channel =
        let lexbuf = Lexing.from_channel channel in
        let lexbuf = Lexing.({
          lexbuf with lex_curr_p =
            { lexbuf.lex_curr_p with pos_fname = fname } ;
        }) in
        f lexbuf
      in
      IO.run_in aux fname ;
      IO.chdir cwd
    with e -> ignore (Interface.Catch.io e)
  end ;
  if strict then Interface.exit_if_status ()

let _ =
  let reload ~strict ?(session=(!session)) () =
    System.reset_decls () ;
    Input.Typing.clear () ;
    run_on_string ~strict Interface.defl ~fname:"Bedwyr::stdlib" stdlib ;
    inclfiles := [] ;
    List.iter (run_on_file ~strict Interface.defl) session ;
    List.iter (run_on_string ~strict Interface.defs) !definitions
  in
  System.read_term := Interface.read_term ;
  Interface.reload := reload ~strict:false ;
  Interface.include_file := run_on_file ~strict:false Interface.defl ;
  reload ~strict:true () ;
  List.iter (run_on_string ~strict:true Interface.reps) !queries ;
  if !batch
  then Interface.exit_with_status ()
  else begin
    Format.printf "%s@." welcome_msg ;
    Interface.repl (Lexing.from_channel stdin)
  end
