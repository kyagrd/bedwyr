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

exception Invalid_command
exception Assertion_failed
exception Uncleared_tables

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

let help_msg =
  "Useful commands in query mode:\n\
  #help.                               Display this message.\n\
  #exit.                               Exit.\n\
  #debug [flag].                       Turn debugging [on]/off \
    (initially off).\n\
  #time [flag].                        Turn timing [on]/off (initially off).\n\
  #session \"file_1\" ... \"file_N\".      Load these files as the \
    current session.\n\
  #reload.                             Reload the current session.\n\
  #reset.                              Clears the current session.\n\
  #show_table [pred].                  Displays the predicate's table.\n\
  #save_table [pred] [file].           Save the predicate's table in a file.\n\
  #equivariant [flag].                 Turn equivariant tabling [on]/off \
    (initially on).\n\
  Or type in a formula to ask for its verification.\n\
  For more information (including commands relevant in definition mode),\n\
  see the user guide.\n\n"

let interactive = ref true
let test_limit  = ref (Some 0)
let session     = ref []
let definitions = ref []
let queries     = ref []
let inclfiles   = ref []
let exit_status = ref None
let strict_mode = ref false
let clean_tables = ref true

let incr_test_limit () =
  test_limit := match !test_limit with
    | Some n -> Some (n+1)
    | None -> None
let decr_test_limit = function
  | Some n when n > 0 -> Some (n-1)
  | Some _ -> Some 0
  | None -> None

let _ =
  Arg.parse
    (Arg.align
       [ "-I", Arg.Clear interactive,
           " Do not enter interactive mode" ;
         "-t", Arg.Unit incr_test_limit,
           " Run tests in top-level files (use twice for included files too)" ;
         "--strict", Arg.Set strict_mode,
           " Quit at the first non-interactive error" ;
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

let position_range (start,curr) =
  let position (start,curr) =
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
     * but character information is *)
    Printf.sprintf "At %s:" (position (start,curr))
  else
    Printf.sprintf "In file %S, %s:" name (position (start,curr))

let position_lex lexbuf =
  let start = lexbuf.Lexing.lex_start_p in
  let curr = lexbuf.Lexing.lex_curr_p in
  start,curr

let do_cleanup f x clean =
  try f x ; clean () with e -> clean () ; raise e

let bool_of_flag = function
  | None | Some "on" | Some "true" -> true
  | Some "off" | Some "false" -> false
  | _ -> raise Invalid_command

let rec process_input ~run_input ~test_limit ?(interactive=false) parse lexbuf =
  let flush_input () =
    Lexing.flush_input lexbuf ;
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
          Lexing.pos_bol = 0 ;
          Lexing.pos_lnum = 1 }
  in
  let basic_error
        ?(interactive_fun=flush_input)
        ?(non_interactive_fun=ignore)
        error_code =
    begin
      if interactive then interactive_fun ()
      else if !strict_mode then exit error_code
      else begin
        begin
          if !exit_status = None
          then exit_status := Some error_code
        end ;
        non_interactive_fun ()
      end
    end ;
    None
  in
  let skip_input () = Parser.skip_invalid Lexer.invalid lexbuf in
  let lexer_error _ = basic_error 1 ~non_interactive_fun:skip_input in
  let parser_error _ = basic_error 1 in
  let def_error _ = basic_error 2 in
  let ndcore_error _ = basic_error 3 in
  let solver_error _ = basic_error 4 in
  let bedwyr_error _ = basic_error 5 in
  let critical_error _ =
    basic_error 5
      ~interactive_fun:(fun () -> exit 5)
      ~non_interactive_fun:(fun () -> exit 5)
  in
  let wprintf ?(p=position_lex lexbuf) f =
    Format.fprintf
      (if interactive then Format.std_formatter else Format.err_formatter)
      ("@[<hov>Warning: %s@;<1 1>@[" ^^ f ^^ "@]@]@.")
      (position_range p)
  in
  let eprintf k ?(p=position_lex lexbuf) f =
    Format.kfprintf k
      (if interactive then Format.std_formatter else Format.err_formatter)
      ("@[<hov>%s@;<1 1>@[" ^^ f ^^ "@]@]@.")
      (position_range p)
  in
  try while true do
    if interactive then Format.printf "?= %!" ;
    begin match match
      try Some (parse Lexer.token lexbuf) with
        (* I/O - Lexer *)
        | End_of_file -> raise End_of_file
        | Input.Illegal_string c ->
            eprintf lexer_error
              "Illegal string starting with %C in input."
              c
        | Input.Illegal_string_comment ->
            eprintf lexer_error
              "Unmatched comment delimiter in string."
        | Input.Illegal_token (n1,n2) ->
            eprintf lexer_error
              "%S is illegal in a token, did you mean %S?"
              (Lexing.lexeme lexbuf)
              (String.concat " " [n1;n2])
        | Input.Unknown_command n ->
            eprintf lexer_error
              "Unknown command %S, use \"#help.\" for a short list."
              n

        (* I/O - Parser *)
        | Parsing.Parse_error ->
            eprintf lexer_error
              "Unexpected input."
        | Input.Parse_error (p,s1,s2) ->
            eprintf parser_error ~p
              "%s while parsing@ %s."
              s1 s2
        | Input.Qed_error p ->
            eprintf parser_error ~p
              "\"Qed\" command used while not in proof mode."
    with
      | Some input ->
          begin try Some (run_input ~test_limit input) with
            (* Declarations *)
            | System.Invalid_type_declaration (n,p,ki,s) ->
                eprintf def_error ~p
                  "Cannot declare type %s of kind %a:@ %s."
                  n
                  Input.Typing.pp_kind ki
                  s
            | System.Missing_type (n,_) ->
                eprintf def_error
                  "Undeclared type %s."
                  n
            | System.Invalid_const_declaration (n,p,ty,s) ->
                eprintf def_error ~p
                  "Cannot declare constant %s of type %a:@ %s."
                  n
                  (Input.Typing.get_pp_type ()) ty
                  s
            | System.Invalid_flavour (n,p,gf,f) ->
                let string_of_flavour = function
                  | Input.Normal -> "Normal"
                  | Input.Inductive -> "Inductive"
                  | Input.CoInductive -> "CoInductive"
                in
                eprintf def_error ~p
                  "Cannot declare predicate %s of flavour %s:@ \
                    this definition block is %s."
                  n
                  (string_of_flavour f)
                  (string_of_flavour gf)
            | System.Invalid_pred_declaration (n,p,ty,s) ->
                eprintf def_error ~p
                  "Cannot declare predicate %s of type %a:@ %s."
                  n
                  (Input.Typing.get_pp_type ()) ty
                  s
            | Input.Typing.Invalid_pred_declaration (n,p,ty) ->
                eprintf def_error ~p
                  "Cannot declare predicate %s of type %a:@ \
                    target type must be %s."
                  n
                  (Input.Typing.get_pp_type ()) ty
                  (Input.Typing.get_type_to_string () Input.Typing.tprop)

            (* Definitions and theorems *)
            | System.Missing_declaration (n,p) ->
                eprintf def_error ?p
                  "Undeclared object %s."
                  n
            | System.Stratification_error (n,p) ->
                eprintf def_error ~p
                  "Inconsistent stratification:@ %s is forbidden here."
                  n
            | System.Inconsistent_definition (n,p,s) ->
                eprintf def_error ~p
                  "Inconsistent extension of definition for %s:@ %s."
                  n
                  s
            | System.Inconsistent_theorem (n,p,s) ->
                eprintf def_error ~p
                  "Inconsistent theorem specification for %s:@ %s."
                  n
                  s

            (* Kind/type checking *)
            | Input.Typing.Type_kinding_error (n,p,ki1,ki2) ->
                eprintf def_error ~p
                  "Kinding error: the type constructor %s has kind %a \
                    but is used as %a."
                  n
                  Input.Typing.pp_kind ki2
                  Input.Typing.pp_kind ki1
            | Input.Typing.Undefinite_type (n,p,ty,tp) ->
                let type_to_string = Input.Typing.get_type_to_string () in
                eprintf def_error ~p
                  "Polymorphism error for %s: parameter%s %s@ of type %s@ \
                    %s not transparant."
                  n
                  (if List.length tp > 1 then "s" else "")
                  (String.concat ", "
                     (List.map
                        (fun i -> Format.sprintf "%s"
                                    (type_to_string (Input.Typing.tparam i))) tp))
                  (type_to_string ty)
                  (if List.length tp > 1 then "are" else "is")
            | Input.Typing.Type_order_error (n,p,ty) ->
                begin match n with
                  | Some n ->
                      eprintf def_error ~p
                        "Typing error: cannot give free variable %s the type %a." n
                        (Input.Typing.get_pp_type ()) ty
                  | None ->
                      eprintf def_error ~p
                        "Typing error: cannot quantify over type %a."
                        (Input.Typing.get_pp_type ()) ty
                end
            | Input.Term_typing_error (p,ty1,ty2,unifier) ->
                eprintf def_error ~p
                  "Typing error: this term has type %a but is used as %a."
                  (Input.Typing.get_pp_type ~unifier ()) ty2
                  (Input.Typing.get_pp_type ~unifier ()) ty1

            (* Using predicates and tables *)
            | System.Missing_definition (n,p) ->
                eprintf def_error ?p
                  "Undefined predicate (%s was declared as a constant)."
                  n
            | System.Missing_table (n,p) ->
                eprintf def_error ?p
                  "No table (%s is neither inductive nor coinductive)."
                  n
            | Uncleared_tables ->
                eprintf def_error
                  "Unable to export tables (some have been cleared, \
                    state might be inconsistent).@ Run #clear_tables to fix."

            (* Core *)
            | Unify.NotLLambda t ->
                eprintf ndcore_error
                  "Not LLambda unification encountered:@ %a."
                  Pprint.pp_term t

            (* Solving *)
            | Prover.Level_inconsistency ->
                eprintf solver_error
                  "This formula cannot be handled by the left prover!"
            | Prover.Left_logic t ->
                eprintf ndcore_error
                  "Logic variable encountered on the left:@ %a."
                  Pprint.pp_term t

            (* Misc Bedwyr errors *)
            | Assertion_failed ->
                eprintf solver_error
                  "Assertion failed."
            | System.Interrupt ->
                eprintf bedwyr_error
                  "User interruption."
            | System.Abort_search ->
                eprintf bedwyr_error
                  "Proof search aborted!"
            | IO.File_error (s1,n,s2) ->
                eprintf bedwyr_error
                  "Couldn't %s@ %S:@ %s."
                  s1 n s2
            | Invalid_command ->
                eprintf bedwyr_error
                  "Invalid command, or wrong arguments."
          end
      | None -> None
    with
      | Some (singletons,proof) ->
          List.iter
            (fun (p,n) -> wprintf ~p "%s is a singleton variable." n)
            singletons ;
          if proof then Parser.skip_proof Lexer.proof lexbuf
      | None -> ()
    end ;
    if interactive then flush stdout ;
    begin match !exit_status with
      | None -> ()
      | Some error_code -> exit error_code
    end
  done with
    | End_of_file ->
        if interactive then Format.printf "@."
    (* Unhandled errors *)
    | Failure s ->
        let _ =
          eprintf critical_error
            "Error:@ %s"
            s
        in
        ()
    | e ->
        let _ =
          eprintf critical_error
            "Unexpected error:@ %s"
            (Printexc.to_string e)
        in
        ()

and run_query_or_def ~test_limit =
  let reset =
    let s = Term.save_state () in
    let ns = Term.save_namespace () in
    fun () -> Term.restore_state s ; Term.restore_namespace ns
  in function
    | Input.KKind (l, k) ->
        List.iter (fun s -> System.declare_type s k) l ;
        [],false
    | Input.TType (l, t) ->
        List.iter (fun s -> System.declare_const s t) l ;
        [],false
    | Input.Def (decls,defs) ->
        let stratum = System.declare_preds decls in
        (List.rev (System.add_clauses stratum defs)),false
    | Input.Theorem thm ->
        System.add_theorem thm ;
        [],true
    | Input.Qed p -> raise (Input.Qed_error p)
    | Input.Query t ->
        do_cleanup
          (fun pre_query ->
             let query = System.translate_query pre_query in
             if !exit_status = None then Prover.toplevel_prove query)
          t
          reset ;
        [],false
    | Input.Cert t ->
        let cert = System.translate_cert t in
        (*
         Prover.toplevel_prove cert
         *)
        ignore cert ;
        [],false
    | Input.Command c ->
        command ~test_limit c reset ;
        [],false

and input_from_file ~test_limit file =
  let channel = IO.open_in file in
  let lexbuf = Lexing.from_channel channel in
  input_defs ~test_limit lexbuf file ;
  IO.close_in file channel
and input_defs ?(test_limit=(!test_limit)) lexbuf file =
  lexbuf.Lexing.lex_curr_p <- {
    lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = file } ;
  let run_input = run_query_or_def in
  process_input ~run_input ~test_limit Parser.input_def lexbuf
and input_queries ?(test_limit=(!test_limit)) ?(interactive=false) lexbuf =
  let run_input = run_query_or_def in
  process_input ~run_input ~test_limit ~interactive Parser.input_query lexbuf

and load_session () =
  System.reset_decls () ;
  Input.Typing.clear () ;
  let lexbuf = (Lexing.from_string stdlib) in
  input_defs ~test_limit:(Some 0) lexbuf "Bedwyr::stdlib" ;
  inclfiles := [] ;
  List.iter (fun fname -> include_file fname) !session

and include_file ?(test_limit=(!test_limit)) fname =
  let cwd = Sys.getcwd () in
  let fname =
    if (Filename.is_relative fname &&
        not (String.length fname > 2 && fname.[0]='~' && fname.[1]='/'))
    then Filename.concat cwd fname
    else fname
  in
  if (List.mem fname !inclfiles) then
    Format.eprintf "File %S already included, skipping.@." fname
  else begin
    Format.eprintf "Now including %S.@." fname ;
    inclfiles := fname :: !inclfiles ;
    IO.chdir (Filename.dirname fname) ;
    input_from_file ~test_limit (Filename.basename fname);
    IO.chdir cwd
  end

(* Execute meta-commands.
 * @raise Invalid_command if an argument is unexpected
 * (especially if a boolean flag is given something other than
 * "", "true", "on", "false" or "off")
 * @raise Assertion_failed if [#assert formula.], [#assert_not formula.]
 * or [#assert_raise formula.] fails *)
and command ~test_limit c reset =
  let aux = function
    | Input.Exit ->
        IO.close_user_files () ;
        begin match !exit_status with
          | None -> exit 0
          | Some error_code -> exit error_code
        end
    | Input.Help -> Format.printf "%s" help_msg

    (* Session management *)
    | Input.Include l -> List.iter (include_file ~test_limit:(decr_test_limit test_limit)) l
    | Input.Reload -> load_session ()
    | Input.Session l -> session := l ; load_session ()

    (* Turn debugging on/off. *)
    | Input.Debug value -> System.debug := (bool_of_flag value)

    (* Turn timing on/off. *)
    | Input.Time value -> System.time := (bool_of_flag value)

    (* Tabling-related commands *)
    | Input.Equivariant value -> Table.O.set_eqvt (bool_of_flag value)
    | Input.Freezing temp -> Prover.freezing_point := temp
    | Input.Saturation pressure -> Prover.saturation_pressure := pressure
    | Input.Env -> System.print_env ()
    | Input.Type_of pre_term -> System.print_type_of pre_term
    | Input.Show_def (p,name) ->
        System.show_def (p,Term.atom ~tag:Term.Constant name)
    | Input.Show_table (p,name) ->
        System.show_table (p,Term.atom ~tag:Term.Constant name)
    | Input.Clear_tables ->
        clean_tables := true ;
        System.clear_tables ()
    | Input.Clear_table (p,name) ->
        clean_tables := false ;
        System.clear_table (p,Term.atom ~tag:Term.Constant name)
    (* save the content of a table to a file. An exception is thrown if
     * file already exists. *)
    | Input.Save_table (p,name,file) ->
        System.save_table (p,Term.atom ~tag:Term.Constant name) name file
    | Input.Export name ->
        if !clean_tables then System.export name else raise Uncleared_tables

    (* Testing commands *)
    | Input.Assert pre_query ->
        let query = System.translate_query pre_query in
        begin match test_limit with Some n when n <= 0 -> () | _ ->
          if !exit_status = None then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
              Pprint.pp_term query ;
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:(fun _ _ -> ())
              ~failure:(fun () -> raise Assertion_failed)
          end
        end
    | Input.Assert_not pre_query ->
        let query = System.translate_query pre_query in
        begin match test_limit with Some n when n <= 0 -> () | _ ->
          if !exit_status = None then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
              Pprint.pp_term query ;
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
          end
        end
    | Input.Assert_raise pre_query ->
        let query = System.translate_query pre_query in
        begin match test_limit with Some n when n <= 0 -> () | _ ->
          if !exit_status = None then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@."
              Pprint.pp_term query ;
            if try
              Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
                ~success:(fun _ _ -> true) ~failure:(fun _ -> true)
            with _ -> false
            then raise Assertion_failed
          end
        end
  in
  let reset = match c with
    | Input.Include _ | Input.Reload | Input.Session _ -> ignore
    | _ -> reset
  in
  do_cleanup aux c reset

let _ =
  begin try load_session ()
  with IO.File_error (s1,n,s2) ->
    Format.eprintf
      ("@[Couldn't %s@ %S:@ %s.@]@.")
      s1 n s2 ;
    exit 5
  end ;
  List.iter
    (fun s -> input_defs (Lexing.from_string s) "") !definitions ;
  List.iter
    (fun s -> input_queries (Lexing.from_string s)) !queries ;
  match !exit_status with
    | None ->
        if !interactive then begin
          Format.printf "%s@." welcome_msg ;
          input_queries ~interactive:true
            (Lexing.from_channel stdin)
        end
    | Some error_code -> exit error_code
