(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2012 Baelde, Tiu, Ziegler, Gacek, Heath               *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

exception Invalid_command
exception Assertion_failed

let welcome_msg =
  Printf.sprintf
    "%s %s%s welcomes you.

This software is under GNU Public License.
Copyright (C) 2005-2012 Slimmer project.

For a little help, type \"#help.\"

"
    Config.package_name
    Config.package_version
    (if Config.build="v"^Config.package_version || Config.build="" then ""
     else " (revision " ^ Config.build ^ ")")

(* TODO split into usage_msg and info_msg,
 * add support, both external (Abella version supported, etc)
 * and internal (oUnit version, ndcore version, etc). *)
let usage_msg =
  Printf.sprintf
    "%s prover version %s (%s).
Built with OCaml %s on the %s.
This software is under GNU Public License.
Copyright (c) 2005-2012 Slimmer project.

Usage: bedwyr [filename | option]*
"
    Config.package_name
    Config.package_version
    (if Config.build="" then "unknown revision"
     else "revision " ^ Config.build ^ "")
    Config.ocaml_version
    Config.build_date

let help_msg =
  "Useful commands in query mode:
#help.                               Display this message.
#exit.                               Exit.
#debug [flag].                       Turn debugging [on]/off (initially off).
#time [flag].                        Turn timing [on]/off (initially off).
#session \"file_1\" ... \"file_N\".      Load these files as the current \
session.
#reload.                             Reload the current session.
#reset.                              Clears the current session.
#show_table [pred].                  Displays the predicate's table.
#save_table [pred] [file].           Save the predicate's table in a file.
#equivariant [flag].                 Turn equivariant tabling [on]/off (initially on).
Or type in a formula to ask for its verification.
For more information (including commands relevant in definition mode),
see the user guide.

"

let interactive = ref true
let test        = ref false
let session     = ref []
let queries     = ref []
let inclfiles   = ref []
let good_input  = ref true
let strict_file = ref false

let _ =
  Arg.parse
    (Arg.align
       [ "-I", Arg.Clear interactive,
           " Do not enter interactive mode" ;
         "-t", Arg.Set test,
           " Run tests in definition files" ;
         "-e", Arg.String (fun s -> queries := s::!queries),
           "<s> Execute query" ;
         "--freezing", Arg.Set_int Prover.freezing_point,
           "<n> Enable backward chaining and set its limit" ;
         "--saturation", Arg.Set_int Prover.saturation_pressure,
           "<n> Enable forward chaining and set its limit"
       ])
    (fun f -> session := f::!session)
    usage_msg ;
  session := List.rev (!session)

let position_range (start,curr) =
  let position (start,curr) =
    let l1 = start.Lexing.pos_lnum in
    let l2 = curr.Lexing.pos_lnum in
    let c1 = start.Lexing.pos_cnum - start.Lexing.pos_bol + 1 in
    let c2 = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if l1 < l2 then
      Printf.sprintf "line %d, byte %d - line %d, byte %d" l1 c1 l2 c2
    else if c1 < c2  then
      Printf.sprintf "line %d, byte %d-%d" l2 c1 c2
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

let rec process ?(interactive=false) parse lexbuf =
  let basic_error k =
    if interactive then begin
      Lexing.flush_input lexbuf ;
      lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
            Lexing.pos_bol = 0 ;
            Lexing.pos_lnum = 1 }
    end else k ()
  in
  let bedwyr_error _ = basic_error (fun () -> exit 1) in
  let input_error _ =
    basic_error (fun () ->
                   if !strict_file then exit 2
                   else good_input := false)

  in
  let lexer_error _ =
    input_error () ;
    Parser.input_error Lexer.invalid lexbuf
  in
  let solver_error _ = basic_error (fun () -> exit 3) in
  let eprintf ?(k=input_error) ?(p=position_lex lexbuf) f =
    Format.kfprintf
      k
      (if interactive then Format.std_formatter else Format.err_formatter)
      ("@[<hov>%s@;<1 1>@[" ^^ f ^^ "@]@]@.")
      (position_range p)
  in
  try while true do
    let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
    in
    if interactive then Format.printf "?= %!" ;
    begin try match (parse Lexer.token lexbuf) with
      | Input.KKind (l, k) ->
          List.iter (fun s -> System.declare_type s k) l
      | Input.TType (l, t) ->
          List.iter (fun s -> System.declare_const s t) l
      | Input.Def (decls,defs) ->
          let new_predicates = System.declare_preds decls in
          System.add_clauses new_predicates defs ;
          List.iter
            (fun (v,ty) -> Input.Typing.check_ground (Term.get_var_name v) ty)
            new_predicates
      | Input.Theorem thm -> System.add_theorem thm
      | Input.Query t ->
          do_cleanup
            (fun pre_query ->
               let query = System.translate_query pre_query in
               if !good_input then Prover.toplevel_prove query)
            t
            reset
      | Input.Command c -> command c reset
    with
      (* I/O - Lexer *)
      | End_of_file -> raise End_of_file
      | Input.Illegal_string c ->
          eprintf ~k:lexer_error
            "Illegal string starting with %C in input."
            c
      | Input.Illegal_name (n1,n2) ->
          eprintf ~k:lexer_error
            "%S is an illegal token, did you mean %S?"
            (Lexing.lexeme lexbuf)
            (String.concat " " [n1;n2])
      | Input.Unknown_command n ->
          eprintf ~k:lexer_error
            "Unknown command %S, use \"#help.\" for a short list."
            n

      (* I/O - Parser *)
      | Parsing.Parse_error ->
          eprintf
            "Syntax error."
      | Input.Syntax_error (p,s) ->
          eprintf ~p
            "Unexpected input while parsing@ %s."
            s

      (* Declarations *)
      | System.Invalid_type_declaration (n,p,ki,s) ->
          eprintf ~p
            "Cannot declare type %s of kind %a:@ %s."
            n
            Input.Typing.pp_kind ki
            s
      | System.Missing_type (n,_) ->
          eprintf
            "Undeclared type %s."
            n
      | System.Invalid_const_declaration (n,p,ty,s) ->
          eprintf ~p
            "Cannot declare constant %s of type %a:@ %s."
            n
            Input.Typing.pp_type ty
            s
      | System.Invalid_flavour (n,p,gf,f) ->
          eprintf ~p
            "Cannot declare predicate %s of flavour %s:@ %s was used in the same definition block."
            n
            (System.string_of_flavour f)
            (System.string_of_flavour gf)
      | System.Invalid_pred_declaration (n,p,ty,s) ->
          eprintf ~p
            "Cannot declare predicate %s of type %a:@ %s."
            n
            Input.Typing.pp_type ty
            s

      (* Definitions and theorems *)
      | System.Missing_declaration (n,p) ->
          eprintf ?p
            "Undeclared object %s."
            n
      | System.Inconsistent_definition (n,p,s) ->
          eprintf ~p
            "Inconsistent extension of definition for %s:@ %s."
            n
            s
      | System.Inconsistent_theorem (n,p,s) ->
          eprintf ~p
            "Inconsistent theorem specification for %s:@ %s."
            n
            s

      (* Kind/type checking *)
      | Input.Typing.Type_kinding_error (_,ki1,ki2) ->
          eprintf
            "Kinding error: this type has kind %a but is used as %a."
            Input.Typing.pp_kind ki2
            Input.Typing.pp_kind ki1
      | Input.Term_typing_error (p,ty1,ty2,unifier) ->
          eprintf ~p
            "Typing error: this term has type %a but is used as %a."
            (Input.Typing.pp_type_norm ~unifier) ty2
            (Input.Typing.pp_type_norm ~unifier) ty1
      | Input.Var_typing_error (n,p,ty) ->
          begin match n with
            | Some n ->
                eprintf ~p
                  "Typing error: cannot give free variable %s the type %a.@." n
                  Input.Typing.pp_type ty
            | None ->
                eprintf ~p
                  "Typing error: cannot quantify over type %a.@."
                  Input.Typing.pp_type ty
          end
      | Input.Typing.Hollow_type n ->
          eprintf
            "Typing error: type incompletely inferred for %s."
            n

      (* Using predicates *)
      | System.Missing_definition (n,p) ->
          eprintf ?p
            "Undefined predicate (%s was declared as a constant)."
            n
      | System.Missing_table (n,p) ->
          eprintf ?p
            "No table (%s is neither inductive nor coinductive)."
            n

      (* Solving *)
      | Assertion_failed ->
          eprintf ~k:solver_error
            "Assertion failed."
      | Prover.Level_inconsistency ->
          eprintf ~k:solver_error
            "This formula cannot be handled by the left prover!"
      | Unify.NotLLambda t ->
          eprintf ~k:solver_error
            "Not LLambda unification encountered:@ %a."
            Pprint.pp_term t
      | Unify.Left_logic ->
          eprintf ~k:solver_error
            "Logic variable on the left."
      | Unify.Formula_as_Term t ->
          eprintf ~k:solver_error
            "Formula encounterd by the unifier:@ %a."
            Pprint.pp_term t

      (* Misc Bedwyr errors *)
      | System.Interrupt ->
          eprintf ~k:bedwyr_error
            "User interruption."
      | Prover.Abort_search ->
          eprintf ~k:bedwyr_error
            "Proof search aborted!"
      | Invalid_command ->
          eprintf ~k:bedwyr_error
            "Invalid command, or wrong arguments."

      (* Unhandled errors *)
      | Failure s ->
          eprintf ~k:bedwyr_error
            "Error:@ %s"
            s
      | e ->
          eprintf ~k:bedwyr_error
            "Unknown OCaml error:@ %s"
            (Printexc.to_string e)
    end ;
    if interactive then flush stdout
  done with
    | End_of_file -> ()

and input_from_file file =
  let cwd = Sys.getcwd () in
  let lexbuf = Lexing.from_channel (open_in file) in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = file } ;
    input_defs lexbuf ;
    Sys.chdir cwd
and input_defs lexbuf =
  process Parser.input_def lexbuf
and input_queries ?(interactive=false) lexbuf =
  process ~interactive Parser.input_query lexbuf

and load_session () =
  System.reset_decls () ;
  Input.Typing.clear () ;
  inclfiles := [] ;
  List.iter include_file !session

and toggle_flag flag value =
  flag :=
    begin match value with
      | None | Some "on" | Some "true" -> true
      | Some "off" | Some "false" -> false
      | _ -> raise Invalid_command
    end

and include_file fname =
  if not (List.mem fname !inclfiles) then begin
    input_from_file fname;
    inclfiles := fname :: !inclfiles
  end

and command c reset =
  let aux = function
    | Input.Exit -> System.close_all_files () ;
                    if !good_input then exit 0 else exit 2
    | Input.Help -> Format.printf "%s" help_msg

    (* Session management *)
    | Input.Include l -> List.iter include_file l
    | Input.Reset -> session := [] ; load_session ()
    | Input.Reload -> load_session ()
    | Input.Session l -> session := l ; load_session ()

    (* Turn debugging on/off. *)
    | Input.Debug value -> toggle_flag System.debug value

    (* Turn timing on/off. *)
    | Input.Time value -> toggle_flag System.time value

    (* Tabling-related commands *)
    | Input.Equivariant value -> toggle_flag Index.eqvt_index value
    | Input.Freezing temp -> Prover.freezing_point := temp
    | Input.Saturation pressure -> Prover.saturation_pressure := pressure
    | Input.Env -> System.print_env ()
    | Input.Type_of pre_term -> System.print_type_of pre_term
    | Input.Show_table (p,name) ->
        System.show_table (p,Term.atom ~tag:Term.Constant name)
    | Input.Clear_tables -> System.clear_tables ()
    | Input.Clear_table (p,name) ->
        System.clear_table (p,Term.atom ~tag:Term.Constant name)
    (* save the content of a table to a file. An exception is thrown if
     * file already exists. *)
    | Input.Save_table (p,name,file) ->
        System.save_table (p,Term.atom ~tag:Term.Constant name) file

    (* Testing commands *)
    | Input.Assert pre_query ->
        if !test then
          let query = System.translate_query pre_query in
          if !good_input then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
              Pprint.pp_term query ;
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:(fun _ _ -> ())
              ~failure:(fun () -> raise Assertion_failed)
          end
    | Input.Assert_not pre_query ->
        if !test then
          let query = System.translate_query pre_query in
          if !good_input then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
              Pprint.pp_term query ;
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
          end
    | Input.Assert_raise pre_query ->
        if !test then
          let query = System.translate_query pre_query in
          if !good_input then begin
            Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@."
              Pprint.pp_term query ;
            if
              try
                Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
                  ~success:(fun _ _ -> true) ~failure:(fun _ -> true)
              with _ -> false
            then raise Assertion_failed
          end
  in
  let reset = match c with
    | Input.Include _ | Input.Reset | Input.Reload | Input.Session _ -> ignore
    | _ -> reset
  in
  do_cleanup aux c reset

let _ =
  load_session () ;
  List.iter
    (fun s -> input_queries (Lexing.from_string s))
    (List.rev !queries) ;
  if not !good_input then exit 2
  else if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end
