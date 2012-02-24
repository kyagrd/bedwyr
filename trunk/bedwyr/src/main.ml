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

For a little help, type #help.

"
    Config.package_name
    Config.package_version
    (if Config.build="" then ""
     else " (revision " ^ Config.build ^ ")")
    

let usage_msg =
  Config.package_name ^ " prover.
This software is under GNU Public License.
Copyright (c) 2005-2012 Slimmer project.

Usage: bedwyr [filename | option]*
"

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

let _ =
  Arg.parse [
      "-I", Arg.Clear interactive,
      "Do not enter interactive mode." ;

      "-t", Arg.Set test, "Run tests in definition files." ;

      "-e", Arg.String (fun s -> queries := s::!queries),
      "Execute query."
    ]
    (fun f -> session := f::!session)
    usage_msg

let position (start,curr) =
  let line1 = start.Lexing.pos_lnum in
  let line2 = curr.Lexing.pos_lnum in
  let char1 = start.Lexing.pos_cnum - start.Lexing.pos_bol + 1 in
  let char2 = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in

  if line1 < line2 then
    Printf.sprintf "line %d, character %d - line %d, character %d" line1 char1 line2 char2
  else if char1 < char2  then
    Printf.sprintf "line %d, characters %d-%d" line2 char1 char2
  else
    Printf.sprintf "line %d, character %d" line2 char2

let position_range (start,curr) =
  let name = curr.Lexing.pos_fname in
  if name = "" then
    (* lexbuf line information is rarely accurate at the toplevel,
     * but character information is *)
    Printf.sprintf "At %s:\n" (position (start,curr))
  else
    Printf.sprintf "In file \"%s\", %s:\n" name (position (start,curr))

let position_lex lexbuf =
  let start = lexbuf.Lexing.lex_start_p in
  let curr = lexbuf.Lexing.lex_curr_p in
  position_range (start,curr)

let do_cleanup f x clean =
  try f x ; clean () with e -> clean () ; raise e

let rec process ?(interactive=false) parse lexbuf =
  let interactive_or_exit () =
    if interactive
    then begin
      Lexing.flush_input lexbuf ;
      lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
            Lexing.pos_bol = 0 ;
            Lexing.pos_lnum = 1 }
    end else exit 1
  in
  try while true do
    let reset =
      let s = Term.save_state () in
      let ns = Term.save_namespace () in
        fun () -> Term.restore_state s ; Term.restore_namespace ns
    in
    if interactive then Format.printf "?= %!" ;
    begin try match (parse Lexer.token lexbuf) with
      | System.KKind (l, k) ->
          List.iter
            (fun s -> System.declare_type s k)
            l
      | System.TType (l, t) ->
          List.iter
            (fun s -> System.declare_const s t)
            l
      | System.Def (decls,defs) ->
          let new_predicates,_ = List.fold_left
                                   System.create_def
                                   ([],System.Normal)
                                   decls
          in
          List.iter (System.add_clause (List.map fst new_predicates)) defs ;
          List.iter
            (fun (v,ty) ->
               if not (Typing.check_ground ty)
               then raise (Typing.Hollow_type v))
            new_predicates
      | System.Query t ->
          do_cleanup
            (fun pre_query ->
               let query = System.translate_query pre_query in
               Prover.toplevel_prove query)
            t
            reset
      | System.Command c -> command c reset
    with
      (* I/O *)
      | End_of_file -> raise End_of_file
      | Lexer.Illegal_string c ->
          Format.printf "%sIllegal string starting with '%s' in input.@."
            (position_lex lexbuf)
            (Char.escaped c) ;
          interactive_or_exit ()
      | Lexer.Illegal_name (n1,n2) ->
          Format.printf "%s%s is an illegal token, did you mean \"%s %s\"?@."
            (position_lex lexbuf)
            (Lexing.lexeme lexbuf)
            n1 n2 ;
          interactive_or_exit ()
      | Lexer.Unknown_command n ->
          Format.printf "%sUnknown command %s, use #help for a short list.@."
            (position_lex lexbuf)
            n ;
          interactive_or_exit ()
      | Parsing.Parse_error ->
          Format.printf "%sSyntax error.@."
            (position_lex lexbuf) ;
          interactive_or_exit ()

      (* declarations *)
      | System.Missing_type (n,_) ->
          Format.printf
            "%sUndeclared type %s.@."
            (position_lex lexbuf)
            n ;
          interactive_or_exit ()
      | System.Invalid_type_declaration (n,p,ki,s) ->
          Format.printf
            "%sCannot declare type %s of kind %a: %s.@."
            (position_range p)
            n
            Pprint.pp_kind ki
            s ;
          exit 1
      | System.Invalid_const_declaration (n,p,ty,s) ->
          Format.printf
            "%sCannot declare constant %s of type %a: %s.@."
            (position_range p)
            n
            Pprint.pp_type ty
            s ;
          exit 1
      | System.Invalid_flavour (n,p,gf,f) ->
          Format.printf
            "%sCannot declare predicate %s of flavour %s: %s was used in the same definition block.@."
            (position_range p)
            n
            gf
            f ;
          exit 1
      | System.Invalid_pred_declaration (n,p,ty,s) ->
          Format.printf
            "%sCannot declare predicate %s of type %a: %s.@."
            (position_range p)
            n
            Pprint.pp_type ty
            s ;
          exit 1

      (* definitions *)
      | System.Missing_declaration (n,p) ->
          Format.printf
            "%sUndeclared object %s.@."
            (match p with
               | Some p -> position_range p
               | None -> position_lex lexbuf)
            n ;
          interactive_or_exit ()
      | System.Missing_definition (n,p) ->
          Format.printf
            "%sUndefined predicate (%s was declared as a constant).@."
            (match p with
               | Some p -> position_range p
               | None -> position_lex lexbuf)
            n ;
          interactive_or_exit ()
      | System.Missing_table (n,p) ->
          Format.printf
            "%sNo table (%s is neither inductive nor coinductive).@."
            (match p with
               | Some p -> position_range p
               | None -> position_lex lexbuf)
            n ;
          interactive_or_exit ()
      | Typing.Type_kinding_error (_,ki1,ki2) ->
          Format.printf
            "%sKinding error: this type has kind %a but is used as %a.@."
            (position_lex lexbuf)
            Pprint.pp_kind ki2
            Pprint.pp_kind ki1 ;
          interactive_or_exit ()
      | Typing.Term_typing_error (p,ty1,ty2,unifier) ->
          Format.printf
            "%sTyping error: this expression has type %a but is used as %a.@."
            (position_range p)
            (Pprint.pp_type_norm (Some unifier)) ty2
            (Pprint.pp_type_norm (Some unifier)) ty1 ;
          interactive_or_exit ()
      | Typing.Var_typing_error (n,p,ty) ->
          Format.printf
            "%sTyping error: cannot "
            (position_range p) ;
          (match n with
             | Some n -> Format.printf
                           "give free variable %s the type %a.@." n
             | None -> Format.printf
                         "quantify over type %a.@.")
            Pprint.pp_type ty ;
          interactive_or_exit ()
      | Typing.Hollow_type v ->
          Format.printf
            "%sTyping error: type incompletely inferred for %s."
            (position_lex lexbuf)
            (Term.get_var_name v) ;
          interactive_or_exit ()
      | System.Inconsistent_definition (n,p,s) ->
          Format.printf
            "%sInconsistent extension of definition for %s: %s.@."
            (position_range p)
            n
            s ;
          exit 1

      (* queries *)
      | Assertion_failed ->
          Format.printf "Assertion failed.@." ;
          interactive_or_exit ()

      (* unhandled non-interactive errors *)
      | e when not interactive -> raise e

      (* interactive errors *)
      | System.Interrupt ->
          Format.printf "User interruption.@." ;
          interactive_or_exit ()
      | Prover.Level_inconsistency ->
          Format.printf "This formula cannot be handled by the left prover!@." ;
          interactive_or_exit ()
      | Prover.Abort_search ->
          Format.printf "Proof search aborted!@." ;
          interactive_or_exit ()
      | Unify.NotLLambda t ->
          Format.printf "Not LLambda unification encountered: %a@."
            Pprint.pp_term t ;
          interactive_or_exit ()
      | Unify.Formula_as_Term t ->
          Format.printf "Formula encounterd by the unifier: %a@."
            Pprint.pp_term t ;
          interactive_or_exit ()
      | Invalid_command ->
          Format.printf "Invalid command, or wrong arguments.@." ;
          interactive_or_exit ()
      | Failure s ->
          Format.printf "%sError: %s@."
            (position_lex lexbuf)
            s ;
          interactive_or_exit ()
      | e ->
          Format.printf "%sUnknown error: %s@."
            (position_lex lexbuf)
            (Printexc.to_string e) ;
          interactive_or_exit ()
    end ;
    if interactive then flush stdout
  done with
    | End_of_file -> ()
    | Failure s ->
        Format.printf "%sError: %s@."
          (position_lex lexbuf)
          s ;
        exit 1
    | e ->
        Format.printf "%sUnknown error: %s@."
          (position_lex lexbuf)
          (Printexc.to_string e) ;
        exit 1

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
  inclfiles := [] ;
  List.iter input_from_file !session

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
    | System.Exit -> System.close_all_files (); exit 0
    | System.Help -> Format.printf "%s" help_msg

    (* Session management *)
    | System.Include l -> List.iter include_file l
    | System.Reset -> inclfiles := [] ; session := [] ; load_session ()
    | System.Reload -> load_session ()
    | System.Session l ->
        session := l ;
        load_session ()

    (* Turn debugging on/off. *)
    | System.Debug value -> toggle_flag System.debug value

    (* Turn timing on/off. *)
    | System.Time value -> toggle_flag System.time value

    (* Tabling-related commands *)
    | System.Equivariant value -> toggle_flag Index.eqvt_tbl value
    | System.Env -> System.print_env ()
    | System.Type_of pre_term -> System.print_type_of pre_term
    | System.Show_table (p,name) -> System.show_table (p,Term.atom ~tag:Term.Constant name)
    | System.Clear_tables -> System.clear_tables ()
    | System.Clear_table (p,name) -> System.clear_table (p,Term.atom ~tag:Term.Constant name)
    (* save the content of a table to a file. An exception is thrown if
     * file already exists. *)
    | System.Save_table (p,name,file) -> System.save_table (p,Term.atom ~tag:Term.Constant name) file

    (* Testing commands *)
    | System.Assert pre_query ->
        if !test then begin
          let query = System.translate_query pre_query in
          Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
            Pprint.pp_term query ;
          Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
            ~success:(fun _ _ -> ()) ~failure:(fun () -> raise Assertion_failed)
        end
    | System.Assert_not pre_query ->
        if !test then begin
          let query = System.translate_query pre_query in
          Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
            Pprint.pp_term query ;
          Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
            ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
        end
    | System.Assert_raise pre_query ->
        if !test then begin
          let query = System.translate_query pre_query in
          Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@."
            Pprint.pp_term query ;
          if
            try
              Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
                ~success:(fun _ _ -> ()) ~failure:ignore ;
              true
            with _ -> false
          then raise Assertion_failed
        end
  in
  let reset = match c with
    | System.Include _ | System.Reset | System.Reload | System.Session _ -> ignore
    | _ -> reset
  in
  do_cleanup aux c reset

let _ =
  load_session () ;
  List.iter (fun s -> input_queries (Lexing.from_string s)) (List.rev !queries) ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end
