(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2006 David Baelde, Alwen Tiu, Axelle Ziegler          *)
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
  "Bedwyr " ^ Config.version ^ " (revision " ^ Config.build ^ ") welcomes you.

This software is under GNU Public License.
Copyright (c) 2005-2011 Slimmer project.

For a little help, type #help.
\n"

let usage_msg =
  "Bedwyr prover.
This software is under GNU Public License.
Copyright (c) 2005-2011 Slimmer project.

Usage: bedwyr [filename | option]*
"

let help_msg =
  "Useful commands in query mode:
#help.                               Display this message.
#exit.                               Exit.
#debug [flag].                       Turn debugging on/off (default off).
#time [flag].                        Turn timing on/off (default off).
#session \"file_1\" ... \"file_N\".      Load these files as the current \
session.
#reload.                             Reload the current session.
#reset.                              Clears the current session.
#show_table [pred].                  Displays the predicate's table.
#save_table [pred] [file].           Save the predicate's table in a file.
#equivariant [flag].                 Turn equivariant tabling on/off (flag=on/off).
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
  let file = start.Lexing.pos_fname in
  let line1 = start.Lexing.pos_lnum in
  let line2 = curr.Lexing.pos_lnum in
  let char1 = start.Lexing.pos_cnum - start.Lexing.pos_bol + 1 in
  let char2 = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  if line1 < line2 then
    Format.sprintf "file \"%s\", line %d, character %d - line %d, character %d" file line1 char1 line2 char2
  else if char1 < char2  then
    Format.sprintf "file \"%s\", line %d, characters %d-%d" file line2 char1 char2
  else
    Format.sprintf "file \"%s\", line %d, character %d" file line2 char2

let position_range (start,curr) =
  if curr.Lexing.pos_fname = "" then
    "" (* lexbuf information is rarely accurate at the toplevel *)
  else
    Format.sprintf "In %s:\n" (position (start,curr))

let position_lex lexbuf =
  let start = lexbuf.Lexing.lex_start_p in
  let curr = lexbuf.Lexing.lex_curr_p in
  position_range (start,curr)

let do_cleanup f x clean =
  try f x ; clean () with e -> clean () ; raise e

let rec process ?(interactive=false) parse lexbuf =
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
          let new_predicates = List.map System.create_def decls in
          List.iter (System.add_clause new_predicates) defs
      | System.Query t ->
          do_cleanup
            (fun query' ->
               let query = System.type_check_query query' in
               Prover.toplevel_prove query)
            t
            reset
      | System.Command c -> command c reset
    with
      (* I/O *)
      | End_of_file -> raise End_of_file
      | Lexer.Illegal_string ->
          Format.printf "%sIllegal string \"%s\" in input.\n%!"
            (position_lex lexbuf)
            (String.escaped (Lexing.lexeme lexbuf)) ;
          if interactive then Lexing.flush_input lexbuf else exit 1
      | Parsing.Parse_error ->
          Format.printf "%sSyntax error.\n%!"
            (position_lex lexbuf) ;
          if interactive then Lexing.flush_input lexbuf else exit 1

      (* declarations *)
      | System.Invalid_type_declaration (n,p,k,s) ->
          Format.printf
            "%sCannot declare type %s of kind %a: %s.\n%!"
            (position_range p)
            n
            Pprint.pp_kind k
            s ;
          exit 1
      | System.Invalid_const_declaration (n,p,t,s) ->
          Format.printf
            "%sCannot declare constant %s of type %a: %s.\n%!"
            (position_range p)
            n
            (Pprint.pp_type None) t
            s ;
          exit 1
      | System.Invalid_pred_declaration (n,p,t,s) ->
          Format.printf
            "%sCannot declare predicate %s of type %a: %s.\n%!"
            (position_range p)
            n
            (Pprint.pp_type None) t
            s ;
          exit 1

      (* definitions *)
      | System.Missing_declaration (n) -> (* TODO add a position *)
          Format.printf
            "%sUndeclared constant or predicate %s.\n%!"
            (position_lex lexbuf)
            n ;
          if interactive then Lexing.flush_input lexbuf else exit 1
      | Typing.Term_typing_error (ty1,ty2,unifier,term) -> (* TODO add a position and s/the expression %s/this expression/ *)
          Format.printf
            "%sTyping error: the expression %s has type %s but is used as %s.%!"
            (position_lex lexbuf)
            (Pprint.term_to_string term)
            (Pprint.type_to_string (Some unifier) ty2)
            (Pprint.type_to_string (Some unifier) ty1) ;
          if interactive then Lexing.flush_input lexbuf else exit 1
      | System.Inconsistent_definition (n,p,s) ->
          Format.printf
            "%sInconsistent extension of definition for %s: %s.\n%!"
            (position_range p)
            n
            s ;
          exit 1

      (* queries *)
      | System.Arity_mismatch (t,a) ->
          Format.printf "Definition %a doesn't have arity %d !\n%!"
            Pprint.pp_term t a ;
          if interactive then Lexing.flush_input lexbuf else exit 1
      | Assertion_failed ->
          Format.printf "Assertion failed.\n%!" ;
          if interactive then Lexing.flush_input lexbuf else exit 1

      (* unhandled non-interactive errors *)
      | Failure s when not interactive ->
          Format.printf "%sError: %s\n"
            (position_lex lexbuf)
            s ;
          exit 1
      | e when not interactive ->
          Format.printf "%sUnknown error: %s\n"
            (position_lex lexbuf)
            (Printexc.to_string e) ;
          exit 1

      (* interactive errors *)
      | System.Interrupt ->
          Format.printf "User interruption.\n%!" ;
          Lexing.flush_input lexbuf
      | Prover.Level_inconsistency ->
          Format.printf "This formula cannot be handled by the left prover!\n%!" ;
          Lexing.flush_input lexbuf
      | Prover.Abort_search ->
          Format.printf "Proof search aborted!\n" ;
          Lexing.flush_input lexbuf
      | Unify.NotLLambda t ->
          Format.printf "Not LLambda unification encountered: %a\n%!"
            Pprint.pp_term t ;
          Lexing.flush_input lexbuf
      | Invalid_command ->
          Format.printf "Invalid command, or wrong arguments.\n%!" ;
          Lexing.flush_input lexbuf
      | Failure s ->
          Format.printf "%sError: %s\n"
            (position_lex lexbuf)
            s ;
          Lexing.flush_input lexbuf
      | e ->
          Format.printf "%sUnknown error: %s\n"
            (position_lex lexbuf)
            (Printexc.to_string e) ;
          Lexing.flush_input lexbuf
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
and input_defs lexbuf = process Parser.input_def lexbuf
and input_queries ?(interactive=false) lexbuf =
  process ~interactive Parser.input_query lexbuf


and load_session () =
  System.reset_defs () ;
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
    | System.Show_table name -> System.show_table (Term.atom name)
    | System.Clear_tables ->
        Hashtbl.iter
          (fun k v -> match v with
             | (_,_,Some t,_) -> Table.reset t
             | _ -> ())
          System.defs
    | System.Clear_table name ->
        begin match
          try
            let _,_,x,_ = Hashtbl.find System.defs (Term.get_var (Term.atom name)) in x
          with _ -> None
        with
          | Some t ->
              Table.reset t
          | None ->
              Format.printf "Table not found.\n"
        end
    (* save the content of a table to a file. An exception is thrown if *)
    (* file already exists. *)
    | System.Save_table (name,file) -> System.save_table (Term.atom name) file

    (* Testing commands *)
    | System.Assert query' ->
        if !test then begin
          let query = System.type_check_query query' in
          Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@\n%!"
            Pprint.pp_term query ;
          Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
            ~success:(fun _ _ -> ()) ~failure:(fun () -> raise Assertion_failed)
        end
    | System.Assert_not query' ->
        if !test then begin
          let query = System.type_check_query query' in
          Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@\n%!"
            Pprint.pp_term query ;
          Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
            ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
        end
    | System.Assert_raise query' ->
        if !test then begin
          let query = System.type_check_query query' in
          Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@\n%!"
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
    | System.Include _ | System.Reset | System.Reload | System.Session _ -> (fun () -> ())
    | _ -> reset
  in
  do_cleanup aux c reset

let _ =
  load_session () ;
  List.iter (fun s -> input_queries (Lexing.from_string s)) !queries ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end
