(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
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

let rec process ?(interactive=false) parse lexbuf =
  try while true do try
    if interactive then Format.printf "?= %!" ;
    begin match parse Lexer.token lexbuf with
      | System.Def (k,h,a,b) -> System.add_clause k h a b
      | System.Query a       -> Prover.toplevel_prove a
      | System.Command (c,a) -> command lexbuf (c,a)
    end ;
    if interactive then flush stdout
  with
    | e when not interactive -> raise e
    | Failure "lexing: empty token" ->
        Format.printf "Lexing error: Watch your fingers.\n%!" ;
        Lexing.flush_input lexbuf
    | Parsing.Parse_error ->
        Format.printf "Syntax error!\n%!"
    | System.Undefined s ->
        Format.printf "No definition found for %S !\n%!" s
    | System.Inconsistent_definition s ->
        Format.printf "Inconsistent extension of definition %S !\n" s
    | System.Arity_mismatch (s,a) ->
        Format.printf "Definition %S doesn't have arity %d !\n%!" s a
    | System.Interrupt ->
        Format.printf "User interruption.\n%!"
    | Prover.Level_inconsistency ->
        Format.printf "Search fell outside Level-0/1 fragment !\n%!"
    | Unify.NotLLambda t ->
        Format.printf "Not LLambda unification encountered: %a\n%!"
          Pprint.pp_term t
    | Invalid_command ->
        Format.printf "Invalid command, or wrong arity!\n%!"
    | e when e <> Failure "eof" ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()

and input_defs lexbuf = process Parser.input_def lexbuf
and input_queries ?(interactive=false) lexbuf =
  process ~interactive Parser.input_query lexbuf

and command lexbuf = function
  | "debug",[] -> System.debug := true
  | "exit",[] -> exit 0
  | "help",[] ->
        Format.printf
"Available commands:
#help.
#exit.
#debug [flag].
#include \"some/filename.def\".
In query mode, just type a term to ask for its verification.

"
  (* Include a file *)
  | "include",[f] ->
      begin match Term.observe f with
        | Term.Var {Term.name=f} -> input_defs (Lexing.from_channel (open_in f))
        | _ -> raise Invalid_command
      end

  (* Turn debugging on/off. *)
  | "debug",[d] ->
      System.debug :=
        begin match Term.observe d with
          | Term.Var {Term.name="on"}
          | Term.Var {Term.name="true"}  -> true
          | Term.Var {Term.name="off"}
          | Term.Var {Term.name="false"} -> false
          | _ -> raise Invalid_command
        end

  (* Turn timing on/off. *)
  | "time",[d] ->
      System.time :=
        begin match Term.observe d with
          | Term.Var {Term.name="on"}
          | Term.Var {Term.name="true"}  -> true
          | Term.Var {Term.name="off"}
          | Term.Var {Term.name="false"} -> false
          | _ -> raise Invalid_command
        end

  | "show_table",[p] ->
      begin match Term.observe p with
        | Term.Var {Term.name=name} -> System.show_table name
        | _ -> raise Invalid_command
      end

  | _ -> raise Invalid_command

let interactive = ref true

let _ =
  Arg.parse [
      "-I", Arg.Clear interactive,
      "Do not enter interactive mode." ;

      "-e", Arg.String (fun s -> input_queries (Lexing.from_string s)),
      "Execute query."
    ]
    (fun file -> input_defs (Lexing.from_channel (open_in file)))
    "Bedwyr prover.
This software is under GNU Public License.
Copyright (c) 2005-2006 Slimmer project.

Usage: bedwyr [filename | option]*
"

let _ =
  if !interactive then begin
    Format.printf
"Bedwyr welcomes you.

This software is under GNU Public License.
Copyright (c) 2005-2006 Slimmer project.

For a little help, type #help.
\n%!" ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end
