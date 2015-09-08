(****************************************************************************)
(* Bedwyr -- prover input                                                   *)
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

let parse ~k ~parser ~lexer lexbuf =
  try
    try Some (Some (parser lexer lexbuf)) with e ->
      begin match e with
        (* Lexer *)
        | Lexer.EOF_error s ->
            Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
              "Lexing error:@ %s@ at end of input."
              s
        | Lexer.Illegal_byte_sequence c ->
            Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
              "Illegal sequence starting with byte %C in input."
              c
        | Lexer.Illegal_string_comment p ->
            Output.eprintf ~p
              "Unmatched comment delimiter in string."
        | Lexer.Illegal_token (n1,n2) ->
            Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
              "%S is illegal in a token, did you mean %S?"
              (Lexing.lexeme lexbuf)
              (String.concat " " [n1;n2])
        | Lexer.Unknown_command n ->
            Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
              "Unknown meta-command %S, use \"#help.\" for a short list."
              ("#" ^ n)

        (* Parser *)
        | Parsing.Parse_error ->
            Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
              "Unexpected input."
        | Preterm.Parse_error (p,s1,s2) ->
            Output.eprintf ~p
              "%s while parsing@ %s."
              s1 s2

      | e -> raise e
    end ;
    Some (k ())
  with Sys_error e ->
    Output.eprintf "Couldn't parse %S:@ %s."
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_fname) e ;
    None

let definition_mode ~k lexbuf =
  try parse ~k ~parser:Parser.definition_mode ~lexer:Lexer.token lexbuf
  with Preterm.Empty_command -> None

let toplevel ~k lexbuf =
  try parse ~k ~parser:Parser.toplevel ~lexer:Lexer.token lexbuf
  with Preterm.Empty_term -> None

let term_mode ~k lexbuf =
  try parse ~k ~parser:Parser.term_mode ~lexer:Lexer.token lexbuf
  with Preterm.Empty_term -> None

let apply_on_string f ?(fname="") str =
  let lexbuf = Lexing.from_string str in
  let lexbuf = Lexing.({
    lexbuf with lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = fname }
  }) in
  f lexbuf

let apply_on_channel f ?(fname="") channel =
  let lexbuf = Lexing.from_channel channel in
  let lexbuf = Lexing.({
    lexbuf with lex_curr_p =
      { lexbuf.lex_curr_p with pos_fname = fname } ;
  }) in
  f lexbuf
