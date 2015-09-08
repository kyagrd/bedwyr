(****************************************************************************)
(* Bedwyr -- toplevel read                                                  *)
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
  let f lexbuf =
    try Some (parser lexer lexbuf) with e ->
      begin match e with
        (* Lexer *)
        | Parsetree.Lexer.EOF_error s ->
            IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ())
              "Lexing error:@ %s@ at end of input."
              s
        | Parsetree.Lexer.Illegal_byte_sequence c ->
            IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ())
              "Illegal sequence starting with byte %C in input."
              c
        | Parsetree.Lexer.Illegal_string_comment p ->
            IO.Output.eprintf ~p
              "Unmatched comment delimiter in string."
        | Parsetree.Lexer.Illegal_token (n1,n2) ->
            IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ())
              "%S is illegal in a token, did you mean %S?"
              (Lexing.lexeme lexbuf)
              (String.concat " " [n1;n2])
        | Parsetree.Lexer.Unknown_command n ->
            IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ())
              "Unknown meta-command %S, use \"#help.\" for a short list."
              ("#" ^ n)

        (* Parser *)
        | Parsing.Parse_error ->
            IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ())
              "Unexpected input."
        | Parsetree.Preterm.Parse_error (p,s1,s2) ->
            IO.Output.eprintf ~p
              "%s while parsing@ %s."
              s1 s2

        | e -> raise e
      end ;
      k ()
  in
  IO.Input.apply_on_lexbuf f lexbuf

let definition_mode ~k lexbuf =
  try parse ~k ~parser:Parsetree.Parser.definition_mode ~lexer:Parsetree.Lexer.token lexbuf
  with Parsetree.Preterm.Empty_command -> None

let toplevel ~k lexbuf =
  try parse ~k ~parser:Parsetree.Parser.toplevel ~lexer:Parsetree.Lexer.token lexbuf
  with Parsetree.Preterm.Empty_term -> None

let term_mode ~k lexbuf =
  try parse ~k ~parser:Parsetree.Parser.term_mode ~lexer:Parsetree.Lexer.token lexbuf
  with Parsetree.Preterm.Empty_term -> None
