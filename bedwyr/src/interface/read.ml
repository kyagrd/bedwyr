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
  try Some (parser lexer lexbuf) with e ->
    begin match e with
      (* Lexer *)
      | Preterm.EOF_error s ->
          Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
            "Lexing error:@ %s@ at end of input."
            s
      | Preterm.Illegal_byte_sequence c ->
          Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
            "Illegal sequence starting with byte %C in input."
            c
      | Preterm.Illegal_string_comment p ->
          Output.eprintf ~p
            "Unmatched comment delimiter in string."
      | Preterm.Illegal_token (n1,n2) ->
          Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ())
            "%S is illegal in a token, did you mean %S?"
            (Lexing.lexeme lexbuf)
            (String.concat " " [n1;n2])
      | Preterm.Unknown_command n ->
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
    k ()

let definition_mode ~k lexbuf =
  try Some (parse ~k ~parser:Parser.definition_mode ~lexer:Lexer.token lexbuf)
  with Preterm.Empty_command -> None

let toplevel ~k lexbuf =
  try Some (parse ~k ~parser:Parser.toplevel ~lexer:Lexer.token lexbuf)
  with Preterm.Empty_term -> None

let term_mode ~k lexbuf =
  try Some (parse ~k ~parser:Parser.term_mode ~lexer:Lexer.token lexbuf)
  with Preterm.Empty_term -> None
