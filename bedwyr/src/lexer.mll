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

{
  open Parser
  open Lexing

  exception Illegal_string

  (* XXX incrline = new_line in OCaml >= 3.11.0 *)
  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let digit = ['0'-'9']
let number = digit+

let uchar = ['A'-'Z']
let lchar = ['a'-'z']
(* special symbols *)
let prefix_special = ['`' '\'' '$']
let infix_special  = ['+' '-' '*' '^' '<' '>' '=' '~']
let tail_special   = ['/' '?' '!' '@' '#' '&' '_']

let special_char = prefix_special | infix_special | tail_special
let any_char = uchar | lchar | digit | special_char
let safe_char = uchar | lchar | digit |  prefix_special | tail_special

let upper_name = uchar | (uchar any_char* safe_char)
let lower_name = (lchar|prefix_special) | ((lchar|prefix_special) any_char* safe_char)
let infix_name = infix_special (special_char)*
(* XXX alternate version: any character (including +-*^<>=~)
 * is allowed at the end of any name (including upper_names and lower_names),
 * so "x= y" is parsed as App ("x=",["y"])
 * while "x =y" is parsed as Eq ("x","y")
let upper_name = uchar any_char*
let lower_name = (lchar|prefix_special) any_char*
let infix_name = infix_special (special_char)*
*)

let blank = ' ' | '\t' | '\r'

let instring = [^'"']*

rule token = parse
  | "/*"                { comment 0 lexbuf }
  | '%' [^'\n']* '\n'?  { incrline lexbuf; token lexbuf }
  | blank               { token lexbuf }
  | '\n'                { incrline lexbuf; token lexbuf }

  | number as n         { NUM (int_of_string n) }

  | '"' (instring as s) '"'
      { String.iter (function '\n' -> incrline lexbuf | _ -> ()) s ;
        QSTRING s }

  (* lprolog meta-keywords *)
  | "sig"               { SIG }
  | "module"            { MODULE }
  | "accum_sig"         { ACCUMSIG }
  | "accumulate"        { ACCUM }
  | "end"               { END }
  | "kind"              { KIND }
  | "type"              { TYPE }
  | ","                 { COMMA }
  | "->"                { RARROW }
  | ":-"                { CLAUSEEQ }
  | "."                 { DOT }

  (* lprolog term-keywords *)
  | "=>"                { IMP }
  | "\\"                { BSLASH }
  | "("                 { LPAREN }
  | ")"                 { RPAREN }
  | "::"                { CONS }
  (* "pi" is parsed as STRINGID,
   * "sigma", "," and ";" are just missing *)

  (* common meta-keywords (Abella/Bedwyr) *)
  | "Kind"              { KKIND }
  | "Type"              { TTYPE }
  | "Define"            { DEFINE }
  | "inductive"         { INDUCTIVE }
  | "coinductive"       { COINDUCTIVE }
  | ":"                 { COLON }
  | "by"                { BY }
  | ":="                { DEFEQ }
  | ";"                 { SEMICOLON }

  (* common term-keywords (Abella/Bedwyr) *)
  | "prop"              { PROP }
  | "="                 { EQ }
  | "/\\"               { AND }
  | "\\/"               { OR }
  | "forall"            { FORALL }
  | "exists"            { EXISTS }
  | "nabla"             { NABLA }
  | "true"              { TRUE }
  | "false"             { FALSE }

  (* Abella only meta-keywords *)
  | "Close"             { CLOSE }
  | "Theorem"           { THEOREM }
  | "Qed"               { QED }
  | "Query"             { QUERY }
  | "Import"            { IMPORT }
  | "Specification"     { SPECIFICATION }
  | "Split"             { SSPLIT }
  | "Set"               { SET }
  | "Show"              { SHOW }
  | "Quit"              { QUIT }

  (* Abella's tactics (minus "exists" and "assert") *)
  | "induction"         { IND }
  | "coinduction"       { COIND }
  | "intros"            { INTROS }
  | "case"              { CASE }
  | "search"            { SEARCH }
  | "apply"             { APPLY }
  | "backchain"         { BACKCHAIN }
  | "unfold"            { UNFOLD }
  | "split"             { SPLIT }
  | "split*"            { SPLITSTAR }
  | "left"              { LEFT }
  | "right"             { RIGHT }
  | "permute"           { PERMUTE }
  | "inst"              { INST }
  | "cut"               { CUT }
  | "monotone"          { MONOTONE }
  | "undo"              { UNDO }
  | "skip"              { SKIP }
  | "abort"             { ABORT }
  | "clear"             { CLEAR }
  | "abbrev"            { ABBREV }
  | "unabbrev"          { UNABBREV }

  (* Abella only keywords *)
  | "to"                { TO }
  | "with"              { WITH }
  | "on"                { ON }
  | "as"                { AS }
  | "keep"              { KEEP }
  | "{"                 { LBRACK }
  | "}"                 { RBRACK }
  | "|-"                { TURN }
  | "*"                 { STAR }
  | "@"                 { AT }
  | "+"                 { PLUS }
  | "_"                 { UNDERSCORE }

  (* Bedwyr only meta-keywords *)
  | "#"                 { HASH }
  | "quit"
  | "exit"              { EXIT }
  | "help"              { HELP }
  | "include"           { INCLUDE }
  | "reset"             { RESET }
  | "reload"            { RELOAD }
  | "session"           { SESSION }
  | "debug"             { DEBUG }
  | "time"              { TIME }
  | "equivariant"       { EQUIVARIANT }
  | "show_table"        { SHOW_TABLE }
  | "clear_tables"      { CLEAR_TABLES }
  | "clear_table"       { CLEAR_TABLE }
  | "save_table"        { SAVE_TABLE }
  | "assert"            { ASSERT }
  | "assert_not"        { ASSERT_NOT }
  | "assert_raise"      { ASSERT_RAISE }

  (* bound variable, free variable in a query *)
  | upper_name as n     { UPPER_ID n }

  (* bound variable, type/prefix constant/predicate *)
  | lower_name as n     { LOWER_ID n }

  (* infix constant *)
  | infix_name as n     { INFIX_ID n }

  (* misc *)
  | '\x04'              (* ctrl-D *)
  | eof                 { EOF }

  | _                   { raise Illegal_string }

and comment level = parse
  | [^ '*' '/' '\n']+   { comment level lexbuf }
  | "/*"                { comment (level + 1) lexbuf }
  | "*/"                { if level = 0 then
                            token lexbuf
                          else
                            comment (level - 1) lexbuf }
  | "*"
  | "/"                 { comment level lexbuf }
  | "\n"                { incrline lexbuf ;
                          comment level lexbuf }
  | eof                 { print_endline
                            "Warning: comment not closed at end of file" ;
                          token lexbuf }
