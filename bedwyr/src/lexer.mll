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
(* other initial characters *)
let ichar = ['_' '\'']
(* other body characters *)
let bchar = ['/' ]
let uname = uchar (digit|uchar|lchar|ichar|bchar)*
let lname = lchar (digit|uchar|lchar|ichar|bchar)*
let iname = ichar (digit|uchar|lchar|ichar|bchar)*

let blank = ' ' | '\t' | '\r'

let instring = [^'"'] *

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
  | "Query"             { QUERY }
  | "Import"            { IMPORT }
  | "Specification"     { SPECIFICATION }
  | "Split"             { SSPLIT }
  | "induction"         { IND }
  | "coinduction"       { COIND }
  | "intros"            { INTROS }
  | "case"              { CASE }
  | "search"            { SEARCH }
  | "apply"             { APPLY }
  | "backchain"         { BACKCHAIN }
  | "unfold"            { UNFOLD }
  | "assert"            { ASSERT }
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
  | "to"                { TO }
  | "with"              { WITH }
  | "on"                { ON }
  | "as"                { AS }
  | "keep"              { KEEP }
  | "Set"               { SET }
  | "Show"              { SHOW }
  | "Quit"              { QUIT }
  | "{"                 { LBRACK }
  | "}"                 { RBRACK }
  | "|-"                { TURN }
  | "*"                 { STAR }
  | "@"                 { AT }
  | "+"                 { PLUS }
  | "_"                 { UNDERSCORE }

  (* Bedwyr only meta-keywords *)
  | "#"                 { HASH }

  (* Uppercase-starting variable *)
  | uname as n          { UPPER_ID n }

  (* Other variable *)
  | lname as n
  | iname as n          { STRINGID n }

  (* misc *)
  | '\x04'              (* ctrl-D *)
  | eof                 { EOF }

  | _                   { failwith ("Illegal character " ^
                                    (Lexing.lexeme lexbuf) ^ " in input") }

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
