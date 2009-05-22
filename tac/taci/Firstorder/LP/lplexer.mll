(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
{
  open Lpparser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }

  let comment_level = ref 0
}

let idchar = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\'' '?' '-' '`' '#' '$' '&' '!' '~']
let id = ['a' - 'z'] idchar *
let cid = ['A' - 'Z' '_'] idchar *
let blank = ' ' | '\t' | '\r'

rule token = parse
| "/*"               { incr comment_level; comment lexbuf }
| '%' [^'\n']* '\n'  { incrline lexbuf; token lexbuf }

| blank              { token lexbuf }
| '\n'               { incrline lexbuf; token lexbuf }

| '"' ([^ '"']* as s) '"'
                     { STRING s }

| "=>"               { IMP }
| ":-"               { COLONDASH }
| ","                { COMMA }
| ";"                { SEMICOLON }
| "."                { DOT }
| "\\"               { BSLASH }
| "("                { LPAREN }
| ")"                { RPAREN }
| "::"               { CONS }
| "="                { EQ }

| "pi"               { PI }
| "sigma"            { SIGMA }
| "nabla"            { NABLA }

| "module"           { MODULE }

| id as n            { ID n }
| cid as n           { CID n }

| eof                { EOF }

and comment = parse
| [^ '*' '/' '\n']+  { comment lexbuf }
| "/*"               { incr comment_level; comment lexbuf }
| "*/"               { decr comment_level ;
                       if !comment_level = 0 then
                         token lexbuf
                       else
                         comment lexbuf }
| "*"                { comment lexbuf }
| "/"                { comment lexbuf }
| "\n"               { incrline lexbuf; comment lexbuf }
| eof                { print_endline
                         "Warning: comment not closed at end of file" ;
                       token lexbuf }
