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
  open Firstorderparser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum}
}

let name = ['A'-'Z' 'a'-'z' '_' '/' '0'-'9' '\''] +
let blank = ' ' | '\t' | '\r'
let instring = [^'"'] *

rule token = parse
| blank              {token lexbuf}
| '\n'               {incrline lexbuf; token lexbuf}

| "(" {LPAREN}
| ")" {RPAREN}
| "{" {LBRACE}
| "}" {RBRACE}
| "[" {LBRACK}
| "]" {RBRACK}

| "_" {UNDERSCORE}

| "=" {EQ}
| ":=" {DEF}

| "," {AND}
| ";" {OR}
| "&" {WITH}
| "|" {PAR}
| "=>" {IMP}

| "+" {PLUS}
| "-" {MINUS}
| "*" {STAR}

| "\\"      {BSLASH}
| "pi"      {PI}
| "sigma"   {SIGMA}
| "nabla"   {NABLA}
| "mu"      {MU}
| "nu"      {NU}

| "inductive" {IND}
| "coinductive" {COIND}

| name as n {ID n}
| '"' (instring as n) '"'
    {String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ; STRING n}
| _ as c {raise (Absyn.SyntaxError("invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof    {EOF}
