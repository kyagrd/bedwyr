(*****************************************************************************
* Logics_gen                                                                 *
* Copyright (C) 2007 Zach Snow                                               *
*                                                                            *
* This program is free software; you can redistribute it and/or modify       *
* it under the terms of the GNU General Public License as published by       *
* the Free Software Foundation; either version 2 of the License, or          *
* (at your option) any later version.                                        *
*                                                                            *
* This program is distributed in the hope that it will be useful,            *
* but WITHOUT ANY WARRANTY; without even the implied warranty of             *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *
* GNU General Public License for more details.                               *
*                                                                            *
* You should have received a copy of the GNU General Public License          *
* along with this code; if not, write to the Free Software Foundation,       *
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA               *
*****************************************************************************)
{
  open Parser
  open Lexing

  (*  trim: trims whitespace in a silly way...  *)
  let rec trim s =
    let l = String.length s in 
    if l = 0 then
      s
    else if s.[0] = ' ' || s.[0]='\t' || s.[0]='\n' || s.[0]='\r' then
      trim (String.sub s 1 (l-1))
    else if s.[l-1]=' ' || s.[l-1]='\t' || s.[l-1]='\n' || s.[l-1]='\r' then
      trim (String.sub s 0 (l-1))
    else
      s

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let name = ['A' - 'Z' 'a'-'z' '_' '0'-'9' '.' '-'] +
let blank = ' ' | '\t' | '\r'

rule command = parse
| "//" [^'\n'] * '\n' {incrline lexbuf; command lexbuf}
| blank               {command lexbuf}
| '\n'                {incrline lexbuf; command lexbuf}

| ";"           {SEMICOLON}
| ","           {COMMA}
| "("           {LPAREN}
| ")"           {RPAREN}
| "output"      {OUTPUT}
| "logic"       {LOGIC}
| name as n     {ID n}
| _ as c  {failwith ("invalid character '" ^ (String.make 1 c) ^ "'")}
| eof           {EOF}
