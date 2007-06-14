{
  open Toplevelparser
  open Lexing

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

let name = ['A' - 'Z' 'a'-'z' '_' '0'-'9'] +
let blank = ' ' | '\t' | '\r'
let anything = [^'.' '\n'] *
let line = [^'.' '\n'] *
let instring = [^'"'] *

let line = [^'.' '\n'] +

rule command = parse
| '%' [^'\n'] * '\n' { incrline lexbuf; command lexbuf }
| blank              { command lexbuf }
| '\n'               { incrline lexbuf; command lexbuf }

| "." {DOT }
| "#" {SHARP}
| "(" {LPAREN}
| ")" {RPAREN}
| "," {COMMA}

| "reset"   {RESET}
| "include" {INCLUDE}
| "exit"    {EXIT}
| "undo"    {UNDO}
| "redo"    {REDO}

| "help"  {HELP}

| "clear" {CLEAR}
| "debug" {DEBUG}
| "time"  {TIME}
| "on"    {ON}
| "off"   {OFF}

| "tactical"    {TACTICAL}
| "tacticals"   {TACTICALS}
| "logic"       {LOGIC}
| "logics"      {LOGICS}

| "theorem"     {THEOREM}
| "define"  {DEFINITION}
| '"' (instring as n) '"' {String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ; STRING(n)}
| name as n     {ID n}
| _ as c  {raise (Absyn.SyntaxError("invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof     {raise (Absyn.SyntaxError("end of input"))}
