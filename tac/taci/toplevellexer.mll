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

| "." { DOT }
| "#" { SHARP }

| "reset" { RESET }
| "include" { INCLUDE }
| "exit"  { EXIT  }

| "help"  { HELP  }

| "clear" { CLEAR }
| "debug" { DEBUG }
| "time"  { TIME  }
| "on"    { ON  }
| "off"   { OFF }

| "theorem"     {(theorem lexbuf)}
| "definition"  { match (anonymous lexbuf) with
                      LINE(s) -> DEFINITION(s)
                    | _ -> failwith "DEFINITION: invalid argument"}
| '"' (instring as n) '"' {String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ; STRING(n)}
| name as n { match (tactical lexbuf) with
                  LINE(s) -> TACTICAL(n,s)
                | _ -> failwith "TACTICAL: invalid argument"}
| _ as c  {raise (Command.SyntaxError("command: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}

(**********************************************************************
*theorem
**********************************************************************)
and theorem = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| blank {theorem lexbuf}
| name as n { match (anonymous lexbuf) with
                      LINE(s) -> THEOREM(n,s)
                    | _ -> failwith "THEOREM: invalid argument"}
| _ as c  {raise (Command.SyntaxError("theorem: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}

(**********************************************************************
*tactical:
**********************************************************************)
and tactical = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| '.'   {LINE ""}
| (line as n) '.' {LINE (trim n)}
| _ as c  {raise (Command.SyntaxError("tactical: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}

(**********************************************************************
*anonymous:
**********************************************************************)
and anonymous = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| anything as n {LINE (trim n)}
| _ as c  {raise (Command.SyntaxError("anonymous: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}
