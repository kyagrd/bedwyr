{
  open Toplevelparser
  open Lexing

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

and theorem = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| blank {theorem lexbuf}
| name as n { match (anonymous lexbuf) with
                      LINE(s) -> THEOREM(n,s)
                    | _ -> failwith "THEOREM: invalid argument"}
| _ as c  {raise (Command.SyntaxError("theorem: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}

and anonymous = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| anything as n {LINE n}
| _ as c  {raise (Command.SyntaxError("anonymous: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}

and tactical = parse
| '\n'  {incrline lexbuf; anonymous lexbuf}
| '.'   {LINE ""}
| (line as n) '.' {LINE n}
| _ as c  {raise (Command.SyntaxError("tactical: invalid character '" ^ (String.make 1 c) ^ "'"))}
| eof   {raise (Command.SyntaxError("end of input"))}
