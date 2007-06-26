{
  open Firstorderparser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum}
}

let name = ['A' - 'Z' 'a'-'z' '_' '/' '0'-'9' '\''] +
let blank = ' ' | '\t' | '\r'
let instring = [^'"'] *

rule token = parse
| blank              {token lexbuf}
| '\n'               {incrline lexbuf; token lexbuf}

| "(" {LPAREN}
| ")" {RPAREN}

| "_" {ANONYMOUS}
| "=" {EQ}
| "," {AND}
| "&" {AND}
| ";" {OR}
| "=>" {IMP}
| ":=" {DEF}
| "\\" {BSLASH}

| "pi"      {PI}
| "sigma"   {SIGMA}
| "nabla"   {NABLA}

| "inductive" {IND}
| "coinductive" {COIND}

| name as n {ID n}
| '"' (instring as n) '"'
    {String.iter (function '\n' -> incrline lexbuf | _ -> ()) n ; STRING n}
| eof    {EOF}
