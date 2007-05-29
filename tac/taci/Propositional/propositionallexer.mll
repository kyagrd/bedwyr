{
  open Propositionalparser
  open Lexing

  let incrline lexbuf =
    lexbuf.lex_curr_p <- {
        lexbuf.lex_curr_p with
          pos_bol = lexbuf.lex_curr_p.pos_cnum ;
          pos_lnum = 1 + lexbuf.lex_curr_p.pos_lnum }
}

let name = ['A' - 'Z' 'a'-'z' '_' '0'-'9'] +
let blank = ' ' | '\t' | '\r'

rule term = parse
| blank               {term lexbuf}
| '\n'                {incrline lexbuf; term lexbuf}

| "("                 {LPAREN}
| ")"                 {RPAREN}

| "/\\"               {AND}
| "\\/"               {OR}
| "->"                {IMPLICATION}
| "~"                 {NOT}
| name as n           {ID n}
| _ as c  {raise (Propositionalabsyn.SyntaxError("invalid character: " ^ (String.make 1 c)))}
| eof     {raise (Propositionalabsyn.SyntaxError("end of input"))}
