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
| "true"              {TRUE}
| "false"             {FALSE}
| name as n           {ID n}
| _ as c  {raise (Propositionalabsyn.SyntaxError("invalid character: " ^ (String.make 1 c)))}
| eof     {EOF}

and tactics = parse
| blank                 {tactics lexbuf}
| '\n'                  {incrline lexbuf; tactics lexbuf}

| '('                   {LPAREN}
| ')'                   {RPAREN}
| name as n             {match (tactic lexbuf) with
                            LINE s -> TACTIC(n,s)
                          | _ -> TACTIC(n,"")}
| _ as c {raise (Propositionalabsyn.SyntaxError("invalid character: " ^ (String.make 1 c)))}
| eof     {EOF}

and tactic = parse
| [^'(' ')']+ as l  {LINE l}
| _ as c            {raise (Propositionalabsyn.SyntaxError("invalid character: " ^ (String.make 1 c)))}
| eof               {EOF}
