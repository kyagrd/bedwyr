let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  if file = "" then
    "" (* lexbuf information is rarely accurate at the toplevel *)
  else
    Format.sprintf "%s(%d) : " file line

let parseCommand lexbuf s =
  try
    (Toplevelparser.toplevel_command Toplevellexer.command lexbuf)
  with
    Parsing.Parse_error ->
      (print_endline ((position lexbuf) ^ "Syntax error" ^ s);
      Command.NoCommand)
  
let parseStringCommand s =
  let lexbuf = Lexing.from_string s in
  (parseCommand lexbuf (" in: " ^ s))

let parseFile s =
  let c = open_in s in
  let lexbuf = Lexing.from_channel c in
  (parseCommand lexbuf "")
