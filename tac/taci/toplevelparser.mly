%{
  let split s =
    let result = Str.bounded_split (Str.regexp " \\|\t") s 2 in
    let len = List.length result in
    if len == 2 then
      (List.hd result, List.hd (List.tl result))
    else if len == 1 then
      (List.hd result, "")
    else
      failwith "Toplevelparser.split: invalid string"
%}

%token DOT SHARP
%token HELP EXIT RESET INCLUDE TIME DEBUG ON OFF CLEAR
%token <string> DEFINITION
%token <string * string> THEOREM TACTICAL
%token <string> ID STRING LINE

%start toplevel_command toplevel_file
%type <Command.command list> toplevel_file
%type <Command.command> toplevel_command
%%

toplevel_file:
  | file  {$1}
  ;

file:
  | SHARP command DOT file  {$2 :: $4}
  | SHARP command DOT       {[$2]}
  ;


toplevel_command:
  |                     {Command.NoCommand}
  | SHARP command DOT   {$2}
  | TACTICAL            {Command.Tactical($1)}
  ;

command:
  | EXIT  {Command.Exit}
  | RESET {Command.Reset}
  | INCLUDE filenames {Command.Include($2)}
  
  | CLEAR       {Command.Clear}
  | DEBUG onoff {Command.Debug($2)}
  | TIME onoff  {Command.Timing($2)}
  
  | HELP        {Command.Help}
  | THEOREM     {Command.Theorem($1)}
  | DEFINITION  {Command.Definition($1)}
  ;

filenames:
  | STRING filenames  {$1 :: $2}
  | STRING            {[$1]}
  ;

onoff:
  | ON  {true}
  | OFF {false}
  ;

%%
