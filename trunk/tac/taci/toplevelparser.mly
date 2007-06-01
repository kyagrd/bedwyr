%{
%}

%token DOT SHARP LPAREN RPAREN COMMA
%token HELP EXIT RESET INCLUDE TIME DEBUG
%token ON OFF CLEAR THEOREM TACTICAL 
%token DEFINITION UNDO REDO
%token <string> ID STRING

%start toplevel_command toplevel_file
%type <Absyn.command list> toplevel_file
%type <Absyn.command> toplevel_command
%%

toplevel_file:
  | file  {$1}
  ;

file:
  | SHARP command DOT file  {$2 :: $4}
  | SHARP command DOT       {[$2]}
  ;


toplevel_command
  :                     {Absyn.NoCommand}
  | SHARP command DOT   {$2}
  | tactical DOT        {Absyn.PreTactical($1)}
  ;

tactical
  : ID                              {Absyn.ApplicationPreTactical($1, [])}
  | ID LPAREN tactical_list RPAREN  {Absyn.ApplicationPreTactical($1, $3)}
  | STRING                          {Absyn.StringPreTactical($1)}
  | LPAREN tactical RPAREN          {$2}
  ;

tactical_list
  : tactical COMMA tactical_list  {$1::$3}
  | tactical                      {$1::[]}
  ;

command
  : EXIT  {Absyn.Exit}
  | RESET {Absyn.Reset}
  | INCLUDE filenames {Absyn.Include($2)}
  
  | CLEAR       {Absyn.Clear}
  | UNDO        {Absyn.Undo(1)}
  | REDO        {Absyn.Redo(1)}
  | DEBUG onoff {Absyn.Debug($2)}
  | TIME onoff  {Absyn.Timing($2)}
  
  | HELP                {Absyn.Help}
  | THEOREM ID STRING   {Absyn.Theorem($2, $3)}
  | DEFINITION STRING   {Absyn.Definition($2)}
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
