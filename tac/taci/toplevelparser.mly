%{
%}

%token DOT SHARP LPAREN RPAREN COMMA
%token HELP EXIT RESET OPEN INCLUDE TIME DEBUG
%token ON OFF CLEAR THEOREM
%token TACTICAL TACTICALS LOGIC LOGICS
%token DEFINE UNDO REDO
%token EOF
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
  | EOF                     {[]}
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
  : EXIT                {Absyn.Exit}
  | RESET               {Absyn.Reset}
  | OPEN stringlist     {Absyn.Open($2)}
  | INCLUDE stringlist  {Absyn.Include($2)}
  
  | CLEAR       {Absyn.Clear}
  
  | UNDO        {Absyn.Undo(1)}
  | REDO        {Absyn.Redo(1)}
  
  | DEBUG onoff {Absyn.Debug($2)}
  | TIME onoff  {Absyn.Timing($2)}
  
  | HELP                  {Absyn.Help}
  | THEOREM ID STRING     {Absyn.Theorem($2, $3)}
  | DEFINE stringlist {Absyn.Definitions($2)}
  
  | TACTICALS             {Absyn.Tacticals}
  | TACTICAL ID tactical  {Absyn.TacticalDefinition($2, $3)}
  
  | LOGIC ID              {Absyn.Logic($2)}
  | LOGICS                {Absyn.Logics}
  ;

stringlist
  : STRING stringlist {$1 :: $2}
  | STRING            {[$1]}
  ;

onoff:
  | ON  {true}
  | OFF {false}
  ;

%%
