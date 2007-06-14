%{
  let addOutput output (outputs, logics) = (output::outputs, logics)
  let addLogic logic (outputs, logics) = (outputs, logic::logics)
%}

%token LOGIC OUTPUT LPAREN RPAREN COMMA SEMICOLON EOF
%token <string> ID

%start toplevel_file
%type <Absyn.output list * Absyn.logic list> toplevel_file
%%

toplevel_file:
  | file      {$1}
  | file EOF  {$1}
  ;

file:
  | output file {addOutput $1 $2}
  | logic file  {addLogic $1 $2}
  | output      {addOutput $1 ([],[])}
  | logic       {addLogic $1 ([],[])}
  ;


output
  : OUTPUT LPAREN ID COMMA ID RPAREN SEMICOLON {Absyn.Output($3, $5)}
  ;

logic
  : LOGIC LPAREN ID COMMA ID RPAREN SEMICOLON  {Absyn.Logic($3, $5)}
  ;

%%
