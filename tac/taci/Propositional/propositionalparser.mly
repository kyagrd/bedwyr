%{
  open Propositional
%}

%token AND OR IMPLICATION NOT TRUE FALSE ID
%token LPAREN RPAREN
%token <string> ID

%nonassoc IMPLICATION
%right OR
%right AND
%right UNARY
%start term
%type <Propositionalabsyn.term> term
%%

term:
  | term AND term         {Propositionalabsyn.AndTerm($1, $3)}
  | term OR term          {Propositionalabsyn.OrTerm($1, $3)}
  | term IMPLICATION term {Propositionalabsyn.ImplicationTerm($1, $3)}
  | NOT term %prec UNARY  {Propositionalabsyn.NotTerm($2)}
  | ID                    {Propositionalabsyn.ConstantTerm($1)}
  | TRUE                  {Propositionalabsyn.TrueTerm}
  | FALSE                 {Propositionalabsyn.FalseTerm}
  | LPAREN term RPAREN    {$2}
  ;

%%
