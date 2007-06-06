%{
%}

%token AND OR IMPLICATION NOT TRUE FALSE EOF
%token LPAREN RPAREN
%token <string> ID LINE
%token <string * string> TACTIC

%start term tactics
%type <Propositionalabsyn.term> term
%type <Propositionalabsyn.tactic list> tactics
%%

tactics
  : TACTIC                {[$1]}
  | TACTIC EOF            {[$1]}
  | tactic_list           {$1}
  | tactic_list EOF       {$1}
  ;

tactic_list
  : LPAREN TACTIC RPAREN tactic_list  {$2 :: $4}
  | LPAREN TACTIC RPAREN              {$2 :: []}
  ;

term
  : implication_term      {$1}
  | implication_term EOF  {$1}
  ;

primary_term
  : ID                    {Propositionalabsyn.ConstantTerm($1)}
  | TRUE                  {Propositionalabsyn.TrueTerm}
  | FALSE                 {Propositionalabsyn.FalseTerm}
  | LPAREN term RPAREN    {$2}
  ;

not_term
  : primary_term          {$1}
  | NOT not_term          {Propositionalabsyn.NotTerm($2)}
  ;

and_term
  : not_term              {$1}
  | not_term AND and_term {Propositionalabsyn.AndTerm($1, $3)} 
  ;

or_term
  : and_term              {$1}
  | and_term OR or_term   {Propositionalabsyn.OrTerm($1, $3)}
  ;

implication_term
  : or_term               {$1}
  | or_term IMPLICATION or_term
                          {Propositionalabsyn.ImplicationTerm($1, $3)}
  ;
%%
