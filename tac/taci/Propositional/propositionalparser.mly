/**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************/
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
