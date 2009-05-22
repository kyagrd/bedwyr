/**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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
  module LPA = Lpabsyn
  let constants = ref []
  let addClause cl =
    let add name clause constant =
      if name = LPA.getConstantName constant then
        let arity = LPA.getConstantArity constant in
        LPA.Constant(name, arity, clause :: (LPA.getConstantClauses constant))
      else
        constant
    in
    let find name constant =
      name = LPA.getConstantName constant
    in
    let (LPA.Clause(head, body)) = cl in
    let name = LPA.getAtomName (LPA.getApplicationHead head) in
    if List.exists (find name) !constants then
      constants := List.map (add name cl) !constants
    else
      let arity =
        List.length
          (LPA.getApplicationArguments (LPA.getClauseHead cl))
      in
      constants := (LPA.Constant(name, arity, [cl])) :: !constants
    
%}

%token IMP COLONDASH COMMA DOT
%token BSLASH LPAREN RPAREN CONS EQ
%token PI SIGMA NABLA SEMICOLON MODULE

%token <int> NUM
%token <string> ID CID STRING
%token EOF

/* Lower */

%left SEMICOLON
%left COMMA
%right CONS

%nonassoc BSLASH
%right IMP
%nonassoc EQ

/* Higher */


%start lp_module term
%type <Lpabsyn.constant list> lp_module
%type <Lpabsyn.term> term

%%

id:
  | ID                                   {LPA.AtomicTerm($1)}
  | CID                                  {LPA.VariableTerm($1)}

term:
  | term IMP term                        {LPA.ImplicationTerm($1, $3)}
  | term CONS term                       {LPA.ApplicationTerm(LPA.AtomicTerm("cons"), [$1; $3])}
  | term COMMA term                      {LPA.ConjunctionTerm($1, $3)}
  | term SEMICOLON term                  {LPA.DisjunctionTerm($1, $3)}
  | abstraction                          {$1}
  | exp exp_list                         {LPA.ApplicationTerm($1, $2)}
  | PI abstraction                       {LPA.PiTerm($2)}
  | SIGMA abstraction                    {LPA.SigmaTerm($2)}
  | NABLA abstraction                    {LPA.NablaTerm($2)}
  | exp                                  {$1}

exp:
  | LPAREN term RPAREN                   {$2}
  | id                                   {$1}

exp_list:
  | exp exp_list                         {$1::$2}
  | exp                                  {[$1]}
  | abstraction                          {[$1]}

abstraction:
  | ID BSLASH term                       {LPA.AbstractionTerm($1, $3)}
  | CID BSLASH term                      {LPA.AbstractionTerm($1, $3)}

clauses:
  | clause clauses                       {addClause $1}
  | MODULE id DOT clauses                {()}
  |                                      {()}

clause:
  | term DOT                             {LPA.Clause($1, None)}
  | term COLONDASH clause_body DOT       {LPA.Clause($1, Some $3)}

clause_body:
  | term                                 {$1}
  
lp_module:
  | clauses                              {let cl = !constants in (constants := []; cl)}
  | clauses EOF                          {let cl = !constants in (constants := []; cl)}
