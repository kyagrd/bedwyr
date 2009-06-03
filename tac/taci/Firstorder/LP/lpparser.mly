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
  let addDefinition def =
    let add name arity clause constant =
      if name = LPA.getConstantName constant then
        let clauses = LPA.getConstantClauses constant in
        let progress = LPA.getConstantProgress constant in
        let arity' = LPA.getConstantArity constant in
        if arity <> arity' then
          raise (LPA.Error("constant '" ^ name ^ "' defined with differing arities"))
        else
          LPA.Constant(name, arity, progress, clause :: clauses)
      else
        constant
    in
    let prog name progress constant =
      if name = LPA.getConstantName constant then
        let clauses = LPA.getConstantClauses constant in
        let progress' = LPA.getConstantProgress constant in
        let arity = List.length progress in
        let arity' = LPA.getConstantArity constant in

        if Option.isSome progress' then
          raise (LPA.Error("constant '" ^ name ^ "' with multiple progress annotations"))
        else if arity <> arity' then
          raise (LPA.Error("constant '" ^ name ^ "' progress defined with differing arities"))
        else
          LPA.Constant(name, arity, Some progress, clauses)
      else
        constant
    in
    let find name constant =
      name = LPA.getConstantName constant
    in
    let forceApplication head =
      match head with
          LPA.ApplicationTerm _ -> head
        | LPA.AtomicTerm _ -> LPA.ApplicationTerm(head, [])
        | _ -> raise (LPA.Error("clause with invalid head"))
    in
    match def with
        LPA.ClauseDefinition(head, body) ->
          let head = forceApplication head in
          let cl = LPA.Clause(head, body) in
          let name = LPA.getAtomName (LPA.getApplicationHead head) in
          let arity =
            List.length
              (LPA.getApplicationArguments head)
          in
          if List.exists (find name) !constants then
            constants := List.map (add name arity cl) !constants
          else
            constants := (LPA.Constant(name, arity, None, [cl])) :: !constants
      | LPA.ProgressDefinition(id, progress) ->
          if List.exists (find id) !constants then
            constants := List.map (prog id progress) !constants
          else
            let arity = List.length progress in
            constants := (LPA.Constant(id, arity, Some progress, [])) :: !constants
  let addProgress p =
    let (id, progress) = p in
    addDefinition (LPA.ProgressDefinition(id, progress))
%}

%token MODULE 
%token IMP COLONDASH COMMA DOT CONS EQ NEQ
%token PI SIGMA NABLA BSLASH
%token LPAREN RPAREN LBRACE RBRACE SEMICOLON

%token <(string * Lpabsyn.progress list)> PROGRESS
%token <int> NUM
%token <string> ID CID STRING
%token EOF

/* Lower */

%left SEMICOLON
%left COMMA
%right CONS

%nonassoc BSLASH
%right IMP
%nonassoc EQ NEQ

/* Higher */


%start lp_module term
%type <Lpabsyn.constant list> lp_module
%type <Lpabsyn.term> term

%%
lp_module:
  | clauses                              {let cl = !constants in (constants := []; cl)}
  | clauses EOF                          {let cl = !constants in (constants := []; cl)}

clauses:
  | clause clauses                        {addDefinition $1}
  | PROGRESS clauses                      {addProgress $1}
  | MODULE ID DOT clauses                 {()}
  |                                       {()}

progress_list:
  | progress progress_list               {$1 :: $2}
  | progress                             {$1 :: []}
  
progress:
  | LBRACE CID RBRACE                    {LPA.Progressing}
  | CID                                  {LPA.NonProgressing}

clause:
  | term DOT                             {LPA.ClauseDefinition($1, None)}
  | term COLONDASH clause_body DOT       {LPA.ClauseDefinition($1, Some $3)}

clause_body:
  | term                                 {$1}

term:
  | term IMP term                        {LPA.ImplicationTerm($1, $3)}
  | term CONS term                       {LPA.ApplicationTerm(LPA.AtomicTerm("cons"), [$1; $3])}
  | term COMMA term                      {LPA.ConjunctionTerm($1, $3)}
  | term EQ term                         {LPA.EqualityTerm($1, $3)}
  | term NEQ term                        {LPA.ImplicationTerm(LPA.EqualityTerm($1, $3), LPA.AtomicTerm("false"))}
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

id:
  | ID                                   {LPA.AtomicTerm($1)}
  | CID                                  {LPA.VariableTerm($1)}

exp_list:
  | exp exp_list                         {$1::$2}
  | exp                                  {[$1]}
  | abstraction                          {[$1]}

abstraction:
  | ID BSLASH term                       {LPA.AbstractionTerm($1, $3)}
  | CID BSLASH term                      {LPA.AbstractionTerm($1, $3)}
