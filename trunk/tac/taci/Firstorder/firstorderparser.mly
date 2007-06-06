/****************************************************************************
 * Bedwyr prover                                                            *
 * Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *
 *                                                                          *
 * This program is free software; you can redistribute it and/or modify     *
 * it under the terms of the GNU General Public License as published by     *
 * the Free Software Foundation; either version 2 of the License, or        *
 * (at your option) any later version.                                      *
 *                                                                          *
 * This program is distributed in the hope that it will be useful,          *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of           *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *
 * GNU General Public License for more details.                             *
 *                                                                          *
 * You should have received a copy of the GNU General Public License        *
 * along with this code; if not, write to the Free Software Foundation,     *
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *
 ****************************************************************************/

%{
  let eq f1 f2 = Firstorderabsyn.EqualityFormula(f1, f2)
  let conj f1 f2 = Firstorderabsyn.AndFormula(f1, f2)
  let disj f1 f2 = Firstorderabsyn.OrFormula(f1, f2)
  let imp f1 f2 = Firstorderabsyn.ImplicationFormula(f1, f2)
  let pi v f = Firstorderabsyn.PiFormula(Firstorderabsyn.abstract v f)
  let sigma v f = Firstorderabsyn.SigmaFormula(Firstorderabsyn.abstract v f)
  let nabla v f = Firstorderabsyn.NablaFormula(Firstorderabsyn.abstract v f)
  let atom t = Firstorderabsyn.AtomicFormula(t)
%}

%token BSLASH LPAREN RPAREN DOT SHARP
%token EQ AND OR IMP IF
%token PI SIGMA NABLA
%token EOF
%token <string> ID
%token <string> STRING

%nonassoc BSLASH
%right IMP
%left OR
%left AND
%nonassoc EQ

%start toplevel_formula toplevel_term
%type <Firstorderabsyn.formula> toplevel_formula
%type <Firstorderabsyn.term> toplevel_term

%%
toplevel_formula
  : formula     {$1}
  | formula EOF {$1}
  ;

formula
  : formula AND formula {conj $1 $3}
  | formula OR formula {disj $1 $3}
  | formula IMP formula {imp $1 $3}
  | term EQ term {eq $1 $3}
  | PI ID BSLASH formula {pi (Term.atom $2) $4}
  | SIGMA ID BSLASH formula {sigma (Term.atom $2) $4}
  | NABLA ID BSLASH formula {nabla (Term.atom $2) $4}
  | LPAREN formula RPAREN {$2}
  | term {atom $1}
  ;

toplevel_term
  : term      {$1}
  | term EOF  {$1}
  ;

term
  : lterm {match $1 with
          | [] -> assert false
          | t::l -> (Term.app t l)}
  ;
lterm
  : primaryterm       {[$1]}
  | ID BSLASH term    {[Term.abstract $1 $3]}
  | primaryterm lterm {$1::$2}
  ;

primaryterm
  : LPAREN term RPAREN {$2}
  | ID {Term.atom $1}
  | STRING {Term.string $1}
  ;
%%
