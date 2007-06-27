(**********************************************************************
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
**********************************************************************)
%{
  let eqFormula f1 f2 = Linearabsyn.EqualityFormula(f1, f2)
  let andFormulaL f1 f2 = Linearabsyn.LinearAndFormula(f1, f2)
  let andFormula f1 f2 = Linearabsyn.AndFormula(f1, f2)
  let orFormulaL f1 f2 = Linearabsyn.LinearOrFormula(f1, f2)
  let orFormula f1 f2 = Linearabsyn.OrFormula(f1, f2)
  let impFormula f1 f2 = Linearabsyn.ImplicationFormula(f1, f2)
  
  let rec getAbstractions f =
    match f with
        Linearabsyn.AbstractionFormula(name, f') ->
          let (names,f'') = (getAbstractions f') in
          (name::names, f'')
      | _ -> ([], f)

  let makeAbstractions make f =
    let rec makeAbs' names make f =
      match names with
        [] -> raise (Linearabsyn.SemanticError ("argument does not have toplevel abstractions: " ^ (Linearabsyn.string_of_formula f)))
      | [name] -> make name (Linearabsyn.AbstractionFormula(name,f))
      | name::names ->
          (makeAbs' (names) make (make name (Linearabsyn.AbstractionFormula(name,f))))        
    in
    let (names,f') = getAbstractions f in
    (makeAbs' names make f')

  let pi f =
    let make name f = Linearabsyn.PiFormula(f) in
    (makeAbstractions make f)

  let sigma f =
    let make name f = Linearabsyn.SigmaFormula(f) in
    (makeAbstractions make f)

  let nabla f =
    let make name f = Linearabsyn.NablaFormula(f) in
    (makeAbstractions make f)

  let atomic f = Linearabsyn.AtomicFormula(f)
  
  let anon () = failwith "Linearparser.anon: not implemented."

  let abstract id f =
    Linearabsyn.AbstractionFormula(id, f)

  let atom t = failwith "Linearparser.atom: not implemented."
    
  let application term = 
    match term with
        [] -> failwith "Linearparser.tterm: invalid lterm."
      | t::l -> (Term.app t l)
  
%}

%token BSLASH LPAREN RPAREN DOT SHARP UNDERSCORE
%token EQ AND ANDL OR ORL IMP DEF
%token PI SIGMA NABLA
%token IND COIND
%token EOF
%token <string> ID
%token <string> STRING

%nonassoc BSLASH PI SIGMA NABLA MU
%right IMP
%left OR ORL
%left AND ANDL
%nonassoc EQ

%start toplevel_formula toplevel_term toplevel_definition
%type <Linearabsyn.formula> toplevel_formula
%type <Linearabsyn.term> toplevel_term
%type <Linearabsyn.predefinition> toplevel_definition

%%
toplevel_formula
  : formula     {$1}
  | formula EOF {$1}
  ;

toplevel_definition
  : definition      {$1}
  | definition EOF  {$1}
  ;

definition
  : ID definitionargs DEF formula   {Linearabsyn.PreDefinition($1, $2, $4, Linearabsyn.Inductive)}
  | IND ID definitionargs DEF formula   {Linearabsyn.PreDefinition($2, $3, $5, Linearabsyn.Inductive)}
  | COIND ID definitionargs DEF formula   {Linearabsyn.PreDefinition($2, $3, $5, Linearabsyn.CoInductive)}
  ;

definitionargs
  : ID definitionargs   {$1::$2}
  |                     {[]}
  ;

formula
  : formula ANDL formula {andFormulaL $1 $3}
  | formula AND formula {andFormula $1 $3}
  | formula ORL formula {orFormulaL $1 $3}
  | formula OR formula {orFormula $1 $3}
  | formula IMP formula {impFormula $1 $3}
  | term EQ term {eqFormula $1 $3}
  
  | PI formula {pi $2}
  | SIGMA formula {sigma $2}
  | NABLA formula {nabla $2}
  
  | ID BSLASH formula {abstract $1 $3}
  
  | LPAREN formula RPAREN {$2}
  | term {atomic $1}
  ;

toplevel_term
  : term      {$1}
  | term EOF  {$1}
  ;


term
  : lterm {application $1}
  ;

lterm
  : primaryterm       {[$1]}
  | primaryterm lterm {$1::$2}
  ;

primaryterm
  : LPAREN term RPAREN  {$2}
  | ID                  {atom $1}
  | STRING              {Term.string $1}
  | UNDERSCORE          {anon ()}   
  ;
%%
