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
  let eq f1 f2 = Firstorderabsyn.EqualityFormula(f1, f2)
  let conj f1 f2 = Firstorderabsyn.AndFormula(f1, f2)
  let disj f1 f2 = Firstorderabsyn.OrFormula(f1, f2)
  let imp f1 f2 = Firstorderabsyn.ImplicationFormula(f1, f2)
  
  let rec getAbstractions f =
    match f with
        Firstorderabsyn.AbstractionFormula(name, f') ->
          let (names,f'') = (getAbstractions f') in
          (name::names, f'')
      | _ -> ([], f)

  let makeAbstractions make f =
    let rec makeAbs' names make f =
      match names with
        [] -> raise (Firstorderabsyn.SemanticError ("argument does not have toplevel abstractions: " ^ (Firstorderabsyn.string_of_formula f)))
      | [name] -> make name (Firstorderabsyn.AbstractionFormula(name,f))
      | name::names ->
          (makeAbs' (names) make (make name (Firstorderabsyn.AbstractionFormula(name,f))))        
    in
    let (names,f') = getAbstractions f in
    (makeAbs' names make f')

  let pi f =
    let make name f = Firstorderabsyn.PiFormula(f) in
    (makeAbstractions make f)

  let sigma f =
    let make name f = Firstorderabsyn.SigmaFormula(f) in
    (makeAbstractions make f)

  let nabla f =
    let make name f = Firstorderabsyn.NablaFormula(f) in
    (makeAbstractions make f)

  let anon () = Firstorderabsyn.AnonymousFormula

  let abstract id f =
    Firstorderabsyn.AbstractionFormula(id, f)

  let atom t = Firstorderabsyn.AtomicFormula(t)
    
  let application term = 
    match term with
        [] -> failwith "Firstorderparser.tterm: invalid lterm."
      | t::l -> (Term.app t l)
  
%}

%token BSLASH LPAREN RPAREN DOT SHARP ANONYMOUS
%token EQ AND OR IMP DEF
%token PI SIGMA NABLA
%token IND COIND
%token EOF
%token <string> ID
%token <string> STRING

%nonassoc BSLASH PI SIGMA NABLA MU
%right IMP
%left OR
%left AND
%nonassoc EQ

%start toplevel_formula toplevel_term toplevel_definition
%type <Firstorderabsyn.formula> toplevel_formula
%type <Firstorderabsyn.term> toplevel_term
%type <Firstorderabsyn.predefinition> toplevel_definition

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
  : ID definitionargs DEF formula   {Firstorderabsyn.PreDefinition($1, $2, $4, Firstorderabsyn.Inductive)}
  | IND ID definitionargs DEF formula   {Firstorderabsyn.PreDefinition($2, $3, $5, Firstorderabsyn.Inductive)}
  | COIND ID definitionargs DEF formula   {Firstorderabsyn.PreDefinition($2, $3, $5, Firstorderabsyn.CoInductive)}
  ;

definitionargs
  : ID definitionargs   {$1::$2}
  |                     {[]}
  ;

formula
  : formula AND formula {conj $1 $3}
  | formula OR formula {disj $1 $3}
  | formula IMP formula {imp $1 $3}
  | term EQ term {eq $1 $3}
  
  | PI formula {pi $2}
  | SIGMA formula {sigma $2}
  | NABLA formula {nabla $2}
  
  | ID BSLASH formula {abstract $1 $3}
  
  | ANONYMOUS {anon ()}
  
  | LPAREN formula RPAREN {$2}
  | term {atom $1}
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
  : LPAREN term RPAREN {$2}
  | ID {Term.atom $1}
  | STRING {Term.string $1}
  ;
%%
