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
  module FOA = Firstorderabsyn
  
  let eqFormula f1 f2 = FOA.EqualityFormula(f1, f2)
  let andFormula f1 f2 = FOA.AndFormula(f1, f2)
  let orFormula f1 f2 = FOA.OrFormula(f1, f2)
  let impFormula f1 f2 = FOA.ImplicationFormula(f1, f2)
  
  let rec getAbstractions f =
    match f with
        FOA.AbstractionFormula(name, f') ->
          let (names,f'') = (getAbstractions f') in
          (name::names, f'')
      | _ -> ([], f)

  let makeAbstractions make f =
    let rec makeAbs' names make f =
      match names with
        [] -> raise (FOA.SemanticError ("argument does not have toplevel abstractions: " ^ (FOA.string_of_formula f)))
      | [name] -> make (FOA.AbstractionFormula(name,f))
      | name::names ->
          make (FOA.AbstractionFormula(name, makeAbs' (names) make f))
    in
    if (FOA.isAnonymousFormula f) then
      make f
    else
      let (names,f') = getAbstractions f in
      (makeAbs' names make f')

  let pi f =
    let make f = FOA.PiFormula(f) in
    (makeAbstractions make f)

  let sigma f =
    let make f = FOA.SigmaFormula(f) in
    (makeAbstractions make f)

  let nabla f =
    let make f = FOA.NablaFormula(f) in
    (makeAbstractions make f)

  let atomic t =
    let result = FOA.getTermHeadAndArgs t in
    if (Option.isSome result) then
      let (head,args) = Option.get result in
      FOA.AtomicFormula(head, args)
    else
      raise (FOA.SemanticError("term is neither a first order application nor an atom"))

  let anonymous () = FOA.makeAnonymousTerm ()
  let atom t = Term.atom t
  
  let abstract id f =
    FOA.abstract id f
    
  let application tlist =
    match tlist with
        [] -> failwith "Firstorder.application: invalid lterm."
      | head::tl -> Term.app head tl
  
  let definition name args body fix =
    let (_,argnames) = List.split args in
    let abstract arg f =
      FOA.abstract arg f
    in
    let free (f,name) =
      if f then
        (Term.free name)
      else
        ()
    in
    let result = FOA.PreDefinition(name,argnames,List.fold_right abstract argnames body,fix) in
    (List.iter free args;
    result)
%}

%token BSLASH LPAREN RPAREN DOT SHARP UNDERSCORE
%token EQ AND ANDL OR ORL IMP DEF
%token PI SIGMA NABLA MU NU
%token IND COIND
%token EOF
%token <string> ID
%token <string> STRING

%nonassoc BSLASH PI SIGMA NABLA MU NU
%right IMP
%left OR ORL
%left AND ANDL
%nonassoc EQ

%start toplevel_formula toplevel_term toplevel_definition toplevel_template
%type <Firstorderabsyn.formula> toplevel_formula toplevel_template
%type <Firstorderabsyn.term> toplevel_term
%type <Firstorderabsyn.predefinition> toplevel_definition

%%
toplevel_formula
  : formula     {$1}
  | formula EOF {$1}
  ;

toplevel_template
  : formula           {$1}
  | formula EOF       {$1}
  | template          {$1}
  | template EOF      {$1}
  ;

template
  : MU UNDERSCORE     {FOA.ApplicationFormula(FOA.MuFormula("_", [], FOA.makeAnonymousFormula  ()), [])}
  | NU UNDERSCORE     {FOA.ApplicationFormula(FOA.NuFormula("_", [], FOA.makeAnonymousFormula  ()), [])}
  ;

toplevel_definition
  : def      {$1}
  | def EOF  {$1}
  ;

def
  : ID definitionargs DEF formula         {(definition $1 $2 $4 FOA.Inductive)}
  | IND ID definitionargs DEF formula     {(definition $2 $3 $5 FOA.Inductive)}
  | COIND ID definitionargs DEF formula   {(definition $2 $3 $5 FOA.CoInductive)}
  ;

definitionargs
  : ID definitionargs   {let free = Term.is_free $1 in
                        let result = (free, $1) in
                        if List.exists ((=) result) $2 then
                          raise (FOA.SemanticError("argument appears more than once"))
                        else
                          result::$2}
  |                     {[]}
  ;

formula
  : formula AND formula {andFormula $1 $3}
  | formula OR formula {orFormula $1 $3}
  | formula IMP formula {impFormula $1 $3}
  | term EQ term {eqFormula $1 $3}
  
  | PI formula    {pi $2}
  | SIGMA formula {sigma $2}
  | NABLA formula {nabla $2}
  
  | binder formula            {let (free, name) = $1 in
                              let abs = abstract name $2 in
                              if (free) then
                                (Term.free name;
                                abs)
                              else
                                abs}
  
  | LPAREN formula RPAREN     {$2}
  | term                      {atomic $1}
  ;

binder
  : ID BSLASH                 {(Term.is_free $1, $1)}
  | UNDERSCORE BSLASH         {(false, "_")}
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
  | UNDERSCORE          {anonymous ()}   
  ;
%%
