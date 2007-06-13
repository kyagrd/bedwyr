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
  
  let rec getAbstractions f =
    match f with
        Firstorderabsyn.AbstractionFormula(name, f') ->
          let (i,f'') = (getAbstractions f') in
          (i + 1, f'')
      | _ -> (0, f)

  let makeAbstractions make f =
    let rec makeAbs' i make f =
      if (i <= 0) then
        raise (Firstorderabsyn.SemanticError ("argument does not have toplevel abstractions: " ^ (Firstorderabsyn.string_of_formula f)))
      else if (i = 1) then
        make f
      else
        (makeAbs' (i - 1) make (make f))
    in
    let (num,f') = getAbstractions f in
    (makeAbs' num make f')

  let pi f =
    let make f = Firstorderabsyn.PiFormula(f) in
    (makeAbstractions make f)

  let sigma f =
    let make f = Firstorderabsyn.SigmaFormula(f) in
    (makeAbstractions make f)

  let nabla f =
    let make f = Firstorderabsyn.NablaFormula(f) in
    (makeAbstractions make f)

  let anon () = Firstorderabsyn.AnonymousFormula

  let abstract id f =
    (Firstorderabsyn.AbstractionFormula(
      id,
      Firstorderabsyn.abstract (Term.atom id) f))

  let atom t =
    let result = Firstorderabsyn.getTermHeadAndArgs t in
    if Option.isSome result then
      let (head,args) = Option.get result in
      Firstorderabsyn.AtomicApplicationFormula(head,args)
    else
      raise (Firstorderabsyn.SemanticError
        ("term has non-atomic head: " ^ (Firstorderabsyn.string_of_term t)))
  
  exception HasAbstractions
  let hasFormulaAbstractions f =      
    let tf t = t in
    let rec ff f =
      match f with
          Firstorderabsyn.AbstractionFormula(_) -> raise HasAbstractions
        | _ -> (Firstorderabsyn.mapFormula ff tf f)
    in
    try
      let _ = (ff f) in
      false
    with
      HasAbstractions -> true
  
  let tterm term = 
    match term with
        [] -> failwith "Firstorderparser.tterm: invalid lterm."
      | t::l -> (Term.app t l)
  
  let analyzeFormula f =
    if (hasFormulaAbstractions f) then
      raise (Firstorderabsyn.SemanticError ("formula has toplevel abstractions: " ^ (Firstorderabsyn.string_of_formula f)))
    else
    f

  let analyzeDefinition d =
    d
%}

%token BSLASH LPAREN RPAREN DOT SHARP ANONYMOUS
%token EQ AND OR IMP DEF
%token PI SIGMA NABLA MU LAMBDA
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
  : formula     {analyzeFormula $1}
  | formula EOF {analyzeFormula $1}
  ;

toplevel_definition
  : definition      {analyzeDefinition $1}
  | definition EOF  {analyzeDefinition $1}
  ;

definition
  : ID definitionargs DEF formula   {Firstorderabsyn.PreDefinition($1, $2, $4)}
  | ID DEF formula                  {Firstorderabsyn.PreDefinition($1, [] ,$3)}
  ;

definitionargs
  : ID definitionargs   {$1::$2}
  | ID                  {$1::[]}
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
  : lterm {tterm $1}
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
