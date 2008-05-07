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
/**********************************************************************
* Firstorderparser
***********************************************************************
* This is the ocamlyacc specification for the first order logic grammar.
* It is by no means a well put together grammar, but it seems to work
* well enough.
*
* The grammar has a special case for quantification: a formula may
* be quantified over a number of variables very easily by simply stringing
* lambdas together.  That is, the following two lines are equivalent.
*   sigma x\ y\ z\ ...
*   sigma x\ sigma y\ sigma z\ ...
* The same holds for pi and nabla.
*
* Templates are handled in a relatively tricky way: underscores indicate
* "holes" in a formula level pattern, but are indicated by term-level
* variables.  Furthermore, explicit mu.nu quantification patterns are allowed
* as well, in order to allow the user to write templates that match only
* mu/nu application formulas.
**********************************************************************/
%{
  module FOA = Firstorderabsyn
  
  let eqFormula t1 t2 = (FOA.Synchronous,FOA.`EqualityFormula(t1, t2))
  let connFormula p c f1 f2 = (p,FOA.`BinaryFormula(c,f1,f2)
  
  (********************************************************************
  *getAbstractions:
  * Returns a list of the toplevel abstractions on a formula, and the
  * formula immediately beneath said abstractions.
  ********************************************************************)
  let rec getAbstractions (f : ('a,'b) FOA._abstraction) =
    match f with
        FOA.`AbstractionFormula(name, f') ->
          let (names,f'') = (getAbstractions f') in
          (name::names, f'')
      | _ -> ([], f)
(* |`Wildcard -> ([],`Wildcard)*)

  (********************************************************************
  *makeAbstractions:
  * Given a constructor function and a formula, peels all toplevel
  * abstractions from the formula and then reapplies them with the
  * correct quantification formula "on top of" each abstraction.  The
  * quantification is made by the constructor function.
  ********************************************************************)
  let makeAbstractions make f =
    let rec makeAbs' names make f =
      match names with
        [] ->
          let f = FOA.string_of_formula ~generic:[] f in
          let msg = "argument does not have toplevel abstractions: " ^ f in
            raise (FOA.SemanticError msg)
      | [name] -> make (FOA.`AbstractionFormula(name,f))
      | name::names ->
          make (`FOA.AbstractionFormula(name, makeAbs' (names) make f))
    in
(*    if (FOA.isAnonymousFormula f) then
      make f
    else *)
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

  (********************************************************************
  *atomic:
  * Constructs an atomic formula from a term by splitting the term
  * into a head (a string) and a list of arguments (terms).
  ********************************************************************)
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
  
  (********************************************************************
  *definition:
  * Creates a predefinition with a body that has already been abstracted
  * over the argument names.
  ********************************************************************)
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

%nonassoc BSLASH
%nonassoc PI SIGMA NABLA MU NU
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

  | binder formula %prec BSLASH
                  { let (free, name) = $1 in
                    let abs = abstract name $2 in
                      if free then Term.free name ;
                      abs }

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
  | LPAREN binder term RPAREN
                        {let (free,name) = $2 in
                         let abs = Term.abstract (Term.atom name) $3 in
                           if free then Term.free name ;
                           abs}
  ;
%%
