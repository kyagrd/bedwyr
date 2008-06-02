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

  let default f =
    (FOA.defaultPatternAnnotation, f)

  let frozen f =
    let (p,f') = f in
    ({p with FOA.freezing_pattern = Some FOA.Frozen}, f')
  
  let focused f =
    let (p,f') = f in
    ({p with FOA.control_pattern = Some FOA.Focused}, f')
  
  let positive f =
    let (p,f') = f in
    ({p with FOA.polarity_pattern = Some FOA.Positive}, f')

  let negative f =
    let (p,f') = f in
    ({p with FOA.polarity_pattern = Some FOA.Negative}, f')

  let eqFormula f1 f2 = default (FOA.EqualityPattern(f1, f2))
  let binaryFormula f1 f2 c = default (FOA.BinaryPattern(c, f1, f2))
 
  (********************************************************************
  *getAbstractions:
  * Returns a list of the toplevel abstractions on a formula, and the
  * formula immediately beneath said abstractions.
  ********************************************************************)
  let rec getAbstractions f =
    match f with
        FOA.AbstractionPattern(name, f') ->
          let (names,f'') = (getAbstractions f') in
          (name::names, f'')
      | FOA.AbstractionBodyPattern(f) -> ([], f)
      | FOA.AnonymousAbstraction ->
          ([FOA.anonymousBinder], (default (FOA.ApplicationPattern(FOA.AnonymousPredicate, []))))

  (********************************************************************
  *makeAbstractions:
  * Given a constructor function and a formula, peels all toplevel
  * abstractions from the formula and then reapplies them with the
  * correct quantification formula "on top of" each abstraction.  The
  * quantification is made by the constructor function.
  ********************************************************************)
  let makeAbstractions formulaConstructor f =
    let rec makeAbs' names make f =
      match names with
        [] ->
          let msg = "argument does not have toplevel abstractions" in
            raise (FOA.SemanticError msg)
      | [name] ->
          (formulaConstructor name (FOA.AbstractionBodyPattern(f)))
      | name::names ->
         formulaConstructor name (FOA.AbstractionBodyPattern(makeAbs' names formulaConstructor f))
    in
    let (names,f') = getAbstractions f in
    (makeAbs' names formulaConstructor f')

  let quantified pol q body =
    let make name body = pol (FOA.QuantifiedPattern(q, FOA.AbstractionPattern(name, body))) in
    (makeAbstractions make body)

  (********************************************************************
  *atomic:
  * Constructs an atomic formula from a term by splitting the term
  * into a head (a string) and a list of arguments (terms).
  ********************************************************************)
  let atomic t =
    let result = FOA.getTermHeadAndArgs t in
    if (Option.isSome result) then
      let (head,args) = Option.get result in
      if head = "_" then
        default (FOA.ApplicationPattern(FOA.AnonymousPredicate, args))
      else
        default (FOA.ApplicationPattern(FOA.AtomicPattern(head), args))
    else
      raise (FOA.SemanticError("term is neither a first order application nor an atom"))

  let anonymousTerm () = FOA.makeAnonymousTerm ()
  let atom t = Term.atom t
  
  let abstract id f =
    (FOA.abstractPattern id).FOA.abstp f
    
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
    let (argnames, _, p) = Listutils.split3 args in

    let free (name, f, _) =
      if f then
        (Term.free name)
      else
        ()
    in
    let body' = FOA.AbstractionBodyPattern(body) in
    let result =
      FOA.PreDefinition(
        name,
        List.combine argnames p,
        List.fold_right abstract argnames body',
        fix)
    in
    (List.iter free args;
    result)
%}

%token BSLASH LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK UNDERSCORE
%token EQ AND AND OR WITH PAR IMP DEF
%token PI SIGMA NABLA MU NU
%token PLUS MINUS STAR
%token IND COIND
%token EOF
%token <string> ID
%token <string> STRING

%nonassoc BSLASH
%nonassoc PI SIGMA NABLA MU NU
%right IMP
%left OR PAR
%left AND WITH
%nonassoc EQ
%nonassoc PLUS MINUS
%nonassoc STAR

%start toplevel_pattern toplevel_term toplevel_definition toplevel_invariant
%type <Firstorderabsyn.pattern_annotation Firstorderabsyn.polarized_pattern> toplevel_pattern pattern
%type <Firstorderabsyn.term> toplevel_term
%type <Firstorderabsyn.pattern_annotation Firstorderabsyn.predefinition> toplevel_definition
%type <Firstorderabsyn.pattern_annotation Firstorderabsyn.abstraction_pattern> toplevel_invariant

%%
toplevel_pattern
  : pattern           {$1}
  | pattern EOF       {$1}
  ;

toplevel_invariant
  : abstracted_pattern  {$1}
  ;

toplevel_definition
  : def      {$1}
  | def EOF  {$1}
  ;

def
  : ID definition_args DEF pattern         {(definition $1 $2 $4 FOA.Inductive)}
  | IND ID definition_args DEF pattern     {(definition $2 $3 $5 FOA.Inductive)}
  | COIND ID definition_args DEF pattern   {(definition $2 $3 $5 FOA.CoInductive)}
  ;

definition_args
  : arg definition_args  {let (id, _, _) = $1 in
                          if List.exists (fun (id',_,_) -> id = id') $2 then
                            raise (FOA.SemanticError("argument appears more than once"))
                          else
                            $1::$2}
  |                      {[]}
  ;

arg
  : ID                {($1, Term.is_free $1, FOA.Unknown)}
  | LBRACE ID RBRACE  {($2, Term.is_free $2, FOA.Progressing)}
  ;

pattern
  : MU UNDERSCORE     {default (FOA.ApplicationPattern(FOA.AnonymousMu, []))}
  | NU UNDERSCORE     {default (FOA.ApplicationPattern(FOA.AnonymousNu, []))}
  | PI UNDERSCORE     {default (FOA.QuantifiedPattern(FOA.Pi, FOA.AnonymousAbstraction))}
  | SIGMA UNDERSCORE  {default (FOA.QuantifiedPattern(FOA.Sigma, FOA.AnonymousAbstraction))}
  | NABLA UNDERSCORE  {default (FOA.QuantifiedPattern(FOA.Nabla, FOA.AnonymousAbstraction))}

  | pattern AND pattern   {positive (binaryFormula $1 $3 FOA.And)}
  | pattern OR pattern    {positive (binaryFormula $1 $3 FOA.Or)}
  | pattern WITH pattern  {positive (binaryFormula $1 $3 FOA.And)}
  | pattern PAR pattern   {positive (binaryFormula $1 $3 FOA.Or)}
  | pattern IMP pattern   {positive (binaryFormula $1 $3 FOA.Imp)}
  | term EQ term          {eqFormula $1 $3}
  
  | PI abstracted_pattern     {quantified default FOA.Pi $2}
  | SIGMA abstracted_pattern  {quantified default FOA.Sigma $2}
  | NABLA abstracted_pattern  {quantified default FOA.Nabla $2}

  | LPAREN pattern RPAREN     {$2}
  | LBRACK pattern RBRACK     {(focused $2)}
  | atom                      {$1}
  ;

atom
  : term            {(atomic $1)}
  | term STAR       {(frozen (atomic $1))}
  | PLUS term       {positive (atomic $2)}
  | PLUS term STAR  {positive (frozen (atomic $2))}
  | MINUS term      {negative (atomic $2)}
  | MINUS term STAR {negative (frozen (atomic $2))}
  ;

abstracted_pattern
  : binder abstracted_pattern %prec BSLASH  { let (name, free) = $1 in
                                              let abs = abstract name $2 in
                                              if free then
                                                Term.free name ;
                                              abs}
  | binder pattern %prec BSLASH             { let (name, free) = $1 in
                                              let abs = abstract name (FOA.AbstractionBodyPattern($2)) in
                                              if free then
                                                Term.free name ;
                                              abs}
  ;

binder
  : ID BSLASH                 {($1, Term.is_free $1)}
  | UNDERSCORE BSLASH         {("_", false)}
  ;

toplevel_term
  : term      {$1}
  | term EOF  {$1}
  ;

term
  : lterm             {application $1}
  ;

lterm
  : primaryterm       {[$1]}
  | primaryterm lterm {$1::$2}
  ;

primaryterm
  : LPAREN term RPAREN  {$2}
  | ID                  {atom $1}
  | STRING              {Term.string $1}
  | UNDERSCORE          {anonymousTerm ()}   
  | LPAREN binder term RPAREN
                        { let (name,free) = $2 in
                          let abs = Term.abstract (Term.atom name) $3 in
                          if free then Term.free name ;
                          abs}
  ;

%%
