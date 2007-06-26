%{
  let eq f1 f2 = Linearabsyn.EqualityFormula(f1, f2)
  let andFormulaL f1 f2 = Linearabsyn.LinearAndFormula(f1, f2)
  let andFormula f1 f2 = Linearabsyn.AndFormula(f1, f2)
  let orFormulaL f1 f2 = Linearabsyn.LinearOrFormula(f1, f2)
  let orFormula f1 f2 = Linearabsyn.OrFormula(f1, f2)
  let imp f1 f2 = Linearabsyn.ImplicationFormula(f1, f2)
  
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

  let anon () = Linearabsyn.AnonymousFormula

  let abstract id f =
    Linearabsyn.AbstractionFormula(id, f)

  let atom t = Linearabsyn.AtomicFormula(t)
    
  let application term = 
    match term with
        [] -> failwith "Linearparser.tterm: invalid lterm."
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
  : formula AND formula {andFormulaL $1 $3}
  : formula AND formula {andFormula $1 $3}
  | formula OR formula {orFormulaL $1 $3}
  | formula OR formula {orFormula $1 $3}
  | formula IMP formula {impFormula $1 $3}
  | term EQ term {eq $1 $3}
  
  | PI formula {pi $2}
  | SIGMA formula {sigma $2}
  | NABLA formula {nabla $2}
  
  | ID BSLASH formula {abstract $1 $3}
  
  | ANONYMOUS {anon ()}
  
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
  | UNDERSCORE          
  ;
%%
