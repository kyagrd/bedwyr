exception SyntaxError of string
exception SemanticError of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | LinearAndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | LinearOrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * formula
  | NuFormula of string * formula
  | AbstractionFormula of string * formula
  | ApplicationFormula of formula * term list
  | AtomicFormula of term
  | DBFormula of string * int

type fixpoint =
    Inductive
  | CoInductive

type predefinition =
  PreDefinition of (string * string list * formula * fixpoint)

type definition =
  Definition of (string * int * formula * fixpoint)


let getDefinitionArity (Definition(_,a,_,_)) = a
let getDefinitionBody (Definition(_,_,b,_)) = b

let string_of_term t =
  Pprint.term_to_string t

let rec getFormulaName = function
    MuFormula(name,_) -> name
  | NuFormula(name,_) -> name
  | DBFormula(name,_) -> name
  | f -> string_of_formula f

and string_of_formula f =
  match f with
      AndFormula(l,r) -> "(" ^ (string_of_formula l) ^ ", " ^ (string_of_formula r) ^ ")"
    | OrFormula(l,r) -> "(" ^ (string_of_formula l) ^ "; " ^ (string_of_formula r) ^ ")"
    | ImplicationFormula(l,r) -> "(" ^ (string_of_formula l) ^ " => " ^ (string_of_formula r) ^ ")"
    | EqualityFormula(l,r) -> "(" ^ (Pprint.term_to_string l) ^ " = " ^ (Pprint.term_to_string r) ^ ")"
    | PiFormula(f) -> "pi " ^ (string_of_formula f)
    | SigmaFormula(f) -> "sigma " ^ (string_of_formula f)
    | NablaFormula(f) -> "nabla " ^ (string_of_formula f)
    | MuFormula(name, f) -> "(" ^ name ^ " " ^ (string_of_formula f) ^ ")"
    | NuFormula(name, f) -> "(" ^ name ^ " " ^ (string_of_formula f) ^ ")"
    | AbstractionFormula(name, f) -> name ^ "\\ " ^ (string_of_formula f)
    | ApplicationFormula(mu,tl) ->
        (getFormulaName mu) ^ " " ^
          (String.concat " " (List.map (Pprint.term_to_string) tl))
    | AtomicFormula(t) ->
        (Pprint.term_to_string t)
    | DBFormula(n,i) -> n

let rec string_of_formula_ast f =
  match f with
      AndFormula(l,r) -> "and(" ^ (string_of_formula_ast l) ^ ", " ^ (string_of_formula_ast r) ^ ")"
    | OrFormula(l,r) -> "or(" ^ (string_of_formula_ast l) ^ ", " ^ (string_of_formula_ast r) ^ ")"
    | ImplicationFormula(l,r) -> "imp(" ^ (string_of_formula_ast l) ^ " -> " ^ (string_of_formula_ast r) ^ ")"
    | EqualityFormula(l,r) -> "eq(" ^ (string_of_term l) ^ ", " ^ (string_of_term r) ^ ")"
    | PiFormula(f) -> "pi(" ^ (string_of_formula_ast f) ^ ")"
    | SigmaFormula(f) -> "sigma(" ^ (string_of_formula_ast f) ^ ")"
    | NablaFormula(f) -> "nabla(" ^ (string_of_formula_ast f) ^ ")"
    | MuFormula(name, f) -> "mu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | NuFormula(name, f) -> "nu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | AbstractionFormula(name, f) -> "lambda(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | ApplicationFormula(mu,tl) ->
        "app(" ^ (string_of_formula_ast mu) ^ ", " ^
          (String.concat " " (List.map string_of_term tl)) ^ ")"
    | AtomicFormula(t) ->
        (Pprint.term_to_string t)
    | DBFormula(n,i) -> "db(" ^ n ^ ", " ^ (string_of_int i) ^ ")"

let string_of_fixpoint = function
    Inductive -> "inductive"
  | CoInductive -> "coinductive"
let string_of_definition (Definition(name,arity,body,ind)) =
  (string_of_fixpoint ind) ^ " " ^ (string_of_formula body)
    
let mapFormula formulafun termfun f =
  match f with
      AndFormula(l,r) -> AndFormula(formulafun l, formulafun r)
    | OrFormula(l,r) -> OrFormula(formulafun l, formulafun r)
    | ImplicationFormula(l,r) -> ImplicationFormula(formulafun l, formulafun r)
    | EqualityFormula(l,r) -> EqualityFormula(termfun l, termfun r)
    | PiFormula(f) -> PiFormula(formulafun f)
    | SigmaFormula(f) -> SigmaFormula(formulafun f)
    | NablaFormula(f) -> NablaFormula(formulafun f)
    | MuFormula(name, f) -> MuFormula(name, formulafun f)
    | NuFormula(name, f) -> NuFormula(name, formulafun f)
    | AbstractionFormula(name, f) -> AbstractionFormula(name, formulafun f)
    | ApplicationFormula(head,tl) -> ApplicationFormula(formulafun head, List.map termfun tl)
    | AtomicFormula(t) -> AtomicFormula(termfun t)
    | DBFormula(n,i) -> f


(**********************************************************************
*abstract:
* Note that this doesn't push a term-level abstraction through
* mu/nu abstractions.
**********************************************************************)
let rec abstract name formula =
  let var = Term.atom name in
  let rec termFun t = Term.abstract_var var t
  and formulaFun f =
    match f with
      AbstractionFormula(n,f') ->
        if name = n then
          let name' = "you_can't_see_me!" in
          AbstractionFormula(n, (abstract name' f'))
        else
          AbstractionFormula(n, formulaFun f')
    | MuFormula(_)
    | NuFormula(_) -> f
    | _ -> (mapFormula formulaFun termFun f)
  in
  (formulaFun formula)

(**********************************************************************
*apply:
* Note that this doesn't push a term-level application through
* mu/nu abstractions.
**********************************************************************)
let rec apply terms formula =
  let rec termFun t = Term.app t terms
  and formulaFun f = 
    match f with
        MuFormula(_)
      | NuFormula(_) -> f
      | _ -> (mapFormula formulaFun termFun f)
  in
  (formulaFun formula)

type unifyresult =
    UnifyFailed
  | UnifySucceeded
  | UnifyError of string

(********************************************************************
*Right, Left:
* Unification modules for right and left unification.
********************************************************************)
module Right =
  Unify.Make (struct
                let instantiatable = Term.Logic
                let constant_like = Term.Eigen
              end)
module Left =
  Unify.Make (struct
                let instantiatable = Term.Eigen
                let constant_like = Term.Constant
              end)

(********************************************************************
*rightUnify:
* Performs unification on the right of the turnstile.
********************************************************************)
let rightUnify a b =
  let state = Term.save_state () in
  try
    (Right.pattern_unify a b;
    UnifySucceeded)
  with
      Unify.Error _ -> (Term.restore_state state; UnifyFailed)
    | Failure s -> (Term.restore_state state; UnifyError s)
    | Unify.NotLLambda t ->
        (Term.restore_state state; 
        UnifyError ("unification outside of higher-order patterns."))

(********************************************************************
*leftUnify:
* Performs unification on the left of the turnstile.
********************************************************************)
let leftUnify a b =
  let state = Term.save_state () in    
  try
    (Left.pattern_unify a b;
    UnifySucceeded)
  with
      Unify.Error _ -> (Term.restore_state state; UnifyFailed)
    | Failure s -> (Term.restore_state state; UnifyError s)
    | Unify.NotLLambda t ->
        (Term.restore_state state; 
        UnifyError ("unification outside of higher-order patterns."))

(**********************************************************************
*unifyList:
* Given a 2 lists of terms, attempts to unify each term in the first
* list with the corresponding term in the second using the passed
* unification function.  If the lists are of different lengths it fails.
* If any unification fails it fails.
**********************************************************************)
let unifyList unifier l1 l2 =
  let rec unify l1 l2 =
    match (l1,l2) with
        (l1hd::l1tl, l2hd::l2tl) ->
          (match (unifier l1hd l2hd) with
              UnifySucceeded -> unify l1tl l2tl
            | UnifyFailed -> UnifyFailed
            | UnifyError _ as u -> u)
      | ([],[]) -> UnifySucceeded
      | (_,_) -> UnifyFailed
  in
  unify l1 l2


(**********************************************************************
*matchFormula:
* Match a template with a formula.  If the match succeeds, returns true,
* otherwise returns false.
**********************************************************************)
let matchFormula template formula =
  let success ur =
    match ur with
      UnifySucceeded -> true
    | _ -> false
  in
  
  (*  Keep track of binding state to undo it later. *)
  let state = Term.save_state () in
  
  (********************************************************************
  *search:
  * Recurse over the structure of two formulas.
  ********************************************************************)
  let rec search template formula =
    match (template, formula) with
      (AndFormula(l,r), AndFormula(l', r'))
    | (LinearAndFormula(l,r), LinearAndFormula(l', r'))
    | (OrFormula(l,r), OrFormula(l', r'))
    | (LinearOrFormula(l,r), LinearOrFormula(l', r'))
    | (ImplicationFormula(l,r), ImplicationFormula(l', r')) ->
        (search l l') && (search r r')
    
    | (EqualityFormula(t1, t2), EqualityFormula(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t1 t1'))

    | (AtomicFormula(t), AtomicFormula(t')) ->
        success (rightUnify t t')
    | (AtomicFormula(t), _) ->
        (*  If this atomic formula is an underscore, then it matches. *)
        false
    | (PiFormula(f), PiFormula(f'))
    | (SigmaFormula(f), SigmaFormula(f'))
    | (NablaFormula(f), NablaFormula(f')) ->
        (search f f')
    | (_, _) -> false
  in
  let result = (search template formula) in
  
  (*  Restore the binding state so later matches can work,
      and return the result.  *)
  (Term.restore_state state;
  result)

(**********************************************************************
*getTermVarName:
* Gets the name of the head of a term (if it is a constant).
**********************************************************************)
let getTermVarName t =
  match Term.observe t with
    Term.Var(v) ->
      if v.Term.tag = Term.Constant then
        (v.Term.name)
      else
        failwith "Linearabsyn.getTermVarName: invalid term."
  | _ -> failwith "Linearabsyn.getTermVarName: invalid term."

(**********************************************************************
*getTermHeadAndArgs:
* Gets the head and arguments of a term.  If the term isn't a constant,
* returns None.
**********************************************************************)
let getTermHeadAndArgs t =
  match Term.observe t with
    Term.App(t',args) ->
      (match (Term.observe t') with
        Term.Var(v) ->
          if v.Term.tag = Term.Constant then
            Some (v.Term.name, args)
          else
            None
      | _ -> None)    
  | Term.Var(v) ->
      if v.Term.tag = Term.Constant then
        Some (v.Term.name, [])
      else
        None
  | _ -> None

(**********************************************************************
*getTermHead:
* Gets just the head of a term in a similar way to getTermHeadAndArgs.
**********************************************************************)
let getTermHead t =
  let result = getTermHeadAndArgs t in
  if Option.isSome result then
    let (h,_) = (Option.get result) in
    Some h
  else
    None

(**********************************************************************
*renameAbstractions:
**********************************************************************)
let renameAbstractions formula =      
  let tf t = t in
  let rec ff f =
    match f with
        AbstractionFormula(n,f') ->
          let f'' = abstract n f' in
          let var' = Term.fresh_atom (Term.atom n) in
          let f''' = (apply [var'] f'') in
          AbstractionFormula(getTermVarName var', (ff f'''))
      | _ -> (mapFormula ff tf f)
  in
  ff formula

(**********************************************************************
*applyFixpoint:
**********************************************************************)
let applyFixpoint arg formula =
  let tf t = t in
  let rec ff i f =
    match f with
        MuFormula(name,body) ->
          MuFormula(name, ff (i + 1) body)
      | NuFormula(name,body) ->
          NuFormula(name, ff (i + 1) body)
      | ApplicationFormula(DBFormula(n,i'),args) ->
          if i = i' then
            (arg args)
          else
            f
      | DBFormula(_) -> failwith "invalid DB"
      | _ -> (mapFormula (ff i) tf f)
  in
  ff (0) formula
