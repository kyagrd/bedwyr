exception SyntaxError of string
exception SemanticError of string
exception InvalidAnonymous of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * formula
  | AbstractionFormula of string * formula
  | MuApplicationFormula of formula * term list
  | AtomicApplicationFormula of string * term list
  | DBFormula of int
  | AnonymousFormula

type predefinition =
  PreDefinition of (string * string list * formula)

type definition =
  Definition of (string * int * formula)

let getMuFormulaName = function
    MuFormula(name,_) -> name
  | _ -> failwith "Firstorderabsyn.getMuFormulaName: invalid formula."

let getDefinitionArity (Definition(_,a,_)) = a
let getDefinitionBody (Definition(_,_,b)) = b

let string_of_term t =
  Pprint.term_to_string t

let rec string_of_formula f =
  match f with
      AndFormula(l,r) -> "(" ^ (string_of_formula l) ^ ", " ^ (string_of_formula r) ^ ")"
    | OrFormula(l,r) -> "(" ^ (string_of_formula l) ^ "; " ^ (string_of_formula r) ^ ")"
    | ImplicationFormula(l,r) -> "(" ^ (string_of_formula l) ^ " -> " ^ (string_of_formula r) ^ ")"
    | EqualityFormula(l,r) -> "(" ^ (Pprint.term_to_string l) ^ " = " ^ (Pprint.term_to_string r) ^ ")"
    | PiFormula(f) -> "pi " ^ (string_of_formula f)
    | SigmaFormula(f) -> "sigma " ^ (string_of_formula f)
    | NablaFormula(f) -> "nabla " ^ (string_of_formula f)
    | MuFormula(name, f) -> name ^ " " ^ (string_of_formula f)
    | AbstractionFormula(name, f) -> (string_of_formula f)
    | MuApplicationFormula(mu,tl) ->
        (getMuFormulaName mu) ^ " " ^
          (String.concat " " (List.map (Pprint.term_to_string) tl))
    | AtomicApplicationFormula(hd, tl) ->
        hd ^ " " ^ (String.concat " " (List.map (Pprint.term_to_string) tl))
    | DBFormula(i) -> "#" ^ (string_of_int i)
    | AnonymousFormula -> "_"
    
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
    | AbstractionFormula(name, f) -> AbstractionFormula(name, formulafun f)
    | MuApplicationFormula(head, tl) -> MuApplicationFormula(formulafun head, List.map termfun tl)
    | AtomicApplicationFormula(head, tl) -> AtomicApplicationFormula(head, List.map termfun tl)
    | DBFormula(i) -> f
    | AnonymousFormula -> raise (InvalidAnonymous "Firstorderabsyn.mapFormula")


(**********************************************************************
*abstract:
* Note that this doesn't push a term-level abstraction through
* mu abstractions.
**********************************************************************)
let rec abstract var formula =
  let rec termFun t = Term.abstract_var var t
  and formulaFun f =
    match f with
      MuFormula(_) -> f
    | _ -> (mapFormula formulaFun termFun f)
  in
  (formulaFun formula)

let rec apply terms formula =
  let rec termFun t = Term.app t terms
  and formulaFun f = mapFormula formulaFun termFun f in
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
* Performs unification as on the right.  If unification is successful
* it calls the success continuation with the failure continuation in
* the place of "continue".  Otherwise, it calls the failure
* continuation
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

(********************************************************************
*leftUnify:
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


let anonymousTermTemplate () = (Term.fresh ~tag:Term.Eigen ~lts:0 0)
let anonymousFormulaTemplate () = AnonymousFormula

let matchFormula template formula =
  let success ur =
    match ur with
      UnifySucceeded -> true
    | _ -> false
  in
  
  let state = Term.save_state () in
  let rec search template formula =
    match (template, formula) with
      (AnonymousFormula, _) -> true
    | (_, AnonymousFormula) -> raise (InvalidAnonymous "Firstorderabsyn.matchFormula")
    
    | (AndFormula(l,r), AndFormula(l', r'))
    | (OrFormula(l,r), OrFormula(l', r'))
    | (ImplicationFormula(l,r), ImplicationFormula(l', r')) ->
        (search l l') && (search r r')
    
    | (EqualityFormula(t1, t2), EqualityFormula(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t1 t1'))

    | (AtomicApplicationFormula(h,t), AtomicApplicationFormula(h',t')) ->
        if h = h' then
          (List.exists success (List.map2 rightUnify t t'))
        else
          false

    | (PiFormula(f), PiFormula(f'))
    | (SigmaFormula(f), SigmaFormula(f'))
    | (NablaFormula(f), NablaFormula(f')) ->
        (search f f')
    | (_, _) -> false
  in
  if (search template formula) then
    (Term.restore_state state;
    true)
  else
    (Term.restore_state state;
    false)

let containsAnonymous f =
  let tf t = t in
  let rec ff f = (mapFormula ff tf f) in
  try
    let _ = (ff f) in
    false
  with
    InvalidAnonymous _ -> true

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
  | _ -> None

let getTermHead t =
  let result = getTermHeadAndArgs t in
  if Option.isSome result then
    let (h,_) = (Option.get result) in
    Some h
  else
    None

let applyMu arg formula =
  let tf t = t in
  let rec ff i f =
    match f with
        MuFormula(name,body) ->
          (mapFormula (ff (i + 1)) tf body)
      | DBFormula(i') ->
          if i = i' then
            arg
          else
            f
      | _ -> (mapFormula (ff i) tf f)
  in
  ff 1 formula