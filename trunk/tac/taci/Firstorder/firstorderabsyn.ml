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
exception SyntaxError of string
exception SemanticError of string

type term = Term.term

type formula =
    AndFormula of (formula * formula)
  | OrFormula of (formula * formula)
  | ImplicationFormula of (formula * formula)
  | EqualityFormula of (term * term)
  | PiFormula of formula
  | SigmaFormula of formula
  | NablaFormula of formula
  | MuFormula of string * string list * formula
  | NuFormula of string * string list * formula
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

let getConnective = function
    AndFormula(_) -> ", "
  | OrFormula(_) -> "; "
  | ImplicationFormula(_) -> " => "
  | EqualityFormula(_) -> " = "
  | _ -> ""

let getConnectiveName = function
    AndFormula(_) -> "and"
  | OrFormula(_) -> "or"
  | ImplicationFormula(_) -> "imp"
  | EqualityFormula(_) -> "eq"
  | _ -> ""

let rec getFormulaName = function
    MuFormula(name,_,_) -> name
  | NuFormula(name,_,_) -> name
  | DBFormula(name,_) -> name
  | f -> string_of_formula f

and string_of_term names t =
  Pprint.term_to_string_preabstracted names t

and string_of_term_ast t =
  Pprint.term_to_string t

and string_of_formula ?(names=[]) f =
  match f with
      AndFormula(l,r)
    | OrFormula(l,r)
    | ImplicationFormula(l,r) ->
        let s1 = (string_of_formula ~names l) in
        let s2 = (string_of_formula ~names r) in
        "(" ^ s1 ^ (getConnective f) ^ s2 ^ ")"
    | EqualityFormula(l,r) ->
        let s1 = (string_of_term names l) in
        let s2 = (string_of_term names r) in
        "(" ^ s1 ^ " = " ^ s2 ^ ")"
    | PiFormula(f) -> "pi " ^ (string_of_formula ~names f)
    | SigmaFormula(f) -> "sigma " ^ (string_of_formula ~names f)
    | NablaFormula(f) -> "nabla " ^ (string_of_formula ~names f)
    | MuFormula(name, _, f) -> "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")"
    | NuFormula(name, _, f) -> "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")"
    | AbstractionFormula(hint, f) ->
        let hint = Term.get_dummy_name hint in
        let s = hint ^ "\\ " ^ (string_of_formula ~names:(hint::names) f) in
        (Term.free hint;
        s)
    | ApplicationFormula(mu,tl) ->
        (getFormulaName mu) ^ " " ^
          (String.concat " " (List.map (string_of_term names) tl))
    | AtomicFormula(t) ->
        (string_of_term names t)
    | DBFormula(n,i) -> n

and string_of_formula_ast f =
  match f with
      AndFormula(l,r)
    | OrFormula(l,r)
    | ImplicationFormula(l,r) ->
        let s1 = (string_of_formula_ast l) in
        let s2 = (string_of_formula_ast r) in
        (getConnectiveName f) ^ "(" ^ s1 ^ ", " ^ s2 ^ ")"
    | EqualityFormula(l,r) ->
        let s1 = (string_of_term [] l) in
        let s2 = (string_of_term [] r) in
        "eq(" ^ s1 ^ ", " ^ s2 ^ ")"
    | PiFormula(f) -> "pi(" ^ (string_of_formula_ast f) ^ ")"
    | SigmaFormula(f) -> "sigma(" ^ (string_of_formula_ast f) ^ ")"
    | NablaFormula(f) -> "nabla(" ^ (string_of_formula_ast f) ^ ")"
    | MuFormula(name, _, f) -> "mu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | NuFormula(name, _, f) -> "nu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | AbstractionFormula(hint, f) ->
        let hint = Term.get_dummy_name hint in
        let s = "lambda(" ^ hint ^ ", " ^ (string_of_formula_ast f)  ^ ")" in
        (Term.free hint;
        s)
    | ApplicationFormula(mu,tl) ->
        (string_of_formula_ast mu) ^ " " ^
          (String.concat " " (List.map string_of_term_ast tl))
    | AtomicFormula(t) ->
        (string_of_term_ast t)
    | DBFormula(n,i) -> "#" ^ (string_of_int i)


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
    | MuFormula(name, args, f) -> MuFormula(name, args, formulafun f)
    | NuFormula(name, args, f) -> NuFormula(name, args, formulafun f)
    | AbstractionFormula(name, f) -> AbstractionFormula(name, formulafun f)
    | ApplicationFormula(head,tl) -> ApplicationFormula(formulafun head, List.map termfun tl)
    | AtomicFormula(t) -> AtomicFormula(termfun t)
    | DBFormula(n,i) -> f


(**********************************************************************
*abstract:
**********************************************************************)
let rec abstract name formula =
  let var = Term.atom name in
  let rec termFun t = Term.abstract var t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  AbstractionFormula(name, (formulaFun formula))

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
*isAnonymousTerm:
* Determines whether a term corresponds to an "_".
**********************************************************************)
let isAnonymousTerm t =
  match (Term.observe t) with
    Term.Var(v) ->
      (Term.get_hint t = "_")
  | _ -> false

let isAnonymousFormula f =
  match f with
    AtomicFormula(t) -> isAnonymousTerm t
  | _ -> false


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
    | (OrFormula(l,r), OrFormula(l', r'))
    | (ImplicationFormula(l,r), ImplicationFormula(l', r')) ->
        (search l l') && (search r r')
    
    | (EqualityFormula(t1, t2), EqualityFormula(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t1 t1'))

    | (AtomicFormula(t), AtomicFormula(t')) ->
        success (rightUnify t t')
    | (AtomicFormula(t), _)
    | (_, AtomicFormula(t)) ->
        (*  If this atomic formula is an underscore, then it matches. *)
        (isAnonymousTerm t)
        
    | (MuFormula(n,_,_), MuFormula(n',_,_))
    | (NuFormula(n,_,_), NuFormula(n',_,_)) ->
        n = n'

    | (AbstractionFormula(n,f), AbstractionFormula(n',f')) ->
        (n = n' || n = "_" || n' = "_") && (search f f')
    | (PiFormula(f), PiFormula(f'))
    | (SigmaFormula(f), SigmaFormula(f'))
    | (NablaFormula(f), NablaFormula(f')) ->
        (search f f')

    | (ApplicationFormula(MuFormula(n,_,b),args), ApplicationFormula(MuFormula(n',_,b'),args')) ->
        if isAnonymousFormula b || isAnonymousFormula b' then
          true
        else
          (n = n') && (List.exists success (List.map2 rightUnify args args'))
    | (ApplicationFormula(NuFormula(n,_,b),args), ApplicationFormula(NuFormula(n',_,b'),args')) ->
        if isAnonymousFormula b || isAnonymousFormula b' then
          true
        else
          (n = n') && (List.exists success (List.map2 rightUnify args args'))          
    | (ApplicationFormula(hd,args), ApplicationFormula(hd',args')) ->
        if (isAnonymousFormula hd) || (isAnonymousFormula hd') then
          true
        else
          (search hd hd') && (List.exists success (List.map2 rightUnify args args'))
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
  Term.get_name t

(**********************************************************************
*getTermHeadAndArgs:
* Gets the head and arguments of a term.  If the term isn't a constant,
* returns None.
**********************************************************************)
let rec getTermHeadAndArgs t =
  match Term.observe t with
    Term.App(t',args) ->
      (match (Term.observe t') with
        Term.Var(v) ->
          if v.Term.tag = Term.Constant then
            Some (Term.get_name t', args)
          else
            None
      | _ -> None)    
  | Term.Var(v) ->
      if v.Term.tag = Term.Constant then
        Some (Term.get_name t, [])
      else
        None
  | Term.Lam(_,t) -> getTermHeadAndArgs t
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
*applyFixpoint:
**********************************************************************)
let applyFixpoint arg formula =
  let tf t = t in
  let rec ff i f =
    match f with
        MuFormula(name,args,body) ->
          MuFormula(name,args, ff (i + 1) body)
      | NuFormula(name,args,body) ->
          NuFormula(name,args,ff (i + 1) body)
      | ApplicationFormula(DBFormula(n,i'),args) ->
          if i = i' then
            (arg args)
          else
            f
      | DBFormula(_) -> failwith "invalid DB"
      | _ -> (mapFormula (ff i) tf f)
  in
  ff (0) formula

(********************************************************************
*makeAnonymousTerm:
********************************************************************)
let makeAnonymousTerm () =
  Term.fresh ~name:"_" ~tag:Term.Logic ~lts:max_int ~ts:max_int

(********************************************************************
*makeAnonymousFormula:
* 
********************************************************************)
let makeAnonymousFormula () =
  AtomicFormula(makeAnonymousTerm ())
