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
  | AtomicFormula of string * term list
  | DBFormula of int * string * int

type fixpoint =
    Inductive
  | CoInductive

type predefinition =
  PreDefinition of (string * string list * formula * fixpoint)

type definition =
  Definition of (string * int * formula * fixpoint)


(**********************************************************************
*getTermHeadAndArgs:
* Gets the head and arguments of a term.  If the term isn't a constant,
* returns None.
**********************************************************************)
let getTermHeadAndArgs t =
  let t' = Term.observe t in
  match t' with
    Term.App(t',args) ->
      (match (Term.observe t') with
        Term.Var(v) ->
          if v.Term.tag = Term.Constant then
            Some (Term.get_name t', args)
          else
            None
      | _ -> None)    
  | Term.Var(v) ->
      Some (Term.get_hint t, [])
  | _ -> None
  
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
  | PiFormula(_) -> "pi"
  | SigmaFormula(_) -> "sigma"
  | NablaFormula(_) -> "nabla"
  | MuFormula(_) -> "mu"
  | NuFormula(_) -> "nu"
  | ApplicationFormula(_) -> "app"
  | DBFormula(_) -> "db"
  | AtomicFormula(_) -> "atom"
  | AbstractionFormula(_) -> "lambda"

let getFormulaName = function
    MuFormula(name,_,_) -> name
  | NuFormula(name,_,_) -> name
  | DBFormula(_,name,_) -> name
  | AtomicFormula(name,args) ->
      (* This actually happens, the pattern "_ ..." matches any application,
       * not only atoms but also fixed points, and is thus represented by
       * App(Atom("_",[]),...). *)
      assert (name="_"&& args=[]) ;
      name
  | _ -> assert false

let mapFormula formulafun termfun formula =
  match formula with
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
    | ApplicationFormula(head,tl) ->
        ApplicationFormula(formulafun head, List.map termfun tl)
    | AtomicFormula(head, tl) -> AtomicFormula(head, List.map termfun tl)
    | DBFormula(_,n,i) -> formula

let rec string_of_term ~generic names t =
  Pprint.term_to_string_preabstracted ~generic ~bound:names t

and string_of_term_ast ~generic t =
  Pprint.term_to_string_full ~generic ~bound:[] t

and string_of_formula ~generic ~names f =
  let string_of_formula = string_of_formula ~generic in
  let string_of_term = string_of_term ~generic in
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
    | MuFormula(name, _, f) ->
        "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")"
    | NuFormula(name, _, f) ->
        "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")"
    | AbstractionFormula(hint, f) ->
        let hint = Term.get_dummy_name hint in
        let s = hint ^ "\\ " ^ (string_of_formula ~names:(hint::names) f) in
        Term.free hint;
        s
    | ApplicationFormula(mu,tl) ->
        let name = (getFormulaName mu) in
        let args = (String.concat " " (List.map (string_of_term names) tl)) in
        if args = "" then
          name
        else
          name ^ " " ^ args
    | AtomicFormula(head, tl) ->
        let tl' = String.concat " " (List.map (string_of_term names) tl) in
        if tl' = "" then
          head
        else
          (head ^ " " ^ tl')
    | DBFormula(l,n,i) ->
        let rec name l = if l=0 then n else "lift_" ^ name (l-1) in name l 

and string_of_formula_ast ~generic f =
  let string_of_formula_ast = string_of_formula_ast ~generic in
  let string_of_term_ast = string_of_term_ast ~generic in
  match f with
      AndFormula(l,r)
    | OrFormula(l,r)
    | ImplicationFormula(l,r) ->
        let s1 = (string_of_formula_ast l) in
        let s2 = (string_of_formula_ast r) in
        (getConnectiveName f) ^ "(" ^ s1 ^ ", " ^ s2 ^ ")"
    | EqualityFormula(l,r) ->
        let s1 = (string_of_term_ast l) in
        let s2 = (string_of_term_ast r) in
        "eq(" ^ s1 ^ ", " ^ s2 ^ ")"
    | PiFormula(f) -> "pi(" ^ (string_of_formula_ast f) ^ ")"
    | SigmaFormula(f) -> "sigma(" ^ (string_of_formula_ast f) ^ ")"
    | NablaFormula(f) -> "nabla(" ^ (string_of_formula_ast f) ^ ")"
    | MuFormula(name, _, f) ->
        "mu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | NuFormula(name, _, f) ->
        "nu(" ^ name ^ ", " ^ (string_of_formula_ast f) ^ ")"
    | AbstractionFormula(hint, f) ->
        let hint = Term.get_dummy_name hint in
        let s = "lambda(" ^ hint ^ ", " ^ (string_of_formula_ast f)  ^ ")" in
        (Term.free hint;
        s)
    | ApplicationFormula(mu,tl) ->
        "app(" ^ (string_of_formula_ast mu) ^ ", " ^
          (String.concat " " (List.map string_of_term_ast tl)) ^ ")"
    | AtomicFormula(head,tl) ->
        let args = (String.concat " " (List.map (string_of_term_ast) tl)) in
        let args' = if args = "" then "" else ", " ^ args in
        "atom(" ^ head ^ args' ^ ")"
    | DBFormula(l,n,i) -> 
        let rec name l =
          if l=0 then "#" ^ (string_of_int i) else "lift_" ^ name (l-1)
        in
          name l 

let string_of_formula ~generic f =
  string_of_formula ~generic ~names:[] f

let string_of_fixpoint = function
    Inductive -> "inductive"
  | CoInductive -> "coinductive"

let string_of_definition (Definition(name,arity,body,ind)) =
  (string_of_fixpoint ind) ^ " " ^ (string_of_formula ~generic:[] body)
    
(**********************************************************************
*abstract:
* Abstracts the given formula over the given name. Doesn't go through
* mu/nu abstractions.
**********************************************************************)
let rec abstract name formula =
  let var = Term.atom name in
  let rec termFun t = Term.abstract var t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  AbstractionFormula(name, (formulaFun formula))

(** The [var] should have a naming hint attached to it. *)
let rec abstractVar var formula =
  let rec termFun t = Term.abstract var t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  let result = getTermHeadAndArgs var in
  if (Option.isSome result) then
    let (name,_) = Option.get result in
    AbstractionFormula(name, formulaFun formula)
  else
    failwith "un-named variable"

let dummyvar = Term.var ~ts:0 ~lts:0 ~tag:Term.Constant
let rec abstractDummyWithoutLambdas formula =
  let rec termFun t = Term.abstract dummyvar t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  (formulaFun formula)

let rec abstractWithoutLambdas name formula =
  let var = Term.atom name in
  let rec termFun t = Term.abstract var t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  (formulaFun formula)

let rec abstractVarWithoutLambdas var formula =
  let rec termFun t = Term.abstract var t
  and formulaFun f = (mapFormula formulaFun termFun f) in
  (formulaFun formula)

(**********************************************************************
*apply:
**********************************************************************)
let rec apply terms formula =
  let app term f =
    let rec termFun t = Norm.deep_norm (Term.app t [term])
    and formulaFun f = (mapFormula formulaFun termFun f) in
    match f with
        AbstractionFormula(_,f) -> Some(formulaFun f)
      | _ -> None
  in
  match terms with
      [] -> Some formula
    | a::aa ->
        let f' = app a formula in
        if Option.isSome f' then
          (apply aa (Option.get f'))
        else
          None

type state = Term.state
type unifyresult =
    UnifyFailed
  | UnifySucceeded of state
  | UnifyError of string

(**********************************************************************
*nabla elimination:
* Compute the normal form of (nabla tv_1..tv_n\ form).
* The formula is not passed as an abstraction, but has been applied to [tv].
* The list [tv] contains only nabla indices, but not necessarily
* contiguous ones.
* The list [pv] associates to one bound predicate name the local level
* up to which it has already been raised.
**********************************************************************)
let eliminateNablas tv form =
  let rec range_downto m n =
    if m>=n then m :: range_downto (m-1) n else []
  in
  let lift_pname tv name =
    List.fold_left (fun name _ -> "lift_"^name) name tv
  in
  let lift_tname tv name =
    List.fold_left (fun name _ -> name^"'") name tv
  in

  (** [f pv tv form] computes [φ^pv_{rev(tv)}(form)]. *)
  let rec f pv tv form =
    (* Printf.printf "...%s\n" (string_of_formula_ast ~generic:[] form) ; *)
    let fresh () = Term.var ~ts:0 ~lts:0 ~tag:Term.Constant in

    (* Abstract term [t] over variables [tv]. *)
    let tf t =
      Norm.deep_norm (List.fold_left (fun a b -> Term.abstract b a) t tv)
    in

    (* Abstract a fixed point body. *)
    let abstract_body name argnames body =

      (* Cosmetic name annotations. *)
      let name = lift_pname tv name in
      let argnames = List.map (lift_tname tv) argnames in

      (* Create eigenvariables for the parameters. *)
      let heads = List.map (fun _ -> fresh ()) argnames in
      let params = List.map (fun h -> Term.app h (List.rev tv)) heads in
        begin match apply params body with
          | None -> failwith "not a formula"
          | Some body ->
              (* Keep track the number of raisings that have occured
               * above the introduction of that fixed point. *)
              let pv   = List.length tv :: pv in
              let body = f pv tv body in
              let body =
                (* Abstract on the raised parameters' variables. *)
                List.fold_right2
                  (fun h name body ->
                     AbstractionFormula
                       (name,
                        abstractVarWithoutLambdas h body))
                  heads argnames body
              in
                (name,argnames,body)
        end
    in

    let g = f pv tv in

      match form with
        (** Generic abstraction commutes with all connectives. *)
        | AtomicFormula (n,terms) when n="true" || n="false" -> form
        | AndFormula (a,b)         -> AndFormula (g a, g b)
        | OrFormula  (a,b)         -> OrFormula  (g a, g b)
        | ImplicationFormula (a,b) -> ImplicationFormula (g a, g b)
        | EqualityFormula    (u,v) -> EqualityFormula (tf u, tf v)
        | PiFormula    f -> PiFormula    (g f)
        | SigmaFormula f -> SigmaFormula (g f)
        | NablaFormula form ->
            let head = fresh () in
            let tv = head :: tv in
              begin match apply [head] form with
                | None -> failwith "not a formula"
                | Some form -> f pv tv form
              end
        | AtomicFormula (name,terms) ->
            (* For undefined atoms, the only thing we can do
             * is lifting the name.. *)
            let terms = List.map tf terms in
              AtomicFormula (lift_pname tv name, terms)
        | ApplicationFormula (DBFormula (liftings,name,i),terms) ->
            let s   = List.nth pv i in
            let s'  = List.length tv - s in
            let s'' = liftings in
              (* Computing φ_{ss'}^{p:s}( φ_{s''}(p) (s''\tss's'') )
               *         = φ_{s's''}(p) (s's''s\tss's'')       *)
              ApplicationFormula
                (DBFormula (liftings+s',name,i),
                 let rec init n =
                   (* Create a list of [n] fresh variables. *)
                   if n = 0 then [] else fresh () :: init (n-1)
                 in
                 let s = init s in
                 let s's'' = init (s'+s'') in
                 let src = s@s's'' in
                 let dst = s's''@s in
                 let wrap t =
                   let t = tf t in
                     List.fold_right Term.abstract dst (Term.app t src)
                 in
                 let wrap t = Norm.deep_norm (wrap t) in
                   List.map wrap terms)
        | ApplicationFormula (head,terms) ->
            ApplicationFormula (g head, List.map tf terms)
        (** Interesting cases: first and second-order abstractions. *)
        | AbstractionFormula (name,_) ->
            let name = lift_tname tv name in
            let head = fresh () in
            let x = Term.app head (List.rev tv) in
              begin match apply [x] form with
                | None -> failwith "invalid formula: cannot apply" 
                | Some form ->
                    let form = f pv tv form in
                    let form = abstractVarWithoutLambdas head form in
                      AbstractionFormula (name,form)
              end
        | MuFormula (name,argnames,body) ->
            let n,a,b = abstract_body name argnames body in
              MuFormula (n,a,b)
        | NuFormula (name,argnames,body) ->
            let n,a,b = abstract_body name argnames body in
              NuFormula (n,a,b)
        | DBFormula _ -> assert false
  in
    f [] tv form

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
*undoUnify:
********************************************************************)
let undoUnify s = Term.restore_state s

(********************************************************************
*rightUnify:
* Performs unification on the right of the turnstile.
********************************************************************)
let rightUnify a b =
  let state = Term.save_state () in
  try
    (Right.pattern_unify a b;
    UnifySucceeded(state))
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
    UnifySucceeded(state))
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
  let state = Term.save_state () in
  let rec unify l1 l2 =
    match (l1,l2) with
        (l1hd::l1tl, l2hd::l2tl) ->
          (match (unifier l1hd l2hd) with
              UnifySucceeded(_) -> unify l1tl l2tl
            | UnifyFailed -> UnifyFailed
            | UnifyError _ as u -> u)
      | ([],[]) -> UnifySucceeded(state)
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
    AtomicFormula(head, t) -> (head = "_") && (t = [])
  | _ -> false


(**********************************************************************
*matchFormula:
* Match a template with a formula.  If the match succeeds, returns true,
* otherwise returns false.
**********************************************************************)
let matchFormula template formula =
  let success ur =
    match ur with
      UnifySucceeded(s) -> true
    | _ -> false
  in
  
  (*  Keep track of binding state to undo it later. *)
  let state = Term.save_state () in
  
  (********************************************************************
  *search:
  * Recurse over the structure of two formulas.
  ********************************************************************)
  let rec search template' formula' =
    match (template', formula') with
      (AndFormula(l,r), AndFormula(l', r'))
    | (OrFormula(l,r), OrFormula(l', r'))
    | (ImplicationFormula(l,r), ImplicationFormula(l', r')) ->
        (search l l') && (search r r')
    
    | (EqualityFormula(t1, t2), EqualityFormula(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t2 t2'))

    | (AtomicFormula("_", []), _) ->
        true
    | (AtomicFormula(head,tl), AtomicFormula(head',tl')) ->
        (* let () = print_endline ("Pattern: " ^ (string_of_formula_ast template)) in
        let () = print_endline ("Formula: " ^ (string_of_formula_ast formula)) in *)
        (head = head') && (List.for_all success (List.map2 rightUnify tl tl'))
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
          (n = n') && (List.for_all success (List.map2 rightUnify args args'))
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
*applyFixpoint:
* Substitutes the given argument formula for the DB formulas in the
* target formula.  If the argument formula has fewer abstractions than
* the DB formula, new abstractions are added.  These abstractions don't
* refer to anything in the argument formula, and so "generic" abstractions
* can be pushed down.
**********************************************************************)
exception InvalidFixpointApplication
let applyFixpoint argument formula =
  (* Normalizing the argument must be done first, before the normalization
   * that might occur during instantiation. The downside is that even if you
   * never abstracted anything your invariant gets abstracted here. TODO *)
  let argument = eliminateNablas [] argument in

  (********************************************************************
  *normalizeAbstractions:
  * Creates n new variables (where n is the number of lambdas the DB
  * is under) and applies them to the arguments.  Then, it applies
  * the now lambdaless arguments to the target.  It then re-absracts
  * the result over the same n variables.  Finally it frees the
  * generated variables.
  ********************************************************************)
  let rec normalizeAbstractions lambdas target arguments =
    let free (name,info) = if info then Term.free name else () in
    let makeFreeInfo name = (name, Term.is_free name) in
    let makeArg name = Term.var ~tag:Term.Constant ~lts:0 ~ts:0 in
    
    (*  Collect info about variable freeness. *)
    let freeInfo = List.map makeFreeInfo lambdas in
    
    (*  Make "dummy" variables and apply them to each argument. *)
    let lambdas' = List.map makeArg lambdas in
    let lambdalessargs = List.map (fun t -> Term.app t lambdas') arguments in
    
    (*  Apply the lambdaless args.  *)
    let target' = apply lambdalessargs target in
    
    (*  Reabstract. *)
    if (Option.isSome target') then
      let abstarget =
        List.fold_right
          (abstractVarWithoutLambdas)
          lambdas' (Option.get target')
      in
      
      (*  Free any bound vars (shouldn't be any). *)
      (List.iter free freeInfo;
      abstarget)
    else
      raise InvalidFixpointApplication
  in

  let tf t = t in
  let rec ff lam db f =
    match f with
      | MuFormula(name,args,body) ->
          MuFormula(name,args, ff lam (db + 1) body)
      | NuFormula(name,args,body) ->
          NuFormula(name,args, ff lam (db + 1) body)
      | ApplicationFormula(DBFormula(lifts,n,db'),args) ->
          if db <> db' then f else
            let argument =
              if lifts = 0 then argument else
                let fresh _ = Term.var ~ts:0 ~lts:0 ~tag:Term.Constant in
                let generics =
                  let rec mk = function 0 -> [] | n -> fresh () :: mk (n-1) in
                    mk lifts
                in
                  eliminateNablas generics argument
            in
              normalizeAbstractions lam argument args
      | AbstractionFormula(name,body) ->
          AbstractionFormula(name, (ff (name::lam) db body))
      | DBFormula(_) ->
          failwith "Firstorderabsyn.applyFixpoint: encountered invalid DB."
      | _ -> mapFormula (ff lam db) tf f
  in
  try
    Some (ff [] 0 formula)
  with
    InvalidFixpointApplication ->
      None


(********************************************************************
*makeAnonymousTerm:
********************************************************************)
let makeAnonymousTerm () =
  Term.fresh ~name:"_" ~tag:Term.Logic ~lts:max_int ~ts:max_int

(********************************************************************
*makeAnonymousFormula:
********************************************************************)
let makeAnonymousFormula () =
  AtomicFormula("_",[])
