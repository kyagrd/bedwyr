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

type fixpoint =
    Inductive
  | CoInductive

type quantifier =
    Pi
  | Sigma
  | Nabla

type 'a pol_formula = ('a * 'a formula)

and 'a app_formula = 
    FixpointFormula of (fixpoint * (string * string list * 'a abs_formula))
  | DBFormula of int * string * int
  | AtomicFormula of string

and 'a abs_formula = 
    AbstractionFormula of (string * 'a abs_formula)
  | AbstractionBody of 'a pol_formula

and 'a formula =
    AndFormula of ('a pol_formula * 'a pol_formula)
  | OrFormula of ('a pol_formula * 'a pol_formula)
  | ImplicationFormula of ('a pol_formula * 'a pol_formula)
  | EqualityFormula of (term * term)
  | QuantifiedFormula of (quantifier * 'a abs_formula)
  | ApplicationFormula of ('a app_formula * term list)

type 'a predefinition =
  PreDefinition of (string * string list * 'a pol_formula * fixpoint)

type 'a definition =
  Definition of (string * int * 'a pol_formula * fixpoint)


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
      Some (try Term.get_hint t, [] with _ -> "x$",[])
  | _ -> None
  
let getDefinitionArity (Definition(_,a,_,_)) = a
let getDefinitionBody (Definition(_,_,b,_)) = b

let getConnective = function
    AndFormula(_) -> ", "
  | OrFormula(_) -> "; "
  | ImplicationFormula(_) -> " => "
  | EqualityFormula(_) -> " = "
  | _ -> ""

let getQuantifierName = function 
    Pi -> "pi" 
  | Sigma -> "sigma" 
  | Nabla -> "nabla"

let getFixpointName = function 
    Inductive -> "mu" 
  | CoInductive -> "nu"

let getApplicationKind = function
    FixpointFormula(fix,_) -> getFixpointName fix
  | DBFormula(_) -> "db"
  | AtomicFormula(_) -> "atom"

let getConnectiveName = function
    AndFormula(_) -> "and"
  | OrFormula(_) -> "or"
  | ImplicationFormula(_) -> "imp"
  | EqualityFormula(_) -> "eq"
  | QuantifiedFormula(q,_) -> getQuantifierName q
  | ApplicationFormula(f,_) -> getApplicationKind f

let getApplicationName = function
    FixpointFormula(_,(name,_,_))
  | DBFormula(_,name,_) -> name
  | AtomicFormula(name) ->
      (* This actually happens, the pattern "_ ..." matches any application,
       * not only atoms but also fixed points, and is thus represented by
       * App(Atom("_",[]),...). *)
      assert (name="_") ;
      name

let mapFormula (formulafun,appformulafun,absformulafun) termfun =
  let formulafun (polarity,formula) = (polarity,formulafun formula) in
  ((function 
      AndFormula(l,r) -> AndFormula(formulafun l, formulafun r)
    | OrFormula(l,r) -> OrFormula(formulafun l, formulafun r)
    | ImplicationFormula(l,r) -> ImplicationFormula(formulafun l, formulafun r)
    | EqualityFormula(l,r) -> EqualityFormula(termfun l, termfun r)
    | QuantifiedFormula(q,f) -> QuantifiedFormula(q,absformulafun f)
    | ApplicationFormula(f,tl) -> ApplicationFormula(appformulafun f,List.map termfun tl)),
   (function 
      FixpointFormula(fix,(name,args,f)) -> FixpointFormula (fix,(name,args,absformulafun f))
    | AtomicFormula(head) -> AtomicFormula(head)
    | DBFormula(a,b,c) -> DBFormula(a,b,c)),
   (function 
      AbstractionFormula(name,f) -> AbstractionFormula(name,absformulafun f)
    | AbstractionBody f -> AbstractionBody (formulafun f))) 

let termsFormula = 
  let rec f =
  let f (_,formula) = f formula in
  function
      AndFormula(l,r)  
    | OrFormula(l,r)  
    | ImplicationFormula(l,r) -> (f l)@(f r)
    | EqualityFormula(l,r) -> [l;r]
    | QuantifiedFormula(_,formula) -> absf formula
    | ApplicationFormula(_,tl) -> tl
  and absf = (function
      AbstractionFormula(_,formula) -> absf formula
    | AbstractionBody(_,formula) -> f formula) in (f,absf) 

let rec string_of_term ~generic names t =
  Pprint.term_to_string_preabstracted ~generic ~bound:names t

and string_of_term_ast ~generic t =
  Pprint.term_to_string_full ~generic ~bound:[] t

and string_of_formula ~generic ~names =
  let string_of_formula (_,f) = string_of_formula ~generic ~names f in
  let string_of_term = string_of_term ~generic in 
fun f -> match f with 
      AndFormula(l,r)
    | OrFormula(l,r)
    | ImplicationFormula(l,r) ->
        let s1 = (string_of_formula l) in
        let s2 = (string_of_formula r) in
        "(" ^ s1 ^ (getConnective f) ^ s2 ^ ")"
    | EqualityFormula(l,r) ->
        let s1 = (string_of_term names l) in
        let s2 = (string_of_term names r) in
        "(" ^ s1 ^ " = " ^ s2 ^ ")"
    | QuantifiedFormula(q,f) -> 
	let q = getQuantifierName q and f = string_of_absformula ~generic ~names f in (q ^ f)
    | ApplicationFormula(f,tl) ->
        let args = (String.concat " " (List.map (string_of_term names) tl)) in
	let name = string_of_appformula f in
        if args = "" then name else name ^ " " ^ args

and string_of_appformula = function
    FixpointFormula(_,(name,_,_))
  | AtomicFormula(name) -> name
  | DBFormula(l,n,i) -> 
      let rec name l = if l=0 then n else "lift_" ^ name (l-1) in name l 

(*   | MuFormula(name, _, f) ->
 *       "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")"
 *   | NuFormula(name, _, f) ->
 *       "(" ^ name ^ " " ^ (string_of_formula ~names f) ^ ")" *)

and string_of_absformula ~generic ~names = function
      AbstractionFormula (hint,f) -> let hint = Term.get_dummy_name hint in 
	let s = hint ^ "\\ " ^ (string_of_absformula ~generic ~names:(hint::names) f) in 
	(Term.free hint; s)
    | AbstractionBody (_,f) -> string_of_formula ~generic ~names f 

and string_of_formula_ast ~generic f =
  let string_of_formula_ast (_,f) = string_of_formula_ast ~generic f in
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
    | QuantifiedFormula(q,f) ->
	let q = getQuantifierName q and f = string_of_absformula_ast ~generic f in  (q ^ "(" ^ f  ^ ")")
    | ApplicationFormula(f,tl) ->
        let args = (String.concat " " (List.map (string_of_term_ast) tl)) in
        let args' = if args = "" then "" else "(" ^ args ^")" in
        (string_of_appformula_ast ~generic f) ^ args'


and string_of_appformula_ast ~generic = function
    FixpointFormula(i,(name,_,f)) -> 
      (getFixpointName i) ^ "[" ^ name ^ ": " ^ (string_of_absformula_ast ~generic f) ^ "]"
  | AtomicFormula(name) -> 
      "atom["^name^"]"
  | DBFormula(l,n,i) -> 
      let rec name l = if l=0 then "#" ^ (string_of_int i) else "lift_" ^ name (l-1) in name l 


and string_of_absformula_ast ~generic  = function
      AbstractionFormula (hint,f) -> let hint = Term.get_dummy_name hint in 
	let s = "lambda(" ^ hint ^ ", " ^ (string_of_absformula_ast ~generic f) ^")" in 
	(Term.free hint; s)
    | AbstractionBody (_,f) -> string_of_formula_ast ~generic f 

let string_of_formula ~generic (_,f) =
  string_of_formula ~generic ~names:[] f

let string_of_absformula ~generic (_,f) =
  string_of_absformula ~generic ~names:[] f

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

let abstract0 var = let rec f = mapFormula f (Term.abstract var) in f

let dummyvar = Term.var ~ts:0 ~lts:0 ~tag:Term.Constant

let abstractDummyWithoutLambdas = abstract0 dummyvar
let abstractWithoutLambdas name = abstract0 (Term.atom name)
let abstractVarWithoutLambdas var = abstract0 var

let abstract name = let (f,appf,absf) = abstractWithoutLambdas name in
  (fun (polarity,formula) ->
  AbstractionFormula (name, AbstractionBody(polarity,f formula))),
  (fun absformula ->
  AbstractionFormula (name, absf absformula))

(** The [var] should have a naming hint attached to it. *)
let abstractVar var  =
  let result = getTermHeadAndArgs var in
  if (Option.isSome result) then
    let (name,_) = Option.get result in abstract name
  else
    failwith "un-named variable"


(**********************************************************************
*apply:
**********************************************************************)
let rec apply terms formula =
  let app term =
    let rec termFun t = Norm.deep_norm (Term.app t [term])
    and formulaFun = (mapFormula formulaFun termFun) in
    let (_,_,absf) = formulaFun in 
    function AbstractionFormula(_,f) -> Some (absf f)
      | AbstractionBody _ -> None
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
  let abstractVarWithoutLambdas var = let (_,_,f) = abstractVarWithoutLambdas var in f in
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
  let rec f pv tv =
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
              let body = let (_,f,_) = f pv tv in f body in
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

    let (gf,gabs,gapp) = f pv tv in
    let gf (polarity,formula) = (polarity,gf formula) in
    ((function
        (** Generic abstraction commutes with all connectives. *)
        | AndFormula (a,b)         -> AndFormula (gf a, gf b)
        | OrFormula  (a,b)         -> OrFormula  (gf a, gf b)
        | ImplicationFormula (a,b) -> ImplicationFormula (gf a, gf b)
        | EqualityFormula    (u,v) -> EqualityFormula (tf u, tf v)
	| QuantifiedFormula(q,form) -> begin match q with
	      Pi
	    | Sigma -> QuantifiedFormula(q,gabs form)
            | Nabla ->
            let head = fresh () in
            let tv = head :: tv in
              begin match apply [head] form with
                | None -> failwith "not a formula"
                | Some (AbstractionBody (_,form)) -> let (f,_,_) = f pv tv in f form 
						(* A nabla's polarity has to be the same as the polarity behind it *)
		| Some (AbstractionFormula form) -> failwith "nabla elimination was incomplete"
              end
	    end
        | ApplicationFormula (f,terms) -> gapp (f,terms)),

     (fun form -> match form with
          AbstractionFormula (name,_) ->
            let name = lift_tname tv name in
            let head = fresh () in
            let x = Term.app head (List.rev tv) in
              begin match apply [x] form with
                | None -> failwith "invalid formula: cannot apply" 
                | Some form ->
                    let form = gabs form in
                    let form = abstractVarWithoutLambdas head form in
                      AbstractionFormula (name,form)
              end
	| AbstractionBody f -> AbstractionBody (gf f)),

     (fun (form,terms) -> match form with
          AtomicFormula (name) when name="true" || name="false" -> ApplicationFormula(form,terms)
        | AtomicFormula (name) ->
            (* For undefined atoms, the only thing we can do
             * is lifting the name.. *)
            let terms = List.map tf terms in ApplicationFormula(AtomicFormula(lift_pname tv name), terms)
	| DBFormula (liftings,name,i) ->
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
        | FixpointFormula (i,(name,argnames,body)) ->
	    let n,a,b = abstract_body name argnames body in
            ApplicationFormula (FixpointFormula(i,(n,a,b)), List.map tf terms)))

  in
  let (f,_,_) = f [] tv in f form

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
    AtomicFormula(head) -> (head = "_") (* && (t = []) *)
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
