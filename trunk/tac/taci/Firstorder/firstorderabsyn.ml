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

type progress =
    Progressing
  | Unknown

type fixpoint =
    Inductive
  | CoInductive

type quantifier =
    Pi
  | Sigma
  | Nabla

type connective =
    And
  | Or
  | Imp

(*  Annotations *)
type polarity = Positive | Negative
type freezing = Frozen | Unfrozen
type control  = Normal | Focused | Delayed
type junk     = Clean | Dirty of (unit -> unit)
type annotation = {
  polarity : polarity ;
  freezing : freezing ;
  control  : control ;
  junk     : junk
}
  
let defaultAnnotation =
  {polarity = Negative;
   freezing = Unfrozen;
   control = Normal;
   junk = Clean}

let freeze a = { a with freezing = Frozen }
let thaw a = { a with freezing = Unfrozen }
let focus a = { a with control = Focused }
let delay a = { a with control = Delayed }
(*  Formulas  *)
type 'a polarized = ('a * 'a formula)

and 'a predicate =
    FixpointFormula of fixpoint * string * (string * progress) list * 'a abstraction
  | DBFormula of int * string * int
  | AtomicFormula of string

and 'a formula =
    BinaryFormula of (connective * 'a polarized * 'a polarized)
  | EqualityFormula of (term * term)
  | QuantifiedFormula of (quantifier * 'a abstraction)
  | ApplicationFormula of ('a predicate * term list)

and 'a abstraction =
    AbstractionFormula of string * 'a abstraction
  | AbstractionBody of 'a polarized

let negativeFormula f = { defaultAnnotation with polarity = Negative },f
let positiveFormula f = { defaultAnnotation with polarity = Positive },f
let changeAnnotation f (a,form) = (f a, form)

(*  Patterns  *)
type pattern_annotation = {
  polarity_pattern : polarity option ;
  freezing_pattern : freezing option ;
  control_pattern  : control option ;
  junk_pattern     : junk option
}

let defaultPatternAnnotation =
  {polarity_pattern = None;
   freezing_pattern = None;
   control_pattern = None;
   junk_pattern = None}

type fixpoint_pattern =
    InductivePattern
  | CoinductivePattern
  | AnonymousFixpoint

type 'a polarized_pattern = 'a * 'a formula_pattern

and 'a predicate_pattern =
    AtomicPattern of string
  | AnonymousPredicate
  | AnonymousMu
  | AnonymousNu

and 'a formula_pattern =
    BinaryPattern of connective * 'a polarized_pattern * 'a polarized_pattern
  | EqualityPattern of term * term
  | QuantifiedPattern of quantifier * 'a abstraction_pattern
  | ApplicationPattern of 'a predicate_pattern * term list

and 'a abstraction_pattern =
    AbstractionPattern of string * 'a abstraction_pattern
  | AbstractionBodyPattern of 'a polarized_pattern
  | AnonymousAbstraction

let anonymousBinder = "_"

type 'a predefinition =
  PreDefinition of (string * (string * progress) list * 'a abstraction_pattern * fixpoint)

type 'a definition =
  Definition of (string * (string * progress) list * 'a abstraction * fixpoint)

(*  map_formula: mapping over formulas.  *)
type ('a,'b,'c,'d,'e) map_formula =
  {polf : 'a polarized -> 'b ;
  predf : 'a predicate -> 'c ;
  abstf : 'a abstraction -> 'd ;
  formf : 'a formula -> 'e}

(*  mappattern: mapping over formulas.  *)
type ('a,'b,'c,'d,'e) map_pattern =
  {polp : 'a polarized_pattern -> 'b ;
  predp : 'a predicate_pattern -> 'c ;
  abstp : 'a abstraction_pattern -> 'd ;
  formp : 'a formula_pattern -> 'e}

(*  isSpecialAtom: returns true if the atom is allowed to be unbound;
    only matters for true and false.  *)
let isSpecialAtom a = a = "true" || a = "false"

(********************************************************************
*makeAnonymousTerm:
********************************************************************)
let makeAnonymousTerm () =
  Term.fresh ~name:"_" ~tag:Term.Logic ~lts:max_int ~ts:max_int

(**********************************************************************
*getTermHeadAndArgs:
* Gets the head and arguments of a term.  If the term isn't a constant,
* returns None.
*
* Note the hackery with get_hint: this is used to check if the head is
* an underscore (an anonymous formula/term).  Hint must be used, because
* name could be something ugly like "_7", etc.
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
      (try
        let h = Term.get_hint t in
        Some(h, [])
      with
        Not_found -> Some(Term.get_name t, []))
  | _ -> None

let getDefinitionArity (Definition(_,a,_,_)) = List.length a
let getDefinitionBody (Definition(_,_,b,_)) = b
let predicateofDefinition (Definition(n,p,b,t)) = FixpointFormula(t,n,p,b)

let getConnective = function
    And -> ", "
  | Or -> "; "
  | Imp -> " => "

let getQuantifierName = function 
    Pi -> "pi" 
  | Sigma -> "sigma" 
  | Nabla -> "nabla"

let getFixpointName = function 
    Inductive -> "mu" 
  | CoInductive -> "nu"

let getApplicationKind = function
    FixpointFormula(fix,_,_,_) -> getFixpointName fix
  | DBFormula(_) -> "db"
  | AtomicFormula(_) -> "atom"

let getConnectiveName = function
    And -> "and"
  | Or -> "or"
  | Imp -> "imp"

let getApplicationName = function
    FixpointFormula(_,name,_,_)
  | DBFormula(_,name,_) -> name
  | AtomicFormula(name) -> name

let mapFormula x termsf = {
  polf = (fun (p,f) -> p,(x ()).formf f) ; 
  predf = (function 
      FixpointFormula(fix,name,args,f) -> FixpointFormula (fix,name,args,(x ()).abstf f)
    | AtomicFormula(head) -> AtomicFormula(head)
    | DBFormula(a,b,c) -> DBFormula(a,b,c)) ;
  abstf = (function
      AbstractionFormula(name,f) -> AbstractionFormula(name,(x ()).abstf f)
    | AbstractionBody(f) -> AbstractionBody((x ()).polf f)) ;
  formf = (function 
      BinaryFormula(c,l,r) -> BinaryFormula(c,(x ()).polf l, (x ()).polf r)
    | EqualityFormula(l,r) -> EqualityFormula(termsf l, termsf r)
    | QuantifiedFormula(q,f) -> QuantifiedFormula(q,(x ()).abstf f)
    | ApplicationFormula(f,tl) -> ApplicationFormula((x ()).predf f,List.map termsf tl))}


let mapFormula2 f1 f2 x termsf a = {
  polf = (fun (p,f) -> p,(x a).formf f) ; 
  predf = (fun f tl -> ApplicationFormula((match f with 
      FixpointFormula(fix,name,args,f) -> FixpointFormula (fix,name,args,(x a).abstf f)
    | AtomicFormula(head) -> AtomicFormula(head)
    | DBFormula(a,b,c) -> DBFormula(a,b,c)),tl)) ;
  abstf = (function
      AbstractionFormula(name,f) -> AbstractionFormula(name,(x (f1 name a)).abstf f)
    | AbstractionBody(f) -> AbstractionBody((x a).polf f)) ;
  formf = (function 
      BinaryFormula(c,l,r) -> let (al,ar) = f2 c a in BinaryFormula(c,(x al).polf l, (x ar).polf r)
    | EqualityFormula(l,r) -> EqualityFormula(termsf l, termsf r)
    | QuantifiedFormula(q,f) -> QuantifiedFormula(q,(x a).abstf f)
    | ApplicationFormula(f,tl) -> ((x a).predf f (List.map termsf tl)))}

let patternAnnotationToFormulaAnnotation polarity p =
  let get default = function None -> default | Some x -> x in
  {polarity = get polarity p.polarity_pattern;
   freezing = get Unfrozen p.freezing_pattern;
   control = get Normal p.control_pattern;
   junk   = get Clean p.junk_pattern}


let mapPattern x termsf = {
  polp = (fun (p,f) -> (p,(x ()).formp f)) ; 
  predp = (function 
      AtomicPattern(head) -> AtomicPattern(head)
    | AnonymousPredicate -> AnonymousPredicate
    | AnonymousMu -> AnonymousMu
    | AnonymousNu -> AnonymousNu) ;
  abstp = (function
      AbstractionPattern(name,f) -> AbstractionPattern(name,(x ()).abstp f)
    | AbstractionBodyPattern(f) -> AbstractionBodyPattern((x ()).polp f)
    | AnonymousAbstraction -> AnonymousAbstraction) ;
  formp = (function 
      BinaryPattern(c,l,r) -> BinaryPattern(c,(x ()).polp l, (x ()).polp r)
    | EqualityPattern(l,r) -> EqualityPattern(termsf l, termsf r)
    | QuantifiedPattern(q,f) -> QuantifiedPattern(q,(x ()).abstp f)
    | ApplicationPattern(f,tl) -> ApplicationPattern((x ()).predp f, List.map termsf tl))}

let rec termsPolarized (p,f) = termsFormula f
and termsAbstraction = function  
    AbstractionFormula(_,f) -> termsAbstraction f
  | AbstractionBody(f) -> termsPolarized f
and termsFormula = function
    BinaryFormula(_,l,r) -> (termsPolarized l)@(termsPolarized r)
  | EqualityFormula(l,r) -> [l;r]
  | QuantifiedFormula(_,f) -> termsAbstraction f
  | ApplicationFormula(_,tl) -> tl

let string_of_polarity = function Positive -> "+" | Negative -> "-"
let string_of_freezing = function Frozen -> "*" | Unfrozen -> ""
let string_of_control = function
  Normal -> " " | Focused -> "#" | Delayed -> "?"

let string_of_pattern _ = ""

let string_of_term ?(norm=fun x->x) ~generic names t =
  Pprint.term_to_string_preabstracted ~generic ~bound:names (norm t)

let rec string_of_formula ~generic ~names =
  let s = string_of_formula ~generic in
  { polf = (fun (p,f) -> (s ~names).formf f) ;
    predf = (function
        FixpointFormula(_,name,_,_)
      | AtomicFormula(name) -> name
      | DBFormula(l,n,i) -> 
          (*  TODO: eep!  Such hackery! *)
          let rec name l = if l=0 then n else "lift_" ^ name (l-1) in
          name l) ;

    abstf = (function
        AbstractionFormula (hint,f) ->
          let hint = Term.get_dummy_name hint in 
          let s = hint ^ "\\ " ^ ((s ~names:(hint::names)).abstf f) in 
            (Term.free hint; s)
      | AbstractionBody (f) -> (s ~names).polf f) ; 

    formf = (function
        BinaryFormula(c,l,r) ->
          let s1 = ((s ~names).polf l) in
          let s2 = ((s ~names).polf r) in
          "(" ^ s1 ^ (getConnective c) ^ s2 ^ ")"
      | EqualityFormula(l,r) ->
          let s1 = (string_of_term ~norm:Norm.deep_norm ~generic names l) in
          let s2 = (string_of_term ~norm:Norm.deep_norm ~generic names r) in
          "(" ^ s1 ^ " = " ^ s2 ^ ")"
      | QuantifiedFormula(q,f) -> 
          let s1 = getQuantifierName q in 
          let s2 = (s ~names).abstf f in 
          (s1 ^ " " ^ s2)
      | ApplicationFormula(f,tl) ->
          let args =
            String.concat " "
              (List.map (string_of_term ~norm:Norm.deep_norm ~generic names) tl)
          in
          let name = (s ~names).predf f in
          if args = "" then name else name ^ " " ^ args)}

let rec string_of_pattern_ast =
  let s = string_of_pattern_ast in
  { polp = (fun (_,f) -> s.formp f) ;
    predp = (function
      | AtomicPattern(name) -> name
      | AnonymousPredicate -> "<anon>"
      | AnonymousMu -> "mu <anon>"
      | AnonymousNu -> "nu <anon>") ;

    abstp = (function
        AbstractionPattern (hint,f) ->
          let s = hint ^ "\\ " ^ (s.abstp f) in 
          s
      | AbstractionBodyPattern (f) -> s.polp f
      | AnonymousAbstraction -> "_\\ _") ; 

    formp = (function
        BinaryPattern(c,l,r) ->
          let s1 = (s.polp l) in
          let s2 = (s.polp r) in
          (getConnectiveName c) ^ "(" ^ s1 ^ ", " ^ s2 ^ ")"
      | EqualityPattern(l,r) ->
          let s1 = (string_of_term ~generic:[] [] l) in
          let s2 = (string_of_term ~generic:[] [] r) in
          "eq(" ^ s1 ^ ", " ^ s2 ^ ")"
      | QuantifiedPattern(q,f) -> 
          let s1 = getQuantifierName q in 
          let s2 = s.abstp f in 
          (s1 ^ " " ^ s2)
      | ApplicationPattern(f,tl) ->
          let args = (String.concat " " (List.map (fun _ -> "<term>") tl)) in
          let name = "app(" ^ (s.predp f) in
          if args = "" then name ^ ")" else name ^ ", " ^ args ^ ")")}
let string_of_pattern_ast = string_of_pattern_ast.polp

let string_of_term_ast ~generic t =
  Pprint.term_to_string_full ~generic ~bound:[] t

let rec string_of_formula_ast ~generic =
  let s=string_of_formula_ast in 
    { polf = (fun (p,f) -> (s ~generic).formf f) ;

      predf = (function
       FixpointFormula(i,name,_,f) -> 
         (getFixpointName i) ^ "[" ^ name ^ ": " ^ ((s ~generic).abstf f) ^ "]"
     | AtomicFormula(name) -> 
         "atom["^name^"]"
     | DBFormula(l,n,i) -> 
         let rec name l =
           if l=0 then "#" ^ (string_of_int i) else "lift_" ^ name (l-1)
         in name l) ;

      abstf = (function
       AbstractionFormula (hint,f) -> 
         let hint = Term.get_dummy_name hint in 
         let s = "lambda(" ^ hint ^ ", " ^ ((s ~generic).abstf f) ^")" in 
           (Term.free hint; s)
     | AbstractionBody (f) -> (s ~generic).polf f) ;
      
      formf = (function
       BinaryFormula(c,l,r) ->
         let s1 = ((s ~generic).polf l) in
         let s2 = ((s ~generic).polf r) in
           (getConnectiveName c) ^ "(" ^ s1 ^ ", " ^ s2 ^ ")"
     | EqualityFormula(l,r) ->
         let s1 = (string_of_term_ast ~generic l) in
         let s2 = (string_of_term_ast ~generic r) in
              "eq(" ^ s1 ^ ", " ^ s2 ^ ")"
     | QuantifiedFormula(q,f) ->
         let s1 = getQuantifierName q and 
       s2 = (s ~generic).abstf f in  
           (s1 ^ "(" ^ s2  ^ ")")
     | ApplicationFormula(f,tl) ->
         let args =
           String.concat " " (List.map (string_of_term_ast ~generic) tl)
         in
         let args = if args = "" then "" else "(" ^ args ^")" in
           ((s ~generic).predf f) ^ args)}
      
let string_of_fixpoint = function
    Inductive -> "inductive"
  | CoInductive -> "coinductive"

let string_of_formula = string_of_formula ~names:[]

let string_of_definition (Definition(name,arity,body,ind)) =
  (string_of_fixpoint ind) ^ " " ^ name ^ " " ^
  ((string_of_formula ~generic:[]).abstf body)
    
(**********************************************************************
*abstract:
* Abstracts the given formula over the given name. Doesn't go through
* mu/nu abstractions.
**********************************************************************)

let abstract0 var = let rec x () = mapFormula x (Term.abstract var) in x

let dummyvar = Term.var ~ts:0 ~lts:0 ~tag:Term.Constant
let lift = abstract0 dummyvar ()
let rec lift_pred n p =
  if n>0 then lift_pred (n-1) (lift.predf p) else p

let abstractWithoutLambdas name = abstract0 (Term.atom name)

let abstractVarWithoutLambdas = abstract0

let abstractVar var = 
  {polf =
     (fun f -> AbstractionFormula(String.lowercase (Term.get_hint var),
                AbstractionBody((abstractVarWithoutLambdas var ()).polf f))) ;
   abstf =
     (fun f -> AbstractionFormula(String.lowercase (Term.get_hint var),
                (abstractVarWithoutLambdas var ()).abstf f)) ;
   formf = (fun _ -> ()) ; 
   predf = (fun _ -> ())}

let abstractPattern0 var = let rec x () = mapPattern x (Term.abstract var) in x
let abstractPatternWithoutLambdas name = abstractPattern0 (Term.atom name)
let abstractPattern name =
  {polp =
     (fun f -> AbstractionPattern(String.lowercase name,
                 AbstractionBodyPattern(
                   (abstractPatternWithoutLambdas name ()).polp f))) ;
   abstp =
     (fun f -> AbstractionPattern(String.lowercase name,
                 (abstractPatternWithoutLambdas name ()).abstp f)) ;
   formp = (fun _ -> ()) ; 
   predp = (fun _ -> ())}

(** The [var] should have a naming hint attached to it. *)

(**********************************************************************
*apply:
* Given a list of terms, applies each in turn to the given abstracted
* formula.
**********************************************************************)
let rec apply terms formula =
  let app term =
    let termFun t = Norm.deep_norm (Term.app t [term]) in
    let rec appfun () = mapFormula appfun termFun in
    function 
        AbstractionFormula(_,f) -> Some ((appfun ()).abstf f)
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

(*  fullApply: applies the given terms, requiring that the resultant
    formula is no longer abstracted.  *)
let fullApply args f = match apply args f with
  | Some (AbstractionBody formula) -> Some formula
  | _ -> None

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
let eliminateNablas tv =
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
              let body = (f pv tv).abstf body in
              let body =
                (* Abstract on the raised parameters' variables. *)
                List.fold_right2
                  (fun h name body ->
                     AbstractionFormula
                       (name,
                        (abstractVarWithoutLambdas h ()).abstf body))
                  heads argnames body
              in
                (name,argnames,body)
        end
    in

      {polf = (fun (p,form) -> (p,(f pv tv).formf form)) ;

       formf = (function
        (** Generic abstraction commutes with all connectives. *)
        | BinaryFormula (c,a,b) ->
            BinaryFormula (c, (f pv tv).polf a, (f pv tv).polf b)
        | EqualityFormula (u,v) ->
            EqualityFormula (tf u, tf v)
        | QuantifiedFormula(q,form) ->
            begin match q with
              Pi
            | Sigma -> QuantifiedFormula(q,(f pv tv).abstf form)
                  | Nabla ->
                  let head = fresh () in
                  let tv = head :: tv in
                    begin match apply [head] form with
                      | None -> failwith "not a formula"
                      | Some (AbstractionBody (form)) ->
                          (* A nabla's polarity has to be the same as that of the
                           * connective under it, because it will override it.
                           * It should be ensured by construction. *)
                          snd ((f pv tv).polf form)
                      | Some (AbstractionFormula _) ->
                          failwith "nabla elimination was incomplete"
                    end
            end
        | ApplicationFormula (form,terms) -> (f pv tv).predf form terms) ;
 
      abstf = (function
          AbstractionFormula (name,_) as form ->
            let name = lift_tname tv name in
            let head = fresh () in
            let x = Term.app head (List.rev tv) in
              begin match apply [x] form with
                | None -> failwith "invalid formula: cannot apply" 
                | Some form ->
                    let form = (f pv tv).abstf form in
                    let form = (abstractVarWithoutLambdas head ()).abstf form in
                    AbstractionFormula (name,form)
              end
        | AbstractionBody form ->
            AbstractionBody ((f pv tv).polf form)) ;

      predf = (fun form terms -> match form with
          AtomicFormula (name) when (isSpecialAtom name) ->
            ApplicationFormula(form,terms)
        | AtomicFormula (name) -> 
            (* For undefined atoms, the only thing we can do
             * is lifting the name.. *)
            let terms = List.map tf terms in
            ApplicationFormula(AtomicFormula(lift_pname tv name), terms)
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
        | FixpointFormula (i,name,args,body) ->
            let (names,progs) = List.split args in
            let n,a,b = abstract_body name names body in
            ApplicationFormula (FixpointFormula(i,n,List.combine a progs,b), List.map tf terms))}

  in
  f [] tv

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
* If any unification fails it fails.  After a call to unifyList,
* the term state is in a valid state: either the unify succeeded, and
* the state before unification is returned for later restoration, or
* the term state remains unchanged.
**********************************************************************)
let unifyList unifier l1 l2 =
  let state = Term.save_state () in
  let rec unify l1 l2 =
    match (l1,l2) with
        (l1hd::l1tl, l2hd::l2tl) ->
          (match (unifier l1hd l2hd) with
              UnifySucceeded(_) -> unify l1tl l2tl
            | (UnifyFailed as u)
            | (UnifyError _ as u) -> (Term.restore_state state; u))
      | ([],[]) -> UnifySucceeded(state)
      | (_,_) -> (Term.restore_state state; UnifyFailed)
  in
  unify l1 l2


(**********************************************************************
*applyFixpoint:
* Substitutes the given argument formula for the DB formulas in the
* target formula.  If the argument formula has fewer abstractions than
* the DB formula, new abstractions are added.  These abstractions don't
* refer to anything in the argument formula, and so "generic" abstractions
* can be pushed down.
**********************************************************************)
exception InvalidFixpointApplication
let applyFixpoint argument =
  (* Normalizing the argument must be done first, before the normalization
   * that might occur during instantiation. The downside is that even if you
   * never abstracted anything your invariant gets abstracted here. *)
  let argument = (eliminateNablas []).abstf argument in

  (********************************************************************
  *normalizeAbstractions:
  * Creates n new variables (where n is the number of lambdas the DB
  * is under) and applies them to the arguments.  Then, it applies
  * the now lambdaless arguments to the target.  It then re-absracts
  * the result over the same n variables.  Finally it frees the
  * generated variables.
  *
  * The reason is this: if you are substituting some P for #0, and
  * you have #0 x y, you want P x y.  But suppose #0 x y is under some
  * abstractions x1\ x2\ #0 x y.  If you substitute x and y into P
  * by application, you get P x y where some parts of P aren't abstracted
  * over x1 and x2, and some parts that are (namely, x and y).  So you
  * make sure to replace x and y (which in this case are really x1\x2\x,
  * and x1\x2\y) with 'ground' x and y.   Then nothing in P x y is
  * abstracted over x1 and x2, so you can just go ahead and do the
  * abstraction and be done.
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
          (fun x -> (abstractVarWithoutLambdas x ()).abstf)
          lambdas' (Option.get target')
      in
      
      (*  Free any bound vars (shouldn't be any). *)
      (List.iter free freeInfo;
      abstarget)
    else
      raise InvalidFixpointApplication
  in

  let tf t = t in
  let rec ff lam db () = {

    formf = (mapFormula (ff lam db) tf).formf ;

    predf = (function
      | FixpointFormula (i,name,args,body) ->
          FixpointFormula (i,name,args,(ff lam (db+1) ()).abstf body)
      | DBFormula(_) -> failwith "Firstorderabsyn.applyFixpoint: \
                                  encountered invalid DB."
      | AtomicFormula(name) -> AtomicFormula name) ;

    abstf = (function
        AbstractionFormula(name,body) -> AbstractionFormula(name,(ff (name::lam) db ()).abstf body)
      | AbstractionBody(f) -> AbstractionBody((ff lam db ()).polf f)) ;

    polf = (function
              | p,ApplicationFormula (DBFormula (lifts,n,db'), args) as f ->
                  if db <> db' then f else
                    let argument =
                      if lifts = 0 then argument else
                        let fresh _ =
                          Term.var ~ts:0 ~lts:0 ~tag:Term.Constant
                        in
                        let generics =
                          let rec mk =
                            function 0 -> [] | n -> fresh () :: mk (n-1)
                          in
                            mk lifts
                        in
                          (eliminateNablas generics).abstf argument
                    in
                      begin match normalizeAbstractions lam argument args with
                        | AbstractionBody pf -> pf
                        | AbstractionFormula _ ->
                            failwith "Firstorderabsyn.applyFixpoint: \
                                      ill-formed fixpoint."
                      end
              | p,f -> p, (ff lam db ()).formf f)
    }
  in

  let catch f x = try Some (f x) with InvalidFixpointApplication -> None in
  let mapf = ff [] 0 () in
  {polf = catch mapf.polf ; predf = catch mapf.predf ; abstf = catch mapf.abstf ; formf = catch mapf.formf}


(**********************************************************************
*matchPattern:
* Match a pattern with a pattern.  If the match succeeds, returns true,
* otherwise returns false.  Note that the less specific pattern should
* be the first argument, so that you don't get false positives: if the
* first argument is "pi _" and the second is "_", the result is false,
* so that if you are using the first to require the second to have the
* the same structure, it actually works.  See firstorderabsyn.ml for
* examples of usage in this way.
**********************************************************************)
let rec matchPattern pattern1 pattern2 =
(*  success: determines whether a unification result indicates
      successful unification. *)
  let success ur =
    match ur with
      UnifySucceeded(s) -> true
    | _ -> false
  in

  (*  Keep track of binding state to undo it later. *)
  let state = Term.save_state () in

  (********************************************************************
  *matchAnnotation:
  * Matches two annotations, respecting 'unspecified' annotations.
  ********************************************************************)
  let matchAnnotation patternAnn formulaAnn =
    (Option.isNone patternAnn.polarity_pattern ||
      patternAnn.polarity_pattern = formulaAnn.polarity_pattern) &&
    (Option.isNone patternAnn.freezing_pattern ||
      patternAnn.freezing_pattern = formulaAnn.freezing_pattern) &&
    (Option.isNone patternAnn.control_pattern ||
      patternAnn.control_pattern = formulaAnn.control_pattern) &&
    (Option.isNone patternAnn.junk_pattern ||
      patternAnn.junk_pattern = formulaAnn.junk_pattern)
  in

  (********************************************************************
  *matchPredicates:
  * Matches predicate patterns.
  ********************************************************************)
  let matchPredicates pattern pred =
    match (pattern, pred) with
        (AtomicPattern(name), AtomicPattern(name')) -> name = name'
      | (AnonymousMu, AnonymousMu)
      | (AnonymousNu, AnonymousNu)
      | (AnonymousPredicate, _) -> true
      | _ -> false
    in
  
  (********************************************************************
  *matchAbstractionFormula:
  ********************************************************************)
  let rec matchAbstractionPattern pattern formula =
    match (pattern, formula) with
        (AbstractionPattern(binder, f), AbstractionPattern(binder', f')) ->
          (binder = "" || binder = binder') && (matchAbstractionPattern f f')
      | (AbstractionBodyPattern(f), AbstractionBodyPattern(f')) ->
          (matchPattern f f')
      | (AnonymousAbstraction, _) -> true
      | _ -> false

  (********************************************************************
  *matchPatterns:
  * Recurse over the structure of patterns, matching them.
  ********************************************************************)
  and matchPatterns pattern1 formula2 =
    let (annotation1, pattern1) = pattern1 in
    let (annotation2, pattern2) = pattern2 in
    
    (*  Polarity Check  *)
    if not (matchAnnotation annotation1 annotation2) then
      false
    else
    
    match (pattern1, pattern2) with
    | (BinaryPattern(c, l,r), BinaryPattern(c', l', r')) ->
        (c = c') && (matchPatterns l l') && (matchPatterns r r')
    | (EqualityPattern(t1, t2), EqualityPattern(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t2 t2'))
    | (QuantifiedPattern(q, f), QuantifiedPattern(q', f')) ->
        (q = q') && (matchAbstractionPattern f f')
    | (ApplicationPattern(AnonymousPredicate,_), _) -> true
    | (ApplicationPattern(head,tl), ApplicationPattern(head',tl')) ->
        (matchPredicates head head') && (List.length tl = List.length tl') &&
        (List.for_all success (List.map2 rightUnify tl tl'))
    | _ -> false
  in
  let result = (matchPatterns pattern1 pattern2) in
  
  (*  Restore the binding state so later matches can work,
      and return the result.  *)
  (Term.restore_state state;
  result)

(**********************************************************************
*matchFormula:
* Match a pattern with a formula.  If the match succeeds, returns true,
* otherwise returns false.
**********************************************************************)
let rec matchFormula pattern formula =
  (*  success: determines whether a unification result indicates
      successful unification. *)
  let success ur =
    match ur with
      UnifySucceeded(s) -> true
    | _ -> false
  in
  
  (*  Keep track of binding state to undo it later. *)
  let state = Term.save_state () in
  
  (********************************************************************
  *matchAnnotation:
  * Matches two annotations, respecting 'unspecified' annotations.
  ********************************************************************)
  let matchAnnotation patternAnn formulaAnn =
    (Option.isNone patternAnn.polarity_pattern ||
      Option.get patternAnn.polarity_pattern = formulaAnn.polarity) &&
    (Option.isNone patternAnn.freezing_pattern ||
      Option.get patternAnn.freezing_pattern = formulaAnn.freezing) &&
    (Option.isNone patternAnn.control_pattern ||
      Option.get patternAnn.control_pattern = formulaAnn.control) &&
    (Option.isNone patternAnn.junk_pattern ||
      Option.get patternAnn.junk_pattern = formulaAnn.junk)
  in

  (********************************************************************
  *matchPredicates:
  * Matches a predicate pattern and a predicate formula.  This match
  * 'hides' the bodies of fixpoints, comparing only names.
  ********************************************************************)
  let matchPredicates p1 p2 =
    
    let (pattern, tl) = p1 in
    let (pred, tl') = p2 in
    match (pattern, pred) with
        (AtomicPattern(name), FixpointFormula(_, name', _, _))
      | (AtomicPattern(name), AtomicFormula(name')) ->
          (name = name') && (List.length tl = List.length tl') &&
          (List.for_all success (List.map2 rightUnify tl tl'))
      | (AnonymousPredicate, _)
      | (AnonymousMu, FixpointFormula(Inductive, _, _, _))
      | (AnonymousNu, FixpointFormula(CoInductive, _, _, _)) -> true
      | _ -> false
  in
  
  (********************************************************************
  *matchAbstractionFormula:
  ********************************************************************)
  let rec matchAbstractionFormula pattern formula =
    match (pattern, formula) with
        (AbstractionPattern(binder, f), AbstractionFormula(binder', f')) ->
          (binder = "" || binder = binder') && (matchAbstractionFormula f f')
      | (AbstractionBodyPattern(f), AbstractionBody(f')) ->
          (matchFormula f f')
      | (AnonymousAbstraction, _) -> true
      | _ -> false

  (********************************************************************
  *matchFormulas:
  * Recurse over the structure of a formula and a pattern, matching
  * them.
  ********************************************************************)
  and matchFormulas pattern formula =
    let (annotation, formula) = formula in
    let (patternAnnotation, pattern) = pattern in
    
    (*  Polarity Check  *)
    if not (matchAnnotation patternAnnotation annotation) then
      false
    else
    
    match (pattern, formula) with
    | (ApplicationPattern(AnonymousPredicate, _), _) -> true
    | (ApplicationPattern(head,tl), ApplicationFormula(head',tl')) ->
        matchPredicates (head,tl) (head', tl')
    | (BinaryPattern(c, l,r), BinaryFormula(c', l', r')) ->
        (c = c') && (matchFormulas l l') && (matchFormulas r r')
    | (EqualityPattern(t1, t2), EqualityFormula(t1', t2')) ->
        (success (rightUnify t1 t1')) && (success (rightUnify t2 t2'))
    | (QuantifiedPattern(q, f), QuantifiedFormula(q', f')) ->
        (q = q') && (matchAbstractionFormula f f')
    | (p,f) -> false
  in
  let result = (matchFormulas pattern formula) in
  
  (*  Restore the binding state so later matches can work,
      and return the result.  *)
  (Term.restore_state state;
  result)

let abstractVarWithoutLambdas var = abstractVarWithoutLambdas var ()
