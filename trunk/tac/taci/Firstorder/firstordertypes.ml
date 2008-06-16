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
module type ParamSig =
sig
  (** The print name of the logic. *)
  val name : string

  (** Determines whether or not strict nabla comparisons are used in the
    * axiom rule. *)
  val strictNabla : bool
  
  (** Indicates whether the logic is intuitionistic instead of classical. *)
  val intuitionistic : bool
end

module type TypesSig =
sig
  (********************************************************************
  *formula:
  * Represent formulae in sequents.  Formulae consist of a local
  * context level and an abstract syntax formula.
  ********************************************************************)
  type formula_annotation = {context : int}
  type formula =
    Formula of (formula_annotation * (Firstorderabsyn.annotation Firstorderabsyn.polarized))
  
  (********************************************************************
  *sequent:
  * A sequent has a left and right side, each a list of formulas, along
  * with an index approximating its signature (set of eigenvariables).
  * Additionally, there are three bounds: bound is the maximum number
  * of synchronous stages to do, async_bound is the maximum number of
  * asynchronous 'progressing' unfoldings to perform, and lemma_bound
  * is the number of times to introduce lemmas.
  ********************************************************************)
  type sequent = {
    lvl : int ;
    lhs : formula list ;
    rhs : formula list ;
    bound : int option ;
    async_bound : int option ;
    lemma_bound : int option ;
  }

  (********************************************************************
  *proof:
  * rule: the name of the rule applied
  * formula: the formula on which the rule was applied
  * sequent: the sequent on which the rule was applied
  * params: the parameters (their names and their values); these are
  *   rule-specific
  * bindings:
  * subs: sub-proofs
  ********************************************************************)
  type proof = {
    rule : string;
    formula : formula option;
    sequent : sequent;
    params : (string * string) list;
    bindings : Term.term list;
    subs : proof list
  }

  (********************************************************************
  *lemmas:
  * Represent
  ********************************************************************)
  type lemma = string * Firstorderabsyn.annotation Firstorderabsyn.polarized * proof

  (********************************************************************
  *session:
  * A session is:
  *   tactical table
  *   definition table
  *   sequents
  *   proof builder
  *   undo info
  *   redo info
  *   lemmas
  ********************************************************************)  
  type session = {
    tactics :
      (session, (sequent, proof) Logic.tactic) Logic.tactical Logic.table ;
    definitions : (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table ;
    sequents : sequent list ; (* current goals *)
    builder : proof Logic.proofbuilder ;
    state : Term.state ;
    diff : Term.subst ;
    initial_namespace : Term.namespace ;
    proof_namespace   : Term.namespace ;
    theorem_name : string option ;
    theorem : (Firstorderabsyn.annotation Firstorderabsyn.polarized) option ;
    lemmas : lemma list
  }

  val annotateFormula : Firstorderabsyn.annotation -> string -> string
  val string_of_formula : formula -> string
  val string_of_formula_ast : formula -> string
  val xml_of_formula : formula -> string

  val parsePattern : string -> Firstorderabsyn.pattern_annotation Firstorderabsyn.polarized_pattern option
  val parseInvariant :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.abstraction option
  val parseFormula :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.polarized option
  val parseDefinition :
    (Firstorderabsyn.annotation Firstorderabsyn.definition) Logic.table -> string -> 
    Firstorderabsyn.annotation Firstorderabsyn.definition option

  val parseTerm : string -> Term.term option

  val updateBound : int option -> int option
  val resetAsyncBound : sequent -> sequent
  val outOfBound : sequent -> bool
  val lemmaOutOfBound : sequent -> bool
  
  val makeExistentialVar : string -> int -> int -> (int * Term.term)
  val makeUniversalVar : string -> int -> int -> (int * Term.term)
  val makeNablaVar : int -> int -> (int * int * Term.term)
  
  val modifyFormulaAnnotations :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    Firstorderabsyn.annotation Firstorderabsyn.polarized ->
    Firstorderabsyn.annotation Firstorderabsyn.polarized
  val modifySequentAnnotations :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    sequent ->
    sequent
  
  val composeModifiers :
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation) ->
    (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)

  val freezeModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val unfreezeModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val unfocusModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  val idModifier : (Firstorderabsyn.annotation Firstorderabsyn.polarized -> Firstorderabsyn.annotation)
  
  val focusFormula : formula -> formula
  val freezeFormula : formula -> formula
  
  val makeFormula : Firstorderabsyn.annotation Firstorderabsyn.polarized -> formula
end

module Types (O : Output.Output) =
struct
  module FOA = Firstorderabsyn

  type formula_annotation = {context : int}
  type formula =
    Formula of (formula_annotation * (Firstorderabsyn.annotation Firstorderabsyn.polarized))
  
  type sequent = {
    lvl : int ;
    lhs : formula list ;
    rhs : formula list ;
    bound : int option ;
    async_bound : int option ;
    lemma_bound : int option ;
  }

  type proof = {
    rule : string;
    formula : formula option;
    sequent : sequent;
    params : (string * string) list;
    bindings : Term.term list;
    subs : proof list
  }

  type lemma = string * FOA.annotation FOA.polarized * proof

  type session = {
    tactics :
      (session, (sequent, proof) Logic.tactic) Logic.tactical Logic.table ;
    definitions : (FOA.annotation FOA.definition) Logic.table ;
    sequents : sequent list ; (* current goals *)
    builder : proof Logic.proofbuilder ;
    state : Term.state ;
    diff : Term.subst ;
    initial_namespace : Term.namespace ;
    proof_namespace   : Term.namespace ;
    theorem_name : string option ;
    theorem : (FOA.annotation FOA.polarized) option ;
    lemmas : lemma list
  }


  let annotateFormula ann formula =
    (FOA.string_of_control ann.FOA.control) ^ " " ^
    (FOA.string_of_polarity ann.FOA.polarity) ^
    formula ^
    (FOA.string_of_freezing ann.FOA.freezing)

  let string_of_formula (Formula(local,(a,t))) =
    let generic = Term.get_dummy_names ~start:1 local.context "n" in
    let result = (FOA.string_of_formula ~generic).FOA.formf t in
      List.iter Term.free generic ;
      (String.concat "," generic) ^ ">> " ^ (annotateFormula a result)

  let string_of_formula_ast (Formula(local,(a,t))) =
    let generic = Term.get_dummy_names ~start:1 local.context "n" in
    let result = (FOA.string_of_formula_ast ~generic).FOA.formf t in
      List.iter Term.free generic ;
      (String.concat "," generic) ^ ">> " ^ (annotateFormula a result)

  (********************************************************************
  *escapeTerm:
  * Hackery to escape xml.
  *
  * TODO: fill in this list.
  ********************************************************************)
  let regexes =
    [(Str.regexp "<", "&lt;");
    (Str.regexp ">", "&gt;")]
  let escapeTerm s =
    List.fold_left
      (fun s (regex, replace) -> Str.global_replace regex replace s)
      s
      regexes

  (********************************************************************
  *xml_of_formula:
  * Generates valid xml from a formula.
  ********************************************************************)
  let xml_of_formula (Formula(local,(a,t))) = 
    let generic = Term.get_dummy_names ~start:1 local.context "n" in
    let result = escapeTerm ((FOA.string_of_formula ~generic).FOA.formf t) in
      List.iter Term.free generic ;
      Printf.sprintf "<formula>%s%s</formula>"
         ("<generic>" ^ String.concat "," generic ^ "</generic>")
        (annotateFormula a result)

  let generateSymbol =
    let currentId = ref (-1) in
      fun () ->
        incr currentId ;
        ("_" ^ (string_of_int !currentId))

  (********************************************************************
  *replaceApplications:
  * Replaces applications in a formula with the correct definition,
  * if one exists.  If the application doesn't have the correct number
  * of arguments (relative to the body of the definition) then new
  * arguments are created to bring the number up to the correct amount,
  * and abstractions are inserted.  If the atom being replaced is under
  * any abstractions, the body of the definition that is being inserted
  * must be abstracted the same number of times as the atom is under
  * abstractions.
  ********************************************************************)
  let replaceApplications defs =
    (******************************************************************
    *makeArgs:
    * Generates a list of new names of length i.  This is only used
    * if the incorrect number of arguments were applied to a definition,
    * for example if using the body of definition as an invariant.
    ******************************************************************)
    let rec makeArgs i =
      if i = 0 then
        []
      else
        (generateSymbol ()) :: makeArgs (i - 1)
    in
    
    (******************************************************************
    *makeAbstractions:
    * Used to abstract the body of a definition over the new arguments;
    * used in the case that too few arguments are passed to the
    * definition.
    ******************************************************************)
    let rec makeAbstractions args formula =
      match args with
        [] -> formula
      | a::aa ->
          (FOA.abstractWithoutLambdas a ()).FOA.formf
            (makeAbstractions aa formula)
    in

    (* Takes the predicate f applied to args, and the surrounding annotation.
     * Returns a polarized. *)
    let predp lambdas annot f args =
      let head =
        match f with FOA.AtomicPattern head -> head | _ -> assert false
      in
        match Logic.find head defs with
          | None ->
              let default_pol =
                if head = "true" || head = "false" then
                  FOA.Positive
                else
                  FOA.Negative
              in
              FOA.patternAnnotationToFormulaAnnotation default_pol annot,
              FOA.ApplicationFormula(FOA.AtomicFormula head, args)
          | Some def ->
              let arity = FOA.getDefinitionArity def in
              let body = FOA.predicateofDefinition def in
              let annot =
                FOA.patternAnnotationToFormulaAnnotation
                  (match annot.FOA.polarity_pattern with
                     | Some p -> p
                     | None ->
                         begin match body with
                           | FOA.FixpointFormula (FOA.Inductive,_,_,_) ->
                               FOA.Positive
                           | FOA.FixpointFormula (FOA.CoInductive,_,_,_) ->
                               FOA.Negative
                           | _ -> assert false
                         end)
                  annot
              in
              if arity = List.length args then
                (*  Correct number of arguments.  *)
                annot,
                FOA.ApplicationFormula
                  (FOA.lift_pred lambdas body, args)
              else if arity > List.length args then
                (*  Too few arguments; eta-expansion.  *)
                let argnames = makeArgs (arity - (List.length args)) in
                let args' = args @ (List.map (Term.atom) argnames) in
                annot,
                makeAbstractions argnames
                  (FOA.ApplicationFormula
                     ((FOA.lift_pred lambdas body),args'))
              else             
                raise (FOA.SemanticError("'" ^ head ^
                                         "' applied to too many arguments"))
    in
    let defpos = FOA.patternAnnotationToFormulaAnnotation FOA.Positive in
    let defneg = FOA.patternAnnotationToFormulaAnnotation FOA.Negative in
    let rec ff lambdas =
      let rec self = {

        FOA.predp =
          (fun _ _ ->
            (* We shouldn't need it ?
             * We can't use the above predp function because it wants
             * a polarity annotation, and there is none: I prefer to wait for a
             * need rather than fake a polarity here. *)
            assert false) ;

        FOA.formp = (fun f -> (* Everything is done in polp *) assert false) ;

        FOA.abstp = (function
          | FOA.AbstractionPattern (name,f) ->
              FOA.AbstractionFormula (name,(ff (1+lambdas)).FOA.abstp f)
          | FOA.AbstractionBodyPattern f ->
              FOA.AbstractionBody (self.FOA.polp f)
          | _ -> assert false) ;

        FOA.polp = (fun (p,f) -> match f with

          (* Positive connectives *)
          | FOA.BinaryPattern((FOA.And|FOA.Or as c),l,r) ->
              defpos p, FOA.BinaryFormula (c,self.FOA.polp l, self.FOA.polp r)
          | FOA.EqualityPattern(l,r) ->
              defpos p, FOA.EqualityFormula (l,r)
          | FOA.QuantifiedPattern(FOA.Sigma,f) ->
              defpos p, FOA.QuantifiedFormula(FOA.Sigma,self.FOA.abstp f)

          (* Negative connectives *)
          | FOA.BinaryPattern(FOA.Imp,l,r) ->
              defneg p,
              FOA.BinaryFormula (FOA.Imp,self.FOA.polp l, self.FOA.polp r)
          | FOA.QuantifiedPattern(FOA.Pi,f) ->
              defneg p, FOA.QuantifiedFormula(FOA.Pi,self.FOA.abstp f)

          (* Special cases *)
          | FOA.QuantifiedPattern(FOA.Nabla,f) ->
              let f = self.FOA.abstp f in
              let subp =
                let rec get = function
                  | FOA.AbstractionFormula (_,f) -> get f
                  | FOA.AbstractionBody (p,f) -> p
                in
                  get f
              in
                FOA.patternAnnotationToFormulaAnnotation
                  (match p.FOA.polarity_pattern with
                     | Some pol -> pol | None -> subp.FOA.polarity)
                  p,
                FOA.QuantifiedFormula (FOA.Nabla,f)
          | FOA.ApplicationPattern(pred,args) -> predp lambdas p pred args) }
      in self
    in
    ff 0

  (********************************************************************
  *parseTerm:
  * Parses the argument into a term using the ocamlyacc grammar (see
  * firstorderparser.mly).  If successful, returns Some with the parsed
  * term, otherwise it returns None.
  ********************************************************************)
  let parseTerm t =
    try
      let term =
        Firstorderparser.toplevel_term
          Firstorderlexer.token (Lexing.from_string t)
      in
        Some term
    with
      | FOA.SyntaxError(s) ->
          O.error (s ^ ".\n");
          None

  (********************************************************************
  *parsePattern:
  * Parses the argument into a pattern.  If successful, returns Some
  * with the parsed pattern, otherwise it returns None.
  ********************************************************************)
  let parsePattern t =
    try
      Some
       (Firstorderparser.toplevel_pattern
         Firstorderlexer.token (Lexing.from_string t))
    with
        FOA.SyntaxError(s) ->
          O.error (s ^ ".\n");
          None
      | FOA.SemanticError(s) ->
          O.error (s ^ ".\n");
          None
      | Parsing.Parse_error ->
          O.error "Syntax error.\n";
          None

  (********************************************************************
  *parseFormula:
  * Parses the argument into a formula.  If successful, returns Some
  * with the parsed formula, otherwise it returns None.
  ********************************************************************)
  let parseFormula defs t =        
    try
      let formula =
        Firstorderparser.toplevel_pattern
          Firstorderlexer.token (Lexing.from_string t)
      in
      let formula = (replaceApplications defs).FOA.polp formula in

        (* TODO note that it prints a string, thus uses names *)
        O.debug (Printf.sprintf
          "Firstorder.parseFormula: formula: %s.\n"
          ((FOA.string_of_formula ~generic:[]).FOA.polf formula)) ;
        O.debug (Printf.sprintf
          "Firstorder.parseFormula: formula ast: %s.\n"
          ((FOA.string_of_formula_ast ~generic:[]).FOA.polf formula)) ;

        Some formula
    with
        FOA.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          None)
      | FOA.SemanticError(s) ->
          (O.error (s ^ ".\n");
          None)
      | Parsing.Parse_error ->
          (O.error "Syntax error.\n";
          None)

  (********************************************************************
  *parseInvariant
  * Parses the argument into an invariant.  If successful, returns Some
  * with the parsed invariant, otherwise it returns None.  Note that
  * this does not guarantee an invariant of a particular arity (i.e.,
  * the arity could be 0).
  ********************************************************************)
  let parseInvariant defs t =        
    try
      let invariant =
        Firstorderparser.toplevel_invariant
          Firstorderlexer.token (Lexing.from_string t)
      in
      let invariant' = (replaceApplications defs).FOA.abstp invariant in

        O.debug (Format.sprintf
          "Firstorder.parseInvariant: invariant: %s\n"
          ((FOA.string_of_formula ~generic:[]).FOA.abstf invariant')) ;
        O.debug (Printf.sprintf
          "Firstorder.parseInvariant: invariant ast: %s\n"
          ((FOA.string_of_formula_ast ~generic:[]).FOA.abstf invariant')) ;

        Some invariant'
    with
        FOA.SyntaxError(s) ->
          O.error (s ^ ".\n");
          None
      | FOA.SemanticError(s) ->
          O.error (s ^ ".\n");
          None
      | Parsing.Parse_error ->
          O.error "Syntax error.\n";
          None

  (********************************************************************
  *parseDefinition:
  * Parses the argument into a definition.  If successful, returns Some
  * with the parsed definition, otherwise it returns None.
  ********************************************************************)
  let parseDefinition defs t =        
    try
      let FOA.PreDefinition (name,args,body,ind) =
        Firstorderparser.toplevel_definition
          Firstorderlexer.token (Lexing.from_string t)
      in
      let body = (replaceApplications defs).FOA.abstp body in
      let () =
        O.debug (Printf.sprintf
          "Firstorder.parseDefinition: predefinition ast: %s %s.\n"
          name
          ((FOA.string_of_formula_ast ~generic:[]).FOA.abstf body)) ;
        O.debug (Printf.sprintf
          "Firstorder.parseDefinition: predefinition: %s %s.\n"
          name
          ((FOA.string_of_formula ~generic:[]).FOA.abstf body))
      in
      Some (FOA.Definition(name,args,body,ind))
    with
        FOA.SyntaxError(s) ->
          O.error (s ^ ".\n");
          None
      | FOA.SemanticError(s) ->
          O.error (s ^ ".\n");
          None
      | Parsing.Parse_error ->
          O.error "Syntax error.\n";
          None

  (********************************************************************
  *Bound Manipulation
  ********************************************************************)
  let updateBound = function
    | None -> None
    | Some b -> Some (b-1)

  let resetAsyncBound s =
    { s with async_bound =
      (if Properties.getBool "firstorder.asyncbound" then
        Some (Properties.getInt "firstorder.defaultasyncbound")
      else
        None)}

  let outOfBound seq =
    (match seq with
       | { bound = Some b } -> b<0 | { bound = None } -> false) ||
    (match seq with
       | { async_bound = Some b } -> b<0 | { async_bound = None } -> false)

  let lemmaOutOfBound seq =
    (match seq with
       | { lemma_bound = Some b } -> b <= 0
       | { lemma_bound = None } -> assert false)

  (********************************************************************
  *makeExistentialVar/makeUniversalVar/makeNablaVar:
  * Makes a new Term var (see ndcore/term.mli) of the approriate type
  * and returns it along with the updated local context and sequent level.
  ********************************************************************)
  let makeExistentialVar hint lvl lts =
    let hint = String.capitalize hint in
    let var = Term.fresh ~name:hint ~lts:0 ~ts:lvl ~tag:Term.Logic in
    let rec raise_over x n =
      if n = 0 then x else
        Term.app (raise_over x (n-1)) [Term.nabla n]
    in
    let var = raise_over var lts in
    (lvl, var)

  let makeUniversalVar hint lvl lts =
    let lvl = lvl+1 in
    let var = Term.fresh ~name:hint ~lts:0 ~ts:lvl ~tag:Term.Eigen in
    let rec raise_over x n =
      if n = 0 then x else
        Term.app (raise_over x (n-1)) [Term.nabla n]
    in
    let var = raise_over var lts in
    (lvl, var)

  let makeNablaVar lvl i =
    (lvl, i + 1, Term.nabla (i + 1))

  (********************************************************************
  *modifyFormulaAnnotations:
  * Modifies *all* of the annotations in a formula.
  ********************************************************************)
  let modifyFormulaAnnotations modifier f =
    let tf x = x in
    let rec ff () =
      let f' = FOA.mapFormula ff tf in
      {f' with
        FOA.polf = fun ((ann, f) as arg) ->
          let ann' = modifier arg in
          (ann', (ff ()).FOA.formf f)}
    in
    (ff ()).FOA.polf f

  (*  focusFormula/freezeFormula: similar to above, but only modify the
      toplevel annotation. *)
  let focusFormula (Formula(i,(a,f))) = Formula (i,({a with FOA.control=FOA.Focused},f))
  let freezeFormula (Formula(i,(a,f))) = Formula (i, ({a with FOA.freezing = FOA.Frozen}, f))

  (********************************************************************
  *modifySequentAnnotations:
  * For every formula in a sequent, applies the annotation modifying
  * function.
  ********************************************************************)
  let modifySequentAnnotations modifier seq =
    let modifySequentFormula (Formula(i,f)) =
      Formula(i, modifyFormulaAnnotations modifier f)
    in
    {seq with
      lhs = List.map modifySequentFormula seq.lhs;
      rhs = List.map modifySequentFormula seq.rhs}
  
  (*  Useful modifiers  *)
  let unfreezeModifier (ann, f) = {ann with FOA.freezing = FOA.Unfrozen}
  let unfocusModifier (ann, f) = {ann with FOA.control = FOA.Normal}
  let freezeModifier (ann, f) = {ann with FOA.freezing = FOA.Frozen}
  let idModifier (ann, f) = ann
  
  (*  Compose two modifiers so that they work one after the other.  *)
  let composeModifiers m1 m2 ((ann, f) as arg) =
    let ann' = (m1 arg) in
    m2 (ann', f)

  let makeFormula f = Formula({context = 0}, f)

end
