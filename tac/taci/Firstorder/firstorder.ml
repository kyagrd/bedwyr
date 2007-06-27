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
* MERCHANTABILITY or FITNESS FOR A PARTICUFOAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
module FOA = Firstorderabsyn

(**********************************************************************
*NablaSig:
* Contains a value strictNabla determining whether or not strict nabla
* comparisons are used in the axiom rule.  Passed to Firstorder
**********************************************************************)
module type ParamSig =
sig
  val name : string
  val strictNabla : bool
  val intuitionistic : bool
end

(**********************************************************************
*Firstorder:
* Implements a simple first order logic with equality.  Parameterized
* so that logics with or without nabla strictness can be constructed.
**********************************************************************)
module Firstorder (Param : ParamSig) (O : Output.Output) : Logic.Logic =
struct
  let name = Param.name
  let info = Param.name
  let start = info
  
  (********************************************************************
  *Formula:
  * Represent formulae in sequents, with a local context.
  ********************************************************************)
  type formula = (int * FOA.formula)
  let getFormulaFormula (_,f) = f
  let string_of_formula (_,t) = FOA.string_of_formula t
  let string_of_formula_ast (_,t) = FOA.string_of_formula_ast t
  let makeFormula t = (0, t)
  let string_of_definition def = FOA.string_of_definition def
  
  (********************************************************************
  *Sequent:
  * A sequent has a left and right side, each a list of terms, along
  * with an index used during unification to determine which variables
  * may bind with what terms.
  ********************************************************************)
  type sequent = (int * formula list * formula list)
  let makeSequent l r = (0, l, r)
  let emptySequent = (0, [], [])
  let getSequentLevel (l,_,_) = l
  let getSequentLHS (_,l,_) = l
  let getSequentRHS (_,_,r) = r

  (********************************************************************
  *Proof:
  ********************************************************************)
  type proof = string
  let string_of_proofs proofs =
    "\t" ^ (String.concat "\n\t" proofs) ^ "\n"

  (********************************************************************
  *Session:
  * A session is:
  *   tactical table
  *   definition table
  *   sequents
  *   proof builder
  *   undo info
  *   redo info
  ********************************************************************)  
  type session = Session of
    ((session, (sequent, proof) Logic.tactic) Logic.tactical Logic.table *
    FOA.definition Logic.table *
    sequent list *
    proof Logic.proofbuilder *
    Term.bind_state * Term.subst)

  let getSessionSequents (Session(_,_,sequents,_,_,_)) = sequents
  let setSessionSequents sequents (Session(t,d,_,pb,u,r)) = (Session(t,d,sequents,pb,u,r))
  let getSessionBuilder (Session(_,_,_,b,_,_)) = b
  let setSessionBuilder builder (Session(t,d,s,_,u,r)) = (Session(t,d,s,builder,u,r))
  let getSessionUndo (Session(_,_,_,_,u,_)) = u
  let getSessionRedo (Session(_,_,_,_,_,r)) = r
  let getSessionTacticals (Session(t,_,_,_,_,_)) = t
  let setSessionTacticals tacs (Session(_,d,s,pb,u,r)) = (Session(tacs,d,s,pb,u,r))
  let getSessionDefinitions (Session(_,d,_,_,_,_)) = d
  let setSessionDefinitions defs (Session(t,_,s,pb,u,r)) = (Session(t,defs,s,pb,u,r))
  
  let proof session = getSessionBuilder session
  
  let string_of_sequent seq =
    let lhs = getSequentLHS seq in
    let rhs = getSequentRHS seq in
    let lvl = getSequentLevel seq in
    let top = (String.concat "\n" (List.map string_of_formula lhs)) in
    let bottom = (String.concat "\n" (List.map string_of_formula rhs)) in
    (top ^ "\n" ^ (string_of_int lvl) ^ ": " ^ (String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)

  let string_of_sequent_rhs seq =
    let rhs = getSequentRHS seq in
    let lvl = getSequentLevel seq in
    let bottom = (String.concat "\n" (List.map string_of_formula rhs)) in
    ((string_of_int lvl) ^ ": " ^ (String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)
    
  let string_of_sequents sequents =
    let mainseq = List.hd sequents in
    let seqs = List.tl sequents in
    if (List.length seqs) > 0 then
      (string_of_sequent mainseq) ^ "\n\n" ^ (String.concat "\n\n" (List.map string_of_sequent_rhs seqs)) ^ "\n"
    else
      (string_of_sequent mainseq) ^ "\n"

  (********************************************************************
  *incl:
  * Given a list of files, include all definitions in them.
  ********************************************************************)
  let incl files session =
    (O.error "logic does not implement #include.";
    session)
  
  (********************************************************************
  *parseTerm:
  * Parses the argument into a term.  If successful, returns Some
  * with the parsed term, otherwise it returns None.
  ********************************************************************)
  let parseTerm t =
    try
      let term = Firstorderparser.toplevel_term Firstorderlexer.token (Lexing.from_string t) in
      Some term
    with
      FOA.SyntaxError(s) ->
        (O.error (s ^ ".\n");
        None)
  
  let currentId = ref 0
  let generateSymbol () =
    let s = "_" ^ (string_of_int !currentId) in
    let () = currentId := !currentId + 1 in
    s

  (********************************************************************
  *replaceApplications:
  * Replaces applications in a formula with the correct definition,
  * if one exists.  If the application doesn't have the correct number
  * of arguments (relative to the body of the definition) then new
  * arguments are created to bring the number up to the correct amount,
  * and abstractions are inserted.
  ********************************************************************)
  let replaceApplications defs formula =
    let rec makeArgs i =
      if i = 0 then
        []
      else
        (generateSymbol ()) :: makeArgs (i - 1)
    in
    
    let rec makeAbstractions args formula =
      match args with
        [] -> formula
      | a::aa ->  FOA.AbstractionFormula(a, (makeAbstractions aa formula))
    in
      

    let tf t = t in
    let rec ff f =
      match f with
          FOA.AtomicFormula(t) ->
            let ha = FOA.getTermHeadAndArgs t in
            if (Option.isSome ha) then
              let (head, args) = Option.get ha in
              let def = Logic.find head defs in
              if (Option.isSome def) then
                let def = (Option.get def) in
                let arity = FOA.getDefinitionArity def in
                let body = FOA.getDefinitionBody def in
                if (arity = List.length args) then
                  FOA.ApplicationFormula(body, args)
                else if arity > List.length args then
                  let args' = makeArgs (arity - (List.length args)) in
                  makeAbstractions args' (FOA.ApplicationFormula(body, args@(List.map (Term.atom) args')))
                else             
                  raise (FOA.SemanticError("'" ^ head ^ "' applied to too many arguments"))
              else
                f
            else
              f
        | _ -> (FOA.mapFormula ff tf f)
    in
    (ff formula)
  
  
  (********************************************************************
  *application:
  * Apply arguments.
  ********************************************************************)
  let rec application args formula =
    match args with
      [] -> Some formula
    | a::aa ->
        (match formula with
            FOA.AbstractionFormula(name,f) ->
              let f' = FOA.abstract name f in
              (application aa (FOA.apply [a] f'))
          | _ -> (O.error "expected abstraction.\n"; None))

  (********************************************************************
  *processFormula:
  * Replaces applications and then applies abstractions.
  ********************************************************************)
  let processFormula defs f =
    let f' = replaceApplications defs f in
    f'
    
  (********************************************************************
  *parseFormula:
  * Parses the argument into a formula.  If successful, returns Some
  * with the parsed formula, otherwise it returns None.
  ********************************************************************)
  let parseFormula defs t =        
    try
      let formula = Firstorderparser.toplevel_formula Firstorderlexer.token (Lexing.from_string t) in
      Some (processFormula defs formula)
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
  *parseDefinition:
  * Parses the argument into a definition.  If successful, returns Some
  * with the parsed definition, otherwise it returns None.
  ********************************************************************)
  let parseDefinition defs t =        
    try
      let FOA.PreDefinition(name,args,body,ind) = Firstorderparser.toplevel_definition Firstorderlexer.token (Lexing.from_string t) in
      Some (FOA.PreDefinition(name,args,(replaceApplications defs body),ind))
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
  *prove:
  * Parses the argument into a formula, and then prepares the session to
  * prove the formula.
  ********************************************************************)
  let prove name t session =
    let defs = getSessionDefinitions session in
    let f = parseFormula defs t in
    if Option.isSome f then
      let f = Option.get f in
      let seq = makeSequent [] [makeFormula f] in
      (setSessionBuilder Logic.idProofBuilder (setSessionSequents [seq] session))
    else
      session

  (********************************************************************
  *definitions:
  * Given a list of strings representing possibly mutually-recursive
  * definitions, parses the definitions and adds them to the definition
  * table.
  ********************************************************************)
  let definitions defstrings session =
    (******************************************************************
    *processPreDefinitions:
    * Processes a list of mutually recursive predefinitions into
    * a list of definitions.
    ******************************************************************)
    let processPreDefinitions predefs =
      (****************************************************************
      *makeFixpoint:
      * Makes a mu or nu formula based on the combinator type.
      ****************************************************************)
      let makeFixpoint ind name body =
        match ind with
            FOA.Inductive ->
              FOA.MuFormula(name,body)
          | FOA.CoInductive ->
              FOA.NuFormula(name,body)
      in
      
      (****************************************************************
      *abstractDefinition:
      * Abstracts a definition.  Iterates over a definition body.
      * If it hits an application whose name is in the abstractions
      * list, it inserts the correct DB index.  If it hits an application
      * whose head is not in the abstractions list (but is in then pre-
      * definitions list), it adds the name to the abstractions list 
      * and abstracts the body of the pre-definition.
      ****************************************************************)
      let abstractDefinition abstractions f =
        (**************************************************************
        *getDB:
        * Get the DB index of a name.
        **************************************************************)
        let getDB name abs =
          let rec get name abs =
            match abs with
              [] -> None
            | a::abs' ->
                if a = name then
                  Some 0
                else
                  let r = (get name abs') in
                  if Option.isSome r then
                    Some (1 + (Option.get r))
                  else
                    None
          in
          let i = (get name abs) in
          i
        in
        
        (**************************************************************
        *findDefinition:
        * Finds a pre-definition in the pre-definition list.
        **************************************************************)
        let findDefinition name predefs =
          try
            let find name (FOA.PreDefinition(name',ids,formula,ind)) =
              name' = name
            in
            Some (List.find (find name) predefs)
          with
            Not_found -> None
        in
        
        
        let tf t = t in  
        let rec ff abstractions f =
          match f with
              FOA.AtomicFormula(t) ->
                let ha = FOA.getTermHeadAndArgs t in
                if (Option.isSome ha) then
                  let (head,args) = Option.get ha in
                  let db = getDB head abstractions in
                  if Option.isSome db then
                    FOA.ApplicationFormula(FOA.DBFormula(head, Option.get db), args)
                  else
                    let def = findDefinition head predefs in
                    if Option.isSome def then
                      let FOA.PreDefinition(_,_,f',ind) = (Option.get def) in
                      (makeFixpoint ind head (ff (head::abstractions) f'))
                    else
                      f
                else
                  (O.error ("term has no head: " ^ (FOA.string_of_term t));
                  f)
            | _ -> (FOA.mapFormula (ff abstractions) tf f)
        in
        (ff abstractions f)
      in
      
      (****************************************************************
      *abstractArguments:
      * Pushes down the argument abstractions.
      *****************************************************************)
      let rec abstractArguments ids formula =
        match ids with
          [] -> formula
        | id::ids' ->
            FOA.AbstractionFormula(id, (abstractArguments ids' formula))
      in
      
      (****************************************************************
      *processPreDefinition:
      * Mu/Nu-abstracts the body of the predefinition, wraps the body
      * in a Mu/Nu formula, and applies abstractions in the formula.
      ****************************************************************)
      let processPreDefinition (FOA.PreDefinition(name, ids, formula, ind)) =
        let formula' = abstractDefinition [name] formula in
        let formula'' = abstractArguments ids formula' in
        let formula''' = makeFixpoint ind name formula'' in
        
        FOA.Definition(name, List.length ids, formula''', ind)
      in
      (List.map processPreDefinition predefs)
    in
    
    (******************************************************************
    *addDefinitions:
    * Given a list of definitions and a table, adds the definitions
    * to the table, but doesn't allow for redefinitions.
    ******************************************************************)
    let rec addDefinitions defs table =
      match defs with
        [] -> table
      | (FOA.Definition(name,arity,formula,ind) as def)::ds ->
          if (Logic.contains name table) then
            (O.error ("'" ^ name ^ "' already defined.\n");
            table)
          else
            let () = O.output ("Definition: " ^ (string_of_definition def) ^ ".\n") in
            Logic.Table.add name def (addDefinitions ds table)
    in
        
    let predefs = (List.map (parseDefinition (getSessionDefinitions session)) defstrings) in
    if (List.exists (Option.isNone) predefs) then
      (O.error "definitions contain errors.\n";
      session)
    else
      let defs = processPreDefinitions (List.map (Option.get) predefs) in
      let defs' = (addDefinitions defs (getSessionDefinitions session)) in
      (setSessionDefinitions defs' session)

  let operator name fix prec session = session
  let update sequents builder session =
    (setSessionSequents sequents (setSessionBuilder builder session))

  let validSequent session =
    let sequents = (getSessionSequents session) in
    (List.length sequents > 0)

  let undo session =
    let undo = getSessionUndo session in
    let () = Term.restore_state undo in
    session

  let redo session =
    let redo = getSessionRedo session in
    let _ = Term.apply_subst redo in
    session

  let sequents session = (getSessionSequents session)
      
  (********************************************************************
  *copySequent:
  * Copy the terms in a sequent so that left-unification doesn't
  * introduce invalid unifiers.
  ********************************************************************)
  let copySequent (i,lhs,rhs) =
    let copier = Term.copy () in
    let copyTerm t = copier t in
    let rec copyFormula f = FOA.mapFormula copyFormula copyTerm f in
    
    let lhs' = List.map (fun (i,f) -> (i, copyFormula f)) lhs in
    let rhs' = List.map (fun (i,f) -> (i, copyFormula f)) rhs in
    (i, lhs', rhs')


  let makeExistentialVar lvl lts =
  (lvl, Term.fresh ~tag:Term.Logic ~lts lvl)

  let makeUniversalVar lvl lts =
    (lvl + 1, Term.fresh ~tag:Term.Eigen ~lts (lvl + 1))

  let makeNablaVar lvl i =
    (lvl, i + 1, Term.nabla (i + 1))

  (********************************************************************
  *Tacticals:
  ********************************************************************)
  module FirstorderSig =
  struct
    type logic_session = session
    type logic_sequent = sequent
    type logic_proof = proof
  end
  module G = Logic.GenericTacticals (FirstorderSig) (O)
  
  (********************************************************************
  *makeProofBuilder:  
  ********************************************************************)
  let makeProofBuilder s = fun proofs ->
    s ^ "(" ^ (String.concat ", " proofs) ^ ")"

  (********************************************************************
  *findFormula:
  * Given a template and a list of formulas F, returns the first formula
  * that matches the template along with a function that, when given
  * a list of formulas F', returns F with the found formula replaced
  * with F'.
  ********************************************************************)
  let findFormula template formulas =
    let rec find front formulas =
      match formulas with
        [] -> None
      | formula::fs ->
          let f = getFormulaFormula formula in
          if (FOA.matchFormula template f) then
            let zip rest = fun list ->
              (List.rev_append front list) @ rest
            in
            Some(formula, zip fs)
          else
            find (formula::front) fs
    in
    find [] formulas

  (********************************************************************
  *matchLeft, matchRight:
  * Given a pattern and a sequent, finds the first element on the left
  * (or right) that matches the pattern, and returns a tuple with:
  *   the matching formula
  *   a zipper for the left (or right)
  *   the whole left
  *   the whole right
  ********************************************************************)
  let matchLeft pattern sequent =
    let lhs = getSequentLHS sequent in
    let rhs = getSequentRHS sequent in
    let result = findFormula pattern lhs in
    match result with
      Some(f,zip) -> Some(f,zip,lhs,rhs)
    | None -> None
    
  let matchRight pattern sequent =
    let lhs = getSequentLHS sequent in
    let rhs = getSequentRHS sequent in
    let result = findFormula pattern rhs in
    match result with
      Some(f,zip) -> Some(f,zip,lhs,rhs)
    | None -> None

  (********************************************************************
  *makeTactical:
  * Given a matcher and a tactic, creates a tactical that applies
  * the given tactic to the first formula in the sequent that matches
  * the tactic.  If none match, it fails.
  ********************************************************************)
  let makeTactical name matcher tactic =
    let tactic' = fun sequent sc fc ->
      let sc' s = sc s (makeProofBuilder name) fc in
      match (matcher sequent) with
        Some(f, zip, lhs, rhs) -> tactic sequent f zip lhs rhs sc' fc
      | None -> fc ()
    in
    (G.makeTactical tactic')
  
  (********************************************************************
  *makeBinaryTactical:
  * Given the name of a tactic, a matcher constructore (either matchLeft or
  * matchRight), a default template for use if none is specified, and
  * a tactic, finds a formula to operate on using the matcher and applies
  * the tactic.
  ********************************************************************)
  let makeBinaryTactical name (matchbuilder, defaulttemplate) tactic =
    fun session args ->
      let defaulttemplate =
        parseFormula (getSessionDefinitions session) defaulttemplate in
      if Option.isSome defaulttemplate then
        let defaulttemplate = Option.get defaulttemplate in
        match args with
            [] -> (makeTactical name (matchbuilder defaulttemplate) tactic)
          | Absyn.String(s)::[] ->
              let template = parseFormula (getSessionDefinitions session) s in
              if (Option.isSome template) &&
                (FOA.matchFormula defaulttemplate (Option.get template)) then
                (makeTactical name (matchbuilder (Option.get template)) tactic)
              else
                (G.invalidArguments (name ^ ": invalid template."))
          | _ -> (G.invalidArguments (name ^ ": incorrect number of arguments."))
      else
        (G.invalidArguments (name ^ ": invalid default template."))
  
  (********************************************************************
  *axiom:
  ********************************************************************)
  let axiomTactical session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec unifyList sc lhs f =
            match f with
                (i, FOA.AtomicFormula(t)) ->
                  (match lhs with
                    [] -> ()
                  | (i', FOA.AtomicFormula(t'))::ls ->
                      if (not Param.strictNabla) || i = i' then
                        (match (FOA.rightUnify t t') with
                            FOA.UnifySucceeded -> sc ()
                          | FOA.UnifyFailed -> (unifyList sc ls f)
                          | FOA.UnifyError(s) ->
                              (O.error (s ^ ".\n");
                              fc ()))
                      else
                        (unifyList sc ls f)
                  | _::ls ->
                      (unifyList sc ls f))
              | (i,FOA.ApplicationFormula(FOA.MuFormula(n1,_),args)) ->
                  (match lhs with
                    [] -> ()
                  | (i', FOA.ApplicationFormula(FOA.MuFormula(n1',_),args'))::ls ->
                      if n1 = n1' then
                        (match (FOA.unifyList FOA.rightUnify args args') with
                            FOA.UnifySucceeded -> sc ()
                          | FOA.UnifyFailed -> (unifyList sc ls f)
                          | FOA.UnifyError(s) ->
                              (O.error (s ^ ".\n");
                              fc ()))
                      else
                        (unifyList sc ls f)
                  | _::ls ->
                      (unifyList sc ls f))
              | (i,FOA.ApplicationFormula(FOA.NuFormula(n1,_),args)) ->
                  (match lhs with
                    [] -> ()
                  | (i', FOA.ApplicationFormula(FOA.NuFormula(n1',_),args'))::ls ->
                      if n1 = n1' then
                        (match (FOA.unifyList FOA.rightUnify args args') with
                            FOA.UnifySucceeded -> sc ()
                          | FOA.UnifyFailed -> (unifyList sc ls f)
                          | FOA.UnifyError(s) ->
                              (O.error (s ^ ".\n");
                              fc ()))
                      else
                        (unifyList sc ls f)
                  | _::ls ->
                      (unifyList sc ls f))
              | _ -> ()
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          
          let sc' () = sc [] (makeProofBuilder "axiom") fc in
          (List.iter (unifyList sc' lhs) rhs;
          fc ())
        in
        G.makeTactical pretactic
    | _ -> (G.invalidArguments "axiom")
  
  (********************************************************************
  *and:
  ********************************************************************)
  let andL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i, FOA.AndFormula(l,r)) ->
          let s = (lvl, zip [(i,l);(i, r)], rhs) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "and_l" (matchLeft,"_,_") tactic)

  let andR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i,FOA.AndFormula(l,r)) ->
          let s1 = (lvl, lhs, zip [(i,l)]) in
          let s2 = (lvl, lhs, zip [(i,r)]) in
          sc [s1;s2]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    makeBinaryTactical "and_r" (matchRight,"_,_") tactic

  let andTactical session args = match args with
      [] -> (G.orElseTactical (andL session []) (andR session []))
    | _ -> G.invalidArguments "and"

  (********************************************************************
  *or:
  ********************************************************************)
  let orL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i, FOA.OrFormula(l,r)) ->
          let s1 = (lvl, zip [(i,l)], rhs) in
          let s2 = (lvl, zip [(i,r)], rhs) in
          sc [s1;s2]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    makeBinaryTactical "or_l" (matchLeft, "_;_") tactic

  let orR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i, FOA.OrFormula(l,r)) ->
          let rhs' = zip [(i,l);(i, r)] in
          let s = (lvl, rhs', lhs) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "or_r" (matchRight,"_;_") tactic)

  let orTactical session args = match args with
      [] -> (G.orElseTactical (orL session []) (orR session []))
    | _ -> G.invalidArguments "or"

  (********************************************************************
  *implication:
  ********************************************************************)
  let impL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i, FOA.ImplicationFormula(l,r)) ->
          let rhs' = (i,l)::rhs in
          let s1 = (lvl, lhs, rhs') in
          let s2 = (lvl, zip [(i,r)], rhs) in
          sc [s1;s2]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "imp_l" (matchLeft,"_=>_") tactic)

  let impR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        (i, FOA.ImplicationFormula(l,r)) ->
          let lhs' = (i, l)::lhs in
          let s = (lvl, lhs', zip [(i, r)]) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "imp_r" (matchRight,"_=>_") tactic)

  let impTactical session args = match args with
      [] -> (G.orElseTactical (impL session []) (impR session []))
    | _ -> G.invalidArguments "imp"

  
  (*  Additive Or Right  *)
  let orRleft session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i, FOA.OrFormula(l,r))::ts ->
                  let rhs' = (List.rev_append rhs ts) in
                  let s = (lvl, lhs, (i,l)::rhs') in
                  (sc [s] (makeProofBuilder "or_r") fc)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "or_r"
  
  let orRright session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i, FOA.OrFormula(l,r))::ts ->
                  let rhs' = (List.rev_append rhs ts) in
                  let s = (lvl, lhs, (i,r)::rhs') in
                  (sc [s] (makeProofBuilder "or_r") fc)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "or_r"
  
  (*  Pi L  *)
  let piL session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,FOA.PiFormula(f))::ts ->
                  let lhs' = (List.rev_append lhs ts) in
                  let (lvl', var) = makeExistentialVar lvl i in
                  let f' = application [var] f in 
                  if Option.isSome f' then
                    let s = (lvl', (i,Option.get f')::lhs', rhs) in
                    (sc [s] (makeProofBuilder "pi_l") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "pi_l"

  (* Mu Right *)
  let muR session args = match args with
      Absyn.String(n)::[] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> (O.error ("definition '" ^ n ^ "' not found.\n"); fc ())
              | (i,FOA.ApplicationFormula(
                FOA.MuFormula(name,body) as mu, args) as t)::ts ->
                  if n = name then
                    let rhs' = (List.rev_append rhs ts) in
                    let mu' = FOA.applyFixpoint (fun alist -> FOA.ApplicationFormula(mu,alist)) body in
                    let f' = application args mu' in
                    if Option.isSome f' then
                      let s = (lvl, lhs, (i,Option.get f')::rhs') in
                      (sc [s] (makeProofBuilder "mu_r") fc)
                    else
                      (O.error ("'" ^ name ^ "': incorrect number of arguments.");
                      fc ())
                  else
                    (apply lvl ts (t::rhs) lhs)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "mu_r"

  (*  Mu Left -- does not check monotonicity *)
  let muL session args = match args with
      Absyn.String(n)::[] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> (O.error ("definition '" ^ n ^ "' not found.\n"); fc ())
              | ((i,FOA.ApplicationFormula(FOA.MuFormula(name,body)as mu,args)) as t)::ts ->
                  if n = name then
                    let lhs' = (List.rev_append lhs ts) in
                    let mu' = FOA.applyFixpoint (fun args -> FOA.ApplicationFormula(mu,args)) body in
                    let f' = application args mu' in
                    if Option.isSome f' then
                      let s = (lvl, (i,Option.get f')::lhs', rhs) in
                      (sc [s] (makeProofBuilder "mu_l") fc)
                    else
                      (O.error ("'" ^ name ^ "': incorrect number of arguments.");
                      fc ())
                  else
                    (apply lvl ts (t::lhs) rhs)
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "mu_l"

  (*  Induction *)
  let inductionTactical session args = match args with
      Absyn.String(n)::Absyn.String(s)::[] ->
        let pretactic = fun sequent sc fc ->
          let rec makeArgs lvl lts args =
            match args with
              [] -> (lvl, [])
            | a::aa ->
                let (lvl', a') = makeUniversalVar lvl lts in
                let (lvl'', aa') = makeArgs lvl' lts aa in
                (lvl'',  a'::aa')
          in
          
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> (O.error ("definition '" ^ n ^ "' not found.\n"); fc ())
              | ((i,FOA.ApplicationFormula(FOA.MuFormula(name,mu),args)) as t)::ts ->
                  if n = name then
                    let lhs' = (List.rev_append lhs ts) in
                    
                    let s' = parseFormula (getSessionDefinitions session) s in
                    if Option.isSome s' then
                      let s' = FOA.renameAbstractions (Option.get s') in
                      let f' = application args s' in
                      if Option.isSome f' then
                        let f' = Option.get f' in
                        let s1 = (lvl, (i,f')::lhs', rhs) in

                        let (lvl', args') = makeArgs lvl i args in
                        
                        let r = application args' s' in
                        let mu' = application args' mu in
                        
                        if (Option.isSome r) && (Option.isSome mu') then
                          let l = FOA.applyFixpoint (fun alist -> Option.get (application alist s')) (Option.get mu') in
                          let s2 = (lvl', [(i, l)], [(i, Option.get r)]) in
                          (sc [s1;s2] (makeProofBuilder "induction") fc)
                        else
                          (O.error ("incorrect number of arguments.\n");
                          fc ())
                      else
                        fc ()
                    else
                      (O.error ("unable to parse argument formula: " ^ s ^ ".\n");
                      fc ())
                  else
                    (apply lvl ts (t::lhs) rhs)
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "induction"

  (*  Nu Left *)
  let nuL session args = match args with
      Absyn.String(n)::[] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> (O.error ("definition '" ^ n ^ "' not found.\n"); fc ())
              | ((i,FOA.ApplicationFormula(FOA.NuFormula(name,body)as nu,args)) as t)::ts ->
                  if n = name then
                    let lhs' = (List.rev_append lhs ts) in
                    let nu' = FOA.applyFixpoint (fun args -> FOA.ApplicationFormula(nu,args)) body in
                    let f' = application args nu' in
                    if Option.isSome f' then
                      let s = (lvl, (i,Option.get f')::lhs', rhs) in
                      (sc [s] (makeProofBuilder "nu_r") fc)
                    else
                      (O.error ("'" ^ name ^ "': incorrect number of arguments.");
                      fc ())
                  else
                    (apply lvl ts (t::lhs) rhs)
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "nu_l"

  (*  Coinduction *)
  let coinductionTactical session args = match args with
      Absyn.String(n)::Absyn.String(s)::[] ->
        let pretactic = fun sequent sc fc ->
          let rec makeArgs lvl lts args =
            match args with
              [] -> (lvl, [])
            | a::aa ->
                let (lvl', a') = makeUniversalVar lvl lts in
                let (lvl'', aa') = makeArgs lvl' lts aa in
                (lvl'',  a'::aa')
          in
          
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> (O.error ("definition '" ^ n ^ "' not found.\n"); fc ())
              | ((i,FOA.ApplicationFormula(FOA.NuFormula(name,nu),args)) as t)::ts ->
                  if n = name then
                    let rhs' = (List.rev_append rhs ts) in
                    
                    let s' = parseFormula (getSessionDefinitions session) s in
                    if Option.isSome s' then
                      let s' = FOA.renameAbstractions (Option.get s') in
                      let f' = application args s' in
                      if Option.isSome f' then
                        let f' = Option.get f' in
                        let s1 = (lvl, lhs, (i,f')::rhs') in

                        let (lvl', args') = makeArgs lvl i args in
                        
                        let l = application args' s' in
                        let nu' = FOA.applyFixpoint (fun alist -> Option.get (application alist s')) nu in
                        let r = application args' nu' in
                        
                        if (Option.isSome r) && (Option.isSome l) then
                          let s2 = (lvl', [(i, Option.get l)], [(i, Option.get r)]) in
                          (sc [s1;s2] (makeProofBuilder "coinduction") fc)
                        else
                          (O.error ("incorrect number of arguments.\n");
                          fc ())
                      else
                        fc ()
                    else
                      (O.error ("unable to parse argument formula: " ^ s ^ ".\n");
                      fc ())
                  else
                    (apply lvl ts (t::rhs) lhs)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "coinduction"

  (*  Pi Right  *)
  let piR session args = match args with
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,FOA.PiFormula(f))::ts ->
                  let rhs' = (List.rev_append rhs ts) in
                  let (lvl', var) = makeUniversalVar lvl i in
                  let f' = application [var] f in
                  if Option.isSome f' then
                    let s = (lvl', lhs, (i,Option.get f')::rhs') in
                    (sc [s] (makeProofBuilder "pi_r") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "pi_r"

  (*  Sigma Left *)
  let sigmaL session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,FOA.SigmaFormula(f))::ts ->
                  let lhs' = (List.rev_append lhs ts) in
                  let (lvl', var) = makeUniversalVar lvl i in
                  let f' = application [var] f in
                  if (Option.isSome f') then
                    let s = (lvl', (i,Option.get f')::lhs', rhs) in
                    (sc [s] (makeProofBuilder "sigma_l") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "sigma_l"

  (*  Sigma Right *)
  let sigmaR session args = match args with
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,FOA.SigmaFormula(f))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let (lvl', var) = makeExistentialVar lvl i in
                  let f' = application [var] f in
                  if Option.isSome f' then
                    let s = (lvl', lhs, (i,Option.get f')::rhs') in
                    (sc [s] (makeProofBuilder "sigma_r") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "sigma_r"

  (*  Nabla Left  *)
  let nablaL session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,FOA.NablaFormula(f))::ts ->
                  let lhs' = (List.rev_append lhs ts) in
                  let (lvl', i', var) = makeNablaVar lvl i in
                  let f' = application [var] f in
                  if Option.isSome f' then
                    let s = (lvl', (i',Option.get f')::lhs', rhs) in
                    (sc [s] (makeProofBuilder "nabla_l") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::lhs) ts)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "nabla_l"

  (*  Nabla Right *)
  let nablaR session args = match args with
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,FOA.NablaFormula(f))::ts ->
                  let rhs' = (List.rev_append rhs ts) in
                  let (lvl', i', var) = makeNablaVar lvl i in
                  let f' = application [var] f in
                  if Option.isSome f' then
                    let s = (lvl', lhs, (i',Option.get f')::rhs') in
                    (sc [s] (makeProofBuilder "nabla_r") fc)
                  else
                    fc ()
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "nabla_r"
  
  (*  Equality Right *)
  let eqR session args = match args with
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms =
            match terms with
                [] -> fc ()
              | (i,FOA.EqualityFormula(t1, t2))::ts ->                  
                  (match (FOA.rightUnify t1 t2) with
                      FOA.UnifySucceeded -> (sc [] (makeProofBuilder "eq_r") fc)
                    | FOA.UnifyFailed -> (apply lvl ts)
                    | FOA.UnifyError(s) ->
                          (O.error (s ^ ".\n");
                          fc ()))
              | t::ts ->
                  (apply lvl ts)
          in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "eq_r"

  (*  Equality Left *)
  let eqL session args = match args with
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,FOA.EqualityFormula(t1, t2))::ts ->
                  (match (FOA.leftUnify t1 t2) with
                      FOA.UnifyFailed -> (sc [] (makeProofBuilder "eq_l") fc)
                    | FOA.UnifySucceeded ->
                        let lhs' = (List.rev_append lhs ts) in
                        let s = (lvl, lhs', rhs) in
                        (sc [s] (makeProofBuilder "eq_l") fc)
                    | FOA.UnifyError(s) ->
                        (O.error (s ^ ".\n");
                        fc ()))
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let sequent' = copySequent sequent in
          let lhs = getSequentLHS sequent' in
          let rhs = getSequentRHS sequent' in
          let lvl = getSequentLevel sequent' in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "eq_l"

  let orTactical session args = match args with
      [] -> (G.orElseTactical (orL session []) (orR session []))
    | _ -> G.invalidArguments "or"

  let andTactical session args = match args with
      [] -> (G.orElseTactical (andL session []) (andR session []))
    | _ -> G.invalidArguments "and"

  let impTactical session args = match args with
      [] -> (G.orElseTactical (impL session []) (impR session []))
    | _ -> G.invalidArguments "imp"
  
  let piTactical session args = match args with
      [] -> (G.orElseTactical (piR session []) (piL session []))
    | _ -> G.invalidArguments "pi"

  let sigmaTactical session args = match args with
      [] -> (G.orElseTactical (sigmaL session []) (sigmaR session []))
    | _ -> G.invalidArguments "sigma"

  let nablaTactical session args = match args with
      [] -> (G.orElseTactical (nablaL session []) (nablaR session []))
    | _ -> G.invalidArguments "nabla"

  let eqTactical session args = match args with
      [] -> (G.orElseTactical (eqL session []) (eqR session []))
    | _ -> G.invalidArguments "eq"

  let examineTactical session args = match args with
      [] -> fun sequents sc fc ->
            let sequent = List.hd sequents in
            let lhs = getSequentLHS sequent in
            let rhs = getSequentRHS sequent in
            let slhs = String.concat "\n  " (List.map string_of_formula_ast lhs) in
            let srhs = String.concat "\n  " (List.map string_of_formula_ast rhs) in
            (O.output ("Sequent AST:\n  " ^ slhs ^ "\n----------------------------\n  " ^ srhs ^ "\n");
            (sc [] sequents Logic.idProofBuilder fc))
    | _ -> G.invalidArguments "examine"

  let simplifyTactical session args = match args with
      [] ->
        let l = [
          andL session [];
          piR session [];
          impR session [];
          sigmaL session [];
          eqL session [];
          eqR session [];
          axiomTactical session []]
        in
        let l = if Param.intuitionistic then l else (orR session [])::l in
        let allrules = G.orElseListTactical l in
        (G.repeatTactical allrules)
    | _ -> G.invalidArguments "simplify"

  (********************************************************************
  *tacticals:
  * The exported table of tacticals.  These tacticals are the only
  * ones avaible at the toplevel.  GenericTacticals.tacticals is used
  * as the initial table, providing the standard tacticals.
  ********************************************************************)
  let tacticals session =
    let ts = getSessionTacticals session in
    ts

  let defineTactical name tac session =
    let ts = getSessionTacticals session in
    let ts' = Logic.Table.add name tac ts in
    setSessionTacticals ts' session

  let pervasiveTacticals =
    let ts = G.tacticals in    
    let ts = Logic.Table.add "and" andTactical ts in
    let ts = Logic.Table.add "and_l" andL ts in
    let ts = Logic.Table.add "and_r" andR ts in
    
    let ts =
      if Param.intuitionistic then ts else Logic.Table.add "or" orTactical ts
    in
    let ts = Logic.Table.add "or_l" orL ts in
    let ts =
      if Param.intuitionistic then
        Logic.Table.add "left" orRleft
          (Logic.Table.add "right" orRright ts)
      else
        Logic.Table.add "or_r" orR ts
    in
    
    let ts = Logic.Table.add "imp" impTactical ts in
    let ts = Logic.Table.add "imp_r" impR ts in
    let ts = Logic.Table.add "imp_l" impL ts in

    let ts = Logic.Table.add "pi" piTactical ts in
    let ts = Logic.Table.add "pi_l" piL ts in
    let ts = Logic.Table.add "pi_r" piR ts in
    
    let ts = Logic.Table.add "sigma" sigmaTactical ts in
    let ts = Logic.Table.add "sigma_l" sigmaL ts in
    let ts = Logic.Table.add "sigma_r" sigmaR ts in
    
    let ts = Logic.Table.add "nabla" nablaTactical ts in
    let ts = Logic.Table.add "nabla_l" nablaL ts in
    let ts = Logic.Table.add "nabla_r" nablaR ts in
    
    let ts = Logic.Table.add "eq" eqTactical ts in
    let ts = Logic.Table.add "eq_l" eqL ts in
    let ts = Logic.Table.add "eq_r" eqR ts in
    
    let ts = Logic.Table.add "axiom" axiomTactical ts in
    
    
    let ts = Logic.Table.add "mu_l" muL ts in
    let ts = Logic.Table.add "mu_r" muR ts in
    let ts = Logic.Table.add "induction" inductionTactical ts in
    
    let ts = Logic.Table.add "nu_l" nuL ts in
    let ts = Logic.Table.add "coinduction" coinductionTactical ts in
    
    let ts = Logic.Table.add "examine" examineTactical ts in

    let ts = Logic.Table.add "simplify" simplifyTactical ts in
    ts
    
  let emptySession =
    let state = Term.save_state () in
    Session(pervasiveTacticals, Logic.Table.empty, [], Logic.idProofBuilder, state, Term.get_subst state)

  (********************************************************************
  *reset:
  * Provides a new sequent.  This amounts to returning the empty
  * sequent.
  ********************************************************************)
  let reset () = emptySession

end

module Firstordernonstrict =
  Firstorder (struct
    let name = "First Order Classical Logic with Non-Strict Nabla"
    let strictNabla = false
    let intuitionistic = false
  end)

module Firstorderstrict =
  Firstorder (struct
    let name = "First Order Classical Logic with Strict Nabla"
    let strictNabla = true
    let intuitionistic = false
  end)

module MuLJstrict =
  Firstorder (struct
    let name = "Mu-LJ with Strict Nabla"
    let strictNabla = true
    let intuitionistic = true
  end)

module MuLJnonstrict =
  Firstorder (struct
    let name = "Mu-LJ with Non-Strict Nabla"
    let strictNabla = false
    let intuitionistic = true
  end)
