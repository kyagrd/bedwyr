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
module LA = Linearabsyn

(**********************************************************************
*Linear:
* Implements linear logic with some craziness, as well.
**********************************************************************)
module Linear (O : Output.Output) =
struct
  let name = "Linear Logic"
  let info =
"
Linear Logic v0.0

Implements a rather strange and sort of linear logic.
  
"
  let start = info
  
  let copy b = ref (!b)
  
  (********************************************************************
  *Formula:
  * Represent formulae in sequents, with a local context and a flag
  * indicating whether the formula is being focussed on.
  ********************************************************************)
  type formula = Formula of (int * bool ref * LA.formula)
  let string_of_formula (Formula(_,_,t)) = LA.string_of_formula t
  let string_of_formula_ast (Formula(_,_,t)) = LA.string_of_formula_ast t
  let getFormulaFormula (Formula(_,_,f)) = f
  let getFormulaFocus (Formula(_,b,_)) = !b
  let getFormulaFocusRef (Formula(_,b,_)) = b
  let getFormulaLevel (Formula(i,_,_)) = i
  let makeFormula t = Formula(0, ref false, t)
  
  
  let string_of_definition def = LA.string_of_definition def
  
  (********************************************************************
  *Sequent:
  * A sequent has a left and right side, each a list of terms, along
  * with an index used during unification to determine which variables
  * may bind with what terms.
  ********************************************************************)
  type sequent = Sequent of (int * formula list * formula list)
  let makeSequent l r = Sequent(0, l, r)
  let emptySequent = (0, [], [])
  let getSequentLevel (Sequent(l,_,_)) = l
  let getSequentLHS (Sequent(_,l,_)) = l
  let getSequentRHS (Sequent(_,_,r)) = r

  (********************************************************************
  *Proof:
  * For now a proof is simply a string.
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
    LA.definition Logic.table *
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
      let term = Linearparser.toplevel_term Linearlexer.token (Lexing.from_string t) in
      Some term
    with
      LA.SyntaxError(s) ->
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
    (*  Produces a list of generated symbols of length i. *)
    let rec makeArgs i =
      if i = 0 then
        []
      else
        (generateSymbol ()) :: makeArgs (i - 1)
    in
    
    (*  Given a list of arguments, abstracts a formula over all of
        the arguments in turn.  *)
    let rec makeAbstractions args formula =
      match args with
        [] -> formula
      | a::aa ->  LA.AbstractionFormula(a, (makeAbstractions aa formula))
    in
      
    (*  main iteration function, used with Linearabsyn.mapFormula.  *)
    let tf t = t in
    let rec ff f =
      match f with
          LA.AtomicFormula(t) ->
            let ha = LA.getTermHeadAndArgs t in
            if (Option.isSome ha) then
              let (head, args) = Option.get ha in
              let def = Logic.find head defs in
              if (Option.isSome def) then
                let def = (Option.get def) in
                let arity = LA.getDefinitionArity def in
                let body = LA.getDefinitionBody def in
                if (arity = List.length args) then
                  LA.ApplicationFormula(body, args)
                else if arity > List.length args then
                  let args' = makeArgs (arity - (List.length args)) in
                  makeAbstractions args' (LA.ApplicationFormula(body, args@(List.map (Term.atom) args')))
                else             
                  raise (LA.SemanticError("'" ^ head ^ "' applied to too many arguments"))
              else
                f
            else
              f
        | _ -> (LA.mapFormula ff tf f)
    in
    (ff formula)
  
  
  (********************************************************************
  *application:
  * Given a list of arguments, applies each argument to the formul in
  * turn.  This application first entails removing a top-level
  * abstraction for each argument.  If such an abstraction doesn't exists,
  * an error is raised.  This error corresponds to too many arguments
  * being applied to a formula.
  ********************************************************************)
  let rec application args formula =
    match args with
      [] -> Some formula
    | a::aa ->
        (match formula with
            LA.AbstractionFormula(name,f) ->
              let f' = LA.abstract name f in
              (application aa (LA.apply [a] f'))
          | _ -> (O.error "expected abstraction.\n"; None))

    
  (********************************************************************
  *parseFormula:
  * Parses the argument into a formula.  If successful, returns Some
  * with the parsed formula, otherwise it returns None.
  ********************************************************************)
  let parseFormula defs t =        
    try
      let formula = Linearparser.toplevel_formula Linearlexer.token (Lexing.from_string t) in
      Some (replaceApplications defs formula)
    with
        LA.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          None)
      | LA.SemanticError(s) ->
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
      let LA.PreDefinition(name,args,body,ind) = Linearparser.toplevel_definition Linearlexer.token (Lexing.from_string t) in
      Some (LA.PreDefinition(name,args,(replaceApplications defs body),ind))
    with
        LA.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          None)
      | LA.SemanticError(s) ->
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
            LA.Inductive ->
              LA.MuFormula(name,body)
          | LA.CoInductive ->
              LA.NuFormula(name,body)
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
            let find name (LA.PreDefinition(name',ids,formula,ind)) =
              name' = name
            in
            Some (List.find (find name) predefs)
          with
            Not_found -> None
        in

        (*  main iteration function, used in conjuction with
            Linearabsyn.mapFormula.  *)
        let tf t = t in  
        let rec ff abstractions f =
          match f with
              LA.AtomicFormula(t) ->
                let ha = LA.getTermHeadAndArgs t in
                if (Option.isSome ha) then
                  let (head,args) = Option.get ha in
                  let db = getDB head abstractions in
                  if Option.isSome db then
                    LA.ApplicationFormula(LA.DBFormula(head, Option.get db), args)
                  else
                    let def = findDefinition head predefs in
                    if Option.isSome def then
                      let LA.PreDefinition(_,_,f',ind) = (Option.get def) in
                      (makeFixpoint ind head (ff (head::abstractions) f'))
                    else
                      f
                else
                  (O.error ("term has no head: " ^ (LA.string_of_term t));
                  f)
            | _ -> (LA.mapFormula (ff abstractions) tf f)
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
            LA.AbstractionFormula(id, (abstractArguments ids' formula))
      in
      
      (****************************************************************
      *processPreDefinition:
      * Mu/Nu-abstracts the body of the predefinition, wraps the body
      * in a Mu/Nu formula, and applies abstractions in the formula.
      ****************************************************************)
      let processPreDefinition (LA.PreDefinition(name, ids, formula, ind)) =
        let formula' = abstractDefinition [name] formula in
        let formula'' = abstractArguments ids formula' in
        let formula''' = makeFixpoint ind name formula'' in
        
        LA.Definition(name, List.length ids, formula''', ind)
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
      | (LA.Definition(name,arity,formula,ind) as def)::ds ->
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

  (********************************************************************
  *operator:
  * Should update the tactical table, but tacticals aren't allowed in
  * any position but head as of yet. (No infix tacticals, etc.)
  ********************************************************************)
  let operator name fix prec session = session

  (********************************************************************
  *update:
  * Main update function, called from the interpreter once a "round".
  * Needs to update the sequents and the session.
  ********************************************************************)
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
    let rec copyFormula f = LA.mapFormula copyFormula copyTerm f in
    
    let lhs' = List.map (fun (i,f) -> (i, copyFormula f)) lhs in
    let rhs' = List.map (fun (i,f) -> (i, copyFormula f)) rhs in
    (i, lhs', rhs')


  (********************************************************************
  *makeExistentialVar, makeUniversalVar, makeNablaVar:
  * Make the corresponding variable type and return necessary levels,
  * updated if needed.  Specifically, universal variables update the
  * sequent level, and nabla variables update the formula level.
  ********************************************************************)
  let makeExistentialVar lvl lts =
    (lvl, Term.fresh ~tag:Term.Logic ~lts lvl)

  let makeUniversalVar lvl lts =
    (lvl + 1, Term.fresh ~tag:Term.Eigen ~lts (lvl + 1))

  let makeNablaVar lvl i =
    (lvl, i + 1, Term.nabla (i + 1))

  (********************************************************************
  *Tacticals:
  ********************************************************************)
  module LinearSig =
  struct
    type logic_session = session
    type logic_sequent = sequent
    type logic_proof = proof
  end
  module G = Logic.GenericTacticals (LinearSig) (O)

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
          if (LA.matchFormula template f) then
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
                (LA.matchFormula defaulttemplate (Option.get template)) then
                (makeTactical name (matchbuilder (Option.get template)) tactic)
              else
                (G.invalidArguments (name ^ ": invalid template."))
          | _ -> (G.invalidArguments (name ^ ": incorrect number of arguments."))
      else
        (G.invalidArguments (name ^ ": invalid default template."))

  (********************************************************************
  *and:
  ********************************************************************)
  let andL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.AndFormula(l,r)) ->
          let s = Sequent(lvl, zip [Formula(i,copy b,l);Formula(i,copy b, r)], rhs) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "and_l" (matchLeft,"_/\\_") tactic)

  let andR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b,LA.AndFormula(l,r)) ->
          let s1 = Sequent(lvl, lhs, zip [Formula(i,copy b,l)]) in
          let s2 = Sequent(lvl, lhs, zip [Formula(i,copy b,r)]) in
          sc [s1;s2]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    makeBinaryTactical "and_r" (matchRight,"_/\\_") tactic

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
        Formula(i, b,LA.OrFormula(l,r)) ->
          let s1 = Sequent(lvl, zip [Formula(i,copy b,l)], rhs) in
          let s2 = Sequent(lvl, zip [Formula(i,copy b,r)], rhs) in
          sc [s1;s2]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    makeBinaryTactical "or_l" (matchLeft, "_\\/_") tactic

  let orR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.OrFormula(l,r)) ->
          let rhs' = zip [Formula(i,copy b,l);Formula(i,copy b, r)] in
          let s = Sequent(lvl, rhs', lhs) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "or_r" (matchRight,"_\\/_") tactic)

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
        Formula(i, b, LA.ImplicationFormula(l,r)) ->
          let rhs' = Formula(i,copy b,l)::rhs in
          let s1 = Sequent(lvl, lhs, rhs') in
          let s2 = Sequent(lvl, zip [Formula(i,copy b,r)], rhs) in
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
        Formula(i, b, LA.ImplicationFormula(l,r)) ->
          let lhs' = Formula(i,copy b, l)::lhs in
          let s = Sequent(lvl, lhs', zip [Formula(i, copy b, r)]) in
          sc [s]
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "imp_r" (matchRight,"_=>_") tactic)

  let impTactical session args = match args with
      [] -> (G.orElseTactical (impL session []) (impR session []))
    | _ -> G.invalidArguments "imp"
  
  (********************************************************************
  *pi:
  ********************************************************************)
  let piL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.PiFormula(f)) ->
          let (lvl',var) = makeExistentialVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i, copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "pi_l" (matchLeft,"pi _") tactic)

  let piR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.PiFormula(f)) ->
          let (lvl',var) = makeUniversalVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i, copy b, Option.get f')]) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "pi_r" (matchRight,"pi _") tactic)

  let piTactical session args = match args with
      [] -> (G.orElseTactical (piR session []) (piL session []))
    | _ -> G.invalidArguments "pi"

  (********************************************************************
  *sigma:
  ********************************************************************)
  let sigmaL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.SigmaFormula(f)) ->
          let (lvl',var) = makeUniversalVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i, copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "sigma_l" (matchLeft,"sigma _") tactic)

  let sigmaR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.SigmaFormula(f)) ->
          let (lvl',var) = makeExistentialVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i, copy b, Option.get f')]) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "sigma_r" (matchRight,"sigma _") tactic)

  let sigmaTactical session args = match args with
      [] -> (G.orElseTactical (sigmaL session []) (sigmaR session []))
    | _ -> G.invalidArguments "sigma"

  (********************************************************************
  *nabla:
  ********************************************************************)
  let nablaL =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.NablaFormula(f)) ->
          let (lvl',i',var) = makeNablaVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i', copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "nabla_l" (matchLeft, "nabla _") tactic)

  let nablaR =
    let tactic seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, LA.NablaFormula(f)) ->
          let (lvl',i',var) = makeNablaVar lvl i in
          let f' = application [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i', copy b, Option.get f')]) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.error "invalid formula.\n";
          fc ())
    in
    (makeBinaryTactical "nabla_r" (matchRight,"nabla _") tactic)

  let nablaTactical session args = match args with
      [] -> (G.orElseTactical (nablaL session []) (nablaR session []))
    | _ -> G.invalidArguments "nabla"

  (********************************************************************
  *eq:
  ********************************************************************)
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

  let contractTactical session args = match args with
      Absyn.String(s)::[] ->
        let template = parseFormula (getSessionDefinitions session) s in
        if (Option.isSome template) then
          let template = Option.get template in
          let pretactic = fun sequent sc fc ->
            let lhs = getSequentLHS sequent in
            let rhs = getSequentRHS sequent in
            let lvl = getSequentLevel sequent in
            
            let (r, rhs') = findFormula template rhs in
            if Option.isSome r then
              let s = (lvl, lhs, (Option.get r)::rhs) in
              (sc [s] (makeBuilder "contract") fc)
            else
              let (l, lhs') = findFormula template lhs in
              if Option.isSome l then
                let s = (lvl, (Option.get l)::lhs, rhs) in
                (sc [s] (makeBuilder "contract") fc)
              else
                (fc ())
          in
          (G.makeTactical pretactic)
        else
          G.invalidArguments "contract"
    | _ -> G.invalidArguments "contract"
  
  let prologPiTactical session args = match args with
    [] ->
      (G.thenTactical
        (contractTactical session [Absyn.String("pi _")])
        (piTactical session []))
  | _ -> G.invalidArguments "prologpi"

  let prologTactical session args = match args with
    [] ->
      (G.iterateTactical
        (G.orElseTactical
          (G.iterateTactical
            (G.orElseListTactical
              [(axiomTactical session []);
              (impTactical session []);
              (andTactical session []);
              (orTactical session [])]))
          (prologPiTactical session [])))
  | _ -> G.invalidArguments "prolog"

  let rotateR session args = match args with
    [] ->
      let pretactic = fun sequent sc fc ->
        let lvl = getSequentLevel sequent in
        let rhs = (getSequentRHS sequent) in
        let lhs = (getSequentLHS sequent) in
        let rhs' = (List.tl rhs)@[(List.hd rhs)] in
        let s = (lvl, lhs, rhs') in
        sc [s] (makeBuilder "rotate_r") fc
      in
      G.makeTactical pretactic
  | _ -> G.invalidArguments "rotate_r"
  
  let rotateL session args = match args with
    [] ->
      let pretactic = fun sequent sc fc ->
        let lvl = getSequentLevel sequent in
        let rhs = (getSequentRHS sequent) in
        let lhs = (getSequentLHS sequent) in
        let lhs' = (List.tl lhs)@[(List.hd lhs)] in
        let s = (lvl, lhs', rhs) in
        sc [s] (makeBuilder "rotate_l") fc
      in
      G.makeTactical pretactic
  | _ -> G.invalidArguments "rotate_l"

  let asyncTactical session args = match args with
      [] ->
        let allrules = (G.orElseListTactical
          [andL session [];
          orR session [];
          piR session [];
          impR session [];
          sigmaL session [];
          eqL session [];
          eqR session [];
          axiomTactical session []]) in
        (G.repeatTactical allrules)
    | _ -> G.invalidArguments "async"

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
    
    let ts = Logic.Table.add "or" orTactical ts in
    let ts = Logic.Table.add "or_l" orL ts in
    let ts = Logic.Table.add "or_r" orR ts in
    
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
    
    let ts = Logic.Table.add "contract" contractTactical ts in
    let ts = Logic.Table.add "contract_l" contractL ts in
    let ts = Logic.Table.add "contract_r" contractR ts in
    
    let ts = Logic.Table.add "mu_r" muR ts in
    let ts = Logic.Table.add "induction" inductionTactical ts in
    
    let ts = Logic.Table.add "nu_l" nuL ts in
    let ts = Logic.Table.add "coinduction" coinductionTactical ts in
    
    let ts = Logic.Table.add "examine" examineTactical ts in
    let ts = Logic.Table.add "rotate_r" rotateR ts in
    let ts = Logic.Table.add "rotate_l" rotateL ts in

    let ts = Logic.Table.add "async" asyncTactical ts in
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

