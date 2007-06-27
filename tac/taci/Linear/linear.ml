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
  
  (********************************************************************
  *Formula:
  * Represent formulae in sequents, with a local context and a flag
  * indicating whether the formula is being focussed on.
  ********************************************************************)
  type formula = Formula of (int * bool ref * LA.formula)
  let string_of_formula (Formula(_,_,t)) = LA.string_of_formula t
  let string_of_formula_ast (Formula(_,_,t)) = LA.string_of_formula_ast t
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
    let rec makeArgs i =
      if i = 0 then
        []
      else
        (generateSymbol ()) :: makeArgs (i - 1)
    in
    
    let rec makeAbstractions args formula =
      match args with
        [] -> formula
      | a::aa ->  LA.AbstractionFormula(a, (makeAbstractions aa formula))
    in
      

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
  * Apply arguments.
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
      let formula = Linearparser.toplevel_formula Linearlexer.token (Lexing.from_string t) in
      Some (processFormula defs formula)
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
    let rec copyFormula f = LA.mapFormula copyFormula copyTerm f in
    
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
  *makeTactical:
  ********************************************************************)
  let makeTactical matcher tactic =
    let tactic' = fun sequent sc fc ->
      match (matcher sequent) with
        
    in
    G.makeTactical tactic'
  
  (********************************************************************
  *and:
  ********************************************************************)
  let andL session args =
    let tactic f lhs rhs sc fc =
      let s' = Sequent() in
      sc [s']
    in
    match args with
      [] -> (makeTactical (matchLeft "_/\_") tactic)
    | Absyn.String(s)::[] -> (makeTactical (matchLeft s) tactic)
    | _ -> G.invalidArguments "and_l"

  let andR session args =
    let tactic f lhs rhs sc fc =
      let s' = Sequent() in
      sc [s']
    in
    match args with
      [] -> (makeTactical (matchRight "_") tactic)
    | Absyn.String(s)::[] -> (makeTactical (matchRight s) tactic)
    | _ -> G.invalidArguments "and_l"

  let andTactical session args = match args with
      [] -> (G.orElseTactical (andL session []) (andR session []))
    | _ -> G.invalidArguments "and"

  let orTactical session args = match args with
      [] -> (G.orElseTactical (orL session []) (orR session []))
    | _ -> G.invalidArguments "or"

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

