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
  let info = Param.name ^ "\n"
  let start = info
  
  (********************************************************************
  *Formula:
  * Represent formulae in sequents, with a local context.
  ********************************************************************)
  let copy b = ref (!b)
  type formula = Formula of (int * bool ref * FOA.formula)
  let string_of_formula (Formula(_,_,t)) = FOA.string_of_formula t
  let string_of_formula_ast (Formula(_,_,t)) = FOA.string_of_formula_ast t
  let getFormulaFormula (Formula(_,_,f)) = f
  let getFormulaFocus (Formula(_,b,_)) = !b
  let getFormulaFocusRef (Formula(_,b,_)) = b
  let getFormulaLevel (Formula(i,_,_)) = i
  let makeFormula t = Formula(0, ref false, t)
  
  let string_of_definition def = FOA.string_of_definition def
  
  (********************************************************************
  *Sequent:
  * A sequent has a left and right side, each a list of terms, along
  * with an index used during unification to determine which variables
  * may bind with what terms.
  ********************************************************************)
  type sequent = Sequent of (int * formula list * formula list)
  let makeSequent l r = Sequent(0, l, r)
  let emptySequent = Sequent(0, [], [])
  let getSequentLevel (Sequent(l,_,_)) = l
  let getSequentLHS (Sequent(_,l,_)) = l
  let getSequentRHS (Sequent(_,_,r)) = r

  (********************************************************************
  *Proof:
  ********************************************************************)
  type proof = string

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
    Term.state * Term.subst * (Term.namespace * Term.namespace))

  let getSessionSequents (Session(_,_,sequents,_,_,_,_)) = sequents
  let setSessionSequents sequents (Session(t,d,_,pb,u,r,ns)) = (Session(t,d,sequents,pb,u,r,ns))
  let getSessionBuilder (Session(_,_,_,b,_,_,_)) = b
  let setSessionBuilder builder (Session(t,d,s,_,u,r,ns)) = (Session(t,d,s,builder,u,r,ns))
  let getSessionUndo (Session(_,_,_,_,u,_,_)) = u
  let setSessionUndo undo (Session(t,d,s,b,_,r,ns)) = (Session(t,d,s,b,undo,r,ns))
  let getSessionRedo (Session(_,_,_,_,_,r,_)) = r
  let setSessionRedo redo (Session(t,d,s,b,u,_,ns)) = (Session(t,d,s,b,u,redo,ns))
  let getSessionTacticals (Session(t,_,_,_,_,_,_)) = t
  let setSessionTacticals tacs (Session(_,d,s,pb,u,r,ns)) = (Session(tacs,d,s,pb,u,r,ns))
  let getSessionDefinitions (Session(_,d,_,_,_,_,_)) = d
  let setSessionDefinitions defs (Session(t,_,s,pb,u,r,ns)) = (Session(t,defs,s,pb,u,r,ns))
  let setSessionNamespaces ns (Session(t,defs,s,pb,u,r,_)) = (Session(t,defs,s,pb,u,r,ns))
  let getSessionProofNamespace (Session(_,_,_,_,_,_,(_,pns))) = pns
  let setSessionProofNamespace pns (Session(t,defs,s,pb,u,r,(ins,_))) = (Session(t,defs,s,pb,u,r,(ins,pns)))
  let getSessionInitialNamespace (Session(_,_,_,_,_,_,(ins,_))) = ins
  let setSessionInitialNamespace ins (Session(t,defs,s,pb,u,r,(_,pns))) = (Session(t,defs,s,pb,u,r,(ins,pns)))
  
  let restoreNamespace ns = Term.restore_namespace ns
  
  let proof session = getSessionBuilder session

  let string_of_proofs session =
    let proofs = (getSessionBuilder session) [] in
    "\t" ^ (String.concat "\n\t" proofs) ^ "\n"
  
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
    
  let string_of_sequents session =
    let sequents = getSessionSequents session in
    let () = restoreNamespace (getSessionProofNamespace session) in
    let mainseq = List.hd sequents in
    let seqs = List.tl sequents in
    if not (Listutils.empty seqs) then
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
    (******************************************************************
    *makeArgs:
    * Generates a list of new names of length i.  This is only used
    * if the incorrect number of arguments were applied to a definition.
    ******************************************************************)
    let rec makeArgs i =
      if i = 0 then
        []
      else
        (generateSymbol ()) :: makeArgs (i - 1)
    in
    
    (******************************************************************
    *abstractReplacement:
    ******************************************************************)
    let abstractReplacement lambdas f =
      List.fold_left (fun f _ -> FOA.abstractDummyWithoutLambdas f) f lambdas
    in
    
    let rec makeAbstractions args formula =
      match args with
        [] -> formula
      | a::aa ->  FOA.abstract a (makeAbstractions aa (formula))
    in

    let tf t = t in
    let rec ff lambdas f =
      match f with
          FOA.AtomicFormula(head,args) ->
            let def = Logic.find head defs in
            if (Option.isSome def) then
              let def = (Option.get def) in
              let arity = FOA.getDefinitionArity def in
              let body = FOA.getDefinitionBody def in
              if (arity = List.length args) then
                (FOA.ApplicationFormula(abstractReplacement lambdas body, args))
              else if arity > List.length args then
                let argnames = makeArgs (arity - (List.length args)) in
                let args' = args @ (List.map (Term.atom) argnames) in
                let f = (FOA.ApplicationFormula(abstractReplacement lambdas body, args')) in
                makeAbstractions argnames f
              else             
                raise (FOA.SemanticError("'" ^ head ^ "' applied to too many arguments"))
            else
              f
        | FOA.AbstractionFormula(n,body) ->
            FOA.AbstractionFormula(n, (ff (n::lambdas) body))
        | _ -> (FOA.mapFormula (ff lambdas) tf f)
    in
    (ff [] formula)
  
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
  let parseTemplate defs t =
    try
      let formula = Firstorderparser.toplevel_template Firstorderlexer.token (Lexing.from_string t) in
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

  let parseFormula defs t =        
    try
      let formula = Firstorderparser.toplevel_formula Firstorderlexer.token (Lexing.from_string t) in
      let () = O.debug ("Firstorder.parseFormula: formula: " ^ (FOA.string_of_formula formula) ^ "\n") in
      let () = O.debug ("Firstorder.parseFormula: formula ast: " ^ (FOA.string_of_formula_ast formula) ^ "\n") in
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
      let () = O.debug ("Firstorder.parseDefinition: predefinition ast:" ^ name ^ " " ^ (FOA.string_of_formula_ast body) ^ ".\n") in
      let () = O.debug ("Firstorder.parseDefinition: predefinition: " ^ name ^ " " ^ (FOA.string_of_formula body) ^ ".\n") in
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
    let initialNamespace = Term.save_namespace () in
    let defs = getSessionDefinitions session in
    let f = parseFormula defs t in
    let proofNamespace = Term.save_namespace () in
    if Option.isSome f then
      let f = Option.get f in
      let seq = makeSequent [] [makeFormula f] in
      (setSessionNamespaces (initialNamespace, proofNamespace)
        (setSessionBuilder Logic.idProofBuilder (setSessionSequents [seq] session)))
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
      *checkMonotonicity:
      * Determines whether a definition is monotonic.
      ****************************************************************)
      let checkMonotonicity f =
        true
      in
      
      (****************************************************************
      *makeFixpoint:
      * Makes a mu or nu formula based on the combinator type.
      ****************************************************************)
      let makeFixpoint ind name argnames body =
        match ind with
            FOA.Inductive ->
              FOA.MuFormula(name,argnames,body)
          | FOA.CoInductive ->
              FOA.NuFormula(name,argnames,body)
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
              FOA.AtomicFormula(head, args) ->
                let db = getDB head abstractions in
                if Option.isSome db then
                  FOA.ApplicationFormula(FOA.DBFormula(head, Option.get db), args)
                else
                  let def = findDefinition head predefs in
                  if Option.isSome def then
                    let FOA.PreDefinition(_,argnames,f',ind) = (Option.get def) in
                    (makeFixpoint ind head argnames (ff (head::abstractions) f'))
                  else
                    f
            | _ -> (FOA.mapFormula (ff abstractions) tf f)
        in
        (ff abstractions f)
      in

      (****************************************************************
      *processPreDefinition:
      * Mu/Nu-abstracts the body of the predefinition, and wraps the body
      * in a Mu/Nu formula.
      ****************************************************************)
      let processPreDefinition (FOA.PreDefinition(name, ids, formula, ind)) =
        let formula' = abstractDefinition [name] formula in
        let formula'' = makeFixpoint ind name ids formula' in
        
        let result = FOA.Definition(name, List.length ids, formula'', ind) in
        if (checkMonotonicity formula'') then
          Some(result)
        else
          (O.error (name ^ ": non-monotonic definition.\n");
          None)
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
            let () = O.debug ("Firstorder.definitions: definition ast: " ^ (FOA.string_of_formula_ast formula) ^ ".\n") in
            let () = O.output ("Definition: " ^ (string_of_definition def) ^ ".\n") in
            Logic.Table.add name def (addDefinitions ds table)
    in
        
    let predefs = (List.map (parseDefinition (getSessionDefinitions session)) defstrings) in
    if (List.exists (Option.isNone) predefs) then
      (O.error "definitions contain errors.\n";
      session)
    else
      let defs = processPreDefinitions (List.map (Option.get) predefs) in
      if (List.exists (Option.isNone) defs) then
        (O.error ("definitions contain errors.\n");
        session)
      else
        let defs' = (List.map (Option.get) defs) in
        let defs'' = (addDefinitions defs' (getSessionDefinitions session)) in
        (setSessionDefinitions defs'' session)

  let operator name fix prec session = session
  let update sequents builder session =
    let state = Term.save_state () in
    let subst = Term.get_subst state in
    let session' = setSessionUndo state (setSessionRedo subst session) in
    (setSessionSequents sequents (setSessionBuilder builder session'))

  let validSequent session =
    let sequents = (getSessionSequents session) in
    not (Listutils.empty sequents)

  let undo session =
    let undo = getSessionUndo session in
    let () = Term.restore_state undo in
    session

  let redo session =
    let redo = getSessionRedo session in
    let _ = Term.apply_subst redo in
    session

  let sequents session = (getSessionSequents session)
      
  let copyFormula ?(copier=(Term.copy_eigen ())) (Formula(i,b,f)) =
    let copyTerm t = copier t in
    let rec copyFormula f = FOA.mapFormula copyFormula copyTerm f in
    (Formula(i,copy b,copyFormula f))

  (********************************************************************
  *copySequent:
  * Copy the terms in a sequent so that left-unification doesn't
  * introduce invalid unifiers.
  ********************************************************************)
  let copySequent (i,lhs,rhs) =
    let copier = Term.copy_eigen () in
    let lhs' = List.map (copyFormula ~copier) lhs in
    let rhs' = List.map (copyFormula ~copier) rhs in
    (i,lhs',rhs')


  let makeExistentialVar hint lvl lts =
    let hint = String.capitalize hint in
    let var = Term.fresh ~name:hint ~lts:lts ~ts:lvl ~tag:Term.Logic in
    (lvl, var)

  let makeUniversalVar hint lvl lts =
    let var = Term.fresh ~name:hint ~lts:lts ~ts:lvl ~tag:Term.Eigen in
    (lvl + 1, var)

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
    let () = O.debug ("Firstorder.findFormula: template: " ^ (FOA.string_of_formula template) ^ "\n") in
    let () = O.debug ("Firstorder.findFormula: template ast: " ^ (FOA.string_of_formula_ast template) ^ "\n") in
    let rec find front formulas =
      match formulas with
        [] ->
          let () = O.debug "Firstorder.findFormula: not found.\n" in
          None
      | formula::fs ->
          let f = getFormulaFormula formula in
          if (FOA.matchFormula template f) then
            let zip rest = fun list ->
              (List.rev_append front list) @ rest
            in
            let () = O.debug ("Firstorder.findFormula: found: " ^ (FOA.string_of_formula f) ^ ".\n") in
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
    let () = O.debug ("Template: " ^ (FOA.string_of_formula_ast pattern) ^ ".\n") in
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
  let makeTactical name matcher tactic session =
    let tactic' = fun sequent sc fc ->
      let sc' s = sc s (makeProofBuilder name) fc in
      match (matcher sequent) with
        Some(f, zip, lhs, rhs) -> tactic session sequent f zip lhs rhs sc' fc
      | None -> fc ()
    in
    (G.makeTactical tactic')
  
  (********************************************************************
  *makeSimpleTactical:
  * Given the name of a tactic, a matcher constructor (either matchLeft or
  * matchRight), a default template for use if none is specified, and
  * a tactic, finds a formula to operate on using the matcher and applies
  * the tactic.
  ********************************************************************)
  let makeSimpleTactical name (matchbuilder, defaulttemplate) tactic =
    fun session args ->
      (*  If no default template was specified and there is no argument
          template then bail. *)
      if defaulttemplate = "" && Listutils.empty args then
        (G.invalidArguments (name ^ ": incorrect number of arguments."))
      else
      
      let defaulttemplate =
        parseTemplate (getSessionDefinitions session) defaulttemplate in
      if Option.isSome defaulttemplate then
        let defaulttemplate = Option.get defaulttemplate in
        match args with
            [] ->
              (makeTactical name (matchbuilder defaulttemplate) tactic session)
          | Absyn.String(s)::[] ->
              let template = parseTemplate (getSessionDefinitions session) s in
              if (Option.isSome template) &&
                (FOA.matchFormula defaulttemplate (Option.get template)) then
                (makeTactical name (matchbuilder (Option.get template)) tactic session)
              else
                (G.invalidArguments (name ^ ": invalid template"))
          | _ -> (G.invalidArguments (name ^ ": incorrect number of arguments"))
      else
        (G.invalidArguments (name ^ ": invalid default template."))
  
  (********************************************************************
  *abstractFixpointDefinition:
  * Given a definition of the form FOA.MuFormula() or FOA.NuFormula(),
  * creates an abstracted application term that may be passed to 
  * FOA.applyFixpoint.
  ********************************************************************)
  let abstractFixpointDefinition f argnames =
    match f with
        FOA.MuFormula(_,_,body)
      | FOA.NuFormula(_,_,body) ->
          let args' = List.map
            (fun n -> Term.fresh ~name:"*" ~lts:0 ~ts:0 ~tag:Term.Constant)
            argnames in
          let f' = FOA.ApplicationFormula(f, args') in
          let f'' = (List.fold_right (FOA.abstractVar) args' f') in
          let () = O.debug ("Firstorder.abstractFixpointDefinition: " ^ (FOA.string_of_formula_ast f'') ^ "\n") in
          f''
      | _ -> failwith "Firstorder.abstractFixpointDefinition: invalid formula."

  (********************************************************************
  *axiom:
  ********************************************************************)
  let axiomTactical session args = match args with
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec unifyList sc lhs f =
            match f with
               Formula(i, b, FOA.AtomicFormula(head,tl)) ->
                  (match lhs with
                    [] -> ()
                  | Formula(i', b, FOA.AtomicFormula(head',tl'))::ls ->
                      if (not Param.strictNabla) || i = i' then
                        if head = head' then
                          (match (FOA.unifyList FOA.rightUnify tl tl') with
                              FOA.UnifySucceeded -> sc ()
                            | FOA.UnifyFailed -> (unifyList sc ls f)
                            | FOA.UnifyError(s) ->
                                (O.error (s ^ ".\n");
                                fc ()))
                        else
                          (unifyList sc ls f)
                      else
                        fc ()
                  | _::ls ->
                      (unifyList sc ls f))
              | Formula(i,b,FOA.ApplicationFormula(FOA.MuFormula(n1,_,_),args)) ->
                  (match lhs with
                    [] -> ()
                  | Formula(i',b,FOA.ApplicationFormula(FOA.MuFormula(n1',_,_),args'))::ls ->
                      if ((not Param.strictNabla) || (i = i')) && (n1 = n1') then
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
              | Formula(i,b,FOA.ApplicationFormula(FOA.NuFormula(n1,_,_),args)) ->
                  (match lhs with
                    [] -> ()
                  | Formula(i',b,FOA.ApplicationFormula(FOA.NuFormula(n1',_,_),args'))::ls ->
                      if ((not Param.strictNabla) || (i = i')) && (n1 = n1') then
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
          (*  TODO: Change to continuations.  *)
          (List.iter (unifyList sc' lhs) rhs;
          fc ())
        in
        G.makeTactical pretactic
    | _ -> (G.invalidArguments "axiom")
    
  (********************************************************************
  *and:
  ********************************************************************)
  let andL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.AndFormula(l,r)) ->
          let s = Sequent(lvl, zip [Formula(i,copy b,l);Formula(i,copy b, r)], rhs) in
          sc [s]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "and_l" (matchLeft,"_,_") tactic)

  let andR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b,FOA.AndFormula(l,r)) ->
          let s1 = Sequent(lvl, lhs, zip [Formula(i,copy b,l)]) in
          let s2 = Sequent(lvl, lhs, zip [Formula(i,copy b,r)]) in
          sc [s1;s2]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    makeSimpleTactical "and_r" (matchRight,"_,_") tactic

  let andTactical session args =
    (G.orElseTactical (andL session args) (andR session args))

  (********************************************************************
  *or:
  ********************************************************************)
  let orL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b,FOA.OrFormula(l,r)) ->
          let s1 = Sequent(lvl, zip [Formula(i,copy b,l)], rhs) in
          let s2 = Sequent(lvl, zip [Formula(i,copy b,r)], rhs) in
          sc [s1;s2]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    makeSimpleTactical "or_l" (matchLeft, "_;_") tactic

  let orR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.OrFormula(l,r)) ->
          let rhs' = zip [Formula(i,copy b,l);Formula(i,copy b, r)] in
          let s = Sequent(lvl, lhs, rhs') in
          sc [s]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "or_r" (matchRight,"_;_") tactic)

  let orTactical session args = match args with
      [] -> (G.orElseTactical (orL session args) (orR session args))
    | _ -> G.invalidArguments "or"

  (********************************************************************
  *implication:
  ********************************************************************)
  let impL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ImplicationFormula(l,r)) ->
          let rhs' = Formula(i,copy b,l)::rhs in
          let s1 = Sequent(lvl, zip [], rhs') in
          let s2 = Sequent(lvl, zip [Formula(i,copy b,r)], rhs) in
          sc [s1;s2]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "imp_l" (matchLeft,"_=>_") tactic)

  let impR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ImplicationFormula(l,r)) ->
          let lhs' = Formula(i,copy b, l)::lhs in
          let s = Sequent(lvl, lhs', zip [Formula(i, copy b, r)]) in
          sc [s]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "imp_r" (matchRight,"_=>_") tactic)

  let impTactical session args =
    (G.orElseTactical (impL session args) (impR session args))
  
  (********************************************************************
  *pi:
  ********************************************************************)
  let piL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.PiFormula(FOA.AbstractionFormula(hint,_) as f)) ->
          let (lvl',var) = makeExistentialVar hint lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i, copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "pi_l" (matchLeft,"pi _") tactic)

  let piR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.PiFormula(FOA.AbstractionFormula(hint,_) as f)) ->
          let (lvl',var) = makeUniversalVar hint lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i, copy b, Option.get f')]) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "pi_r" (matchRight,"pi _") tactic)

  let piTactical session args =
    (G.orElseTactical (piR session args) (piL session args))

  (********************************************************************
  *sigma:
  ********************************************************************)
  let sigmaL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.SigmaFormula(FOA.AbstractionFormula(hint,_) as f)) ->
          let (lvl',var) = makeUniversalVar hint lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i, copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "sigma_l" (matchLeft,"sigma _") tactic)

  let sigmaR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.SigmaFormula(FOA.AbstractionFormula(hint,_) as f)) ->
          let (lvl',var) = makeExistentialVar hint lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i, copy b, Option.get f')]) in
            sc [s]
          else
            (O.error "invalid number of arguments.";
            fc ())
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "sigma_r" (matchRight,"sigma _") tactic)

  let sigmaTactical session args =
    (G.orElseTactical (sigmaL session args) (sigmaR session args))

  (********************************************************************
  *nabla:
  ********************************************************************)
  let nablaL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.NablaFormula(FOA.AbstractionFormula(_) as f)) ->
          let (lvl',i',var) = makeNablaVar lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', zip [Formula(i', copy b, Option.get f')], rhs) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "nabla_l" (matchLeft, "nabla _") tactic)

  let nablaR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.NablaFormula(FOA.AbstractionFormula(_) as f)) ->
          let (lvl',i',var) = makeNablaVar lvl i in
          let f' = FOA.apply [var] f in
          if Option.isSome f' then
            let s = Sequent(lvl', lhs, zip [Formula(i', copy b, Option.get f')]) in
            sc [s]
          else
            fc ()
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "nabla_r" (matchRight,"nabla _") tactic)

  let nablaTactical session args =
    (G.orElseTactical (nablaL session args) (nablaR session args))
    
  (********************************************************************
  *mu:
  ********************************************************************)
  let muR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ApplicationFormula(
          FOA.MuFormula(name,argnames,body) as mu, args)) ->
            let body' = FOA.applyFixpoint (abstractFixpointDefinition mu argnames) body in
            if Option.isSome body' then
              let mu' = FOA.apply args (Option.get body') in
              if (Option.isSome mu') then
                let () = O.debug ("muR: after applying arguments: " ^ (FOA.string_of_formula_ast (Option.get mu')) ^ "\n") in
                let s = Sequent(lvl, lhs, zip [Formula(i,copy b, Option.get mu')]) in
                (sc [s])
              else
                (O.impossible "unable to apply arguments to mu formula.\n";
                fc ())
            else
              (O.impossible "definition has incorrect arity.\n";
              fc ())
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "mu_r" (matchRight, "mu _") tactic)

  let muL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ApplicationFormula(
          FOA.MuFormula(name,argnames,body) as mu, args)) ->
            let body' = FOA.applyFixpoint (abstractFixpointDefinition mu argnames) body in
            if Option.isSome body' then
              let mu' = FOA.apply args (Option.get body') in
              if Option.isSome mu' then
                let s = Sequent(lvl, zip [Formula(i,copy b,Option.get mu')], rhs) in
                (sc [s])
              else
                (O.impossible "unable to apply arguments to nu formula.\n";
                fc ())
            else
              (O.impossible "definition has incorrect arity.\n";
              fc ())
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "mu_l" (matchLeft, "mu _") tactic)

  let muTactical session args =
    (G.orElseTactical (muL session args) (muR session args))


  (*  TODO: Induction and coinduction should check for an invariant
      with too GREAT an arity as well as too little.  *)
  (******************************************************************
  *induction:
  ******************************************************************)
  let inductionTactical session args =
    (******************************************************************
    *makeArgs:
    * Makes a list the same length as args of logic variables.
    ******************************************************************)
    let rec makeArgs lvl lts args =
      match args with
        [] -> (lvl, [])
      | a::aa ->
          let (lvl', a') = makeUniversalVar a lvl lts in
          let (lvl'', aa') = makeArgs lvl' lts aa in
          (lvl'',  a'::aa')
    in
    
    (******************************************************************
    *matchTemplate:
    * Finds the correct formula to apply induction to and calls
    * ind on it.
    ******************************************************************)
    let rec matchTemplate template inv = fun sequent sc fc ->
      let lvl = getSequentLevel sequent in
      (****************************************************************
      *ind:
      * Parses the invariant and calls sc with the generated sequents.
      ****************************************************************)
      let ind f zip lhs rhs sc fc =
        match f with
          Formula(i,b,FOA.ApplicationFormula(FOA.MuFormula(name,argnames,body),args)) ->
            let s' = parseFormula (getSessionDefinitions session) inv in
            if Option.isSome s' then
              let s' = Option.get s' in
              let f' = FOA.apply args s' in
              if Option.isSome f' then
                let s1 = Sequent(lvl, zip [Formula(i,copy b,Option.get f')], rhs) in

                let (lvl', args') = makeArgs lvl i argnames in
                
                let r = FOA.apply args' s' in
                let body' = FOA.applyFixpoint s' body in
                if (Option.isSome r) && (Option.isSome body') then
                  let l = FOA.apply args' (Option.get body') in
                  if (Option.isSome l) then
                    let s2 = Sequent(lvl', [Formula(i, copy b, Option.get l)], [Formula(i, copy b, Option.get r)]) in
                    (sc [s1;s2])
                  else
                    (O.impossible "unable to apply arguments to mu formula.\n";
                    fc ())
                else
                  (O.error "invariant has incorrect arity.\n";
                  fc ())
              else
                (O.error ("invariant has incorrect arity.\n");
                fc ())
            else
              (O.error ("unable to parse invariant.\n");
              fc ())
        | _ ->
            (O.impossible "invalid formula.\n";
            fc ())
      in
      let sc' s = sc s (makeProofBuilder "induction") fc in
      match (matchLeft template sequent) with
        Some(f,zip,lhs,rhs) -> (ind f zip lhs rhs sc' fc)
      | None -> fc ()
    in
    
    match args with
        [] -> (G.invalidArguments "no invariant specified.")
      | Absyn.String(inv)::[] ->
          let template = FOA.ApplicationFormula(FOA.makeAnonymousFormula (), []) in 
          G.makeTactical (matchTemplate template inv)
      | Absyn.String(inv)::Absyn.String(template)::[] ->
          let template = parseFormula (getSessionDefinitions session) template in
          if (Option.isSome template) then
            G.makeTactical (matchTemplate (Option.get template) inv)
          else
            (O.error "induction: unable to parse template.\n";
            G.failureTactical)
      | _ -> G.invalidArguments "induction: incorrect number of arguments."
  (********************************************************************
  *nu:
  ********************************************************************)
  let nuR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ApplicationFormula(
          FOA.NuFormula(name,argnames,body) as mu, args)) ->
            let body' = FOA.applyFixpoint (abstractFixpointDefinition mu argnames) body in
            if Option.isSome body' then
              let mu' = FOA.apply args (Option.get body') in
              if Option.isSome mu' then
                let s = Sequent(lvl, lhs, zip [Formula(i,copy b,Option.get mu')]) in
                (sc [s])
              else
                (O.impossible "unable to apply arguments to nu formula.\n";
                fc ())
            else
              (O.impossible "definition has incorrect arity.\n";
              fc ())
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "nu_r" (matchRight, "nu _") tactic)

  let nuL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.ApplicationFormula(
          FOA.NuFormula(name,argnames,body) as mu, args)) ->
            let body' = FOA.applyFixpoint (abstractFixpointDefinition mu argnames) body in
            if Option.isSome body' then
              let mu' = FOA.apply args (Option.get body') in
              if Option.isSome mu' then
                let s = Sequent(lvl, zip [Formula(i,copy b,Option.get mu')], rhs) in
                (sc [s])
              else
                (O.impossible "unable to apply arguments to nu formula.\n";
                fc ())
            else
              (O.impossible ("definition has incorrect arity.\n");
              fc ())
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "nu_l" (matchLeft, "nu _") tactic)

  let nuTactical session args =
    (G.orElseTactical (nuL session args) (nuR session args))

  (******************************************************************
  *coinduction:
  ******************************************************************)
  let coinductionTactical session args =
    (******************************************************************
    *makeArgs:
    * Makes a list the same length as args of logic variables.
    ******************************************************************)
    let rec makeArgs lvl lts args =
      match args with
        [] -> (lvl, [])
      | a::aa ->
          let (lvl', a') = makeUniversalVar a lvl lts in
          let (lvl'', aa') = makeArgs lvl' lts aa in
          (lvl'',  a'::aa')
    in
    
    (******************************************************************
    *matchTemplate:
    * Finds the correct formula to apply induction to and calls
    * ind on it.
    ******************************************************************)
    let rec matchTemplate template inv = fun sequent sc fc ->
      let lvl = getSequentLevel sequent in
      (****************************************************************
      *coind:
      * Parses the invariant and calls sc with the generated sequents.
      ****************************************************************)
      let coind f zip lhs rhs sc fc =
        match f with
          Formula(i,b,FOA.ApplicationFormula(FOA.NuFormula(name,argnames,body),args)) ->
            let s' = parseFormula (getSessionDefinitions session) inv in
            if Option.isSome s' then
              let s' = (Option.get s') in
              let f' = FOA.apply args s' in
              if Option.isSome f' then
                let s1 = Sequent(lvl, lhs, zip [Formula(i,copy b,Option.get f')]) in

                let (lvl', args') = makeArgs lvl i argnames in
                
                let l = FOA.apply args' s' in
                let body' = FOA.applyFixpoint s' body in
                
                if (Option.isSome l) && (Option.isSome body') then
                  let () = O.debug ("coinduction: apply fixpoint result: " ^ (FOA.string_of_formula_ast (Option.get body')) ^ "\n") in

                  let r = FOA.apply args' (Option.get body') in
                  if Option.isSome r then
                    let () = O.debug ("coinduction: result: " ^ (FOA.string_of_formula_ast (Option.get r)) ^ "\n") in
                    let s2 = Sequent(lvl', [Formula(i, copy b, Option.get l)], [Formula(i, copy b, Option.get r)]) in
                    (sc [s1;s2])
                  else
                    (O.impossible "unable to apply arguments to nu formula.\n";
                    fc ())
                else
                  (O.error "coinvariant has incorrect arity.\n";
                  fc ())
              else
                (O.error "coinvariant has incorrect arity.\n";
                fc ())
            else
              (O.error ("unable to parse coinvariant: " ^ inv ^ ".\n");
              fc ())
        | _ ->
            (O.impossible "invalid formula.\n";
            fc ())
      in
      let sc' s = sc s (makeProofBuilder "coinduction") fc in
      match (matchRight template sequent) with
        Some(f,zip,lhs,rhs) -> (coind f zip lhs rhs sc' fc)
      | None -> fc ()
    in
    
    match args with
        [] -> (G.invalidArguments "no invariant specified.")
      | Absyn.String(inv)::[] ->
          let template = FOA.ApplicationFormula(FOA.makeAnonymousFormula (), []) in 
          G.makeTactical (matchTemplate template inv)
      | Absyn.String(inv)::Absyn.String(template)::[] ->
          let template = parseFormula (getSessionDefinitions session) template in
          if (Option.isSome template) then
            G.makeTactical (matchTemplate (Option.get template) inv)
          else
            (O.error "coinduction: unable to parse template.\n";
            G.failureTactical)
      | _ -> (G.invalidArguments "coinduction: incorrect number of arguments.")

  (********************************************************************
  *eq:
  ********************************************************************)
  let eqL =
    let tactic session seq f zip lhs rhs sc fc =
      let copier = Term.copy_eigen () in
      let zip' = List.map (copyFormula ~copier) (zip []) in
      let rhs' = List.map (copyFormula ~copier) rhs in
      let f' = copyFormula ~copier f in
      let lvl = getSequentLevel seq in
      match f' with
        Formula(i, b, FOA.EqualityFormula(t1, t2)) ->
          (match (FOA.leftUnify t1 t2) with
              FOA.UnifyFailed -> (sc [])
            | FOA.UnifySucceeded ->
                let s = Sequent(lvl, zip', rhs') in
                (sc [s])
            | FOA.UnifyError(s) ->
                (O.error (s ^ ".\n");
                fc ()))
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "eq_l" (matchLeft, "_ = _") tactic)

  let eqR =
    let tactic session seq f zip lhs rhs sc fc =
      match f with
        Formula(i, b, FOA.EqualityFormula(t1,t2)) ->
          (match (FOA.rightUnify t1 t2) with
              FOA.UnifySucceeded -> (sc [])
            | FOA.UnifyFailed -> fc ()
            | FOA.UnifyError(s) ->
                  (O.error (s ^ ".\n");
                  fc ()))
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "eq_r" (matchRight,"_ = _") tactic)
    
  let eqTactical session args =
      (G.orElseTactical (eqL session args) (eqR session args))

  (********************************************************************
  *examineTactical:
  * Prints the ast of all sequents.
  ********************************************************************)
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

  (********************************************************************
  *contraction:
  ********************************************************************)
  let contractL =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      let s = Sequent(lvl, (zip [f;f]), rhs) in
      sc [s]
    in
    (makeSimpleTactical "contract_l" (matchLeft, "") tactic)
  
  let contractR =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      let s = Sequent(lvl, lhs, (zip [f;f])) in
      sc [s]
    in
    (makeSimpleTactical "contract_r" (matchRight, "") tactic)
  
  let contractTactical session args =
    (G.orElseTactical (contractL session args) (contractR session args))
  
  (********************************************************************
  *simplify:
  * Applies all asynchronous rules.
  ********************************************************************)
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
  *Additive Or:
  ********************************************************************)
  let orRRight =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.OrFormula(l,r)) ->
          let rhs' = zip [Formula(i,copy b, r)] in
          let s = Sequent(lvl, lhs, rhs') in
          sc [s]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "right" (matchRight,"_;_") tactic)
    
  let orRLeft =
    let tactic session seq f zip lhs rhs sc fc =
      let lvl = getSequentLevel seq in
      match f with
        Formula(i, b, FOA.OrFormula(l,r)) ->
          let rhs' = zip [Formula(i,copy b, l)] in
          let s = Sequent(lvl, lhs, rhs') in
          sc [s]
      | _ ->
          (O.impossible "invalid formula.\n";
          fc ())
    in
    (makeSimpleTactical "left" (matchRight,"_;_") tactic)
 
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

    let ts = Logic.Table.add "or_l" orL ts in
    
    let ts =
      if Param.intuitionistic then ts else Logic.Table.add "or" orTactical ts
    in
    let ts =
      if Param.intuitionistic then
        Logic.Table.add "left" orRLeft
          (Logic.Table.add "right" orRRight ts)
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
      Session(pervasiveTacticals, Logic.Table.empty, [],
      Logic.idProofBuilder, state, Term.get_subst state,
      (Term.save_namespace (), Term.save_namespace ()))

  (********************************************************************
  *reset:
  * Provides a new sequent.  This amounts to returning the empty
  * sequent.
  ********************************************************************)
  let initialNamespace = Term.save_namespace ()
  let reset () =
    (Term.restore_namespace initialNamespace;
    emptySession)

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
