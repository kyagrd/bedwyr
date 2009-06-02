(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
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

(**********************************************************************
* Firstorder Properties:
*
* NOTE: These are shared across all logics constructed by the functor;
* in particular if you load a new logic these aren't reset.
**********************************************************************)
let () = Properties.setBool "firstorder.proofsearchdebug" false
let () = Properties.setBool "firstorder.debug" false
let () = Properties.setBool "firstorder.term-debug" false
let () = Properties.setInt "firstorder.defaultbound" 3
(* The following is a bad name, for historical reasons *)
let () = Properties.setBool "firstorder.asyncbound" true
let () = Properties.setInt "firstorder.defaultasyncbound" 10
let () = Properties.setBool "firstorder.lemmas" false
let () = Properties.setInt "firstorder.lemmas.bound" 1
let () = Properties.setString "firstorder.frozens" "thaw"
let () = Properties.setBool "firstorder.induction-unfold" false
let () = Properties.setBool "firstorder.coinduction-unfold" false
let () = Properties.setBool "firstorder.thawasync" false

(*  fix-nabla-induction:  this will attempt to abstract the appropriate
    things during invariant generation so that the generic context
    gets properly taken into account.  Problem is, it doesn't quite
    work, because the naive vision of nabla doesn't work with induction.
*)
let () = Properties.setBool "firstorder.fix-nabla-induction" true

(**********************************************************************
*Firstorder:
* Implements a simple first order logic.  The logic includes equality
* and fixed points, with a definition-like facility to handle them.
**********************************************************************)
module Firstorder (Param : Firstordertypes.ParamSig) (O : Output.Output) : Logic.Logic =
struct
  module FOA = Firstorderabsyn
  module FOT = Firstordertypes.Types (O)
  open FOT
  
  exception NonMonotonic

  let name = Param.name
  let info = Param.name ^ "\n"
  let start = info

  type session = FOT.session
  type proof = FOT.proof
  type sequent = FOT.sequent

  (********************************************************************
  *string_of_sequent:
  * Convert a sequent to a string, including the sequent's level.
  ********************************************************************)
  let string_of_sequent seq =
    let top       = String.concat "\n" (List.map string_of_formula seq.lhs) in
    let bottom    = String.concat "\n" (List.map string_of_formula seq.rhs) in
    let separator = String.make (max (min (String.length bottom) 72) 16) '-' in
    (* top should always start with an empty line (it looks better)
     * whether lhs is empty or not *)
    let top = if top <> "" then "\n" ^ top else top in
      if Properties.getBool "firstorder.proofsearchdebug" then
        Printf.sprintf "%s\n%d: %s\n%s" top seq.lvl separator bottom
      else
        Printf.sprintf "%s\n %s\n%s" top separator bottom

  let ppxml_sequent fmt seq =
    let print_side side forms =
      Format.fprintf fmt "<%s>@," side ;
      List.iter (fun f -> Format.fprintf fmt "%s@," (xml_of_formula f)) forms ;
      Format.fprintf fmt "</%s>" side
    in
    let isFocused seq =
      let check (Formula(_,(ann,f))) = ann.FOA.control = FOA.Focused in
      (List.exists check seq.lhs) || (List.exists check seq.rhs)
    in
    Format.fprintf fmt "@[<><sequent><level>%d</level>@,@[<hov 2>" seq.lvl ;
    print_side "lhs" seq.lhs ;
    Format.fprintf fmt "@," ;
    print_side "rhs" seq.rhs ;
    Format.fprintf fmt "<focused>%b</focused>" (isFocused seq) ;
    Format.fprintf fmt "@]</sequent>@]"

  let xml_of_sequent seq =
    ppxml_sequent Format.str_formatter seq ; Format.flush_str_formatter ()

  let string_of_sequent_rhs seq =
    let bottom    = String.concat "\n" (List.map string_of_formula seq.rhs) in
    let separator = String.make (max (min (String.length bottom) 72) 16) '-' in
      if Properties.getBool "firstorder.proofsearchdebug" then
        Printf.sprintf "%d: %s\n%s" seq.lvl separator bottom
      else
        Printf.sprintf " %s\n%s" separator bottom
  
  let sequents session = session.sequents
  let validSequent session = [] <> session.sequents

  let tacticals session = session.tactics
  let defineTactical name tac session =
    let ts = session.tactics in
    let ts' = Logic.Table.add name tac ts in
    (O.output ("Tactical: " ^ name ^ ".\n");
    { session with tactics = ts' })

  let proof session = session.builder

  (********************************************************************
  *undo:
  * Implements undo functionality; the given session is the session
  * that we should undo "to".
  ********************************************************************)
  let undo session =
    Term.restore_state session.state ;
    Term.restore_namespace session.proof_namespace ;
    session

  (********************************************************************
  *redo:
  * Implements redo functionality; the given session is the session
  * that we should redo "to".
  ********************************************************************)
  let redo session =
    (* The idea would be to use the diff field to redo,
     * but this is actually unused and not implemented. *)
    assert false

  (********************************************************************
  *update:
  * Updating to new sequents and proof builders.  We note the state
  * of terms to use when coming back to this point by undoing. 
  ********************************************************************)
  let update sequents builder session =
    let state = Term.save_state () in
    let subst = Term.get_subst state in
      { session with state = state ; diff = subst ;
                     proof_namespace = Term.save_namespace () ;
                     sequents = sequents ; builder = builder }

  let rec string_of_proof proof =
    let s = Printf.sprintf "<rule><name>%s</name>\n" proof.rule in
    (* let p =
      List.map
        (fun (k,v) -> Printf.sprintf "<key>%s</key><value>%s</value>\n" k v)
        proof.params
    in
    let s = List.fold_left (^) s p in *)
    let s =
      s ^ xml_of_sequent proof.sequent
    in
    let s = match proof.formula with
      | None -> s ^ "<formula><generic></generic>stub</formula>"
      | Some f -> s ^ xml_of_formula f
    in
    let s =
      s ^ "<bound>" ^
      String.concat " " (List.map Pprint.term_to_string proof.bindings)
      ^ "</bound>"
    in
    let proofs = List.map string_of_proof proof.subs in
      (* Allow the re-use of variables' names in other branches. *)
      (* List.iter
        (fun b ->
           if match Term.observe b with Term.Var _ -> true | _ -> false then
             Term.free (Term.get_name b)
           (* else we should be smart and free some subvars but not all *))
        proof.bindings ; *)
      List.iter (fun b -> Term.free (Term.get_name b))
        (Term.get_vars (fun _ -> true) proof.bindings) ;
      s ^ "<sub>" ^ List.fold_left (^) "" proofs ^ "</sub>\n</rule>\n"

  let string_of_proofs session =
    Term.restore_namespace session.proof_namespace ;
    let proofs = List.map string_of_proof (session.builder []) in
      String.concat "" proofs

  (********************************************************************
  *string_of_sequents:
  * This is called by the interface to print the currently open leafs.
  * The sequent is printed from within a namespace which has only the
  * constants defined in the theorem's statement (one doesn't want to observe
  * the effects of invisible logic or eigen-variables) and the namespace
  * is left in the state after that printing, so that the next input
  * can rely on what has been displayed.
  ********************************************************************)
  let string_of_sequents session =
    let sequents = session.sequents in
      (* Term.restore_namespace session.proof_namespace  ; *)
      match sequents with
        | [] -> ""
        | mainseq::seqs ->
            if [] <> seqs then
              let mainseq = string_of_sequent mainseq in
                mainseq ^ "\n\n" ^
                (String.concat "\n\n" (List.map string_of_sequent_rhs seqs)) ^
                "\n"
            else
              (string_of_sequent mainseq) ^ "\n"

  (********************************************************************
  *lemmas:
  * Called by the interpreter to print the current set of lemmas.
  * This just prints the names of the lemmas.
  ********************************************************************)
  let lemmas session =
    let output =
    "Lemmas:\n" ^
    (String.concat "\n" (List.map (fun (s,_,_) -> "  " ^ s) session.lemmas)) ^
    "\n"
    in
    O.output output;
    session

   
  (********************************************************************
  *prove:
  * Parses the argument into a formula, and then prepares the session to
  * prove the formula.  It saves the namespaces so that after proving
  * the theorem constant names won't remain "used up".  It also sets
  * the session sequents to be exactly one sequent with the parsed
  * formula on the right.
  ********************************************************************)
  let prove name t session =
    Term.restore_namespace session.initial_namespace ;
    let f = parseFormula session.definitions t in
    let proofNamespace = Term.save_namespace () in
      match f with
        | Some f ->
            { session with
                  proof_namespace = proofNamespace ;
                  builder = Logic.idProofBuilder ;
                  sequents = [{ bound = None ;
                                lemma_bound = None ;
                                lvl=0 ; lhs=[] ; rhs=[makeFormula f] }] ;
                  theorem_name = Some name;
                  theorem = Some f}
        | None -> session

  (********************************************************************
  *lemma:
  * Sets the 'provingLemma' flag, and then calls prove.  In proved
  * we check the 'provingLemma' flag to decide whether to add the
  * lemma to the session's list of lemmas.
  ********************************************************************)
  let lemma name t session =
    prove name t {session with provingLemma = true}
  
  (********************************************************************
  *theorem:
  * Unsets the 'provingLemma' flag, and then calls prove (see lemma
  * above).
  ********************************************************************)
  let theorem name t session =
    prove name t {session with provingLemma = false}
 
  (********************************************************************
  *theoremName:
  * Returns the current theorem name, if it exists.  If it doesn't,
  * its a compiler bug.
  ********************************************************************)
  let theoremName session =
    if Option.isSome session.theorem_name then
      Option.get session.theorem_name
    else
      assert false

  (********************************************************************
  *proved:
  * Called when a theorem has been proven.
  ********************************************************************)
  let proved session =
    match (session.builder []) with
        [proof] ->
        if session.provingLemma then
          let lemmas' =
            (Option.get session.theorem_name,
              Option.get session.theorem,
              proof) ::
            session.lemmas
          in
          {session with lemmas = lemmas'}
        else
          session
      | _ ->
        failwith ("invalid proof of theorem '" ^ (Option.get session.theorem_name) ^ "'")

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
      * Determines whether a definition is monotonic.  A definition is
      * monotonic if none of its DB indices occur under an odd number
      * of negations.  Has to use a thrown exception to indicate
      * non-monotonic definitions because mapFormula only likes to
      * return formulas; probably inefficient, but not called often.
      ****************************************************************)
      let checkMonotonicity body =
        let tf t = t in
        let rec ff (db,neg) =
          let ff =
            FOA.mapFormula2
              (fun name (db,neg) -> (db+1,neg))
              (function
                 | FOA.Imp -> fun (db,neg) -> (db,neg+1),(db,neg)
                 | _ -> fun x -> x,x)
              ff tf (db,neg)
          in
            { ff with FOA.predf =
                function
                  | FOA.DBFormula(_,_,db') as f ->              
                      if (db = db') && (neg mod 2) <> 0 then
                        raise NonMonotonic
                      else
                        ff.FOA.predf f
                  | f -> ff.FOA.predf f }
        in
        try
          ignore ((ff (0,0)).FOA.abstf body) ;
          true
        with
          | NonMonotonic -> false
      in

      (****************************************************************
      *abstractDefinition:
      * Abstracts a definition over other fixed points.
      * Iterates over a definition body.
      * If it hits an application whose name is in the abstractions
      * list, it inserts the correct DB index.  If it hits an application
      * whose head is not in the abstractions list (but is in then pre-
      * definitions list), it adds the name to the abstractions list 
      * and abstracts the body of the pre-definition.
      ****************************************************************)
      let abstractDefinition abstractions f =
        (**************************************************************
        *getDB:
        * Get the DB index of a fixpoint if it's already bound.
        **************************************************************)
        let getDB name abs =
          let rec get name abs =
            match abs with
              [] -> None
            | a::abs' ->
                if a = name then
                  Some 0
                else begin
                  match get name abs' with
                    | Some r -> Some (1 + r)
                    | None -> None
                end
          in
            get name abs
        in

        (**************************************************************
        *findDefinition:
        * Finds a pre-definition in the pre-definition list.
        **************************************************************)
        let findDefinition name predefs =
          try
            let find name (FOA.Definition(name',ids,formula,ind)) =
              name' = name
            in
            Some (List.find (find name) predefs)
          with
            Not_found -> None
        in


        let rec ff bound_terms abstractions =
          let rec self =
          { FOA.abstf =
              (function
                 | FOA.AbstractionFormula (name,af) ->
                     FOA.AbstractionFormula
                       (name,(ff (bound_terms+1) abstractions).FOA.abstf af)
                 | FOA.AbstractionBody f ->
                     FOA.AbstractionBody (self.FOA.polf f)) ;
            FOA.predf =
              (fun f ->
                 match f with
                   | FOA.AtomicFormula(head) ->
                       begin match getDB head abstractions with
                         | Some db ->
                             FOA.DBFormula(0,head,db)
                         | None ->
                             match findDefinition head predefs with
                               | Some (FOA.Definition(_,argnames,f',ind)) ->
                                   let f' =
                                     (ff bound_terms (head::abstractions))
                                       .FOA.abstf f'
                                   in
                                     FOA.lift_pred bound_terms
                                       (FOA.FixpointFormula
                                          (ind,head,argnames,f'))
                               | None ->
                                  (if not (FOA.isSpecialAtom head) then
                                    O.warning ("unbound atom '" ^ head ^ "'.\n") ;
                                  f)
                       end
                   | _ ->
                       (FOA.mapFormula (fun () -> self) (fun x -> x)).FOA.predf
                          f) ;
            FOA.polf  =
              (fun (p,f) ->
                let f' = self.FOA.formf f in
                match f' with
                  | FOA.ApplicationFormula(FOA.FixpointFormula(ind,_,_,_),_) ->
                      let pol =
                        if ind = FOA.Inductive then
                          FOA.Positive
                        else
                          FOA.Negative
                      in
                      ({p with FOA.polarity = pol}, f')
                  | _ ->
                      (p, f')) ;
            FOA.formf =
              (fun f ->
                 (FOA.mapFormula (fun () -> self) (fun x -> x)).FOA.formf f) }
          in self
        in
          ((ff 0 abstractions).FOA.abstf f)
      in

      (****************************************************************
      *processPreDefinition:
      * Mu/Nu-abstracts the body of the predefinition, and wraps the body
      * in a Mu/Nu formula.
      ****************************************************************)
      let processPreDefinition (FOA.Definition(name, ids, formula, ind)) =
        let formula' = abstractDefinition [name] formula in
        let result = FOA.Definition(name, ids, formula', ind) in

        if not (checkMonotonicity formula') then
          O.warning (Printf.sprintf
            "%s: non-monotonic definition.\n"
            name) ;

        Some result
      in
      List.map processPreDefinition predefs
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
          else begin
            O.debug (Printf.sprintf
              "Firstorder.definitions: definition ast: %s %s.\n"
              name
              ((FOA.string_of_formula_ast ~generic:[]).FOA.abstf formula)) ;
            O.output ("Definition: " ^ (FOA.string_of_definition def) ^ ".\n") ;
            Logic.Table.add name def (addDefinitions ds table)
          end
    in
        
    let predefs = List.map (parseDefinition session.definitions) defstrings in
    if (List.exists (Option.isNone) predefs) then
      (O.error "definitions contain syntax errors.\n";
      session)
    else
      let defs = processPreDefinitions (List.map (Option.get) predefs) in
      if (List.exists (Option.isNone) defs) then
        (O.error "definitions contain semantic errors.\n";
        session)
      else
        let defs' = (List.map (Option.get) defs) in
        let defs'' = (addDefinitions defs' session.definitions) in
          { session with definitions = defs'' ;
              (* Always remember constants used in the new definitions. *)
              initial_namespace = Term.save_namespace () }

  (********************************************************************
  *incl:
  * Given a list of files, include all definitions in them.
  ********************************************************************)
  let incl files session =
    try
      let defs = List.concat (List.map Firstorderlp.translateFile files) in
      definitions defs session
    with
      Firstorderlp.Error s ->        
        (O.error ("unable to include definitions: " ^ s ^ "\n");
        session)
  
  (********************************************************************
  *logicDefined:
  * Handle logic defined directives; there are none.
  ********************************************************************)
  let logicDefined id args session =
    (O.error ("unknown directive: " ^ id ^ ".\n");
    session)

  (********************************************************************
  *pervasiveTacticals:
  * The tacticals exported by the logic.  Checks the Param module to
  * see determine which structural and disjunction tacticals to allow.
  ********************************************************************)
  module Tacticals = Firstordertacticals.Tacticals (Param) (FOT) (O)
  let pervasiveTacticals =
    let (++) t (a,b) = Logic.Table.add a b t in
    let (||) a b = Tacticals.orElseTactical a b in

    let ts =
      Tacticals.genericTacticals
        ++ ("admit", Tacticals.admitTactical)

        ++ ("and", Tacticals.andL || Tacticals.andR)
        ++ ("and_l", Tacticals.andL)
        ++ ("and_r", Tacticals.andR)
        
        ++ ("imp", Tacticals.impL || Tacticals.impR)
        ++ ("imp_l", Tacticals.impL)
        ++ ("imp_r", Tacticals.impR)

        ++ ("pi", Tacticals.piL || Tacticals.piR)
        ++ ("pi_l", Tacticals.piL)
        ++ ("pi_r", Tacticals.piR)

        ++ ("sigma", Tacticals.sigmaL || Tacticals.sigmaR)
        ++ ("sigma_l", Tacticals.sigmaL)
        ++ ("sigma_r", Tacticals.sigmaR)

        ++ ("nabla", Tacticals.nablaL || Tacticals.nablaR)
        ++ ("nabla_l", Tacticals.nablaL)
        ++ ("nabla_r", Tacticals.nablaR)

        ++ ("eq", Tacticals.eqL || Tacticals.eqR)
        ++ ("eq_l", Tacticals.eqL)
        ++ ("eq_r", Tacticals.eqR)

        ++ ("axiom", Tacticals.axiom)

        ++ ("mu_l", Tacticals.muL)
        ++ ("mu_r", Tacticals.muR)
        ++ ("nu_l", Tacticals.nuL)
        ++ ("nu_r", Tacticals.nuR)
        ++ ("induction", Tacticals.inductionTactical)
        ++ ("coinduction", Tacticals.coinductionTactical)

        ++ ("examine", Tacticals.examineTactical)
        ++ ("examine_pattern", Tacticals.examinePatternTactical)

        ++ ("simplify", Tacticals.simplifyTactical)

        ++ ("true", Tacticals.trueR)
        ++ ("false", Tacticals.falseL)
        ++ ("trivial", Tacticals.trueR || Tacticals.falseL)

        ++ ("apply", Tacticals.applyTactical)
        ++ ("cut", Tacticals.cutTactical)
        ++ ("cut_lemma", Tacticals.cutLemmaTactical)
        ++ ("force", Tacticals.forceTactical)
        ++ ("prove", Tacticals.iterativeDeepeningProveTactical)
        ++ ("async", Tacticals.asyncTactical)

        ++ ("focus", Tacticals.focusTactical)
        ++ ("focus_r", Tacticals.focusRightTactical)
        ++ ("freeze", Tacticals.freezeTactical)
        ++ ("unfocus", Tacticals.unfocusTactical)
        ++ ("sync", Tacticals.syncStepTactical)
        ++ ("set_bound", Tacticals.setBoundTactical)

        ++ ("abstract", Tacticals.abstractTactical)
        
        ++ ("cases", Tacticals.casesTactical)
        ++ ("intros", Tacticals.introsTactical)
    in

    (* Which structural rules to admit. *)
    let ts =
      let ts =
        if Param.intuitionistic then
          ts
        else
          ts
            ++ ("weak_r", Tacticals.weakR)
            ++ ("contract_r", Tacticals.contractR)
            ++ ("rotate_r", Tacticals.rotateR)
      in
        ts
          ++ ("weak_l", Tacticals.weakL)
          ++ ("contract_l", Tacticals.contractL)
          ++ ("rotate_l", Tacticals.rotateL)
    in

    (* Which disjunction tactics are meaningful. *)
    let ts =
      let ts =
        if Param.intuitionistic then
          ts
            ++ ("left", Tacticals.orLeft)
            ++ ("right", Tacticals.orRight)
        else
          ts
            ++ ("or_r", Tacticals.orR)
            ++ ("or", Tacticals.orL||Tacticals.orR)
      in
        ts ++ ("or_l", Tacticals.orL)
    in
    ts

  (** The empty session starts with the expected empty list of sequents
    * and initial list of tacticals, as well as an empty definition table.
    * Additionally it includes the identity proof builder for simplicity
    * (instead of, say, an option), as well as undo, redo, and namespace
    * info. Note that the redo info is currently unused.  *)
  let emptySession =
    let state = Term.save_state () in
    let ns = Term.save_namespace () in
      { tactics = pervasiveTacticals ; definitions = Logic.Table.empty ;
        sequents = [] ; builder = Logic.idProofBuilder ;
        state = state ; diff = Term.get_subst state ;
        initial_namespace = ns ; proof_namespace = ns;
        theorem_name = None;
        theorem = None;
        provingLemma = false;
        lemmas = []}

  (********************************************************************
  *reset:
  * Provides a new session by returning the empty session.
  ********************************************************************)
  let reset =
    let initialNamespace = Term.save_namespace () in
      fun () ->
        Term.restore_namespace initialNamespace ;
        emptySession

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
