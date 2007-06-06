(**********************************************************************
*Firstorder:
* Implements a simple first order logic with equality.
**********************************************************************)
module Firstorder (O : Output.Output) =
struct
  let name = "First Order Logic"
  let info =
"
First Order Logic v0.0

Implements a simple first order logic with equality.
   
"
  let start = info
  
  (********************************************************************
  *Formula:
  * Represent formulae in sequents, with a local context.
  ********************************************************************)
  type formula = (int * Firstorderabsyn.formula)
  let string_of_formula (_,t) = Firstorderabsyn.string_of_formula t
  let makeFormula t = (0, t)
  
  
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
  *Session:
  * A session is simply the current list of sequents.
  ********************************************************************)  
  type session = Session of sequent list
  let emptySession = Session([])
  let getSessionSequents (Session(sequents)) = sequents
  let setSessionSequents sequents (Session(_)) = (Session(sequents))

  let string_of_sequent seq =
    let lhs = getSequentLHS seq in
    let rhs = getSequentRHS seq in
    let top = (String.concat "\n" (List.map string_of_formula lhs)) in
    let bottom = (String.concat ", " (List.map string_of_formula rhs)) in
    (top ^ "\n" ^ (String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)

  let string_of_sequent_rhs seq =
    let rhs = getSequentRHS seq in
    let bottom = (String.concat ", " (List.map string_of_formula rhs)) in
    ((String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)
    
  let string_of_sequents sequents =
    let mainseq = List.hd sequents in
    let seqs = List.tl sequents in
    if (List.length seqs) > 0 then
      (string_of_sequent mainseq) ^ "\n\n" ^ (String.concat "\n\n" (List.map string_of_sequent_rhs seqs)) ^ "\n"
    else
      (string_of_sequent mainseq) ^ "\n"

  (********************************************************************
  *incl:
  ********************************************************************)
  let incl files session =
    session

  (********************************************************************
  *reset:
  * Provides a new sequent.  This amounts to returning the empty
  * sequent.
  ********************************************************************)
  let reset () = emptySession
  
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
      Firstorderabsyn.SyntaxError(s) ->
        (O.error (s ^ ".\n");
        None)
  
  (********************************************************************
  *parseFormula:
  * Parses the argument into a formula.  If successful, returns Some
  * with the parsed formula, otherwise it returns None.
  ********************************************************************)
  let parseFormula t =
    try
      let formula = Firstorderparser.toplevel_formula Firstorderlexer.token (Lexing.from_string t) in
      Some formula
    with
        Firstorderabsyn.SyntaxError(s) ->
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
    let f = parseFormula t in
    if Option.isSome f then
      let seq = makeSequent [] [makeFormula (Option.get f)] in
      (setSessionSequents [seq] session)
    else
      session

  let definition d session = session
  let operator name fix prec session = session
  let updateSequents sequents session = (setSessionSequents sequents session)
  let validSequent session =
    let sequents = (getSessionSequents session) in
    (List.length sequents > 0)
  let sequent session =    
    let sequents = (getSessionSequents session) in
    if List.length sequents > 0 then
      Some (List.hd sequents, (updateSequents (List.tl sequents) session))
    else
      None
  let sequents session = (getSessionSequents session)
  
  type proof = string
  let string_of_proofs proofs =
    "\t" ^ (String.concat "\n\t" proofs) ^ "\n"
    
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
  * Performs unification as on the right.  If unification is successful
  * it calls the success continuation with the failure continuation in
  * the place of "continue".  Otherwise, it calls the failure
  * continuation
  ********************************************************************)
  let rightUnify a b =
    let state = Term.save_state () in
    try
      (Right.pattern_unify a b;
      true)
    with
      Unify.Error _ -> (Term.restore_state state; false)
     
  let leftUnify a b =
    let state = Term.save_state () in
    match (Term.copy [a;b]) with
        [a';b'] ->
          (try
            (Left.pattern_unify a' b';
            true)
          with
            Unify.Error _ -> (Term.restore_state state; false))
      | _ -> (failwith "Firstorder.leftUnify: Term.copy returned invalid list.")

  let makeExistentialVar lvl =
    (lvl, Term.fresh ~tag:Term.Logic lvl)

  let makeUniversalVar lvl =
    (lvl + 1, Term.fresh ~tag:Term.Eigen (lvl + 1))

  let makeNablaVar lvl i =
    (lvl, i + 1, Term.nabla (i + 1))
  
  (********************************************************************
  *Tacticals:
  ********************************************************************)
  module FirstorderSig =
  struct
    type logic_sequent = sequent
    type logic_proof = proof
  end
  module G = Logic.GenericTacticals (FirstorderSig) (O)
  
  let makeBuilder s = fun proofs ->
    s ^ "(" ^ (String.concat ", " proofs) ^ ")"

  (*  Axiom *)
  let axiomTactical = function
      [] ->
        let rec unifyList sc lhs f =
          match f with
              (i, Firstorderabsyn.AtomicFormula(t)) ->
                (match lhs with
                  [] -> ()
                | (i', Firstorderabsyn.AtomicFormula(t'))::ls ->
                    if (rightUnify t t') then
                      sc ()
                    else
                      (unifyList sc ls f)
                | _::ls ->
                    (unifyList sc ls f))
            | _ -> ()
        in
        let pretactic = fun sequent sc fc ->
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          
          let sc' () = sc [] (makeBuilder "axiom") fc in
          (List.iter (unifyList sc' lhs) rhs;
          fc ())
        in
        G.makeTactical pretactic
    | _ -> (G.invalidArguments "axiom")
  
    (*  Implication Right *)
  let impR = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i, Firstorderabsyn.ImplicationFormula(l,r))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s = (lvl, (i,l)::lhs, (i,r)::rhs') in
                  (sc [s] (makeBuilder "imp_r") fc)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "imp_r"

  (*  Implication Left  *)
  let impL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i, Firstorderabsyn.ImplicationFormula(l,r))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s1 = (lvl, lhs', (i,l)::rhs) in
                  let s2 = (lvl, (i,r)::lhs', rhs) in
                  (sc [s1;s2] (makeBuilder "imp_l") fc)
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "imp_l"

  (*  Or Left  *)
  let orL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.OrFormula(l,r))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s1 = (lvl, (i,l)::lhs', rhs) in
                  let s2 = (lvl, (i,r)::lhs', rhs) in
                  (sc [s1;s2] (makeBuilder "or_l") fc)
              | t::ts ->
                  (apply lvl ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "or_l"

  (*  Or Right  *)
  let orR = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i, Firstorderabsyn.OrFormula(l,r))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s = (lvl, lhs, (i,l)::(i,r)::rhs') in
                  (sc [s] (makeBuilder "or_r") fc)
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
  
  (*  And Left  *)
  let andL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.AndFormula(l,r))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s = (lvl,(i,l)::(i,r)::lhs', rhs) in
                  (sc [s] (makeBuilder "and_l") fc)
              | t::ts ->
                  (apply lvl ts (t::lhs) ts)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "and_l"
    
  (*  And Right *)
  let andR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.AndFormula(l,r))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s1 = (lvl, lhs, (i,l)::rhs') in
                  let s2 = (lvl, lhs, (i,r)::rhs') in
                  (sc [s1;s2] (makeBuilder "and_r") fc)
              | t::ts ->
                  (apply lvl ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "and_r"

  (*  Pi L  *)
  let piL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.PiFormula(f))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let (lvl', var) = makeExistentialVar lvl in
                  let f' = Firstorderabsyn.apply [var] f in 
                  let s = (lvl', (i,f')::lhs', rhs) in
                  (sc [s] (makeBuilder "pi_l") fc)
              | t::ts ->
                  (apply lvl ts (t::lhs) ts)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "pi_l"

  (*  Pi Right  *)
  let piR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.PiFormula(f))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let (lvl', var) = makeUniversalVar lvl in
                  let f' = Firstorderabsyn.apply [var] f in
                  let s = (lvl', lhs, (i,f')::rhs') in
                  (sc [s] (makeBuilder "pi_r") fc)
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
  let sigmaL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.SigmaFormula(f))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let (lvl', var) = makeUniversalVar lvl in
                  let f' = Firstorderabsyn.apply [var] f in 
                  let s = (lvl', (i,f')::lhs', rhs) in
                  (sc [s] (makeBuilder "sigma_l") fc)
              | t::ts ->
                  (apply lvl ts (t::lhs) ts)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "sigma_l"

  (*  Sigma Right *)
  let sigmaR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.SigmaFormula(f))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let (lvl', var) = makeExistentialVar lvl in
                  let f' = Firstorderabsyn.apply [var] f in
                  let s = (lvl', lhs, (i,f')::rhs') in
                  (sc [s] (makeBuilder "sigma_r") fc)
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
  let nablaL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms lhs rhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.NablaFormula(f))::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let (lvl', i', var) = makeNablaVar lvl i in
                  let f' = Firstorderabsyn.apply [var] f in 
                  let s = (lvl', (i',f')::lhs', rhs) in
                  (sc [s] (makeBuilder "nabla_l") fc)
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
  let nablaR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms rhs lhs =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.NablaFormula(f))::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let (lvl', i', var) = makeNablaVar lvl i in
                  let f' = Firstorderabsyn.apply [var] f in
                  let s = (lvl', lhs, (i',f')::rhs') in
                  (sc [s] (makeBuilder "nabla_r") fc)
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
  let eqR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.EqualityFormula(t1, t2))::ts ->                  
                  if (rightUnify t1 t2) then
                    (sc [] (makeBuilder "eq_r") fc)
                  else
                    (apply lvl ts)
              | t::ts ->
                  (apply lvl ts)
          in
          let rhs = getSequentRHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "eq_r"

  (*  Equality Right *)
  let eqL = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply lvl terms =
            match terms with
                [] -> fc ()
              | (i,Firstorderabsyn.EqualityFormula(t1, t2))::ts ->                  
                  if not (leftUnify t1 t2) then
                    (sc [] (makeBuilder "eq_l") fc)
                  else
                    (apply lvl ts)
              | t::ts ->
                  (apply lvl ts)
          in
          let lhs = getSequentLHS sequent in
          let lvl = getSequentLevel sequent in
          (apply lvl lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "eq_l"

  let orTactical = function
      [] -> (G.orElseTactical (orL []) (orR []))
    | _ -> G.invalidArguments "or"

  let andTactical = function
      [] -> (G.orElseTactical (andL []) (andR []))
    | _ -> G.invalidArguments "and"

  let impTactical = function
      [] -> (G.orElseTactical (impL []) (impR []))
    | _ -> G.invalidArguments "imp"
  
  let piTactical = function
      [] -> (G.orElseTactical (piR []) (piL []))
    | _ -> G.invalidArguments "pi"

  let sigmaTactical = function
      [] -> (G.orElseTactical (sigmaL []) (sigmaR []))
    | _ -> G.invalidArguments "sigma"

  let nablaTactical = function
      [] -> (G.orElseTactical (nablaL []) (nablaR []))
    | _ -> G.invalidArguments "nabla"

  let eqTactical = function
      [] -> (G.orElseTactical (eqL []) (eqR []))
    | _ -> G.invalidArguments "eq"

  (********************************************************************
  *tacticals:
  * The exported table of tacticals.  These tacticals are the only
  * ones avaible at the toplevel.  GenericTacticals.tacticals is used
  * as the initial table, providing the standard tacticals.
  ********************************************************************)
  let tacticals =
    let ts = G.tacticals in    
    let ts = Logic.Table.add "and" andTactical ts in
    let ts = Logic.Table.add "or" orTactical ts in
    let ts = Logic.Table.add "imp" impTactical ts in

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
    ts
end