(**********************************************************************
*Propositional:
* Implements simple propositional logic without quantification.
**********************************************************************)
module Propositional (O : Output.Output) =
struct
  let name = "Propositional Logic"
  let info =
"
Propositional Logic v0.0

Implements simple propositional logic.

Tacticals:
  auto.       : Automatically proves a sequent.
   
"
  let start = info
  
  (********************************************************************
  *Sequent:
  * Type representing a sequent.  Both left and right sides of the
  * sequent are lists of terms.  Order doesn't matter; tactics and
  * tacticals should succeed if they would succeed on an element in
  * the list.
  ********************************************************************)
  type sequent = (Propositionalabsyn.term list * Propositionalabsyn.term list)
  let emptySequent = ([], [])
  let getSequentLHS (l,_) = l
  let getSequentRHS (_,r) = r

  (********************************************************************
  *Proof:
  ********************************************************************)
  type proof = string
  let string_of_proofs proofs =
    "\t" ^ (String.concat "\n\t" proofs) ^ "\n"

  (********************************************************************
  *Session:
  * A session is just the current list of sequents.  A session is
  * "complete" when it has no sequents.
  ********************************************************************)
  type session = Session of (sequent list)
  let emptySession = Session([])
  let getSessionSequents (Session(sequents)) = sequents
  let setSessionSequents sequents (Session(_)) = (Session(sequents))

  let string_of_sequent seq =
    let lhs = getSequentLHS seq in
    let rhs = getSequentRHS seq in
    let top = (String.concat "\n" (List.map (Propositionalabsyn.string_of_term) lhs)) in
    let bottom = (String.concat ", " (List.map (Propositionalabsyn.string_of_term) rhs)) in
    (top ^ "\n" ^ (String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)

  let string_of_sequent_rhs seq =
    let rhs = getSequentRHS seq in
    let bottom = (String.concat ", " (List.map (Propositionalabsyn.string_of_term) rhs)) in
    ((String.make (max (min (String.length bottom) 72) 16) '-') ^ "\n" ^ bottom)

  let string_of_sequents sequents =
    let mainseq = List.hd sequents in
    let seqs = List.tl sequents in
    if (List.length seqs) > 0 then
      (string_of_sequent mainseq) ^ "\n\n" ^ (String.concat "\n\n" (List.map string_of_sequent_rhs seqs)) ^ "\n"
    else
      (string_of_sequent mainseq) ^ "\n"

  let incl files session =
    session

  let reset () = emptySession

  let parseTerm t =
    try
     let term = Propositionalparser.term Propositionallexer.term (Lexing.from_string t) in 
     Some term
    with
        Propositionalabsyn.SyntaxError(s) ->
          (O.error (s ^ ".\n");
          None)
      | Parsing.Parse_error ->
          (O.error "Syntax error.\n";
          None)

  (********************************************************************
  *prove:
  * Parses the argument into a term, and then prepares the session to
  * prove the term by inserting the term into a sequent on the right.
  ********************************************************************)
  let prove name t session =
    let term = parseTerm t in
    if Option.isSome term then
      (setSessionSequents [([], [Option.get term])] session)
    else
      session

  let definition d session = session
  let operator name fix prec session = session
  let updateSequents sequents session = (setSessionSequents sequents session)
  let validSequent session =
    match (getSessionSequents session) with
        [] -> false
      | _::_ -> true
  let sequent session =    
    let sequents = (getSessionSequents session) in
    if List.length sequents > 0 then
      Some (List.hd sequents, (updateSequents (List.tl sequents) session))
    else
      None
  let sequents session = (getSessionSequents session)

  (********************************************************************
  *Tacticals:
  ********************************************************************)
  module PropositionalSig =
  struct
    type logic_sequent = sequent
    type logic_proof = proof
  end
  module G = Logic.GenericTacticals (PropositionalSig) (O)

  let makeBuilder s = fun proofs ->
    s ^ "(" ^ (String.concat ", " proofs) ^ ")"

  (*  Axiom *)
  let axiomTactical = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let find list el =
            (List.exists ((=) el) list)
          in
           
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          try
            let t = (List.find (find lhs) rhs) in
            sc [] (makeBuilder ("axiom<" ^ (Propositionalabsyn.string_of_term t) ^ ">")) fc
          with Not_found ->
            (fc ())
        in
        G.makeTactical pretactic
    | _ -> (G.invalidArguments "axiom")
  
  (*  Trivial *)
  let trivialTactical = function
      [] ->
          let pretactic = fun sequent sc fc ->
            let lhs = getSequentLHS sequent in
            let rhs = getSequentRHS sequent in
            if (List.exists ((=) Propositionalabsyn.FalseTerm) lhs) ||
              (List.exists ((=) Propositionalabsyn.TrueTerm) rhs) then
              (sc [] (makeBuilder "trivial") fc)
            else
              (fc ())
          in
          G.makeTactical pretactic
    | _ -> G.invalidArguments "trivial"

  (*  Not Right *)
  let notIR = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms rhs lhs =
            match terms with
                [] -> (fc ())
              | Propositionalabsyn.NotTerm(t)::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s = (t::lhs, rhs') in
                  (sc [s] (makeBuilder "not_i_r") fc)
              | t::ts ->
                  (apply ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "not_i_r"

  (*  Not Left  *)
  let notIL = function
      [] ->
        let pretactic = fun sequent sc fc->
          let rec apply terms lhs rhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.NotTerm(t)::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let seq = (lhs', t::rhs) in
                  (sc [seq] (makeBuilder "not_i_l") fc)
              | t::ts ->
                  (apply ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "not_i_l"
    
  (*  Implication Right *)
  let impIR = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms rhs lhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.ImplicationTerm(l,r)::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s = (l::lhs, r::rhs') in
                  (sc [s] (makeBuilder "imp_i_r") fc)
              | t::ts ->
                  (apply ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "imp_i_r"

  (*  Implication Left  *)
  let impIL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms lhs rhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.ImplicationTerm(l,r)::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s1 = (lhs', l::rhs) in
                  let s2 = (r::lhs', rhs) in
                  (sc [s1;s2] (makeBuilder "imp_i_l") fc)
              | t::ts ->
                  (apply ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "imp_i_l"

  (*  Or Left  *)
  let orIL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms lhs rhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.OrTerm(l,r)::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s1 = (l::lhs', rhs) in
                  let s2 = (r::lhs', rhs) in
                  (sc [s1;s2] (makeBuilder "or_i_l") fc)
              | t::ts ->
                  (apply ts (t::lhs) rhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "or_i_l"

  (*  Or Right  *)
  let orIR = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms rhs lhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.OrTerm(l,r)::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s = (lhs, l::r::rhs') in
                  (sc [s] (makeBuilder "or_i_r") fc)
              | t::ts ->
                  (apply ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "or_i_r"
  
  (*  And Left  *)
  let andIL = function
      [] ->
        let pretactic = fun sequent sc fc ->
          let rec apply terms lhs rhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.AndTerm(l,r)::ts ->
                  let lhs' = (List.rev_append ts lhs) in
                  let s = (l::r::lhs', rhs) in
                  (sc [s] (makeBuilder "and_i_l") fc)
              | t::ts ->
                  (apply ts (t::lhs) ts)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply lhs [] rhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "and_i_l"
    
  (*  And Right *)
  let andIR = function
      [] -> 
        let pretactic = fun sequent sc fc ->
          let rec apply terms rhs lhs =
            match terms with
                [] -> fc ()
              | Propositionalabsyn.AndTerm(l,r)::ts ->
                  let rhs' = (List.rev_append ts rhs) in
                  let s1 = (lhs, l::rhs') in
                  let s2 = (lhs, r::rhs') in
                  (sc [s1;s2] (makeBuilder "and_i_r") fc)
              | t::ts ->
                  (apply ts (t::rhs) lhs)
          in
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          (apply rhs [] lhs)
        in
        G.makeTactical pretactic
    | _ -> G.invalidArguments "and_i_r"

  let orTactical = function
      [] -> (G.orElseTactical (orIL []) (orIR []))
    | _ -> G.invalidArguments "or"

  let andTactical = function
      [] -> (G.orElseTactical (andIL []) (andIR []))
    | _ -> G.invalidArguments "and"

  let impTactical = function
      [] -> (G.orElseTactical (impIL []) (impIR []))
    | _ -> G.invalidArguments "imp"

  let notTactical = function
      [] -> (G.orElseTactical (notIL []) (notIR []))
    | _ -> G.invalidArguments "not"

  let autoTactical s =
    let any = (G.orElseTactical
      (G.orElseTactical (andTactical []) (orTactical []))
      (G.orElseTactical (impTactical []) (notTactical [])))
    in
    
    (G.thenTactical
      (G.repeatTactical any)
      (G.orElseTactical
        (trivialTactical [])
        (axiomTactical [])))

  (********************************************************************
  *tacticals:
  * The exported table of tacticals.  These tacticals are the only
  * ones avaible at the toplevel.  GenericTacticals.tacticals is used
  * as the initial table, providing the standard tacticals.
  ********************************************************************)
  let tacticals =
    let ts = G.tacticals in    
    let ts = Logic.Table.add "and" andTactical ts in
    let ts = Logic.Table.add "and_r" andIR ts in
    let ts = Logic.Table.add "and_l" andIL ts in
    
    let ts = Logic.Table.add "or" orTactical ts in
    let ts = Logic.Table.add "or_r" orIR ts in
    let ts = Logic.Table.add "or_l" orIL ts in
    
    let ts = Logic.Table.add "imp" impTactical ts in
    let ts = Logic.Table.add "imp_r" impIR ts in
    let ts = Logic.Table.add "imp_l" impIL ts in
    
    let ts = Logic.Table.add "not" notTactical ts in
    let ts = Logic.Table.add "not_r" notIR ts in
    let ts = Logic.Table.add "not_l" notIL ts in
    
    let ts = Logic.Table.add "trivial" trivialTactical ts in
    let ts = Logic.Table.add "axiom" axiomTactical ts in
    let ts = Logic.Table.add "auto" autoTactical ts in
    ts
end
