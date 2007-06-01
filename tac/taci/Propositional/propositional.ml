(**********************************************************************
*Propositional:
* A dummy logic module.
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
  
  type sequent = (Propositionalabsyn.term list * Propositionalabsyn.term list)
  let emptySequent = ([], [])
  let getSequentLHS (l,_) = l
  let getSequentRHS (_,r) = r

  type session = (bool * sequent list)
  let emptySession = (false, [])
  let getSessionSequents (_, sequents) = sequents
  let setSessionSequents sequents (b,_) = (b,sequents)

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
    
  let string_of_sequents session =
    let mainseq = List.hd (getSessionSequents session) in
    let seqs = List.tl (getSessionSequents session) in
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


  (********************************************************************
  *prove:
  * Parses the argument into a term, and then prepares the session to
  * prove the term.
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
    let sequents = (getSessionSequents session) in
    (List.length sequents > 0)
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
  module G = Logic.GenericTacticals (struct type logic_sequent = sequent end) (O)

  (*  Axiom *)
  let axiomTactical = function
      [] -> fun sequent sc ->
        let find list el =
          (List.exists ((=) el) list)
        in
         
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        if (List.exists (find lhs) rhs) then
          sc []
        else
          ()
    | _ -> (G.invalidArguments "axiom")
  
  (*  Trivial *)
  let trivialTactical = function
      [] -> fun sequent sc ->
          let lhs = getSequentLHS sequent in
          let rhs = getSequentRHS sequent in
          if (List.exists ((=) Propositionalabsyn.FalseTerm) lhs) ||
            (List.exists ((=) Propositionalabsyn.TrueTerm) rhs) then
            sc []
          else
            ()
    | _ -> G.invalidArguments "trivial"

  (*  Not Right *)
  let notIR = function
      [] -> fun sequent sc ->
        let rec apply terms rhs lhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.NotTerm(t)::ts ->
                let rhs' = (List.rev_append ts rhs) in
                let s = (t::lhs, rhs') in
                (sc [s])
            | t::ts ->
                (apply ts (t::rhs) lhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply rhs [] lhs)
    | _ -> G.invalidArguments "not_i_r"

  (*  Not Left  *)
  let notIL = function
      [] -> fun sequent sc ->
        let rec apply terms lhs rhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.NotTerm(t)::ts ->
                let lhs' = (List.rev_append ts lhs) in
                let seq = (lhs', t::rhs) in
                (sc [seq])
            | t::ts ->
                (apply ts (t::lhs) rhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply lhs [] rhs)
    | _ -> G.invalidArguments "not_i_l"
  (*  Implication Right *)
  let impIR = function
      [] -> fun sequent sc ->
        let rec apply terms rhs lhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.ImplicationTerm(l,r)::ts ->
                let rhs' = (List.rev_append ts rhs) in
                let s = (l::lhs, r::rhs') in
                (sc [s])
            | t::ts ->
                (apply ts (t::rhs) lhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply rhs [] lhs)
    | _ -> G.invalidArguments "imp_i_r"

  (*  Implication Left  *)
  let impIL = function
      [] -> fun sequent sc ->
        let rec apply terms lhs rhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.ImplicationTerm(l,r)::ts ->
                let lhs' = (List.rev_append ts lhs) in
                let s1 = (lhs', l::rhs) in
                let s2 = (r::lhs', rhs) in
                (sc [s1;s2])
            | t::ts ->
                (apply ts (t::lhs) rhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply lhs [] rhs)
    | _ -> G.invalidArguments "imp_i_l"

  (*  Or Left  *)
  let orIL = function
      [] -> fun sequent sc ->
        let rec apply terms lhs rhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.OrTerm(l,r)::ts ->
                let lhs' = (List.rev_append ts lhs) in
                let s1 = (l::lhs', rhs) in
                let s2 = (r::lhs', rhs) in
                (sc [s1;s2])
            | t::ts ->
                (apply ts (t::lhs) rhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply lhs [] rhs)
    | _ -> G.invalidArguments "or_i_l"

  (*  Or Right  *)
  let orIR = function
      [] -> fun sequent sc ->
        let rec apply terms rhs lhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.OrTerm(l,r)::ts ->
                let rhs' = (List.rev_append ts rhs) in
                let s = (lhs, l::r::rhs') in
                (sc [s])
            | t::ts ->
                (apply ts (t::rhs) lhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply rhs [] lhs)
    | _ -> G.invalidArguments "or_i_r"
  
  (*  And Left  *)
  let andIL = function
      [] -> fun sequent sc ->
        let rec apply terms lhs rhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.AndTerm(l,r)::ts ->
                let lhs' = (List.rev_append ts lhs) in
                let s = (l::r::lhs', rhs) in
                (sc [s])
            | t::ts ->
                (apply ts (t::lhs) ts)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply lhs [] rhs)
    | _ -> G.invalidArguments "and_i_l"
    
  (*  And Right *)
  let andIR = function
      [] -> fun sequent sc ->
        let rec apply terms rhs lhs =
          match terms with
              [] -> ()
            | Propositionalabsyn.AndTerm(l,r)::ts ->
                let rhs' = (List.rev_append ts rhs) in
                let s1 = (lhs, l::rhs') in
                let s2 = (lhs, r::rhs') in
                (sc [s1;s2])
            | t::ts ->
                (apply ts (t::rhs) lhs)
        in
        let lhs = getSequentLHS sequent in
        let rhs = getSequentRHS sequent in
        (apply rhs [] lhs)
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
      (G.repeatTactical
        (G.orElseTactical
          (trivialTactical [])
          (axiomTactical []))))
  
  let tacticals =
    let ts = G.tacticals in    
    let ts = Logic.Table.add "and" andTactical ts in
    let ts = Logic.Table.add "or" orTactical ts in
    let ts = Logic.Table.add "imp" impTactical ts in
    let ts = Logic.Table.add "not" notTactical ts in
    
    let ts = Logic.Table.add "trivial" trivialTactical ts in
    let ts = Logic.Table.add "axiom" axiomTactical ts in
    let ts = Logic.Table.add "auto" autoTactical ts in
    ts
end
