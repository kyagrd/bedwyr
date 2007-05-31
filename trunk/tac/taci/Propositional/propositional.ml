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
  
  type tactic = sequent -> (sequent list -> unit) -> unit
  type tactical = string -> tactic

  type tactic' = tactic
  type sequent' = sequent
  module GenericTacticals = Logic.GenericTacticals (struct type sequent = sequent' and tactic = tactic' end)

  (********************************************************************
  *Tactics:
  ********************************************************************)
  (*  Axiom *)
  let axiomTactic args sequent sc =
    let find list el =
      (List.exists ((=) el) list)
    in
     
    let lhs = getSequentLHS sequent in
    let rhs = getSequentRHS sequent in
    if (List.exists (find lhs) rhs) then
      sc []
    else
      ()
  
  (*  Trivial *)
  let trivialTactic args sequent sc =
    let lhs = getSequentLHS sequent in
    let rhs = getSequentRHS sequent in
    if (List.exists ((=) Propositionalabsyn.FalseTerm) lhs) ||
      (List.exists ((=) Propositionalabsyn.TrueTerm) rhs) then
      sc []
    else
      ()

  let notIR args sequent sc =
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

  (*  Not Left  *)
  let notIL args sequent sc =
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

  (*  Implication Right *)
  let impIR args sequent sc =
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
  
  (*  Implication Left  *)
  let impIL args sequent sc =
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
  
  (*  Or Left  *)
  let orIL args sequent sc =
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
  
  (*  Or Right  *)
  let orIR args sequent sc =
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
  
  (*  And Left  *)
  let andIL args sequent sc =
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
  
  (*  And Right *)
  let andIR args sequent sc =
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

  let rec findTactic (n,s)=
    try
      Some ((Logic.Table.find n tactics) s)
    with
      Not_found -> (O.error ("Undefined tactic: " ^ n ^ ".\n"); None)
  
  and tactics =
    let ts = Logic.Table.add "axiom" axiomTactic Logic.Table.empty in
    let ts = Logic.Table.add "id" (fun s -> GenericTacticals.idTactical) ts in
    let ts = Logic.Table.add "trivial" trivialTactic ts in
    let ts = Logic.Table.add "imp_i_l" impIL ts in
    let ts = Logic.Table.add "imp_i_r" impIR ts in
    let ts = Logic.Table.add "and_i_l" andIL ts in
    let ts = Logic.Table.add "and_i_r" andIR ts in
    let ts = Logic.Table.add "or_i_l" orIL ts in
    let ts = Logic.Table.add "or_i_r" orIR ts in
    let ts = Logic.Table.add "not_i_l" notIL ts in
    let ts = Logic.Table.add "not_i_r" notIR ts in
    ts
  
  let parseTactics s =
    try
      let tactics = Propositionalparser.tactics Propositionallexer.tactics (Lexing.from_string s) in
      (List.map findTactic tactics)
    with
      Propositionalabsyn.SyntaxError(s) ->
        (O.error (s ^ ".\n");
        [])


  (********************************************************************
  *Tacticals:
  ********************************************************************)
  let applyTactical s =
    let tactics = parseTactics s in
    if (List.length tactics) == 0 then
      (O.error "No tactic specified.\n";
      GenericTacticals.failureTactical)
    else if (List.length tactics) > 1 then
      (O.error "Too many tactics specified.\n";
      GenericTacticals.failureTactical)
    else
      let tactic = List.hd tactics in
      if Option.isNone tactic then
        (GenericTacticals.failureTactical)
      else
        (GenericTacticals.applyTactical (Option.get tactic))
  
  let orElseTactical s =
    let tactics = parseTactics s in
    if (List.length tactics) == 0 then
      (O.error "No tactic specified.\n";
      GenericTacticals.failureTactical)
    else if (List.length tactics) > 2 then
      (O.error "Too many tactics specified.\n";
      GenericTacticals.failureTactical)
    else
      let tactic1 = List.hd tactics in
      let tactic2 = List.hd (List.tl tactics) in
      if Option.isNone tactic1 || Option.isNone tactic2 then
        (GenericTacticals.failureTactical)
      else
        (GenericTacticals.orTactical (Option.get tactic1) (Option.get tactic2))

  let thenTactical s =
    let tactics = parseTactics s in
    if (List.length tactics) == 0 then
      (O.error "No tactic specified.\n";
      GenericTacticals.failureTactical)
    else if (List.length tactics) > 2 then
      (O.error "Too many tactics specified.\n";
      GenericTacticals.failureTactical)
    else
      let tactic1 = List.hd tactics in
      let tactic2 = List.hd (List.tl tactics) in
      if Option.isNone tactic1 || Option.isNone tactic2 then
        (GenericTacticals.failureTactical)
      else
        (GenericTacticals.thenTactical (Option.get tactic1) (Option.get tactic2))

  let tryTactical s =
    let tactics = parseTactics s in
    if (List.length tactics) == 0 then
      (O.error "No tactic specified.\n";
      GenericTacticals.failureTactical)
    else if (List.length tactics) > 1 then
      (O.error "Too many tactics specified.\n";
      GenericTacticals.failureTactical)
    else
      let tactic = List.hd tactics in
      if Option.isNone tactic then
        (GenericTacticals.failureTactical)
      else
        (GenericTacticals.orTactical (Option.get tactic) (GenericTacticals.idTactical))

  let idTactical s =
    GenericTacticals.idTactical
  
  let repeatTactical s =
    let tactics = parseTactics s in
    if (List.length tactics) == 0 then
      (O.error "No tactic specified.\n";
      GenericTacticals.failureTactical)
    else if (List.length tactics) > 1 then
      (O.error "Too many tactics specified.\n";
      GenericTacticals.failureTactical)
    else
      let tactic = List.hd tactics in
      if Option.isNone tactic then
        (GenericTacticals.failureTactical)
      else
        (GenericTacticals.repeatTactical (Option.get tactic))

  let axiomTactical s =
    (GenericTacticals.applyTactical (axiomTactic ""))
  
  let trivialTactical s =
    (GenericTacticals.applyTactical (trivialTactic ""))

  let orTactical s =
    let either = (GenericTacticals.orTactical (orIL "") (orIR "")) in
    (either)

  let andTactical s =
    let either = (GenericTacticals.orTactical (andIL "") (andIR "")) in
    (either)

  let impTactical s =
    let either = (GenericTacticals.orTactical (impIL "") (impIR "")) in
    (either)

  let notTactical s =
    let either = (GenericTacticals.orTactical (notIL "") (notIR "")) in
    (either)

  let autoTactical s =
    let any = (GenericTacticals.orTactical
      (GenericTacticals.orTactical (andTactical "") (orTactical ""))
      (GenericTacticals.orTactical (impTactical "") (notTactical "")))
    in
    let tac =
      (GenericTacticals.thenTactical
        (GenericTacticals.repeatTactical any)
        (GenericTacticals.repeatTactical
          (GenericTacticals.orTactical
            (trivialTactical "")
            (axiomTactical "")))) in
    fun sequent sc ->
      let sc' sequents =
        if (List.length sequents) == 0 then
          (sc sequents)
        else
          ()
      in
       tac sequent sc'

  let tacticals =    
    let ts = Logic.Table.add "apply" applyTactical Logic.Table.empty in
    let ts = Logic.Table.add "id" idTactical ts in
    let ts = Logic.Table.add "then" thenTactical ts in
    let ts = Logic.Table.add "orelse" orElseTactical ts in
    let ts = Logic.Table.add "try" tryTactical ts in
    let ts = Logic.Table.add "repeat" repeatTactical ts in
    
    let ts = Logic.Table.add "trivial" trivialTactical ts in
    let ts = Logic.Table.add "axiom" axiomTactical ts in
    let ts = Logic.Table.add "auto" autoTactical ts in
    ts
end
