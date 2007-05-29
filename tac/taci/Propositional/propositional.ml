(**********************************************************************
*Propositional:
* A dummy logic module.
**********************************************************************)
module Propositional =
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
  
  type session = (sequent list)
  let emptySession = ([])
  let getSessionSequents (sequents) = sequents
  let setSessionSequents sequents session = (sequents)
  
  let incl files session =
    session

  let tactics = Logic.Table.empty
  let tacticals = Logic.Table.empty

  let reset () = emptySession
  
  (********************************************************************
  *prove:
  * Parses the argument into a term, and then prepares the session to
  * prove the term.
  ********************************************************************)
  let prove name t session =
    let term = Propositionalparser.term Propositionallexer.term (Lexing.from_string t) in
    (setSessionSequents [([], [term])] session)
  
  let definition d session = session
  let operator name fix prec session = session
  let sequents session = (getSessionSequents session)
  let updateSequents sequents session = (setSessionSequents sequents session)
  
  type tactic = string -> sequent -> (sequent list -> unit) -> unit
  type tactical = string -> sequent -> (sequent list -> unit) -> unit
  
  module G = Logic.GenericTacticals (Propositional)
  let tacticals = G.genericTacticals
  
  let tactics =
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
    in
    
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
              (apply lhs (t::rhs) ts)
      in
      let lhs = getSequentLHS sequent in
      let rhs = getSequentRHS sequent in
      (apply rhs [] lhs)
    in
    
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
    in
    
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
    in
    
    let ts = Logic.Table.add "and_i_l" andIL Logic.Table.empty in
    let ts = Logic.Table.add "and_i_r" andIR ts in
    let ts = Logic.Table.add "or_i_l" orIL ts in
    let ts = Logic.Table.add "or_i_r" orIR ts in
    ts
  
end
