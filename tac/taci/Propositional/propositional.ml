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
  
  (********************************************************************
  *Session:
  * A session is just the current list of sequents.  A session is
  * "complete" when it has no sequents.
  ********************************************************************)
  type session = Session of (sequent list * proof Logic.proofbuilder *
    (session, (sequent, proof) Logic.tactic) Logic.tactical Logic.table)

  let theoremName session = ""
  let getSessionTacticals (Session(_,_,t)) = t
  let getSessionSequents (Session(sequents,_,_)) = sequents
  let getSessionBuilder (Session(_,b,_)) = b
  let setSessionSequents sequents (Session(_,b,t)) = (Session(sequents,b,t))
  let setSessionBuilder builder (Session(s,_,t)) = (Session(s,builder,t))
  
  let string_of_proofs session =
    "\t" ^ (String.concat "\n\t" (getSessionBuilder session [])) ^ "\n"

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
    let sequents = getSessionSequents session in
    let mainseq = List.hd sequents in
    let seqs = List.tl sequents in
    if (List.length seqs) > 0 then
      (string_of_sequent mainseq) ^ "\n\n" ^ (String.concat "\n\n" (List.map string_of_sequent_rhs seqs)) ^ "\n"
    else
      (string_of_sequent mainseq) ^ "\n"

  let proof (Session(_,p,_)) = p

  let incl files session =
    session

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
  
  (*  All of these are not implemented. *)
  let proved session = session
  let lemmas session = session
  let definitions ds session = session
  
  let update sequents builder session =
    (setSessionSequents sequents (setSessionBuilder builder session))

  let validSequent session =
    match (getSessionSequents session) with
        [] -> false
      | _::_ -> true
  let sequents session = (getSessionSequents session)
  let undo session = session
  let redo session = session

  (********************************************************************
  *Tacticals:
  ********************************************************************)
  module PropositionalSig =
  struct
    type logic_session = session
    type logic_sequent = sequent
    type logic_proof = proof
  end
  module G = Logic.GenericTacticals (PropositionalSig) (O)

  let makeBuilder s = fun proofs ->
    s ^ "(" ^ (String.concat ", " proofs) ^ ")"

  (*  Axiom *)
  let axiomTactical session args = match args with
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
  let trivialTactical session args = match args with
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
  let notIR session args = match args with
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
  let notIL session args = match args with
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
  let impIR session args = match args with
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
  let impIL session args = match args with
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
  let orIL session args = match args with
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
  let orIR session args = match args with
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
  let andIL session args = match args with
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
  let andIR session args = match args with
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

  let orTactical session args = match args with
      [] -> (G.orElseTactical (orIL session []) (orIR session []))
    | _ -> G.invalidArguments "or"

  let andTactical session args = match args with
      [] -> (G.orElseTactical (andIL session []) (andIR session []))
    | _ -> G.invalidArguments "and"

  let impTactical session args = match args with
      [] -> (G.orElseTactical (impIL session []) (impIR session []))
    | _ -> G.invalidArguments "imp"

  let notTactical session args = match args with
      [] -> (G.orElseTactical (notIL session []) (notIR session []))
    | _ -> G.invalidArguments "not"

  let autoTactical session args = match args with
      [] ->
        let any = (G.orElseTactical
          (G.orElseTactical (andTactical session []) (orTactical session []))
          (G.orElseTactical (impTactical session []) (notTactical session [])))
        in
        
        (G.thenTactical
          (G.repeatTactical any)
          (G.orElseTactical
            (trivialTactical session [])
            (axiomTactical session [])))
    | _ -> G.invalidArguments "auto"

  (********************************************************************
  *tacticals:
  * The exported table of tacticals.  These tacticals are the only
  * ones avaible at the toplevel.  GenericTacticals.tacticals is used
  * as the initial table, providing the standard tacticals.
  ********************************************************************)
  let tacticals session =
    (getSessionTacticals session)

  let pervasiveTacticals =
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
    
    let emptySession = Session([], (fun l -> l), pervasiveTacticals)
    let reset () = emptySession
    let defineTactical name tac (Session(s,pb,t)) =
      Session(s,pb,Logic.Table.add name tac t)
end
