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

module Table = Map.Make(String)
type 'a table = 'a Table.t
let contains el table =
  try
    (Table.find el table;
    true)
  with
    Not_found -> false

let find el table =
  try
    Some (Table.find el table)
  with
    Not_found -> None

(*  Continuations *)
type continue = unit -> unit
type failure = unit -> unit

(*  Pre Tactics *)
type ('a, 'b) pretactic =
  'a -> ('a list -> ('b list -> 'b) -> continue -> unit) -> failure -> unit

(*  Tactics *)
type 'a proofbuilder = 'a list -> 'a list
type ('a, 'b) success = 'a list -> 'a list -> 'b proofbuilder -> continue -> unit
type ('a, 'b) tactic = 'a list -> ('a, 'b) success -> failure -> unit

(*  Tacticals *)
type ('a, 'b) tactical = 'a -> 'b Absyn.tactical list -> 'b

(*  Proofs  *)
let composeProofBuilders b1 b2 =
  fun l -> b2 (b1 l)

let idProofBuilder =
  fun l -> l

(**********************************************************************
*Logic:
**********************************************************************)
module type Logic =
sig
  val name : string
  val info : string
  val start : string
  
  type session
  val incl : string list -> session -> session
  val reset : unit -> session
  val prove : string -> string -> session -> session
  val definitions : string list -> session -> session
  val undo : session -> session
  val redo : session -> session
  
  type sequent
  val validSequent : session -> bool
  val sequents : session -> sequent list
  val string_of_sequents : session -> string
    
  type proof
  val proof : session -> proof proofbuilder
  val string_of_proofs : session -> string
  
  val update : sequent list -> proof proofbuilder -> session -> session

  val tacticals : session -> (session, (sequent, proof) tactic) tactical table
  val defineTactical : string -> (session, (sequent, proof) tactic) tactical -> session -> session
end

 
module type LogicSig =
sig
  type logic_session
  type logic_sequent
  type logic_proof
end

(**********************************************************************
*Ctrl-C Handler:
**********************************************************************)
let interrupt = ref false
exception Interrupt
let _ = Sys.set_signal Sys.sigint
  (Sys.Signal_handle (fun _ -> interrupt := true))

let checkInterrupt () =
  if !interrupt then
    (interrupt := false;
    true)
  else
    false
  
(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module GenericTacticals (L : LogicSig) (O : Output.Output) =
struct
  type logic_pretactic = (L.logic_sequent, L.logic_proof) pretactic
  type logic_tactic = (L.logic_sequent, L.logic_proof) tactic
  type logic_tactical = (L.logic_session, logic_tactic) tactical
    
  (********************************************************************
  *split_nth:
  * Returns a pair (l, r) where l is the first n elements of the given
  * list and r is the rest.
  ********************************************************************)
  let split_nth i l =
    let rec split' i l r =
      match (i, r) with
          (0, _) -> (List.rev l, r)
        | (i',h::t) -> split' (i' - 1) (h :: l) (t)
        | _ -> raise (Failure "split_nth")
    in
    split' i [] l

  (********************************************************************
  *makeTactical:
  * Given a tactic, make a tactical that selects the first sequent
  * in the list, applies the given tactic, and propagates the new
  * sequents accordingly.
  ********************************************************************)
  let makeTactical t sequents sc fc =
    match sequents with
      (seq::sequents') ->
        let sc' newseqs builder k =
          let builder' pnll =
            let (pnl, pl) = split_nth (List.length newseqs) pnll in
            (builder pnl)::pl
          in
          (sc newseqs sequents' builder' k)
        in
        (t seq sc' fc)
    | [] -> (fc ())
    
  (********************************************************************
  *failureTactical:
  * Simply returns, causing a failure.
  ********************************************************************)
  let failureTactical =
    fun _ _ fc -> (fc ())

  (********************************************************************
  *invalidArguments:
  * Used when a tactical is being constructed and receives the wrong
  * arguments.  Returns a failureTactical so that the resulting tactical
  * is still valid, it will just always fail.
  ********************************************************************)
  let invalidArguments s =
    (O.error (s ^ ": invalid arguments.\n");
    failureTactical)

  (********************************************************************
  *idTactical:
  * Returns a tactical that always succeeds the current sequent unchanged.
  ********************************************************************)
  let idTactical =
    fun sequents sc fc -> (sc sequents [] (fun x -> x) fc)
  
  (********************************************************************
  *applyTactical:
  * Simpy returns the given tactical.  Has no real use; used during
  * testing.
  ********************************************************************)
  let applyTactical tac =
    tac

  (********************************************************************
  *orElseTactic:
  * Returns a tactical that tries the first tactical, and if it fails,
  * tries the second.
  ********************************************************************)
  let orElseTactical tac1 tac2 =
    fun sequents sc fc ->
      let fc' () =
        (tac2 sequents sc fc)
      in
      (tac1 sequents sc fc')

  (********************************************************************
  *first:
  * Applies the given tactical to only the first sequent.
  ********************************************************************)
  let firstTactical tac =
    fun sequents sc fc ->
      match sequents with
          [] -> failureTactical sequents sc fc
        | [a] -> tac sequents sc fc
        | a::aa ->
            let sc' newseqs oldseqs pb k =
              let pb' proofs =
                let l = (List.length newseqs + List.length oldseqs) in
                let (pnew,pold) = split_nth l proofs in
                (pb pnew) @ pold
              in
              sc newseqs (oldseqs @ aa) pb' k
            in
            (tac [a] sc' fc)

  (********************************************************************
  *orElseListTactical:
  * Builds a nested disjunction from the list.
  ********************************************************************)
  let rec orElseListTactical tacs =
    match tacs with
      [] -> failureTactical
    | tac::[] -> tac
    | tac::tacs -> orElseTactical tac (orElseListTactical tacs)

  (********************************************************************
  *tryTactical:
  * Returns a tactical that tries a tactical, and if the tactical fails,
  * simply returns the given sequents unchanged.
  ********************************************************************)
  let tryTactical tac =
    orElseTactical tac idTactical
  
  (********************************************************************
  *mapTactical;
  * Maps a given tactical over a list of sequents, accumulating the
  * result.
  ********************************************************************)
  let rec mapTactical tac sequents result sc = ()  

  (********************************************************************
  *iterateTactical:
  * Applies the given tactical.  Then applies the given tactical to the
  * newly created sequents.  Continues to do so until no new sequents
  * are being generated.
  *
  * The returned new sequents should be the collection of all sequents
  * created.  The returned old sequents are those that were returned by
  * the first application of the tactical.
  ********************************************************************)
  let rec iterateTactical tac =
    fun sequents sc fc ->
      (****************************************************************
      *makeBuilder:
      ****************************************************************)
      let makeBuilder oldbuilder builder nseqs =
        match oldbuilder with
          None -> builder
        | Some old ->
            fun proofs ->
              let l = (List.length proofs) - nseqs in
              let (potherseqs, pseqs) = split_nth l proofs in
              (old potherseqs) @ (builder pseqs)
      in

      (****************************************************************
      *sc':
      * Success continuation for applications.
      ****************************************************************)
      let rec sc' oldbuilder realnew rest newseqs oldseqs builder k =
        let newseqs' = newseqs @ oldseqs in
        let builder' =
          Some (makeBuilder oldbuilder builder (List.length newseqs'))
        in
        let realnew' = realnew @ newseqs' in

        match rest with
            [] -> (sc realnew' [] (Option.get builder') k)
          | s::ss -> (tac [s] (sc' builder' realnew' ss) k)
      in
      
      if checkInterrupt () then
        raise Interrupt
      else
        match sequents with
          [] -> sc [] [] idProofBuilder fc
        | s::ss -> (tac [s] (sc' None [] ss) fc)
  
  (********************************************************************
  *wrappedThenTactical:
  * Applies tac1 to the sequents.  Then, for each sequent in the list,
  * applies tac2 to a list containing only that sequent.  Finally,
  * it concatenates the results.
  *
  * The second tactical is wrapped so that recursive tacticals
  * (like repeatTactical) work correctly and don't blow the stack.
  ********************************************************************)
  let wrappedThenTactical cut tac1 tac2 =
    fun sequents sc fc ->
      (****************************************************************
      *scFirst:
      * Success continuation for first tactical application.
      ****************************************************************)
      let rec scFirst newseqs oldseqs builder k =
        let fc' = if cut then fc else k in
        ((iterateTactical (tac2 ())) newseqs (scRest builder oldseqs) fc')

      (****************************************************************
      *scRest:
      * Success continuation for subsequent applications.  Accumulates
      * the new sequents and keeps track of the "real" old sequents
      * that were not changed even by the first tactical.
      ****************************************************************)
      and scRest oldbuilder realoldseqs newseqs oldseqs builder k =
        let n = List.length realoldseqs in
        let builder' proofs =
          let l = (List.length proofs) - n in
          let (pseqs, potherseqs) = split_nth l proofs in
          oldbuilder ((builder pseqs) @ potherseqs)
        in
        (sc (newseqs @ oldseqs) realoldseqs builder' k)
      in
      (tac1 sequents scFirst fc)

  (********************************************************************
  *thenTactical:
  * Exported nterface to wrapped version.
  ********************************************************************)
  let thenTactical tac1 tac2 =
    wrappedThenTactical false tac1 (fun () -> tac2)

  (********************************************************************
  *cutThenTactical:
  * Exported nterface to wrapped version.
  ********************************************************************)
  let cutThenTactical f tac1 tac2 =
    fun sequents sc fc ->
      let f' = f () in
      let fc' () =
        (f' (); fc ())
      in
      (wrappedThenTactical true tac1 (fun () -> tac2)) sequents sc fc'

  (********************************************************************
  *repeatTactical:
  * Applies the given tactical to the list of sequents. Then, for each
  * sequent in the list, applies tac2 to a list containing only that
  * sequent.  Does this recursively until then fails.
  ********************************************************************)
  let rec repeatTactical tac =
    let wrapper () = (repeatTactical tac) in
    (orElseTactical (wrappedThenTactical false tac wrapper) idTactical)

  (********************************************************************
  *completeTactical:
  * Applies the given tactical and succeeds only if the goal generated
  * no new tacticals.
  ********************************************************************)
  let completeTactical tac =
    fun sequents sc fc ->
      let sc' newseqs oldseqs builder k =
        if (Listutils.empty newseqs) then
          (sc newseqs oldseqs builder k)
        else
          (k ())
      in
      (tac sequents sc' fc)

  (********************************************************************
  *rotateTactical:
  * Puts the head of the list of sequents on the tail.
  ********************************************************************)
  let rotateTactical =
    fun sequents sc fc ->
      let builder proofs =
        match proofs with
            [] -> []
          | h::t -> t @ [h]
      in
      match sequents with
          [] -> fc ()
        | h::t -> (sc [] (t @ [h]) builder fc)

  (********************************************************************
  * Interfaces for Tacticals
  ********************************************************************)
  let applyInterface session args = match args with
      Absyn.Tactical(tac)::[] -> tac
    | _ -> invalidArguments "apply"

  let orElseInterface session args = match args with
      Absyn.Tactical(tac1)::Absyn.Tactical(tac2)::[] ->
        (orElseTactical tac1 tac2)
    | _ -> invalidArguments "orelse"

  let thenInterface session args = match args with
      Absyn.Tactical(tac1)::Absyn.Tactical(tac2)::[] ->
        (thenTactical tac1 tac2)
    | _ -> invalidArguments "then"

  let tryInterface session args = match args with
      Absyn.Tactical(tac)::[] ->
        (tryTactical tac)
    | _ -> invalidArguments "try"

  let failureInterface session args = match args with
      [] -> (failureTactical)
    | _ -> invalidArguments "fail"

  let idInterface session args = match args with
      [] -> (idTactical)
    | _ -> invalidArguments "id"
  
  let repeatInterface session args = match args with
      Absyn.Tactical(tac)::[] ->
        (repeatTactical tac)
    | _ -> invalidArguments "repeat"

  let iterateInterface session args = match args with
      Absyn.Tactical(tac)::[] ->
        (iterateTactical tac)
    | _ -> invalidArguments "iterate"

  let rotateInterface session args = match args with
      [] -> (rotateTactical)
    | _ -> invalidArguments "rotate"

  let completeInterface session args = match args with
      Absyn.Tactical(tac)::[] ->
        (completeTactical tac)
    | _ -> invalidArguments "complete"

  let firstInterface session args = match args with
      Absyn.Tactical(tac)::[] ->
        (firstTactical tac)
    | _ -> invalidArguments "first"

  let tacticals =
    let ts = Table.add "apply" applyInterface Table.empty in
    let ts = Table.add "id" idInterface ts in
    let ts = Table.add "fail" failureInterface ts in
    
    let ts = Table.add "orelse" orElseInterface ts in
    let ts = Table.add "try" tryInterface ts in
    
    let ts = Table.add "complete" completeInterface ts in
    
    let ts = Table.add "then" thenInterface ts in
    let ts = Table.add "repeat" repeatInterface ts in
    let ts = Table.add "iterate" iterateInterface ts in
    
    let ts = Table.add "rotate" rotateInterface ts in
    let ts = Table.add "first" firstInterface ts in
    ts
end
