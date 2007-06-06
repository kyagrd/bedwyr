(**********************************************************************
*General string -> 'a map.
**********************************************************************)
module Table = Map.Make(String)
type 'a table = 'a Table.t

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
type 'a tactical = 'a Absyn.tactical list -> 'a
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
  val operator : string -> string -> int -> session -> session
  val prove : string -> string -> session -> session
  val definition : string -> session -> session
  
  type sequent
  val validSequent : session -> bool
  val sequents : session -> sequent list
  val string_of_sequents : sequent list -> string
  val updateSequents : sequent list -> session -> session
  
  type proof
  val string_of_proofs : proof list -> string
  
  val tacticals : (sequent, proof) tactic tactical table
end

 
module type LogicSig =
sig
  type logic_sequent
  type logic_proof
end

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module GenericTacticals (L : LogicSig) (O : Output.Output) =
struct
  type logic_pretactic = (L.logic_sequent, L.logic_proof) pretactic
  type logic_tactic = (L.logic_sequent, L.logic_proof) tactic
  type logic_tactical = logic_tactic tactical
  
  (********************************************************************
  *empty:
  ********************************************************************)
  let empty = function
      [] -> true
    | _::_ -> false

  let id x = x
  
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
    fun sequents sc fc -> (sc [] sequents id fc)
  
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
  *wrappedThenTactical:
  * Applies tac1 to the sequents.  Then, for each sequent in the list,
  * applies tac2 to a list containing only that sequent.  Finally,
  * it concatenates the results.
  *
  * The second tactical is wrapped so that recursive tacticals
  * (like repeatTactical) work correctly and don't blow the stack.
  ********************************************************************)
  let wrappedThenTactical tac1 tac2 =
    fun sequents sc fc ->
      (****************************************************************
      *scFirst:
      * Success continuation for first tactical application.  If the 
      * appplication produces no new subgoals, succeeds.  Otherwise
      * calls
      ****************************************************************)
      let rec scFirst newseqs oldseqs builder k =
        let builder' proofs =
          let (pnewseqs, poldseqs) = split_nth (List.length newseqs) proofs in
          ((builder pnewseqs) @ poldseqs)
        in
        match newseqs with
            [] -> (sc newseqs oldseqs builder' k)
          | s::ss -> ((tac2 ()) [s] (scRest ss [] oldseqs) k)
      
      (****************************************************************
      *scRest:
      * Success continuation for subsequent applications.  Accumulates
      * the new sequents and keeps track of the "real" old sequents
      * that were not changed even by the first tactical.
      ****************************************************************)
      and scRest restseqs realnew realold newseqs oldseqs builder k =
        let builder' proofs =
          let (prealnew, prealold) = split_nth (List.length realnew) proofs in
          ((builder prealnew) @ prealold)
        in
        match restseqs with
            [] -> (sc (newseqs @ oldseqs @ realnew) realold builder' k)
          | s::ss -> ((tac2 ()) [s] (scRest ss (newseqs @ oldseqs @ realnew) realold) k)
      in
      (tac1 sequents scFirst fc)

  (********************************************************************
  *thenTactical:
  * Exported nterface to wrapped version.
  ********************************************************************)
  let thenTactical tac1 tac2 =
    wrappedThenTactical tac1 (fun () -> tac2)
  
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
      *builder':
      ****************************************************************)
      let builder' builder newseqs proofs =
        let (pnewseqs, poldseqs) = split_nth (List.length newseqs) proofs in
        ((builder pnewseqs) @ poldseqs)
      in
      (****************************************************************
      *scFirst:
      * Success continuation for first application.  Used to keep track
      * of the 'real' old sequents.
      ****************************************************************)
      let rec scFirst newseqs oldseqs builder k =
        let builder'' = (builder' builder newseqs) in
        if (empty newseqs) then
          (sc newseqs oldseqs builder'' k)
        else
          (tac newseqs (scRest [] oldseqs) (failure newseqs oldseqs builder'' k))

      (****************************************************************
      *scRest:
      * Success continuation for subsequent applications.
      ****************************************************************)
      and scRest realnew realold newseqs oldseqs builder k =
        let builder'' = (builder' builder newseqs) in
        let realnew' = (oldseqs @ realnew) in
        let failure' = (failure (newseqs @ realnew') realold builder'' k) in
        if (empty newseqs) then
          (sc realnew' realold builder'' k)
        else
          (tac newseqs (scRest realnew' realold) failure')
      
      (****************************************************************
      *failure:
      * If an application fails simply succeed with the new and old
      * sequents obtained thus far.
      ****************************************************************)
      and failure newseqs oldseqs builder k () =
        (sc newseqs oldseqs builder k)
      in
      (tac sequents scFirst fc)
  
  (********************************************************************
  *repeatTactical:
  * Applies the given tactical to the list of sequents. Then, for each
  * sequent in the list, applies tac2 to a list containing only that
  * sequent.  Does this recursively until then fails.
  ********************************************************************)
  let rec repeatTactical tac =
    let wrapper () = (repeatTactical tac) in
    (orElseTactical (wrappedThenTactical tac wrapper) idTactical)

  (********************************************************************
  *completeTactical:
  * Applies the given tactical and succeeds only if the goal generated
  * no new tacticals.
  ********************************************************************)
  let completeTactical tac =
    fun sequents sc fc ->
      let sc' newseqs oldseqs builder k =
        if (empty newseqs) then
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
  let applyInterface = function
      Absyn.Tactical(tac)::[] -> tac
    | _ -> invalidArguments "apply"

  let orElseInterface = function
      Absyn.Tactical(tac1)::Absyn.Tactical(tac2)::[] ->
        (orElseTactical tac1 tac2)
    | _ -> invalidArguments "orelse"

  let thenInterface = function
      Absyn.Tactical(tac1)::Absyn.Tactical(tac2)::[] ->
        (thenTactical tac1 tac2)
    | _ -> invalidArguments "then"

  let tryInterface = function
      Absyn.Tactical(tac)::[] ->
        (tryTactical tac)
    | _ -> invalidArguments "try"

  let failureInterface = function
      [] -> (failureTactical)
    | _ -> invalidArguments "fail"

  let idInterface = function
      [] -> (idTactical)
    | _ -> invalidArguments "id"
  
  let repeatInterface = function
      Absyn.Tactical(tac)::[] ->
        (repeatTactical tac)
    | _ -> invalidArguments "repeat"

  let iterateInterface = function
      Absyn.Tactical(tac)::[] ->
        (iterateTactical tac)
    | _ -> invalidArguments "iterate"

  let rotateInterface = function
      [] -> (rotateTactical)
    | _ -> invalidArguments "rotate"

  let completeInterface = function
      Absyn.Tactical(tac)::[] ->
        (completeTactical tac)
    | _ -> invalidArguments "complete"

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
    ts
end
