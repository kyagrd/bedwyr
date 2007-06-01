(**********************************************************************
*General string -> 'a map.
**********************************************************************)
module Table = Map.Make(String)
type 'a table = 'a Table.t

(**********************************************************************
*Logic:
**********************************************************************)
type 'a tactic = 'a -> ('a list -> unit) -> unit
type 'a tactical = 'a Absyn.tactical list -> 'a
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
  val sequent : session -> (sequent * session) option
  val sequents : session -> sequent list
  val string_of_sequents : session -> string
  val updateSequents : sequent list -> session -> session
  
  val tacticals : (sequent tactic) tactical table
end 
 
module type LogicSig =
sig
  type logic_sequent
end

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module GenericTacticals (L : LogicSig) (O : Output.Output) =
struct
  type logic_tactic = (L.logic_sequent tactic)
  type logic_tactical = logic_tactic tactical
  
  let failureTactical =
    fun _ _ -> ()

  let invalidArguments s =
    (O.error (s ^ ": invalid arguments.\n"); failureTactical)

  let idTactical =
    fun sequent sc -> (sc [sequent])

  let applyTactical tactic =
    tactic

  let orElseTactical tac1 tac2 =
    fun sequent sc ->
      (tac1 sequent sc; tac2 sequent sc)

  let tryTactical tac =
    orElseTactical tac idTactical
  
  let rec mapTactical tac sequents result sc =
    match sequents with
        [] -> (sc result)
      | seq::ss ->
          let sc' sequents =
            (mapTactical tac ss (sequents @ result) sc)
          in
          (tac seq sc')
      
  let thenTactical tac1 tac2 =
    fun sequent sc ->
      let sc' sequents =
        (mapTactical tac2 sequents [] sc)
      in
      (tac1 sequent sc')

  let rec repeatTactical tac =
    fun sequent sc ->
      (orElseTactical (thenTactical tac (repeatTactical tac)) idTactical) sequent sc

  let completeTactical tac =
    fun sequent sc ->
        let sc' sequents =
          if (List.length sequents) == 0 then
            (sc sequents)
          else
            ()
        in
        (tac sequent sc')

  let applyInterface = function
      Absyn.Tactical(tac)::[] ->
        tac
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

  let idInterface = function
      [] ->
        (idTactical)
    | _ -> invalidArguments "id"
  
  let repeatInterface = function
      Absyn.Tactical(tac)::[] ->
        (repeatTactical tac)
    | _ -> invalidArguments "repeat"

  let completeInterface = function
      Absyn.Tactical(tac)::[] ->
        (completeTactical tac)
    | _ -> invalidArguments "complete"

  let tacticals =
    let ts = Table.add "apply" applyInterface Table.empty in
    let ts = Table.add "id" idInterface ts in
    let ts = Table.add "then" thenInterface ts in
    let ts = Table.add "orelse" orElseInterface ts in
    let ts = Table.add "try" tryInterface ts in
    let ts = Table.add "repeat" repeatInterface ts in
    let ts = Table.add "complete" completeInterface ts in
    ts
end
