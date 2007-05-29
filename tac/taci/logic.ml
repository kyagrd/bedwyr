(**********************************************************************
*General string -> 'a map.
**********************************************************************)
module Table = Map.Make(String)
type 'a table = 'a Table.t

(**********************************************************************
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
  val sequents : session -> sequent list
  val updateSequents : sequent list -> session -> session
  
  type tactic = sequent -> (sequent list -> unit) -> unit
  type tactical = string -> session -> (sequent list -> unit) -> unit

  val tactics : tactic table
  val tacticals : tactical table
end  

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module GenericTacticals (L : Logic) =
struct
  let findTactic name session =
    try
      let tactical = Table.find name L.tactics in
      Some tactical
    with
      Not_found -> None
  
  let idTactical args session sc =
    let
    sc [sequent]

  let applyTactical args session sc =
    let tacticname = args in
    let tacticop = findTactic tacticname session in
    if Option.isSome tacticop then
      let tactic = Option.get tacticop in
      applyTactic tactic session sc
    else
      ()

  let orTactical args session sc =
    let t1 = firstWord args in
    let t2 = rest args in
    let t1op = findTactic t1 session in
    let t2op = findTactic t2 session in
    if ((Options.isSome t1op) && (Option.isSome t2op)) then
      (applyTactic (Option.get t1op) session sc; applyTactic (Option.get t2op) session sc)
    else
      ()

  let thenTactical args session sc =
    let t1 = firstWord args in
    let t2 = rest args in
    let t1op = findTactic t1 session in
    let t2op = findTactic t2 session in
    if ((Options.isSome t1op) && (Option.isSome t2op)) then
      let sc' session' =
        (mapTactic (Option.get t2op) session' sc)
      in
      (applyTactic (Option.get t1op) session sc')
    else
      ()
      
  let genericTacticals =
    let ts = Logic.Table.add "id" idTactical Table.empty in
    let ts = Logic.Table.add "apply" applyTactical Table.empty in
    let ts = Logic.Table.add "or" orTactical Table.empty in
    let ts = Logic.Table.add "id" idTactical Table.empty in
    ts
end