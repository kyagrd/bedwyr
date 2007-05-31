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
  val validSequent : session -> bool
  val sequent : session -> (sequent * session) option
  val sequents : session -> sequent list
  val string_of_sequents : session -> string
  val updateSequents : sequent list -> session -> session
  
  type tactic = sequent -> (sequent list -> unit) -> unit
  type tactical = string -> tactic

  val tacticals : tactical table
end 
 
module type LogicSig =
sig
  type sequent
  type tactic = sequent -> (sequent list -> unit) -> unit
end

(**********************************************************************
*Standard Tacticals:
**********************************************************************)
module GenericTacticals (L : sig type tactic end) =
struct
  let failureTactical =
    fun _ _ -> ()

  let idTactical =
    fun sequent sc -> (sc [sequent])

  let applyTactical tactic =
    tactic

  let orTactical tac1 tac2 =
    fun sequent sc ->
      (tac1 sequent sc; tac2 sequent sc)
  
  
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
      (orTactical (thenTactical tac (repeatTactical tac)) idTactical) sequent sc
end
