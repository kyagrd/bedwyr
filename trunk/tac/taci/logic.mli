module Table : Map.S with type key = String.t
type 'a table = 'a Table.t

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
