val logicExists : string -> bool
val outputExists : string -> bool

val logics : (string * string) list
val getLogicInterpreter : string -> string -> (unit -> unit) option

val printLogics : (string -> unit) -> unit
val printOutputs : (string -> unit) -> unit