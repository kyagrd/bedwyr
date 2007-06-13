module type Output =
sig
  val showDebug : bool ref
  val prompt : string -> unit
  val error : string -> unit
  val debug : string -> unit
  val output : string -> unit
  val goal : string -> unit
  val clear : unit -> unit
  val logics : (string * string) list -> unit
  val tacticals : string list -> unit
end

module ConsoleOutput : Output
module XmlOutput : Output
