module type Output =
sig
  val error : string -> unit
  val output : string -> unit
  val clear : unit -> unit
end

module ConsoleOutput : Output
module XmlOutput : Output
