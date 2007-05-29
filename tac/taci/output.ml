module type Output =
sig
  val error : string -> unit
  val output : string -> unit
  val clear : unit -> unit
end

module ConsoleOutput =
struct
  let error s = print_string ("Error: " ^ s)
  let output s = print_string s
  let clear () =
    if Sys.os_type = "Win32" then
      let _ = Sys.command "cls" in
      ()
    else
      let _ = Sys.command "clear" in
      ()

    
end

module XmlOutput =
struct
  let error s = print_string ("<Output type=\"error\" text=\"" ^ s ^ "\"/>")
  let output s = print_string ("<Output type=\"output\" text=\"" ^ s ^ "\"/>")
  let clear () = print_string ("<Output type=\"clear\"/>")
end
