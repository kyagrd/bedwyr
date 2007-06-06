module type Output =
sig
  val showDebug : bool ref
  val prompt : string -> unit
  val error : string -> unit
  val debug : string -> unit
  val output : string -> unit
  val clear : unit -> unit
end


module ConsoleOutput =
struct
  let showDebug = ref false
  let debug s =
    if !showDebug then
      (print_string ("Debug: " ^ s);
      flush stdout)
    else
      ()

  let prompt s = print_string s
  
  let error s = (print_string ("Error: " ^ s); flush stdout)
  let output s = (print_string s; flush stdout)
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
  let map =
    let sq = ("'", "&apos;") in
    let dq = ("\"", "&quot;") in
    let slash = ("\\", "\\\\") in
    let cr = ("\r", "") in    
    let nl = ("\n", "\\n") in
    let amp = ("&", "&amp;") in
    let lt = ("<", "&lt;") in
    let gt = (">", "&gt;") in
    (List.map (fun (r,s) -> (Str.regexp r, s)) [sq;dq;slash;cr;nl;amp;lt;gt])
  
  let escape s =
    let rec escape' regexes result =
      match regexes with
          [] -> result
        | (r,s)::rs ->
            let result' = (Str.global_replace r s result) in
            (escape' rs result')
    in
    escape' map s

  let showDebug = ref false
  let debug s =
    if !showDebug then
      print_string ("<Output type=\"debug\" text=\"" ^ (escape s) ^ "\"/>")
    else
      ()
      
  let error s = print_endline ("<Output type=\"error\" text=\"" ^ (escape s) ^ "\"/>")
  let output s = print_endline ("<Output type=\"output\" text=\"" ^ (escape s) ^ "\"/>")
  let prompt s = print_endline ("<Output type=\"command\" text=\"prompt\"/>")
  let clear () = print_endline ("<Output type=\"command\" text=\"clear\"/>")
end
