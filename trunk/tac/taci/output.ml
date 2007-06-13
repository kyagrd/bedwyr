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


module ConsoleOutput =
struct
  let showDebug = ref false
  let debug s =
    if !showDebug then
      (print_string ("Debug: " ^ s);
      flush stdout)
    else
      ()

  let prompt s = (print_string s; flush stdout)
  let logics ls =
    let logic (key,name) =
      key ^ (String.make (min 0 (20 - (String.length key))) ' ') ^ ":  " ^ name
    in
    (print_string ("Logics:\n  " ^ (String.concat "\n  " (List.map logic ls)) ^ "\n");
    flush stdout)

  let error s = (print_string ("Error: " ^ s); flush stdout)
  let output s = (print_string s; flush stdout)
  let goal s = (print_string s; flush stdout)
  let clear () =
    if Sys.os_type = "Win32" then
      let _ = Sys.command "cls" in
      ()
    else
      let _ = Sys.command "clear" in
      ()

  let tacticals sl =
    let o = "Tacticals:\n  " ^ (String.concat "\n  " sl) ^ "\n" in
    (print_string o;
    flush stdout)

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
  
  let logics ls =
    let logic (key,name) =
      "<Output type=\"logic\" key=\"" ^ (escape key) ^ "\" name=\"" ^ (escape name) ^ "\"/>"
    in
    (print_string (String.concat "" (List.map logic ls));
    flush stdout)

  let tacticals sl =
    let tac name =
      "<Output type=\"tactical\" text=\"" ^ (escape name) ^ "\"/>"
    in
    (print_string (String.concat "" (List.map tac sl));
    flush stdout)

  let error s = print_endline ("<Output type=\"error\" text=\"" ^ (escape s) ^ "\"/>")
  let output s = print_endline ("<Output type=\"output\" text=\"" ^ (escape s) ^ "\"/>")
  let goal s = print_endline ("<Output type=\"goal\" text=\"" ^ (escape s) ^ "\"/>")
  let prompt s = print_endline ("<Output type=\"command\" text=\"prompt\"/>")
  let clear () = print_endline ("<Output type=\"command\" text=\"clear\"/>")
end
