(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007 Zach Snow, David Baelde                          *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
let showDebug = ref false

module type Output =
sig
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
  let debug s =
    if !showDebug then
      (print_string ("Debug: " ^ s);
      flush stdout)
    else
      ()

  let prompt s = (print_string s; flush stdout)
  
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

  let logics ls =
    let get (key, name) =
      key ^ (String.make (20 - (String.length key)) ' ') ^ ":  " ^ name
    in
    output ("Logics:\n  " ^ (String.concat "\n  " (List.map get ls)) ^ "\n")
  
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
    let cr = ("\r", "") in    
    let nl = ("\n", "\\n") in
    let amp = ("&", "&amp;") in
    let lt = ("<", "&lt;") in
    let gt = (">", "&gt;") in
    let slash = ("\\", "\\\\") in
    (List.map (fun (r,s) -> (Str.regexp r, s)) [sq;dq;cr;nl;amp;lt;gt;slash])
  
  let escape s =
    let rec escape' regexes result =
      match regexes with
          [] -> result
        | (r,s)::rs ->
            let result' = (Str.global_replace r s result) in
            (escape' rs result')
    in
    escape' map s

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
