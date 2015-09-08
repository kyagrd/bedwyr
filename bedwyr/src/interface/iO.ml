(****************************************************************************)
(* Bedwyr -- file input/output                                              *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2012,2013,2015 Quentin Heath                               *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

exception File_error of string * string * string


let error name e s =
  let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
  raise (File_error (s,name,msg))

(* Sanity wrappers *)

let paths_are_relative = ref true
let bwd = ref ""
let chrooted = ref false

let chdir name =
  try Sys.chdir name
  with Sys_error e -> error name e "chdir in"

(* [run_on f path] is supposedly functionally equivalent to
 * [f basename path path], except for additional checks on the path.
 * [f ~basename ~nice_path ~full_path] is expected to use [basename] for
 * access, [nice_path] for error messages and [full_path] for unique
 * identification. *)
let run_on f path =
  let clean =
    let old_cwd = Sys.getcwd ()
    and paths_were_relative = !paths_are_relative in
    function () ->
      paths_are_relative := paths_were_relative ;
      chdir old_cwd
  in
  let result = try
    let dirname = Filename.dirname path in
    chdir dirname ;
    if not (Filename.is_relative dirname) then (paths_are_relative := false) ;
    let cwd = Sys.getcwd ()
    and basename = Filename.basename path in
    let full_path = Filename.concat cwd basename in
    let nice_path =
      if !paths_are_relative
      then Str.replace_first (Str.regexp ("^" ^ !bwd ^ "/")) "" full_path
      else full_path
    in
    if !chrooted && nice_path=full_path
    (* XXX we use path instead of nice_path to avoid leaking bwd
     * although technically, by trying to access "../../aa/bb", one
     * can still discover this path *)
    then error path "Outside of the authorized directory" "access"
    else f ~basename ~nice_path ~full_path
  with e ->
    clean () ;
    raise e
  in
  clean () ;
  result

let open_in ~nice_path name =
  try open_in name
  with Sys_error e -> error nice_path e "read from"

let close_in ~nice_path c =
  try close_in c
  with Sys_error e -> error nice_path e "close"

let run_in ~wrap (f : (?fname:string -> in_channel -> 'a)) name =
  let aux ~basename ~nice_path ~full_path =
    let c = open_in ~nice_path basename in
    let clean () = close_in ~nice_path c in
    let result =
      try f ~fname:nice_path c
      with e -> clean () ; raise e
    in
    clean () ;
    result
  in
  run_on (wrap aux) name

let get_in fname =
  run_in ~wrap:(function f -> f)
    (fun ?fname:_ c ->
       (*
        * XXX even if the doc doesn't say so, this is OCaml 4.02 news
       really_input_string c (in_channel_length c)
        *)
       let len = in_channel_length c in
       let s = String.create len in
       really_input c s 0 len ;
       s)
    fname

let open_out ~nice_path name =
  try open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 name
  with Sys_error e -> error nice_path e "create"

let close_out ~nice_path c =
  try close_out c
  with Sys_error e -> error nice_path e "close"

let run_out f name =
  let aux ~basename ~nice_path ~full_path =
    let c = open_out ~nice_path basename in
    let clean () = close_out ~nice_path c in
    let result = try f c with e -> clean () ; raise e in
    clean () ;
    result
  in
  run_on aux name

(* List of open files used for user predicate I/O. *)

module I = struct
  let files : (string,(in_channel * Lexing.lexbuf)) Hashtbl.t = Hashtbl.create 50

  let get name =
    let aux ~basename ~nice_path ~full_path =
      try Some (Hashtbl.find files full_path)
      with Not_found -> None
    in
    run_on aux name

  let add name =
    let aux ~basename ~nice_path ~full_path =
      let c = open_in ~nice_path basename in
      let l = Lexing.from_channel c in
      Hashtbl.replace files full_path (c,l)
    in
    run_on aux name

  let remove name c =
    let aux ~basename ~nice_path ~full_path =
      close_in ~nice_path c ;
      Hashtbl.remove files full_path
    in
    run_on aux name

  let clear () =
    Hashtbl.iter
      (fun _ (c,_) -> try Pervasives.close_in c with Sys_error _ -> ())
      files ;
    Hashtbl.clear files ;
end

module O = struct
  let files : (string,(out_channel * Format.formatter)) Hashtbl.t = Hashtbl.create 50

  let get name =
    let aux ~basename ~nice_path ~full_path =
      try Some (Hashtbl.find files full_path)
      with Not_found -> None
    in
    run_on aux name

  let add name =
    let aux ~basename ~nice_path ~full_path =
      let c = open_out ~nice_path basename in
      let f = Format.formatter_of_out_channel c in
      Hashtbl.replace files full_path (c,f)
    in
    run_on aux name

  let remove name c =
    let aux ~basename ~nice_path ~full_path =
      close_out ~nice_path c ;
      Hashtbl.remove files full_path
    in
    run_on aux name

  let clear () =
    Hashtbl.iter
      (fun _ (c,_) -> try Pervasives.close_out c with Sys_error _ -> ())
      files ;
    Hashtbl.clear files ;
end

let deactivated = ref false

let deactivate_io () =
  deactivated := true

let reactivate_io () =
  deactivated := false

let close_io_files () =
  I.clear () ;
  O.clear ()

(* Term input (stdin and file) *)

let read read_fun goals =
  if !deactivated then None
  else match goals with
    | [pattern] ->
        begin match read_fun () with
          | Some term -> Some (Term.op_eq pattern term)
          | None -> None
        end
    | _ -> assert false

let fopen_in goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match I.get name with
                | Some _ -> false
                | None -> I.add name ; true
              end
          | _ -> false
        end
    | _ -> assert false

let fread read_fun goals =
  if !deactivated then None
  else match goals with
    | [f;pattern] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match I.get name with
                | Some (_,l) ->
                    begin match read_fun l () with
                      | Some term -> Some (Term.op_eq pattern term)
                      | None -> None
                    end
                | None -> None
              end
          | _ -> None
        end
    | _ -> assert false

let fclose_in goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match I.get name with
                | Some (c,_) -> I.remove name c ; true
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false

(* Term output (stdout and file) *)

let print print_fun goals =
  if !deactivated then true
  else match goals with
    | [f] -> print_fun f
    | _ -> assert false

let fopen_out goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match O.get name with
                | Some _ -> false
                | None -> O.add name ; true
              end
          | _ -> false
        end
    | _ -> assert false

let fprint print_fun goals =
  if !deactivated then true
  else match goals with
    | [f;g] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match O.get name with
                | Some (_,f) -> print_fun f g
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false

let fclose_out goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              begin match O.get name with
                | Some (c,_) -> O.remove name c ; true
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false
