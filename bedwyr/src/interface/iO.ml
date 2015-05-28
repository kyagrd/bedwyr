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


(* Sanity wrappers *)

let error name e s =
  let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
  raise (File_error (s,name,msg))

let open_in name =
  try open_in name
  with Sys_error e -> error name e "read from"

let close_in name c =
  try close_in c
  with Sys_error e -> error name e "close"

let run_in f name =
  let c = open_in name in
  let result =
    try f c with e ->
      close_in name c ;
      raise e
  in
  close_in name c ;
  result

let open_out name =
  try open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 name
  with Sys_error e -> error name e "create"

let close_out name c =
  try close_out c
  with Sys_error e -> error name e "close"

let run_out f name =
  let c = open_out name in
  let result =
    try f c with e ->
      close_out name c ;
      raise e
  in
  close_out name c ;
  result

let chdir name =
  try Sys.chdir name
  with Sys_error e -> error name e "chdir in"

(* List of open files used for user I/O. *)

module I = struct
  let files : (string,(in_channel * Lexing.lexbuf)) Hashtbl.t = Hashtbl.create 50

  let get name =
    try Some (Hashtbl.find files name)
    with Not_found -> None

  let add name =
    let c = open_in name in
    let l = Lexing.from_channel c in
    Hashtbl.replace files name (c,l)

  let remove name c =
    close_in name c ;
    Hashtbl.remove files name

  let clear () =
    Hashtbl.iter
      (fun _ (c,_) -> try Pervasives.close_in c with Sys_error _ -> ())
      files ;
    Hashtbl.clear files ;
end

module O = struct
  let files : (string,(out_channel * Format.formatter)) Hashtbl.t = Hashtbl.create 50

  let get name =
    try Some (Hashtbl.find files name)
    with Not_found -> None

  let add name =
    let c = open_out name in
    let f = Format.formatter_of_out_channel c in
    Hashtbl.replace files name (c,f)

  let remove name c =
    close_out name c ;
    Hashtbl.remove files name

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
