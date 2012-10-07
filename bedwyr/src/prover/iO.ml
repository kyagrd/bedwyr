(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012 Quentin Heath                                         *)
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


(* List of open files used for user output. *)
let user_files : (string,out_channel) Hashtbl.t =
  Hashtbl.create 50

(* Sanity wrappers *)

let open_in name =
  try open_in name
  with Sys_error e ->
    let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
    raise (File_error ("read from",name,msg))

let close_in name f =
  try close_in f
  with Sys_error e ->
    let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
    raise (File_error ("close",name,msg))

let open_out name =
  try open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 name
  with Sys_error e ->
    let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
    raise (File_error ("create",name,msg))

let close_out name f =
  try close_out f
  with Sys_error e ->
    let msg = Str.replace_first (Str.regexp (Str.quote (name ^ ": "))) "" e in
    raise (File_error ("close",name,msg))

let get_user_file name =
  try Some (Hashtbl.find user_files name)
  with Not_found -> None

(* Term output (stdout and file) *)

let print print_fun goals = match goals with
  | [f] -> print_fun f
  | _ -> assert false

let open_user_file goals =
  match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              if Hashtbl.mem user_files name then false else begin
                let fout = open_out name in
                Hashtbl.add user_files name fout ;
                true
              end
          | _ -> false
        end
    | _ -> assert false

let fprint print_fun goals = match goals with
  | [f;g] ->
      begin match Term.observe f with
        | Term.QString name ->
            begin match get_user_file name with
              | Some f ->
                  let fmt = Format.formatter_of_out_channel f in
                  print_fun fmt g
              | None -> false
            end
        | _ -> false
      end
  | _ -> assert false

let close_user_file goals =
  match goals with
    | [f] ->
        begin match Term.observe f with
          | Term.QString name ->
              let opened = match get_user_file name with
                  | Some f -> close_out name f ; true
                  | None -> false
              in
              Hashtbl.remove user_files name ;
              opened
          | _ -> false
        end
    | _ -> assert false

let close_user_files () =
  Hashtbl.iter
    (fun n c -> try Pervasives.close_out c with Sys_error _ -> ())
    user_files ;
  Hashtbl.clear user_files
