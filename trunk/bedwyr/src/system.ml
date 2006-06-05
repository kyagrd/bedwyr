(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

module Logic =
struct
  let eq = "="
  let andc = ","
  let orc = ";"
  let imp = "=>"
  let truth = "true"
  let falsity = "false"
  let forall = "pi"
  let exists = "sigma"
  let nabla = "nabla"

  let _ =
    Pprint.set_infix [ imp ; andc ; orc ; eq  ; "+" ; "-" ; "*" ]
end

type defkind = Normal | Inductive | CoInductive

type input =
  | Def     of defkind * string * int * Term.term
  | Query   of Term.term
  | Command of string * Term.term list

(** A simple debug flag, which can be set dynamically from the logic program. *)

let debug = ref false

(** Definitions *)

exception Inconsistent_definition of string
exception Undefined of string
exception Arity_mismatch of string*int

type definition = string * int * Term.term
let defs : (string,(defkind*Term.term*Table.t option)) Hashtbl.t = Hashtbl.create 100

let add_clause kind head arity body =
  let k,b,t =
    try
      let k,b,t = Hashtbl.find defs head in
        match Term.observe b with
          | Term.Lam (a,b) when a=arity && k=kind ->
              k, Term.lambda a
                   (Term.app (Term.atom Logic.orc) [b;body]), t
          | _ -> raise (Inconsistent_definition head)
    with
      | Not_found -> kind, (Term.lambda arity body), None
  in
  let b = Norm.hnorm b in
    Hashtbl.replace defs head (k,b,t) ;
    if !debug then
      Format.printf "%s := %a\n" head Pprint.pp_term b

let get_def ?check_arity head =
  try
    let k,b,t = Hashtbl.find defs head in
      match check_arity with
        | None -> k,b,t
        | Some a ->
            begin match Term.observe b with
              | Term.Lam (n,_) when n=a -> k,b,t
              | _ when a=0 -> k,b,t
              | _ -> raise (Arity_mismatch (head,a))
            end
  with
    | Not_found -> raise (Undefined head)

let table head =
  try
    let k,b,t = Hashtbl.find defs head in
      Hashtbl.replace defs head (k,b,Some (Table.create ()))
  with
    | Not_found -> raise (Undefined head)

(* Common utils *)

let rec make_list f = function
  | 0 -> []
  | n -> (f n)::(make_list f (n-1))

(* Handle user interruptions *)

let interrupt = ref false
exception Interrupt
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; raise Interrupt )
