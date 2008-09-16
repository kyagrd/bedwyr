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
  let eq      = Term.atom "="
  let andc    = Term.atom ","
  let orc     = Term.atom ";"
  let imp     = Term.atom "=>"
  let cimp    = Term.atom "-->"
  let truth   = Term.atom "true"
  let falsity = Term.atom "false"
  let forall  = Term.atom "pi"
  let exists  = Term.atom "sigma"
  let nabla   = Term.atom "nabla"

  let print   = Term.atom "print"
  let parse   = Term.atom "parse"
  let on      = Term.atom "on"
  let off     = Term.atom "off"

  let var_eq      = Term.get_var eq
  let var_andc    = Term.get_var andc
  let var_orc     = Term.get_var orc
  let var_imp     = Term.get_var imp
  let var_cimp    = Term.get_var cimp
  let var_truth   = Term.get_var truth
  let var_falsity = Term.get_var falsity
  let var_forall  = Term.get_var forall
  let var_exists  = Term.get_var exists
  let var_nabla   = Term.get_var nabla

  let var_print   = Term.get_var print
  let var_parse   = Term.get_var parse
  let var_on      = Term.get_var on
  let var_off     = Term.get_var off

  let _ =
    Pprint.set_infix [ ("=>", Pprint.Right) ;
                       ("-->", Pprint.Right);
                       ("->", Pprint.Right);
                       ("<-", Pprint.Left) ;
                       (",",  Pprint.Both) ;
                       (";",  Pprint.Both) ;
                       ("=",  Pprint.Nonassoc) ;
                       ("+",  Pprint.Both) ;
                       ("-",  Pprint.Left) ;
                       ("*",  Pprint.Both) ]
end

type defkind = Normal | Inductive | CoInductive

type input =
  | Def     of defkind * Term.term * int * Term.term
  | Query   of Term.term
  | Command of string * Term.term list

(** A simple debug flag, which can be set dynamically from the logic program. *)

let debug = ref false
let time  = ref false

(** Definitions *)

exception Inconsistent_definition of Term.term
exception Undefined of Term.term
exception Arity_mismatch of Term.term*int

(* type definition = Term.var * int * Term.term *)
let defs : (Term.var,(defkind*Term.term*Table.t option)) Hashtbl.t =
  Hashtbl.create 100

let reset_defs () = Hashtbl.clear defs

let add_clause kind head_tm arity body =
  (* Cleanup all tables.
   * Cleaning only this definition's table is _not_ enough, since other
   * definitions may rely on it.
   * TODO: make it optional to speedup huge definitions ? *)
  Hashtbl.iter
    (fun k v ->
       match v with
         | _,_,Some t -> Table.reset t
         | _ -> ())
    defs ;
  let head = Term.get_var head_tm in
  let k,b,t =
    try
      let k,b,t = Hashtbl.find defs head in
        match Term.observe b with
          | Term.Lam (a,b) ->
              if a=arity && k=kind then
                k, Term.lambda a
                     (Term.app Logic.orc [b;body]), t
              else
                raise (Inconsistent_definition head_tm)
          | _ when arity=0 && k=kind ->
              k, Term.app Logic.orc [b;body], t
          | _ -> raise (Inconsistent_definition head_tm)
    with
      | Not_found ->
          kind, (Term.lambda arity body),
          (if kind=Normal then None else Some (Table.create ()))
  in
  let b = Norm.hnorm b in
    Hashtbl.replace defs head (k,b,t) ;
    if !debug then
      Format.printf "%a := %a\n" Pprint.pp_term head_tm Pprint.pp_term b

let get_def ?check_arity head_tm =
  let head = Term.get_var head_tm in
  try
    let k,b,t = Hashtbl.find defs head in
      match check_arity with
        | None | Some 0 -> k,b,t
        | Some a ->
            begin match Term.observe b with
              | Term.Lam (n,_) when n=a -> k,b,t
              | _ -> raise (Arity_mismatch (head_tm,a))
            end
  with
    | Not_found -> raise (Undefined head_tm)

let show_table head =
  try
    let _,_,table = Hashtbl.find defs (Term.get_var head) in
      match table with
        | Some table -> Table.print head table
        | None ->
            failwith ("No table defined for " ^ (Pprint.term_to_string head))
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
  if !interrupt then ( interrupt := false ; true ) else false
