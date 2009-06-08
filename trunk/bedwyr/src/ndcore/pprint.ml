(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
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

open Term
open Format

exception Found of int

type assoc = Left | Right | Both | Nonassoc
  
let debug = ref false

(* List of infix operators sorted by priority. *)
let infix : (string * assoc) list ref = ref []
let set_infix l = infix := l
let is_infix x = List.mem_assoc x !infix
let get_assoc op = List.assoc op !infix
let priority x =
  try
    ignore (List.fold_left
              (fun i (e, assoc) -> if e = x then raise (Found i) else i+1)
              1 !infix) ;
    0
  with
    | Found i -> i
let get_max_priority () = List.length !infix

(* Generic output function *)

let parenthesis x = "(" ^ x ^ ")"

(** Print a term. Ensures consistent namings, using naming hints when available.
  * Behaves consistently from one call to another unless Term.reset_namespace
  * is called between executions.
  * Two lists of names must be passed for free "bound variables"
  * and generic variables. These names are assumed not to conflict with any
  * other name. The good way to ensure that is to use Term.get_dummy_name and
  * [Term.free].
  * The input term should be fully normalized. *)
let print_full ~generic ~bound chan term =
  let get_nth list n s =
    try
      List.nth list n
    with
      Failure _ -> s
  in
  
  let high_pr = 1 + get_max_priority () in
  let rec pp ~bound pr chan term =
    match observe term with
      | Var v ->
          let name = Term.get_name term in
          if !debug then
            Format.fprintf chan "%s[%d/%d]" name v.ts v.lts
          else
            Format.fprintf chan "%s" name
      | NB i ->
          Format.fprintf chan "%s"
            (get_nth generic (i-1) ("nabla(" ^ (string_of_int (i - 1)) ^ ")"))
      | DB i ->
          Format.fprintf chan "%s"
            (get_nth bound (i-1) ("db(" ^ (string_of_int (i - 1)) ^ ")"))
      | App (t,ts) ->
          begin match (observe t, ts) with
            | Var {tag=Constant}, [a; b] when is_infix (get_name t) ->
                let op = get_name t in
                let op_p = priority op in
                let assoc = get_assoc op in
                let pr_left, pr_right = match assoc with
                  | Left -> op_p, op_p+1
                  | Right -> op_p+1, op_p
                  | _ -> op_p, op_p
                in
                let print =
                  if op_p >= pr then
                    Format.fprintf chan "@[%a@ %s@ %a@]"
                  else
                    Format.fprintf chan "@[<1>(%a@ %s@ %a)@]"
                in
                  print (pp ~bound pr_left) a op (pp ~bound pr_right) b
            | _ ->
                let print =
                  if pr=0 then
                    Format.fprintf chan "@[<2>%a %a%a@]"
                   else
                    Format.fprintf chan "@[<3>(%a %a%a)@]"
                in
                  print (pp ~bound high_pr)
                    t
                    (pp ~bound high_pr) (List.hd ts)
                    (fun chan ->
                      List.iter (Format.fprintf chan "@ %a" (pp ~bound high_pr)))
                    (List.tl ts)
          end
      | Lam (i,t) ->
          assert (i<>0) ;
          (* Get [i] more dummy names for the new bound variables.
           * Release them after the printing of this term. *)
          let more = Term.get_dummy_names ~start:1 i "x" in
          let head = String.concat "\\" more in
          let print =
            if pr=0 then
              Format.fprintf chan "%s\\@ %a"
            else
              Format.fprintf chan "@[<1>(%s\\@ %a)@]"
          in
            print head (pp ~bound:(List.rev_append more bound) 0) t ;
            List.iter Term.free more
      | Susp (t,_,_,l) ->
          Format.fprintf chan "<%d:%a>" (List.length l) (pp ~bound pr) t
      | Ptr  _ -> assert false (* observe *)
  in
    Format.fprintf chan "@[%a@]" (pp ~bound high_pr) term

let term_to_string_full ~generic ~bound tm =
  print_full ~generic ~bound Format.str_formatter tm ;
  Format.flush_str_formatter ()

(* Print a term; allows debugging.  See term_to_string_full. *)
let term_to_string_full_debug ~generic ~bound dbg term =
  let debug' = !debug in
  let () = debug := dbg in
  let s = term_to_string_full ~generic ~bound term in
  (debug := debug';
  s)

let get_generic_names x =
  let nbs = Term.get_nablas x in
  let max_nb = List.fold_left max 0 nbs in
    Term.get_dummy_names ~start:1 max_nb "n"

let print ?(bound=[]) chan term =
  let term = Norm.deep_norm term in
  let generic = get_generic_names term in
  let s = print_full ~generic ~bound chan term in
    List.iter Term.free generic ;
    s

let term_to_string ?(bound=[]) tm =
  print ~bound Format.str_formatter tm ;
  Format.flush_str_formatter ()

let pp_term out term = print out term

(** Output to stdout *)
let print_term ?(bound=[]) term =
  print ~bound Format.std_formatter term

(** Utility for tools such as Taci which push down formula-level abstractions
  * to term level abstractions. Dummy names should be created (and freed)
  * during the printing of the formula, and passed as the bound names to this
  * function, which won't display the lambda prefix.
  * The input term should have at least [List.length bound] abstractions
  * at toplevel. *)
let pp_preabstracted ~generic ~bound chan term =
  (* let term = Norm.hnorm term in *)
  let len = List.length bound in
    match observe term with
      | Lam (n,term) ->
          assert (len <= n) ;
          print_full ~generic ~bound chan (lambda (n-len) term)
      | _ ->
          (* assert (bound = []); *)
          print_full ~generic ~bound chan term

let term_to_string_preabstracted ~generic ~bound term =
  pp_preabstracted ~generic ~bound Format.str_formatter term ;
  Format.flush_str_formatter ()
