(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2012 Andrew Gacek, David Baelde, Alwen Tiu            *)
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

type tag =
  | Proved
  | Working of (bool ref * tag ref list ref * tag ref list ref)
  | Disproved
  | Unset
type t = tag ref Index.t ref

let set_eqvt b = Index.eqvt_index := b

let create () = ref Index.empty

let access ~switch_vars table args =
  let update,found,_ =
    Index.access ~switch_vars !table args
  in
  let update tag =
    try table := update tag ; true
    with Index.Cannot_table -> false
  in
  (*let delete () = table := delete () in*)
  let delete () = update (ref Unset) in
  update,found,delete


(* TODO factorize this with nb_rename *)
(* FIXME the display depends on the current value of Index.eqvt_index,
 * while it should depend on its value when the goal *was* tabled... *)
let nabla_abstract t =
  let t = Norm.deep_norm t in
  let bindings =
    let l = Term.get_nablas t in
    if !Index.eqvt_index then l else
      let max = List.fold_left (fun a b -> if (a < b) then b else a) 0 l in
      let rec make_list = function 0 -> [] | n -> n::make_list (n-1) in
      make_list max
  in
  List.fold_left
    (fun s i -> (Term.quantify Term.Nabla (Term.nabla i) s)) t bindings

let print head table =
  Format.printf
    "@[<v>Table for %a contains (P=Proved, D=Disproved):"
    Pprint.pp_term head ;
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.printf "@;<1 1>[P] %a" Pprint.pp_term t
         | Disproved -> Format.printf "@;<1 1>[D] %a" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false) ;
  Format.printf "@]@."

let fprint fout head table ty =
  let fmt = (Format.formatter_of_out_channel fout) in
  let ty = Input.Typing.ty_arrow [ty] ty in
  Format.fprintf fmt
    "@[%% Table for %a contains :@,@,@[<hov>Define@;<1 2>proved : %a,@;<1 2>disproved : %a"
    Pprint.pp_term head
    (Input.Typing.get_pp_type ()) ty
    (Input.Typing.get_pp_type ()) ty ;
  let first = ref true in
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       let print =
         if !first then begin
           first := false ;
           Format.fprintf fmt "@;<1 0>by@;<1 2>%s %a"
         end else
           Format.fprintf fmt " ;@;<1 2>%s %a"
       in
       match !tag with
         | Proved    -> print "proved" Pprint.pp_term t
         | Disproved -> print "disproved" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false) ;
  Format.fprintf fmt "@;<0 0>.@]@]@."

let reset x = x := Index.empty

let iter table f =
  Index.iter !table (fun t tag -> f t !tag)

