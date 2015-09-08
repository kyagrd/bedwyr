(****************************************************************************)
(* Bedwyr -- tabling                                                        *)
(* Copyright (C) 2006 Alwen Tiu, Axelle Ziegler, Andrew Gacek               *)
(* Copyright (C) 2006,2007,2009 David Baelde                                *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2011-2015 Quentin Heath                                    *)
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

type son =
  | Son of tag ref
  | Loop of tag ref
  | Cut of tag ref
and tag =
  | Proved of (son list ref)
  | Working of ((son list ref) *
                (bool ref * tag ref list ref * tag ref list ref))
  | Disproved of (son list ref)
  | Unset
type t = tag ref Ndcore.Index.t ref

let set_eqvt b = Ndcore.Index.eqvt_index := b

let create () = ref Ndcore.Index.empty

let access ~switch_vars table args =
  let update,found =
    Ndcore.Index.access ~switch_vars !table args
  in
  let update tag =
    try table := update tag ; true
    with Ndcore.Index.Cannot_table -> false
  in
  let delete () = update (ref Unset) in
  update,found,delete

exception OverMatch
exception UnderMatch

let filter ~switch_vars table args =
  let f tag match_status = match !tag,match_status with
    | Working _,_ -> assert false
    | Unset,_ -> ()
    | _,Ndcore.Index.Exact -> assert false
    | Proved _,Ndcore.Index.Over -> raise OverMatch
    | Disproved _,Ndcore.Index.Under -> raise UnderMatch
    | _ -> ()
  in
  try Ndcore.Index.filter ~switch_vars !table args f ; None with
    | OverMatch -> Some true
    | UnderMatch -> Some false


(* TODO factorize this with nb_rename *)
(* FIXME the display depends on the current value of Ndcore.Index.eqvt_index,
 * while it should depend on its value when the goal *was* tabled... *)
let nabla_abstract t =
  let t = Ndcore.Norm.deep_norm t in
  let bindings =
    let l = Ndcore.Term.get_nablas t in
    if !Ndcore.Index.eqvt_index then l else
      let max = List.fold_left (fun a b -> if (a < b) then b else a) 0 l in
      let rec make_list = function 0 -> [] | n -> n::make_list (n-1) in
      make_list max
  in
  List.fold_left
    (fun s i -> (Ndcore.Term.quantify Ndcore.Term.Nabla (Ndcore.Term.nabla i) s)) t bindings

let reset x = x := Ndcore.Index.empty

let iter f table =
  Ndcore.Index.iter (fun t v -> f t !v) !table

let foldr f table x =
  Ndcore.Index.fold (fun t v y -> f t v y) !table x

let print head table =
  Format.printf
    "@[<v>Table for %a contains (P=Proved, D=Disproved):"
    Ndcore.Pprint.pp_term head ;
  iter
    (fun t tag ->
       let t = nabla_abstract (Ndcore.Term.app t [head]) in
       match tag with
         | Proved _    -> Format.printf "@;<1 1>[P] %a" Ndcore.Pprint.pp_term t
         | Disproved _ -> Format.printf "@;<1 1>[D] %a" Ndcore.Pprint.pp_term t
         | Unset       -> ()
         | Working _   -> assert false)
    table ;
  Format.printf "@]@."

let fprint fout head table ty =
  let fmt = (Format.formatter_of_out_channel fout) in
  let ty = Parsetree.Preterm.Typing.Type.arrow [ty] ty in
  Format.fprintf fmt
    "@[%% Table for %a contains :@,@,@[<hov>Define@;<1 2>proved : %a,@;<1 2>disproved : %a"
    Ndcore.Pprint.pp_term head
    Parsetree.Preterm.Typing.Type.pp ty
    Parsetree.Preterm.Typing.Type.pp ty ;
  let first = ref true in
  iter
    (fun t tag ->
       let t = nabla_abstract (Ndcore.Term.app t [head]) in
       let print =
         if !first then begin
           first := false ;
           Format.fprintf fmt "@;<1 0>by@;<1 2>%s %a"
         end else
           Format.fprintf fmt " ;@;<1 2>%s %a"
       in
       match tag with
         | Proved _    -> print "proved" Ndcore.Pprint.pp_term t
         | Disproved _ -> print "disproved" Ndcore.Pprint.pp_term t
         | Unset       -> ()
         | Working _   -> assert false)
    table ;
  Format.fprintf fmt "@;<0 0>.@]@]@."

let xml_export =
  let aux _ _ _ =
    IO.Output.eprintf "XML export disabled, as corresponding module was not loaded.@."
  in
  ref aux
