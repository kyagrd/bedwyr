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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

type tag = Proved | Working of bool ref | Disproved | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args


let nabla_abstract t =
  let t = Norm.deep_norm t in
  let l = Term.get_nablas t in
  let max = List.fold_left (fun a b -> if (a < b) then b else a) 0 l in
  let rec make_list = function 0 -> [] | n -> n::make_list (n-1) in
  let bindings = if !Index.eqvt_tbl then l else make_list max in
  List.fold_left
    (fun s i -> (Term.quantify Term.Nabla (Term.nabla i) s)) t bindings

let print head table =
  Format.printf
    "@[<v>Table for %a contains (P=Proved, D=Disproved):@,"
    Pprint.pp_term head ;
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match !tag with
         | Proved    -> Format.printf " [P] %a@," Pprint.pp_term t
         | Disproved -> Format.printf " [D] %a@," Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false) ;
  Format.printf "@]@."

let fprint fout head table =
  let fmt = (Format.formatter_of_out_channel fout) in
  Format.fprintf fmt
    "@[%% Table for %a contains :@,@,@[<hov>Define@;<1 2>proved,@;<1 2>disproved"
    Pprint.pp_term head ;
  let first = ref true in
  Index.iter !table
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       if !first then begin
         first := false ;
         match !tag with
           | Proved    -> Format.fprintf fmt "@;<1 0>by@;<1 2>proved %a" Pprint.pp_term t
           | Disproved -> Format.fprintf fmt "@;<1 0>by@;<1 2>disproved %a" Pprint.pp_term t
           | Unset     -> ()
           | Working _ -> assert false
       end else begin match !tag with
         | Proved    -> Format.fprintf fmt " ;@;<1 2>proved %a" Pprint.pp_term t
         | Disproved -> Format.fprintf fmt " ;@;<1 2>disproved %a" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false
       end) ;
  Format.fprintf fmt "@;<0 0>.@]@]@."

let reset x = x := Index.empty

let iter_fun table f =
  Index.iter !table (fun t tag -> f t !tag)

