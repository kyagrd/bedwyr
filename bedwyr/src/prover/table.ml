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

let reset x = x := Index.empty

let iter f table =
  Index.iter (fun t v -> f t !v) !table

let fold f table x =
  Index.fold (fun t v y -> f t !v y) !table x

let print head table =
  Format.printf
    "@[<v>Table for %a contains (P=Proved, D=Disproved):"
    Pprint.pp_term head ;
  iter
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       match tag with
         | Proved _    -> Format.printf "@;<1 1>[P] %a" Pprint.pp_term t
         | Disproved _ -> Format.printf "@;<1 1>[D] %a" Pprint.pp_term t
         | Unset       -> ()
         | Working _ -> assert false)
    table ;
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
  iter
    (fun t tag ->
       let t = nabla_abstract (Term.app t [head]) in
       let print =
         if !first then begin
           first := false ;
           Format.fprintf fmt "@;<1 0>by@;<1 2>%s %a"
         end else
           Format.fprintf fmt " ;@;<1 2>%s %a"
       in
       match tag with
         | Proved _    -> print "proved" Pprint.pp_term t
         | Disproved _ -> print "disproved" Pprint.pp_term t
         | Unset       -> ()
         | Working _   -> assert false)
    table ;
  Format.fprintf fmt "@;<0 0>.@]@]@."

let export file all_tables =
  let fresh_id =
    let id = ref 0 in
    function () ->
      incr id ;
      !id
  in
  (* get all the tabled atoms *)
  let all_atoms =
    List.fold_left
      (fun map (head,table) ->
         Index.fold
           (fun atom status m ->
              let atom = nabla_abstract (Term.app atom [head]) in
              (status,(atom,fresh_id (),ref true)) :: m)
           !table map)
      [] all_tables
  in
  (* mark all atoms that are not the root of a computation,
   * get the others *)
  let root_atoms =
    let () =
      List.iter
        (fun (status,(tt,_,_)) -> match !status with
           | Proved sons
           | Disproved sons ->
               List.iter
                 (function
                    | Son st ->
                        begin try
                          let _,_,root = List.assq st all_atoms in
                          root := false
                        with Not_found -> failwith "was #clear_table used?" end
                    | _ -> ())
                 !sons
           | Unset -> ()
           | Working _ -> assert false)
        all_atoms
    in
    List.fold_left
      (fun accum (st,(_,_,root)) -> if !root then st::accum else accum)
      [] all_atoms
  in
  (* TODO sort the root atoms:
   * graph colouring, topological sort of the colours, as so on…
   * or just add an id in each atom of the table *)
  let doctype = "skeleton" in
  let dtd = "bedwyr.dtd" in
  let xsl = "bedwyr-skeleton.xsl" in
  let timestamp = string_of_int (int_of_float (Unix.gettimeofday ())) in
  let channel = IO.open_out file in
  let output = Xmlm.make_output ~nl:true (`Channel channel) in
  Xmlm.output output
    (`Dtd (Some ("<!DOCTYPE " ^ doctype ^ " SYSTEM \"" ^ dtd ^ "\">"))) ;
  Printf.fprintf channel
    ("<?xml-stylesheet type=\"text/xsl\" href=\"%s\"?>\n%!") xsl ;
  Xmlm.output output (* <skeleton> *)
    (`El_start (("","skeleton"),
                [("","timestamp"),timestamp])) ;
  let display_tree status =
    let status_to_string = function
      | Proved x -> x,"proved"
      | Disproved x -> x,"disproved"
      | Unset
      | Working _ -> assert false
    in
    let start_son son_type value id_type id =
      Xmlm.output output
        (`El_start (("",son_type),
                    [("","value"),value ; ("",id_type),(string_of_int id)]))
    in
    (* TODO tail-rec aux *)
    let rec aux n = function
      | Son st ->
          let sons =
            try
              let t,id,_ = List.assq st all_atoms in
              let x,s = status_to_string !st in
              start_son "son" s "id" id ; (* <son> *)
              Xmlm.output output (`El_start (("","atom"),[])) ;
              Xmlm.output output (`Data (Pprint.term_to_string t)) ;
              Xmlm.output output (`El_end) ;
              x
            with Not_found -> assert false
          in
          List.iter
            (fun x -> aux (n+1) x)
            (List.rev !sons) ;
          Xmlm.output output (`El_end) (* </son> *)
      | Loop st ->
          begin try
            let t,id,_ = List.assq st all_atoms in
            let _,value = status_to_string !st in
            start_son "loop" value "ref" id ; (* <loop> *)
            Xmlm.output output (`Data (Pprint.term_to_string t)) ;
          with Not_found -> assert false end ;
          Xmlm.output output (`El_end) (* </loop> *)
      | Cut st ->
          begin try
            let t,id,_ = List.assq st all_atoms in
            let _,value = status_to_string !st in
            start_son "cut" value "ref" id ; (* <cut> *)
            Xmlm.output output (`Data (Pprint.term_to_string t)) ;
          with Not_found -> assert false end ;
          Xmlm.output output (`El_end) (* </cut> *)
    in
    aux 0 (Son status)
  in
  List.iter
    display_tree
    root_atoms ;
  Xmlm.output output (`El_end) ; (* </skeleton> *)
  IO.close_out file channel
