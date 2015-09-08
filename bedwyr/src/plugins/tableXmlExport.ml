(****************************************************************************)
(* Bedwyr -- XML tabling export                                             *)
(* Copyright (C) 2013-2015 Quentin Heath                                    *)
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

let export file all_tables root_atoms =
  let fresh_id =
    let id = ref 0 in
    function () ->
      incr id ;
      !id
  in
  (* get all the tabled atoms *)
  let all_atoms =
    let get head atom status m =
      let atom = Prover.Table.nabla_abstract (Ndcore.Term.app atom [head]) in
      (status,(atom,fresh_id ())) :: m
    in
    List.fold_left
      (fun map (head,table) -> Prover.Table.foldr (get head) table map)
      [] all_tables
  in
  let doctype = "skeleton" in
  let dtd = "bedwyr.dtd" in
  let xsl = "bedwyr-skeleton.xsl" in
  let timestamp = string_of_int (int_of_float (Unix.gettimeofday ())) in
  let aux channel =
    let output = Xmlm.make_output ~nl:true (`Channel channel) in
    Xmlm.output output
      (`Dtd (Some (Printf.sprintf "<!DOCTYPE %s SYSTEM %S>" doctype dtd))) ;
    Printf.fprintf channel
      ("<?xml-stylesheet type=\"text/xsl\" href=%S?>\n%!") xsl ;
    Xmlm.output output (* <skeleton> *)
      (`El_start (("","skeleton"),
                  [("","timestamp"),timestamp])) ;
    let status_to_string = function
      | Prover.Table.Proved x -> x,"proved"
      | Prover.Table.Disproved x -> x,"disproved"
      | Prover.Table.Unset
      | Prover.Table.Working _ -> assert false
    in
    let start_son son_type value id_type id =
      Xmlm.output output
        (`El_start (("",son_type),
                    [("","value"),value ; ("",id_type),(string_of_int id)]))
    in
    let end_son () =
      Xmlm.output output `El_end
    in
    (* TODO tail-rec aux *)
    let rec aux = function
      | Prover.Table.Son st ->
          let sons =
            try
              let t,id = List.assq st all_atoms in
              let x,s = status_to_string !st in
              start_son "son" s "id" id ; (* <son> *)
              Xmlm.output output (`El_start (("","atom"),[])) ;
              Xmlm.output output (`Data (Ndcore.Pprint.term_to_string t)) ;
              Xmlm.output output (`El_end) ;
              x
            with Not_found -> assert false
          in
          List.iter aux (List.rev !sons) ;
          end_son () (* </son> *)
      | Prover.Table.Loop st ->
          begin try
            let t,id = List.assq st all_atoms in
            let _,value = status_to_string !st in
            start_son "loop" value "ref" id ; (* <loop> *)
            Xmlm.output output (`Data (Ndcore.Pprint.term_to_string t)) ;
          with Not_found -> assert false end ;
          end_son () (* </loop> *)
      | Prover.Table.Cut st ->
          begin try
            let t,id = List.assq st all_atoms in
            let _,value = status_to_string !st in
            start_son "cut" value "ref" id ; (* <cut> *)
            Xmlm.output output (`Data (Ndcore.Pprint.term_to_string t)) ;
          with Not_found -> assert false end ;
          end_son () (* </cut> *)
    in
    List.iter aux (List.rev root_atoms) ;
    Xmlm.output output (`El_end) (* </skeleton> *)
  in
  IO.Files.run_out aux file

let () =
  Prover.Table.xml_export := export
