(****************************************************************************)
(* Bedwyr -- level-0/1 prover and tabling testing                           *)
(* Copyright (C) 2012-2014 Quentin Heath                                    *)
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

open OUnit
open Term
open Notations

let fresh ~ts ~lts ~name ~tag = fresh ~ts ~lts ~name tag

let var nm ts = fresh ~tag:Logic ~name:nm ~ts:ts ~lts:0
let eig nm ts = fresh ~tag:Eigen ~name:nm ~ts:ts ~lts:0
let const nm = fresh ~tag:Constant ~name:nm ~ts:0 ~lts:0

let add table terms =
  let add,_,_ = Table.O.access ~switch_vars:false table terms in
  add

let find table terms =
  let _,found,_ = Table.O.access ~switch_vars:false table terms in
  found

let filter table terms =
  Table.O.filter ~switch_vars:false table terms

let test =
  "Prover" >:::
  [
    "Tabling" >:::
    (let x = eig "x" 0 in
     let y = eig "y" 0 in
     let z = eig "z" 0 in
     let a = const "a" in
     let b = const "b" in
     let u = var "u" 0 in
     let v = var "v" 0 in
     let table = Table.O.create () in
     let t1 = (db 1) ^^ [ a ; x ; x ] in
     let t2 = (db 1) ^^ [ x ; b ; y ] in
     let t3 = (db 1) ^^ [ a ; u ; v ] in
     let t4 = (db 1) ^^ [ a ; x ; y ] in
     let t5 = (db 1) ^^ [ x ; b ; x ] in
     let t6 = (db 1) ^^ [ a ; b ; b ] in
     let t7 = (db 1) ^^ [ x ; y ; z ] in
     [
       "Write" >::
       (fun () ->
          assert (add table [t1] (ref (Table.O.Proved (ref [])))) ;
          assert (add table [t2] (ref (Table.O.Disproved (ref [])))) ;
          assert (not (add table [t3] (ref (Table.O.Proved (ref [])))))) ;

       "Read" >::
       (fun () ->
          assert (Some {contents=(Table.O.Proved {contents=[]})} = find table [t1]) ;
          assert (Some {contents=(Table.O.Disproved {contents=[]})} = find table [t2]) ;
          assert (None = find table [t3]) ;
          assert (None = find table [t4]) ;
          assert (None = find table [t5]) ;
          assert (None = find table [t6])) ;

       "Filter" >::
       (fun () ->
          assert (None = filter table [t3]) ;
          assert (None = filter table [t4]) ;
          assert (None = filter table [t5]) ;
          assert (Some true = filter table [t6]) ;
          assert (Some false = filter table [t7]) ;
          ())
     ]) ;

    "Engine" >:::
    [
    ]
  ]

let _ =
  let argv = Array.to_list Sys.argv in
  (* option "-v" to display the names of the tests *)
  let verbose = List.mem "-v" argv in
  let rec get_ids accum = function
    | [] -> List.rev accum
    | h::t ->
        let accum =
          try (int_of_string h)::accum
          with _ -> accum
        in
        get_ids accum t
  in
  match get_ids [] argv with
    | [] ->
        let l = run_test_tt ~verbose test in
        if List.exists (function RSuccess _ -> false | _ -> true) l then exit 1
    | ids ->
        (* Running specific tests (given positions in the tree) so you
         * can trace exceptions or do whatever debugging you want. *)
        let display_test id =
          let rec get_test l n k t =
            let next n = match k with
              | [] -> raise Not_found
              | t::tl -> get_test l n tl t
            in
            match t with
              | TestCase f -> if n = id then l,f else next (n+1)
              | TestList [] -> next n
              | TestLabel (l,t) -> get_test l n k t
              | TestList (h::tl) -> get_test l n (tl@k) h
          in
          let lbl,test = get_test "" 0 [] test in
          Printf.printf "Running test %d: %s\n%!" id lbl ;
          test ()
        in
        List.iter display_test ids
