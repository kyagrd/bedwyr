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

let test =
  "Prover" >:::
  [
    "Tabling" >:::
    (let x = eig "x" 0 in
     let y = eig "y" 0 in
     let a = const "a" in
     let b = const "b" in
     let u = var "u" 0 in
     let v = var "v" 0 in
     let table = Table.O.create () in
     let t1 = (db 1) ^^ [ a ; x ; x ] in
     let t2 = (db 1) ^^ [ x ; b ; y ] in
     let t3 = (db 1) ^^ [ a ; u ; v ] in
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
          assert (None = find table [t3]))
     ]) ;

    "Engine" >:::
    [
    ]
  ]

let _ =
  if Array.length Sys.argv > 1 then
    (* Running a specific test (given its position in the tree)
     * so you can trace exceptions or do whatever debugging you want.. *)
    let id = int_of_string Sys.argv.(1) in
    let lbl = ref "" in
    let test =
      let rec g n k t =
        let next n = match k with
          | [] -> raise Not_found
          | t::tl -> g n tl t
        in
          match t with
            | TestCase f -> if n = id then f else next (n+1)
            | TestList [] -> next n
            | TestLabel (l,t) -> lbl := l ; g n k t
            | TestList (h::tl) -> g n (tl@k) h
      in g 0 [] test
    in
      Printf.printf "Running test %d: %s\n%!" id !lbl ;
      test ()
  else
    let l = run_test_tt ~verbose:true test in
      if List.exists (function RSuccess _ -> false | _ -> true) l then
        exit 1
