(****************************************************************************)
(* Bedwyr -- level-0/1 prover and tabling testing                           *)
(* Copyright (C) 2012-2015 Quentin Heath                                    *)
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
open Ndcore.Term
open Notations

let tabling_test =
  let fresh ~ts ~lts ~name ~tag = fresh ~ts ~lts ~name tag in
  let var nm ts = fresh ~tag:Logic ~name:nm ~ts:ts ~lts:0
  and eig nm ts = fresh ~tag:Eigen ~name:nm ~ts:ts ~lts:0
  and const nm = fresh ~tag:Constant ~name:nm ~ts:0 ~lts:0 in
  let add table terms =
    let add,_,_ = Table.access ~switch_vars:false table terms in
    add
  and find table terms =
    let _,found,_ = Table.access ~switch_vars:false table terms in
    found
  and filter table terms =
    Table.filter ~switch_vars:false table terms
  in
  let x = eig "x" 0
  and y = eig "y" 0
  and z = eig "z" 0
  and a = const "a"
  and b = const "b"
  and u = var "u" 0
  and v = var "v" 0 in
  let table = Table.create ()
  and t1 = (db 1) ^^ [ a ; x ; x ]
  and t2 = (db 1) ^^ [ x ; b ; y ]
  and t3 = (db 1) ^^ [ a ; u ; v ]
  and t4 = (db 1) ^^ [ a ; x ; y ]
  and t5 = (db 1) ^^ [ x ; b ; x ]
  and t6 = (db 1) ^^ [ a ; b ; b ]
  and t7 = (db 1) ^^ [ x ; y ; z ] in
  "Tabling" >::: [
    "Write" >::
    (fun () ->
       assert (add table [t1] (ref (Table.Proved (ref [])))) ;
       assert (add table [t2] (ref (Table.Disproved (ref [])))) ;
       assert (not (add table [t3] (ref (Table.Proved (ref [])))))) ;
    "Read" >::
    (fun () ->
       assert (Some {contents=(Table.Proved {contents=[]})} = find table [t1]) ;
       assert (Some {contents=(Table.Disproved {contents=[]})} = find table [t2]) ;
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
  ]

(*
let translate_term ?head ?free_args ?expected_type ?free_types pre_term =
  match
    Environment.translate_term ?head ?free_args ?expected_type
      ?free_types pre_term ~k:(fun () -> None)
  with
    | Some (_,_,term) -> Some term
    | None -> None

let term_of_string s =
  let f lexbuf =
    Parsetree.(Parser.term_mode Lexer.token) lexbuf
  in
  match IO.Input.apply_on_string f s
  with `Term (_,preterm) -> translate_term preterm

let assert_eq_term =
  assert_equal ~cmp:eq ~printer:Ndcore.Pprint.term_to_string
 *)

(*
"Infix cons" >::
  (fun () ->
     assert_pprint_equal_parse "{member A (A :: B :: L)}") ;

"Simple object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{eval A B}") ;

"Compound object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{eval (abs R) (abs R)}") ;

"Implication object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{eval A B => typeof C D}") ;

"Lambda object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{x1\\typeof x1 A}") ;

"Pi lambda object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{pi x1\\typeof x1 A}") ;

"Pi lambda implies object statement" >::
  (fun () ->
     assert_pprint_equal_parse "{pi x1\\eval x1 A => typeof x1 B}") ;

"Lambda cons" >::
  (fun () ->
     assert_pprint_equal_parse "x1\\a :: b") ;

"Cons equality" >::
  (fun () ->
     assert_pprint_equal_parse "a :: b = a :: b") ;

"Smaller restriction" >::
  (fun () ->
     assert_pprint_equal_parse "{A}*") ;

"CoSmaller restriction" >::
  (fun () ->
     assert_pprint_equal_parse "foo +") ;

"CoEqual restriction" >::
  (fun () ->
     assert_pprint_equal_parse "foo #") ;

"Equal restriction" >::
  (fun () ->
     assert_pprint_equal_parse "{A}@") ;

"Second smaller restriction" >::
  (fun () ->
     assert_pprint_equal_parse "{A}**") ;

"Smaller restriction on predicate" >::
  (fun () ->
     assert_pprint_equal_parse "pred A B *") ;

"Implies statement" >::
  (fun () ->
     assert_pprint_equal_parse "{A} -> {B}") ;

"OR statement" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ {B}") ;

"AND statement" >::
  (fun () ->
     assert_pprint_equal_parse "{A} /\\ {B}") ;

"AND within OR" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ {B} /\\ {C}") ;

"OR statement on right side of arrow" >::
  (fun () ->
     assert_pprint_equal_parse "{A} -> {B} \\/ {C}") ;

"OR statement on left side of arrow" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ {B} -> {C}") ;

"Multiple OR statement" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ {B} \\/ {C}") ;

"Multiple OR statement (right assoc)" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ ({B} \\/ {C})") ;

"Arrow underneath OR" >::
  (fun () ->
     assert_pprint_equal_parse "{A} \\/ ({B} -> {C})") ;

"Forall" >::
  (fun () ->
     assert_pprint_equal_parse "forall A B, {C}") ;

"Exists" >::
  (fun () ->
     assert_pprint_equal_parse "exists A B, {C}") ;

"Exists on left of OR" >::
  (fun () ->
     assert_pprint_equal_parse "(exists A, {B}) \\/ {C}") ;

"OR underneath exists" >::
  (fun () ->
     assert_pprint_equal_parse "exists A, {B} \\/ {C}") ;

"Variable in context" >::
  (fun () ->
     assert_pprint_equal_parse "{L |- A}") ;

"Simple predicate" >::
  (fun () ->
     assert_pprint_equal_parse "head A B") ;

"Complex predicate" >::
  (fun () ->
     assert_pprint_equal_parse "head (hyp A) (conc B)") ;
 *)

let test =
  "Prover" >::: [
    tabling_test ;

    (*
    "Environment" >::: [
    ] ;

    "System" >::: [
    ] ;

    "Proof search" >::: [
    ] ;
     *)
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
        if List.exists (function RSuccess _ -> false | _ -> true)
             (run_test_tt ~verbose test)
        then exit 1
    | ids ->
        (* Running specific tests (given positions in the tree) so you
         * can trace exceptions or do whatever debugging you want. *)
        let display_test id =
          let rec get_test l n k t =
            match t with
              | TestCase _ -> if n = id then l,t else next l (n+1) k
              | TestLabel (l,t) -> get_test l n k t
              | TestList [] -> next l n k
              | TestList (hd::tl) -> get_test l n (tl::k) hd
          and next l n = function
            | [] -> raise Not_found
            | []::tl -> next l n tl
            | (hd1::tl1)::tl2 -> get_test l n (tl1::tl2) hd1
          in
          let lbl,test = get_test "" 0 [] test in
          Printf.printf "\nRunning test %d: %s%!" id lbl ;
          match run_test_tt test with
            | [RSuccess _] -> ()
            | [_] -> exit 1
            | _ -> assert false
        in
        List.iter display_test ids
