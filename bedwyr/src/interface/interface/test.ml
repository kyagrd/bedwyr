(****************************************************************************)
(* Bedwyr -- input/output testing                                           *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open OUnit

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
  "Interface" >::: [
    "Read" >::: [] ;

    "Catch" >::: [] ;

    "Eval" >::: [] ;

    "Run" >::: [] ;

    "Config" >::: [] ;
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
