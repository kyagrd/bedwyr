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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open OUnit

module I = struct
  type pos = Lexing.position * Lexing.position
  let dummy_pos = Lexing.dummy_pos,Lexing.dummy_pos
end
module Typing = Typing.Make (I)


(* TODO add lots and lots *)

let test =
  "Input" >:::
  [
    "Lexer" >:::
    [
    ] ;
    "Parser" >:::
    [
    ] ;
    "Checker" >:::
    [
    ]
      (*
  "Parser" >:::
    [
      "Empty bodied clause" >::
        (fun () ->
           let str = "eval (abs R) (abs R)." in
             match parse_uclauses str with
               | [(t, [])] ->
                   assert_uterm_pprint_equal "eval (abs R) (abs R)" t
               | _ -> assert_failure "Pattern mismatch" ) ;

      "Typical clause" >::
        (fun () ->
           let str = "eval (app M N) V :- eval M (abs R), eval (R N) V." in
             match parse_uclauses str with
               | [(head, [b1; b2])] ->
                   assert_uterm_pprint_equal "eval (app M N) V" head ;
                   assert_uterm_pprint_equal "eval M (abs R)" b1 ;
                   assert_uterm_pprint_equal "eval (R N) V" b2 ;
               | _ -> assert_failure "Pattern mismatch" ) ;

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

    ]
       * *)
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
