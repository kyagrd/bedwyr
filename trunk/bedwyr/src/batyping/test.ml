(****************************************************************************)
(* Prenex polymorphic typing                                                *)
(* Copyright (C) 2012-2013 Andrew Gacek, Quentin Heath                      *)
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

module I = struct
  type pos = unit * unit
  let dummy_pos = (),()
end
module Typing = Typing.Make (I)

open Typing

(*let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let assert_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string*)

(*
let dummy_pos = (Lexing.dummy_pos, Lexing.dummy_pos)

let ucon ?(ty=fresh_typaram ()) v =
  UCon(dummy_pos, v, ty)

let ulam v ?(ty=fresh_typaram ()) t =
  ULam(dummy_pos, v, ty, t)

let uapp t1 t2 =
  UApp(dummy_pos, t1, t2)

let upred t =
  UPred(t, Irrelevant)

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm
 *)

(* TODO add occurs-check, self-application, Andrew's tests (from Abella),
 * definite types, etc *)

let test =
  "BaTyping" >:::
  [
    "environment" >:::
    [
      (get_type_to_string () (fresh_typaram ())) ^
        " <> " ^
        (get_type_to_string () (fresh_typaram ())) >::
      (fun () ->
         assert_bool "polymorphic type variables should not be unifiable"
           (try
              ignore
                (unify_constraint
                   !global_unifier
                   (fresh_typaram ())
                   (fresh_typaram ())) ;
              false
            with
              | Type_unification_error _ -> true
              | _ -> false )) ;

      (get_type_to_string () (fresh_tyvar ())) ^
        " ~~ " ^
        (get_type_to_string () (fresh_tyvar())) >::
      (fun () ->
         assert_bool "type inference parameters should be unifiable"
           (try
              ignore
                (unify_constraint
                   !global_unifier
                   (fresh_tyvar ())
                   (fresh_tyvar ())) ;
              true
            with
              | Type_unification_error _ -> false
              | _ -> true ))
    ]
    (*[
      "Should not allow pi quantification over o in clause" >::
        (fun () ->
           let uclause =
             (ucon "a", [uapp (ucon "pi") (ulam "x" ~ty:oty (ucon "x"))])
           in
             assert_raises
               (Failure "Cannot quantify over type o in the specification logic")
               (fun () -> type_uclause ~sr:!sr ~sign:!sign uclause)
        );

      "Should not allow quantification over prop in definition" >::
        (fun () ->
           let udef =
             (UTrue, UBinding(Forall, [("x", propty)], upred (ucon "x")))
           in
             assert_raises
               (Failure "Cannot quantify over type prop")
               (fun () -> type_udef ~sr:!sr ~sign:!sign udef)
        );

      "Should not allow quantification over prop in metaterm" >::
        (fun () ->
           let umetaterm =
             UBinding(Forall, [("x", propty)], upred (ucon "x"))
           in
             assert_raises
               (Failure "Cannot quantify over type prop")
               (fun () -> type_umetaterm ~sr:!sr ~sign:!sign umetaterm)
        );

      "Should replace underscores in clauses with fresh names" >::
        (fun () ->
           let uclause =
             (uapp (ucon "p1") (ucon "X"),
              [uapp (uapp (ucon "pr") (ucon "_")) (ucon "_")])
           in
             match type_uclause ~sr:!sr ~sign:!sign uclause with
               | _, p::_ ->
                   assert_term_pprint_equal "pr X1 X2" p
               | _ -> assert false
        );
    ]*)
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
