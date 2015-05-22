(****************************************************************************)
(* Bedwyr -- prenex polymorphic typing testing                              *)
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

module Pos = struct
  type t = unit
  let dummy = ()
  let pp _ _ = ()
end
module Typing = Typing.Make (Pos)

open Typing

(*let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let assert_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string*)

(*
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
