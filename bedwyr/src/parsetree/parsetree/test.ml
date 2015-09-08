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
open Preterm
open Typing


(* Simplified type checking, with no support for environment
 * (declared objects, bindings, etc). *)
let type_check_and_translate preterm expected_type =
  (* no constants or a predicates (built in or not) *)
  let typed_declared_obj ~instantiate_type:_ ?forbidden_stratum:_ _ = assert false
  (* no internal predicates *)
  and typed_intern_pred _ = assert false
  (* no declared types *)
  and kind_check ~obj ~p ty =
    kind_check ~obj ~p ty ~get_kind:(fun _ -> assert false)
  in
  let _,term =
    type_check_and_translate
      ~head:false
      ~free_args:[]
      ~free_types:(Hashtbl.create 10)
      preterm
      expected_type
      (typed_declared_obj,typed_intern_pred,kind_check)
  in
  term

let translate preterm =
  type_check_and_translate preterm (Type.fresh_var ())

let type_check preterm expected_type =
  ignore (type_check_and_translate preterm expected_type)

let pos = IO.Pos.dummy

let assert_eq_kind =
  assert_equal ~printer:Kind.to_string

let assert_eq_type =
  assert_equal ~cmp:(fun x y -> Type.compare x y = 0) ~printer:Type.to_string

let assert_eq_pterm =
  let printer pt = Ndcore.Pprint.term_to_string (translate pt) in
  assert_equal ~cmp:(fun x y -> compare x y = 0) ~printer

(* TODO add occurs-check, self-application, Andrew's tests (from Abella),
 * definite types, etc *)

let command_of_string s =
  let f lexbuf =
    Parser.definition_mode Lexer.token lexbuf
  in
  match IO.Input.apply_on_string f s with
    | `Command c -> c
    | _ -> assert_failure "Command not parsed as such"

let test =
  "Parse tree" >::: [
    "Lexing/Parsing" >::: [
      "Kind" >::: [
        "Binary type constructor" >::
          (fun () ->
             let str = "Kind t type -> type -> type." in
             match command_of_string str with
               | Command.Kind ([_,"t"],kind) ->
                   assert_eq_kind ~msg:"Wrong kind arrow precedence"
                     kind Kind.(arrow [ktype;ktype] ktype)
               | _ -> assert_failure "Type declaration ill-parsed") ;

        "No higher-order type constructors" >::
          (fun () ->
             let str = "Kind t (type -> type) -> type." in
             try ignore (command_of_string str) with
               | Parse_error _ -> ()
               | _ -> assert_failure "Higher-order type constructor not rejected by the parser") ;
      ] ;

      "Type" >::: [
        "Binary constructor" >::
          (fun () ->
             let str = "Type a prop -> prop -> prop." in
             match command_of_string str with
               | Command.Type ([_,"a"],ty) ->
                   assert_eq_type ~msg:"Wrong type arrow precedence"
                     ty Type.(arrow [prop;prop] prop)
               | _ -> assert_failure "Constant declaration ill-parsed") ;

        "Higher order constructor" >::
          (fun () ->
             let str = "Type a (prop -> prop) -> prop." in
             match command_of_string str with
               | Command.Type ([_,"a"],ty) ->
                   assert_eq_type ~msg:"Wrong type arrow precedence"
                     ty Type.(arrow [arrow [prop] prop] prop)
               | _ -> assert_failure "Constant declaration ill-parsed") ;

        "Tuple" >::
          (fun () ->
             let str = "Type a prop * prop -> prop * prop -> prop." in
             match command_of_string str with
               | Command.Type ([_,"a"],ty) ->
                   assert_eq_type ~msg:"Wrong type product precedence"
                     ty Type.(arrow [tuple prop prop [];tuple prop prop []] prop)
               | _ -> assert_failure "Constant declaration ill-parsed") ;

        "Application" >::
          (fun () ->
             let str = "Type a list prop." in
             match command_of_string str with
               | Command.Type ([_,"a"],ty) ->
                   assert_eq_type ~msg:"Wrong type application precedence"
                     ty Type.(const pos "list" [prop])
               | _ -> assert_failure "Constant declaration ill-parsed") ;
      ] ;

      "Define" >::: [
        "Empty definition" >::
          (fun () ->
             let str = "Define p : _ -> prop." in
             match command_of_string str with
               | Command.Def ([Normal,_,"p",_],[]) -> ()
               | _ -> assert_failure "Definition ill-parsed" ) ;

        "Empty clause" >::
          (fun () ->
             let str = "Define p : _ -> prop by p." in
             match command_of_string str with
               | Command.Def ([Normal,_,"p",_],[_,_,pt]) ->
                   assert_eq_pterm ~msg:"Wrong definition parsing"
                     pt (pre_true pos)
               | _ -> assert_failure "Definition ill-parsed" ) ;
      ] ;
    ] ;

    "Typing" >::: [
      "checking" >::: [
        "true (success)" >::
        (fun () -> type_check (pre_true pos) Type.prop) ;

        "true true (failure)" >::
        (fun () ->
           assert_bool "ill-typed application"
             (try
                type_check (pre_app pos (pre_true pos) [pre_true pos]) Type.prop ;
                false
              with
                | Term_typing_error _ -> true
                | _ -> false)) ;
      ] ;

      "environment" >::: Type.[
        ((get_to_string () (fresh_param ())) ^
         " <> " ^
         (get_to_string () (fresh_param ()))) >::
        (fun () ->
           assert_bool "polymorphic type variables should not be unifiable"
             (try
                let _ =
                  Unifier.(refine !global_unifier (fresh_param ()) (fresh_param ()))
                in false
              with
                | Unifier.Type_unification_error _ -> true
                | _ -> false )) ;

        ((get_to_string () (fresh_var ())) ^
         " ~~ " ^
         (get_to_string () (fresh_var ()))) >::
        (fun () ->
           assert_bool "type inference parameters should be unifiable"
             (try
                let _ =
                  Unifier.(refine !global_unifier (fresh_var ()) (fresh_var ()))
                in true
              with
                | Unifier.Type_unification_error _ -> false
                | _ -> true )) ;
      ] ;
    ] ;
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
