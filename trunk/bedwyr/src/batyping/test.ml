open OUnit
open Typing

(*let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let assert_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string*)

(*
let dummy_pos = (Lexing.dummy_pos, Lexing.dummy_pos)

let ucon ?(ty=fresh_tyvar ()) v =
  UCon(dummy_pos, v, ty)

let ulam v ?(ty=fresh_tyvar ()) t =
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

let test =
  "BaTyping" >:::
  [
    "environment" >:::
    [
      (type_to_string (fresh_tyvar ())) ^ " <> " ^ (type_to_string (fresh_tyvar ())) >::
      (fun () ->
         assert_bool "polymorphic type variables should not be unifiable"
           (try
              ignore
                (unify_constraint
                   !global_unifier
                   (fresh_tyvar ())
                   (fresh_tyvar ())) ;
              false
            with
              | Type_unification_error _ -> true
              | _ -> false )) ;

      (type_to_string (fresh_typaram ())) ^ " ~~ " ^ (type_to_string (fresh_typaram())) >::
      (fun () ->
         assert_bool "type inference parameters should be unifiable"
           (try
              ignore
                (unify_constraint
                   !global_unifier
                   (fresh_typaram ())
                   (fresh_typaram ())) ;
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
