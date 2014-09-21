(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2012 Nadathur, Linnell, Baelde, Gacek, Heath          *)
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

(* No normalization, plain observational equality. *)
let assert_equal x y =
  assert_equal
    ~cmp:eq
    ~printer:(fun t -> Pprint.term_to_string_full ~generic:[] ~bound:[] t)
    x y
(* No normalization, equivariance checking. *)
and assert_eqvt x y =
  assert_equal
    ~cmp:eqvt
    ~printer:(fun t -> Pprint.term_to_string_full ~generic:[] ~bound:[] t)
    x y

(* Normalized form equality. *)
and assert_equal2 a b c d =
  let eq a b = eq (Norm.deep_norm a) (Norm.deep_norm b) in
  assert_equal
    ~cmp:(fun (a,c) (b,d) -> eq a b && eq c d)
    ~printer:(fun (a,b) ->
                (Pprint.term_to_string a) ^ " and " ^
                  (Pprint.term_to_string b) ^ "\n")
    (a,c) (b,d)
(* Idem. *)
and assert_equal_norm x y =
  let eq a b = eq (Norm.deep_norm a) (Norm.deep_norm b) in
  assert_equal
    ~cmp:eq
    ~printer:Pprint.term_to_string x y

let unify =
  let module Unify =
    Unify.Make (struct
                  let instantiatable = Logic
                  let constant_like  = Eigen
                end)
  in
  Unify.pattern_unify

(* Extracting a variable at some position in a term,
 * used when we know a variable should be there, but don't know what it is
 * since it's fresh. *)
type path = L | A | H
let rec extract path t =
  let hd,tl = match path with h::t -> h,t | [] -> assert false in
  match hd,!!t with
    | L,Lam (_,t) -> extract tl t
    | A,App (_,l) -> extract tl (List.hd l)
    | H,App (t,_) -> t
    | _,_ -> atom "not_found"

let fresh ~ts ~lts ~name ~tag = fresh ~ts ~lts ~name tag

let var ?(lts=0) nm ts = fresh ~tag:Logic ~name:nm ~ts:ts ~lts
let eig ?(lts=0) nm ts = fresh ~tag:Eigen ~name:nm ~ts:ts ~lts
let const nm = fresh ~tag:Constant ~name:nm ~ts:0 ~lts:0

let add index terms =
  let add,_ = Index.access ~switch_vars:false index terms in
  add

let find index terms =
  let _,found = Index.access ~switch_vars:false index terms in
  found

let filter_count ?(o=0) ?(e=0) ?(u=0) index terms =
  let over = ref 0 in
  let exact = ref 0 in
  let under = ref 0 in
  Index.filter
    ~switch_vars:false index terms
    (fun _ ms -> match ms with
         | Index.Over -> incr over
         | Index.Exact -> incr exact
         | Index.Under _ -> incr under) ;
  assert (!over = o) ;
  assert (!exact = e) ;
  assert (!under = u)

let test =
  "NdCore" >:::
  [
    "Term" >:::
    [
      (* Test that there are no empty Term.Binder *)
      "[exists, a]" >::
      (fun () ->
         let a = const "a" in
         let t = 0 &/ a in
         assert_equal a t) ;

      (* Test that Term.Binder is flattened *)
      "[forall x, forall y, x]" >::
      (fun () ->
         let t = 1 @/ (1 @/ (db 1)) in
         assert_equal (2 @/ (db 1)) t) ;

      (* Test that there are no empty Term.Lam *)
      "[[]\\ a]" >::
      (fun () ->
         let a = const "a" in
         let t = 0 // a in
         assert_equal a t) ;

      (* Test that Term.Lam is flattened *)
      "[x\\ (y\\ x)]" >::
      (fun () ->
         let t = 1 // (1 // (db 1)) in
         assert_equal (2 // (db 1)) t) ;

      (* Test that Term.App is flattened *)
      "[(a b) c]" >::
      (fun () ->
         let a = const "a" in
         let b = const "b" in
         let c = const "c" in
         let t = (a ^^ [b]) ^^ [c] in
         assert_equal (a ^^ [b ; c]) t) ;

      (* Test equivariant checking *)
      "[n1]" >::
      (fun () ->
         assert_eqvt (nabla 1) (nabla 2)) ;

      "[exists x, f x y]" >::
      (fun () ->
         let f = const "f" in
         let x = var "x" 1 in
         let y = var "y" 1 in
         let t = x &// (f ^^ [x;y]) in
         assert_equal (1 &/ (f ^^ [db 1;y])) t)

      (* TODO tests for abstract, get_vars and *_copy_* *)
    ] ;

    "Norm" >:::
    [
      "[(x\\ x) c]" >::
      (fun () ->
         let c = const "c" in
         let t = (1 // db 1) ^^ [c] in
         assert_equal c (Norm.hnorm t)) ;

      "[(x\\ y\\ x) a b]" >::
      (fun () ->
         let a = const "a" in
         let b = const "b" in
         let t = (2 // db 2) ^^ [a; b] in
         assert_equal a (Norm.hnorm t)) ;

      "[(x\\ y\\ y) a b]" >::
      (fun () ->
         let a = const "a" in
         let b = const "b" in
         let t = (2 // db 1) ^^ [a; b] in
         assert_equal b (Norm.hnorm t)) ;

      "[(x\\ y\\ z\\ x)]" >::
      (fun () ->
         let t = (3 // db 3) in
         assert_equal (3 // db 3) (Norm.hnorm t)) ;

      "[(x\\ y\\ z\\ x) a]" >::
      (fun () ->
         let a = const "a" in
         let t = (3 // db 3) ^^ [a] in
         assert_equal (2 // a) (Norm.hnorm t)) ;

      "[(x\\ x (x\\ x)) (x\\ y\\ x y)]" >::
      (fun () ->
         let t = 1 // (db 1 ^^ [1 // db 1]) in
         let t = t ^^ [ 2 // (db 2 ^^ [db 1]) ] in
         assert_equal (1 // db 1)  (Norm.hnorm t)) ;

      "[(x\\ x (x\\ x)) (x\\ y\\ x y) c]" >::
      (fun () ->
         let c = const "c" in
         let t = 1 // (db 1 ^^ [1 // db 1]) in
         let t = t ^^ [ 2 // (db 2 ^^ [db 1]) ; c ] in
         assert_equal c (Norm.hnorm t)) ;

      "[x\\ c x]" >::
      (fun () ->
         let c = const "c" in
         let t = 1 // (c ^^ [db 1]) in
         assert_equal (1 // (c ^^ [db 1])) (Norm.hnorm t)) ;

      (* This test needs deep normalization
       * to get rid of a suspension on y. *)
      "[x\\ y\\ ((a\\ b\\ a b) x y)]" >::
      (fun () ->
         let ii = 2 // (db 2 ^^ [db 1]) in
         let t = 2 // (ii ^^ [db 2;db 1]) in
         assert_equal (2 // (db 2 ^^ [db 1])) (Norm.deep_norm t)) ;
    ] ;

    "Unif" >:::
    [
      (********************************************
       * Tests from Nadathur's SML implementation *
       ********************************************)

      (* Example 1, simple test involving abstractions *)
      "[x\\ x = x\\ M x]" >::
      (fun () ->
         let t1 = 1 // db 1 in
         let m = var "m" 1 in
         let t2 = 1 // ( m ^^ [ db 1 ] ) in
         unify t1 t2 ;
         assert_equal_norm (1 // db 1) m) ;

      (* Example 2, adds descending into constructors *)
      "[x\\ c x = x\\ c (N x)]" >::
      (fun () ->
         let n = var "n" 1 in
         let c = const "c" in
         let t1 = 1 // (c ^^ [ db 1 ]) in
         let t2 = 1 // (c ^^ [ n ^^ [ db 1 ] ]) in
         unify t1 t2 ;
         assert_equal_norm (1 // db 1) n) ;

      (* Example 3, needs eta expanding on the fly *)
      "[x\\ y\\ c y x = N]" >::
      (fun () ->
         let n = var "n" 1 in
         let c = const "c" in
         let t = 2 // (c ^^ [ db 1 ; db 2 ]) in
         unify t n ;
         assert_equal_norm (2 // (c ^^ [ db 1 ; db 2 ])) n) ;

      (* Example 4, on-the-fly eta, constructors at top-level *)
      "[x\\ y\\ c x y = x\\ c (N x)]" >::
      (fun () ->
         let n = var "n" 1 in
         let c = const "c" in
         unify (2 // (c ^^ [db 2;db 1])) (1 // (c ^^ [n ^^ [db 1]])) ;
         assert_equal_norm (1 // db 1) n) ;

      (* Example 5, flex-flex case where we need to raise & prune *)
      "[X1 a2 b3 = Y2 b3 c3]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         let t1 = x ^^ [ a ; b ] in
         let t2 = y ^^ [ b ; c ] in
         unify t1 t2 ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;H] x in
           match observe e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith "X should match x\\y\\ H ..."
         in
         assert_equal2
           (2 // (h ^^ [ db 2 ; db 1 ])) x
           (2 // (h ^^ [ a ; db 2 ])) y) ;

      (* Example 6, flex-rigid case involving raise & prune relative to an
       * embedded flex term. *)
      "[X1 a2 b3 = c1 (Y2 b3 c3)]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 1 in
         let c3 = eig "c" 3 in
         unify (x ^^ [a;b]) (c ^^ [y ^^ [b;c3]]) ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;A;H] x in
           match !!e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith "X should match x\\y\\ _ H .."
         in
         assert_equal2
           (2 // (c ^^ [h^^[db 2;db 1]])) x
           (2 // (h ^^ [a;db 2])) y) ;

      (* Example 7, multiple occurences *)
      "[c1 (X1 a2 b3) (X b3 d2) = c1 (Y2 b3 c3) (b3 d2)]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         let d = eig "d" 2 in
         unify
           (c ^^ [ x ^^ [a;b] ; x ^^ [b;d] ])
           (c ^^ [ y ^^ [b;c] ; b ^^ [d] ]) ;
         assert_equal2
           (2 // (db 2 ^^ [db 1])) x
           (2 // (a ^^ [db 2])) y) ;

      (* Example 8, multiple occurences with a bound var as the rigid part
       * instead of a constant *)
      "[x\\ c1 (X1 a2 b3) (X x d2) = x\\ c1 (Y2 b3 c3) (x d2)]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let d = eig "d" 2 in
         let c = eig "c" 3 in
         unify
           (1 // (c ^^ [ x ^^ [a;b] ; x ^^ [db 1;d]]))
           (1 // (c ^^ [ y ^^ [b;c] ; db 1 ^^ [d] ])) ;
         assert_equal2
           (2 // (db 2 ^^ [db 1])) x
           (2 // (a ^^ [db 2])) y) ;

      (* Example 9, flex-flex with same var at both heads *)
      "[X1 a2 b3 c3 = X1 c3 b3 a2]" >::
      (fun () ->
         let x = var "x" 1 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         unify (x ^^ [a;b;c]) (x ^^ [c;b;a]) ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;H] x in
           match !!e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith "X should match x\\y\\z\\ H ..."
         in
         assert_equal_norm (3 // (h^^[db 2])) x) ;

      (* Example 10, failure due to OccursCheck
       * TODO Are the two different timestamps wanted for c ? *)
      "[X1 a2 b3 != c1 (X1 b3 c3)]" >::
      (fun () ->
         let x = var "x" 1 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c1 = eig "c" 1 in
         let c3 = eig "c" 3 in
         try
           unify (x ^^ [a;b]) (c1 ^^ [x ^^ [b;c3]]) ;
           "Expected OccursCheck" @? false
         with Unify.Error Unify.OccursCheck -> ()) ;

      (* 10bis: quantifier dependency violation -- raise OccursCheck too *)
      "[X1 a2 b3 != c3 (X b c)]" >::
      (fun () ->
         let x = var "x" 1 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         try
           unify (x ^^ [a;b]) (c ^^ [x ^^ [b;c]]) ;
           "Expected OccursCheck" @? false
         with Unify.Error Unify.OccursCheck -> ()) ;

      (* Example 11, flex-flex without raising *)
      "[X1 a2 b3 = Y1 b3 c3]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 1 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         unify (x ^^ [a;b]) (y ^^ [b;c]) ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;H] x in
           match !!e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith
                      (Printf.sprintf "X=%s should match Lam (_,(App H _))"
                         (Pprint.term_to_string x))
         in
         assert_equal2
           (2 // (h ^^ [db 1])) x
           (2 // (h ^^ [db 2])) y) ;

      (* Example 12, flex-flex with raising on one var, pruning on the other *)
      "[X1 a2 b3 c3 = Y2 c3]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         unify (x ^^ [a;b;c]) (y ^^ [c]) ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;H] x in
           match !!e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith "X should match x\\y\\z\\ H ..."
         in
         assert_equal2
           (3 // (h ^^ [db 3;db 1])) x
           (1 // (h ^^ [a;db 1])) y) ;

      (* Example 13, flex-rigid where rigid has to be abstracted *)
      "[X1 a2 b3 = a2 (Y2 b3 c3)]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         unify (x ^^ [a;b]) (a ^^ [y ^^ [b;c]]) ;
         let h =
           let x = Norm.hnorm x in
           let e = extract [L;A;H] x in
           match !!e with
             | Var {ts=1;tag=Logic} -> e
             | _ -> failwith "X should match x\\y\\ _ (H ..) .."
         in
         assert_equal2
           (2 // (db 2 ^^ [h ^^ [db 2 ; db 1]])) x
           (2 // (h ^^ [a ; db 2])) y) ;

      (* Example 14, OccursCheck *)
      "[X1 a2 b3 != d3 (Y2 b3 c3)]" >::
      (fun () ->
         let x = var "x" 1 in
         let y = var "y" 2 in
         let a = eig "a" 2 in
         let b = eig "b" 3 in
         let c = eig "c" 3 in
         let d = eig "d" 3 in
         try
           unify (x ^^ [a;b]) (d ^^ [y ^^ [b;c]]) ;
           "Expected OccursCheck" @? false
         with Unify.Error Unify.OccursCheck -> ()) ;

      (* Example 15, unifying constants *)
      "[a = a]" >::
      (fun () ->
         unify (atom "a") (atom "a")) ;

      (* Example 16, unifying rigid terms *)
      "[x\\ a x b = x\\ a x b]" >::
      (fun () ->
         let a = const "a" in
         let b = const "b" in
         let t = 1 // ( a ^^ [ db 1 ; b ] ) in
         unify t t) ;

      (*****************************
       * End of Gopalan's examples *
       ****************************)

      "[f a a = f X X]" >::
      (fun () ->
         let a = eig "a" 1 in
         let f = const "f" in
         let x = var "x" 2 in
         unify (f ^^ [x;x]) (f ^^ [a;a])) ;

      "[x\\x1\\ P x = x\\ Q x]" >::
      (fun () ->
         let p = var "P" 1 in
         let q = var "Q" 1 in
         unify (2 // (p ^^ [db 2])) (1 // (q ^^ [db 1])) ;
         assert_equal_norm (2 // (p ^^ [db 2])) q) ;

      (* This one used to fail, I don't remember having fixed it consciously.. *)
      "[T = a X, T = a Y, Y = T]" >::
      (fun () ->
         let t = var "T" 1 in
         let x = var "X" 1 in
         let y = var "Y" 1 in
         let a = const "a" in
         let a x = a ^^ [x] in
         unify t (a x) ;
         unify t (a y) ;
         try unify y t ; assert false
         with Unify.Error _ -> ()) ;

      (* This one used to fail, but the bug is fixed *)
      "[x\\y\\ H1 x = x\\y\\ G2 x]" >::
      (fun () ->
         let h = var "H" 1 in
         let g = var "G" 2 in
         (* Different timestamps matter *)
         unify (2// (h ^^ [db 2])) (2// (g ^^ [db 2])) ;
         assert_equal_norm (g^^[db 2]) (h^^[db 2])) ;

      "[X1 = y2]" >::
      (fun () ->
         let x = var "X" 1 in
         let y = eig "y" 2 in
         try unify x y ; assert false
         with Unify.Error _ -> ()) ;

      "[X^0 n1 = Y^0]" >::
      (fun () ->
         let x = var "X" 0 in
         let y = var "Y" 0 in
         unify (x ^^ [nabla 1]) y ;
         assert_equal_norm (1 // y) x) ;

      "[X^0 n1 = Y^1]" >::
      (fun () ->
         let x = var "X" 0 in
         let y = fresh ~name:"Y" ~tag:Logic ~lts:1 ~ts:0 in
         unify (x ^^ [nabla 1]) y ;
         assert_equal_norm y (x ^^ [nabla 1]) ;
         match !!x with
           | Var v -> ()
           | _ -> assert_equal_norm (var "a_variable" 0) x) ;

      "[X^0 = Y^1]" >::
      (fun () ->
         let x = var "X" 0 in
         let y = var "Y" 1 in
         unify x y ;
         match !!x,!!y with
           | Var {ts=0}, Var {ts=0} -> ()
           | _ -> assert false) ;

      "[X^0 = Y^0/1]" >::
      (fun () ->
         let x = var "X" 0 in
         let y = fresh ~name:"Y" ~tag:Logic ~lts:1 ~ts:0 in
         unify x y ;
         match !!x,!!y with
           | Var {lts=0}, Var {lts=0} -> ()
           | _ -> assert false) ;

      "[X^0 = c Y^1]" >::
      (fun () ->
         let x = var "X" 0 in
         let c = fresh ~tag:Constant ~name:"c" ~ts:0 ~lts:0 in
         let y = fresh ~tag:Logic ~name:"Y" ~lts:1 ~ts:0 in
         unify x (c ^^ [y]) ;
         match !!y with
           | Var {lts=0} -> () | _ -> Pprint.print_term y ; assert false) ;

      "[X^0 n1 n2 = c Y^2 = c n2]" >::
      (fun () ->
         let x = var "X" 0 in
         let y = fresh ~tag:Logic ~name:"Y" ~lts:2 ~ts:0 in
         let c = const "c" in
         let t = x ^^ [nabla 1 ; nabla 2] in
         unify t (c ^^ [y]) ;
         unify (Norm.hnorm t) (c ^^ [nabla 2]))
    ] ;

    "Indexing" >:::
    [
      "Ground terms" >::
      (fun () ->
         let d = db in
         let t1 = ((d 1) ^^ [ d 2 ; (d 1) ^^ [ d 2 ; d 2 ] ]) in
         let t2 = ((d 1) ^^ [ d 3 ; (d 1) ^^ [ d 4 ; d 5 ] ]) in
         let t3 = ((d 1) ^^ [ d 3 ; (d 1) ^^ [ d 4 ; d 4 ] ]) in
         let t4 = ((d 1) ^^ [ d 3 ; d 2 ]) in
         let i0 = Index.empty in
         let i1 = add i0 [t1] 10 in
         let i2 = add i1 [t2] 20 in
         let i3 = add i2 [t3] 30 in
         assert (None = find i3 [t4]) ;
         let i4 = add i3 [t4] 40 in
         assert (Some 40 = find i4 [t4]) ;
         assert (Some 20 = find i2 [t2]) ;
         assert (Some 20 = find i4 [t2]) ;
         let i5 = add i4 [t4] 42 in
         assert (Some 42 = find i5 [t4])) ;

      "Eigen variables" >:::
      (let x = eig "x" 0 in
       let y = eig "y" 0 in
       let z = eig "z" 0 in
       let t1 = (db 1) ^^ [ x ; y ; y ] in
       let t2 = (db 1) ^^ [ y ; y ; y ] in
       let a = const "a" in
       let b = const "b" in
       let t3 = (db 1) ^^ [ a ; x ; x ] in
       let t4 = (db 1) ^^ [ x ; b ; y ] in
       [
         "Plain" >::
         (fun () ->
            let index = add (add Index.empty [t1] 1) [t2] 2 in
            assert (Some 1 = find index [(db 1) ^^ [ y ; z ; z ]]) ;
            assert (Some 2 = find index [(db 1) ^^ [ x ; x ; x ]]) ;
            assert (None = find index [(db 1) ^^ [ x ; z ; x ]]) ;
            let index = add (add index [t3] 3) [t4] 4 in
            assert (Some 3 = find index [t3]) ;
            assert (Some 4 = find index [t4])) ;

         "Match with eigen variables" >::
         (fun () ->
            let index = add (add Index.empty [t1] 1) [t2] 2 in
            filter_count index [(db 1) ^^ [ y ; z ; z ]] ~e:1 ~u:1 ;
            filter_count index [(db 1) ^^ [ z ; z ; z ]] ~o:1 ~e:1 ;
            filter_count index [(db 1) ^^ [ x ; y ; z ]] ~u:2 ;
            filter_count index [(db 1) ^^ [ x ; x ; y ]] ~u:1 ;
            let index = add (add index [t3] 3) [t4] 4 in
            filter_count index [(db 1) ^^ [ a ; x ; y ]] ~u:1 ;
            filter_count index [(db 1) ^^ [ x ; b ; x ]] ~o:1) ;

         "Match with constants" >::
         (fun () ->
            let index = add (add Index.empty [t3] 3) [t4] 4 in
            filter_count index [(db 1) ^^ [ x ; y ; y ]] ~u:1 ;
            filter_count index [(db 1) ^^ [ a ; b ; b ]] ~o:2 ;
            filter_count index [(db 1) ^^ [ a ; a ; b ]] ~o:0 ;
            let t5 = (db 1) ^^ [ a ; a ; b ] in
            let index = add Index.empty [t5] 5 in
            filter_count index [(db 1) ^^ [ a ; x ; x ]] ~u:0) ;

         "Mixed with nominal variables" >::
         (fun () ->
            let x = eig "x" ~lts:0 0 in
            let y = eig "y" ~lts:1 0 in
            let z = eig "z" ~lts:2 0 in
            let index = add Index.empty [(db 1) ^^ [ x ; y ]] 42 in
            assert (None = find index [(db 1) ^^ [ y ; z ]]) ;
            assert (None = find index [(db 1) ^^ [ y ; x ]])) ;
       ]) ;

      "Nominal variables" >:::
      [
        "Bug in equivariant indexing" >::
        (fun () ->
           let index = add Index.empty [nabla 1 ; nabla 2] 42 in
           assert (Some 42 = find index [nabla 3 ; nabla 1]) ;
           let () = Index.eqvt_index := false in
           assert (None = find index [nabla 3 ; nabla 1])) ;
      ] ;

      "Logic variables" >:::
      [
        (*
        "" >::
        (fun () -> ())
         *)
      ]
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
