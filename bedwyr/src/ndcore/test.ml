
open OUnit
open Term
open Term.Notations

let eq a b = Term.eq (Norm.deep_norm a) (Norm.deep_norm b)

let equal2 a b c d =
  assert_equal
    ~cmp:(fun (a,c) (b,d) -> eq a b && eq c d)
    ~printer:(fun (a,b) ->
                (Pprint.term_to_string a) ^ " and " ^
                  (Pprint.term_to_string b) ^ "\n")
    (a,c) (b,d)

let assert_equal = assert_equal ~cmp:eq ~printer:Pprint.term_to_string

(* Extracting a variable at some position in a term,
 * used when we know a variable should be there, but don't know what it is
 * since it's fresh. *)
type path = L | A | H
let rec extract path t =
  let hd,tl = match path with h::t -> h,t | [] -> assert false in
    match !!t with
      | Lam (_,t) when hd = L -> extract tl t
      | App (_,l) when hd = A -> extract tl (List.nth l 0)
      | App (t,_) when hd = H -> !!t
      | _ -> Const ("notfound",0,Unset)

let test =
  "Tests" >:::
  [
    "Norm" >:::
    [
      "[(x\\ x) c]" >::
      (fun () ->
         let c = const "c" 1 in
         let t = (1 // db 1) ^^ [c] in
         let t = Norm.norm t in
           assert_equal c t) ;

      "[(x\\ x (x\\ x)) (x\\y\\ x y) c]" >::
      (fun () ->
         let c = const "c" 1 in
         let t = 1 // (db 1 ^^ [1 // db 1]) in
         let t = t ^^ [ 2 // (db 2 ^^ [db 1]) ; c ] in
         let t = Norm.norm t in
           assert_equal c t) ;

      "[x\\ c x]" >::
      (fun () ->
         let c = const "c" 1 in
         let t = 1 // (c ^^ [db 1]) in
         let t = Norm.norm t in
           assert_equal (1 // (c ^^ [db 1])) t) ;

      (* This is a normalization pb which appeared to be causing
       * a failure in an unification test below. *)
      "[x\\y\\((a\\b\\ a b) x y)]" >::
      (fun () ->
         let ii = 2 // (db 2 ^^ [db 1]) in
         let t = 2 // (ii ^^ [db 2;db 1]) in
         let t = Norm.norm t in
           assert_equal (2//(db 2 ^^ [db 1])) t) ;
    ] ;

    (* Tests from Nadathur's SML implementation ---------------------------- *)
    "Unif" >:::
    [

    (* Example 1, simple test involving abstractions *)
    "[x\\ x = x\\ M x]" >::
    (fun () ->
       let t1 = 1 // db 1 in
       let m = var "m" 1 in
       let t2 = 1 // ( m ^^ [ db 1 ] ) in
         Unify.unify t1 t2 ;
         assert_equal (1 // db 1) m) ;

    (* Example 2, adds descending into constructors *)
    "[x\\ c x = x\\ c (N x)]" >::
    (fun () ->
       let n = var "n" 1 in
       let c = const "c" 1 in
       let t1 = 1 // (c ^^ [ db 1 ]) in
       let t2 = 1 // (c ^^ [ n ^^ [ db 1 ] ]) in
         Unify.unify t1 t2 ;
         assert_equal (1 // db 1) n) ;

    (* Example 3, needs eta expanding on the fly *)
    "[x\\y\\ c y x = N]" >::
    (fun () ->
       let n = var "n" 1 in
       let c = const "c" 1 in
       let t = 2 // (c ^^ [ db 1 ; db 2 ]) in
         Unify.unify t n ;
         assert_equal (2 // (c ^^ [ db 1 ; db 2 ])) n) ;

    (* Example 4, on-the-fly eta, constructors at top-level *)
    "[x\\y\\ c x y = x\\ c (N x)]" >::
    (fun () ->
       let n = var "n" 1 in
       let c = const "c" 1 in
         Unify.unify (2 // (c ^^ [db 2;db 1])) (1 // (c ^^ [n ^^ [db 1]])) ;
         assert_equal (1 // db 1) n) ;

    (* Example 5, flex-flex case where we need to raise & prune *)
    "[X1 a2 b3 = Y2 b3 c3]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
       let t1 = x ^^ [ a ; b ] in
       let t2 = y ^^ [ b ; c ] in
         Unify.unify t1 t2 ;
         let h =
           let x = Norm.norm x in
           match extract [L;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith "X should match x\\y\\ H ..."
         in
           equal2
             (2 // (h ^^ [ db 2 ; db 1 ])) x
             (2 // (h ^^ [ a ; db 2 ])) y) ;

    (* Example 6, flex-rigid case involving raise & prine relative to an
     * embedded flex term. *)
    "[X1 a2 b3 = c1 (Y2 b3 c3)]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 1 in
       let c3 = const "c" 3 in
         Unify.unify (x ^^ [a;b]) (c ^^ [y ^^ [b;c3]]) ;
         let h =
           let x = Norm.norm x in
           match extract [L;A;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith "X should match x\\y\\ _ H .."
         in
           equal2
             (2 // (c ^^ [h^^[db 2;db 1]])) x
             (2 // (h ^^ [a;db 2])) y) ;

    (* Example 7, multiple occurences *)
    "[c1 (X1 a2 b3) (X b3 d2) = c1 (Y2 b3 c3) (b3 d2)]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
       let d = const "d" 2 in
         Unify.unify
           (c ^^ [ x ^^ [a;b] ; x ^^ [b;d] ])
           (c ^^ [ y ^^ [b;c] ; b ^^ [d] ]) ;
         equal2
           (2 // (db 2 ^^ [db 1])) x
           (2 // (a ^^ [db 2])) y) ;

    (* Example 8, multiple occurences with a bound var as the rigid part
     * instead of a constant *)
    "[x\\ c1 (X1 a2 b3) (X x d2) = x\\ c1 (Y2 b3 c3) (x d2)]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let d = const "d" 2 in
       let c = const "c" 3 in
         Unify.unify
           (1 // (c ^^ [ x ^^ [a;b] ; x ^^ [db 1;d]]))
           (1 // (c ^^ [ y ^^ [b;c] ; db 1 ^^ [d] ])) ;
         equal2
           (2 // (db 2 ^^ [db 1])) x
           (2 // (a ^^ [db 2])) y) ;

    (* Example 9, flex-flex with same var at both heads *)
    "[X1 a2 b3 c3 = X1 c3 b3 a2]" >::
    (fun () ->
       let x = var "x" 1 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
         Unify.unify (x ^^ [a;b;c]) (x ^^ [c;b;a]) ;
         let h =
           let x = Norm.norm x in
           match extract [L;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith "X should match x\\y\\z\\ H ..."
         in
           assert_equal (3 // (h^^[db 2])) x) ;

    (* Example 10, failure due to OccursCheck
     * TODO Are the two different timestamps wanted for c ? *)
    "[X1 a2 b3 != c1 (X1 b3 c3)]" >::
    (fun () ->
       let x = var "x" 1 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c1 = const "c" 1 in
       let c3 = const "c" 3 in
         try
           Unify.unify (x ^^ [a;b]) (c1 ^^ [x ^^ [b;c3]]) ;
           "Expected OccursCheck" @? false
         with
           | Unify.Error Unify.OccursCheck -> ()) ;

    (* 10bis: quantifier dependency violation -- raise OccursCheck too *)
    "[X1 a2 b3 != c3 (X b c)]" >::
    (fun () ->
       let x = var "x" 1 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
         try
           Unify.unify (x ^^ [a;b]) (c ^^ [x ^^ [b;c]]) ;
           "Expected OccursCheck" @? false
         with
           | Unify.Error Unify.OccursCheck -> ()) ;

    (* Example 11, flex-flex without raising *)
    "[X1 a2 b3 = Y1 b3 c3]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 1 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
         Unify.unify (x ^^ [a;b]) (y ^^ [b;c]) ;
         let h =
           let x = Norm.norm x in
           match extract [L;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith
                      (Printf.sprintf "X=%s should match Lam (_,(App H _))"
                         (Pprint.term_to_string x))
         in
           equal2
             (2 // (h ^^ [db 1])) x
             (2 // (h ^^ [db 2])) y) ;

    (* Example 12, flex-flex with raising on one var, pruning on the other *)
    "[X1 a2 b3 c3 = Y2 c3]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
         Unify.unify (x ^^ [a;b;c]) (y ^^ [c]) ;
         let h =
           let x = Norm.norm x in
           match extract [L;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith "X should match x\\y\\z\\ H ..."
         in
           equal2
             (3 // (h ^^ [db 3;db 1])) x
             (1 // (h ^^ [a;db 1])) y) ;

    (* Example 13, flex-rigid where rigid has to be abstracted *)
    "[X1 a2 b3 = a2 (Y2 b3 c3)]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
         Unify.unify (x ^^ [a;b]) (a ^^ [y ^^ [b;c]]) ;
         let h =
           let x = Norm.norm x in
           match extract [L;A;H] x with
             | Var (h,1,Unset) -> var h 1
             | _ -> failwith "X should match x\\y\\ _ (H ..) .."
         in
           equal2
             (2 // (db 2 ^^ [h ^^ [db 2 ; db 1]])) x
             (2 // (h ^^ [a ; db 2])) y) ;

    (* Example 14, OccursCheck *)
    "[X1 a2 b3 != d3 (Y2 b3 c3)]" >::
    (fun () ->
       let x = var "x" 1 in
       let y = var "y" 2 in
       let a = const "a" 2 in
       let b = const "b" 3 in
       let c = const "c" 3 in
       let d = const "d" 3 in
         try
           Unify.unify (x ^^ [a;b]) (d ^^ [y ^^ [b;c]]) ;
           "Expected OccursCheck" @? false
         with
           | Unify.Error Unify.OccursCheck -> ()) ;

    "[a = a]" >::
    (fun () ->
       Unify.unify (const "a" 1) (const "a" 1)) ;

    "[x\\ a x b = x\\ a x b]" >::
    (fun () ->
       let a = const "a" 1 in
       let b = const "b" 1 in
       let t = 1 // ( a ^^ [ db 1 ; b ] ) in
         Unify.unify t t) ;

    (* End of Gopalan's examples *)

    "[f\\ a a = f\\ X X]" >::
    (fun () ->
       let a = const "a" 2 in
       let f = const "f" 1 in
       let x = var "x" 3 in
         Unify.unify (f ^^ [x;x]) (f ^^ [a;a])) ;

    "[x\\x1\\ P x = x\\ Q x]" >::
    (fun () ->
       let p = var "P" 1 in
       let q = var "Q" 1 in
         Unify.unify (2 // (p ^^ [db 2])) (1 // (q ^^ [db 1])) ;
         assert_equal (2 // (p ^^ [db 2])) q) ;

    "[T = a X, T = a Y, Y = T]" >::
    (fun () ->
       let t = var "T" 1 in
       let x = var "X" 1 in
       let y = var "Y" 1 in
       let a = const "a" 0 in
       let a x = a ^^ [x] in
         Unify.unify t (a x) ;
         Unify.unify t (a y) ;
         begin try Unify.unify y t ; assert false with
           | Unify.Error _ -> () end) ;

    "[x\\y\\ H1 x = x\\y\\ G2 x]" >::
    (fun () ->
       let h = var "H" 1 in
       let g = var "G" 2 in
         (* Different timestamps matter *)
         Unify.unify (2// (h ^^ [db 2])) (2// (g ^^ [db 2])) ;
         assert_equal (g^^[db 2]) (h^^[db 2]))

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
