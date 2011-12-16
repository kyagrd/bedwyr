(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2011 David Baelde, Alwen Tiu                          *)
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

type constraints = { max_vid : int ;
                     vid     : int array ;
                     eq      : int array ;
                     lts     : int array }

let dummy_var = Term.get_var (Term.fresh ~ts:(-1) ~lts:(-1) Term.Constant)

exception Found of int

(* Option to turn on/off equivariant tabling *)
let eqvt_tbl = ref true

let get_constraints bindings =
  let n = List.length bindings in
  (* Sorting might be a useless precautions since we always parse the index
   * in the same order, but it's not critical and I need the max anyway. *)
  let bindings = List.sort (fun (i,_) (j,_) -> compare j i) bindings in
  let m = match bindings with (m,_)::_ -> m | _ -> 0 in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let c = {
    max_vid = m ;
    vid     = Array.make n 0 ;
    eq      = Array.make n 0 ;
    lts     = Array.make n 0 }
  in
  let v = Array.make n dummy_var in
    ignore (List.fold_left
              (fun j (i,x) ->
                 c.vid.(j) <- i ;
                 c.lts.(j) <- x.Term.lts ;
                 v.(j) <- x ;
                 j+1)
              0 bindings) ;
    ignore (List.fold_left
              (fun j (i,x) ->
                 (* [a.(i)] gets the least index which has an equal value *)
                 c.eq.(j) <-
                   begin try
                     for k = 0 to j do
                       if v.(k) = x then raise (Found k)
                     done ;
                     assert false
                   with
                     | Found k -> k
                   end ;
                 j+1)
              0 bindings) ;
    c

module ConstraintsOrdered = struct
  type t = constraints
  let compare = compare
end
module ConstraintsMap = Map.Make(ConstraintsOrdered)

let new_leaf bindings data =
  let map = ConstraintsMap.empty in
    ConstraintsMap.add (get_constraints bindings) data map

let update_leaf map bindings data =
  match data with
    | Some data -> ConstraintsMap.add (get_constraints bindings) data map
    | None -> ConstraintsMap.remove (get_constraints bindings) map

let find_leaf map bindings =
  ConstraintsMap.find (get_constraints bindings) map

(* == Indexing ============================================================= *)

(* Patterns allow eigenvariables and nabla variables as deBruijn indices. *)
type pattern =
  | Var    of int
  | Cst    of Term.term * Term.var
  | DB     of int
  | NB     of int
  | True
  | False
  | Eq     of pattern * pattern
  | And    of pattern * pattern
  | Or     of pattern * pattern
  | Arrow  of pattern * pattern
  | Binder of Term.binder * int * pattern
  | Lam    of int * pattern
  | App    of int * pattern list (* Store the length of the list *)
  | Hole

type 'a t        = 'a node list
and  'a node     = pattern list * 'a children
and  'a children = Refine of 'a t | Leaf of 'a ConstraintsMap.t

let empty = []

exception Cannot_table

(* [create_node bindings terms data] compiles the terms into patterns
 * and associates them with a leaf containing the data.
 * Terms are expected to be reversed. *)
let create_node ~allow_eigenvar bindings terms data =
  let bindings = List.sort (fun (i,_) (j,_) -> compare i j) bindings in
  let add bindings v =
    let rec aux accu expect = function
      | (i,x)::l when i=expect -> aux ((i,x)::accu) (expect+1) l
      | l -> expect, List.rev_append accu ((expect,v)::l)
    in
    aux [] 0 bindings
  in
  let rec compile bindings term =
    let term = Norm.hnorm term in
    match Term.observe term with
      | Term.DB i -> DB i, bindings
      | Term.NB i -> NB i, bindings
      | Term.Var ({Term.tag=Term.Constant} as v) ->
          Cst (Term.deref term,v), bindings
      | Term.True -> True, bindings
      | Term.False -> False, bindings
      | Term.Var ({Term.tag=Term.Eigen} as var) when allow_eigenvar ->
          let i,bindings = add bindings var in
          Var i, bindings
      | Term.Lam (i,t) ->
          let pat,bindings = compile bindings t in
          Lam (i,pat),bindings
      | Term.Eq (t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          Eq (pat1,pat2),bindings
      | Term.And (t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          And (pat1,pat2),bindings
      | Term.Or (t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          Or (pat1,pat2),bindings
      | Term.Arrow (t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          Arrow (pat1,pat2),bindings
      | Term.Binder (b,n,t) ->
          let pat,bindings = compile bindings t in
          Binder (b,n,pat),bindings
      | Term.App (h,terms) ->
          let terms = h::terms in
          let patterns,bindings =
            List.fold_left
              (fun (pats,b) t ->
                 let (p,b) = compile b t in
                 (p::pats,b))
              ([],bindings)
              terms
          in
          App (List.length terms, List.rev patterns),bindings
      | _ -> raise Cannot_table
  in
  let patterns,bindings =
    List.fold_left
      (fun (pats,binds) term ->
         let pat,binds = compile binds term in
           pat::pats,binds)
      ([],bindings)
      terms
  in
  patterns, Leaf (new_leaf bindings data)

(* [superficial_match] expects a head-normalized term. *)
let superficial_match patterns terms =
  let sub (pat,term) = match pat, Term.observe term with
    | DB i, Term.DB j
    | NB i, Term.NB j
    | Lam (i,_), Term.Lam (j,_) -> i=j
    | Cst (_,v), Term.Var v' -> v==v'
    | True, Term.True
    | False, Term.False
    | Eq _, Term.Eq _
    | And _, Term.And _
    | Or _, Term.Or _
    | Arrow _, Term.Arrow _
    | Var _, Term.Var {Term.tag=Term.Eigen} -> true
    | Binder (b1,n1,_), Term.Binder (b2,n2,_) -> b1=b2 && n1=n2
    | App (i,_), Term.App (h,l) -> i = 1 + List.length l
    | Hole, _ -> true
    | _ -> false
  in
  List.for_all sub (List.map2 (fun a b -> a,b) patterns terms)

(* [rename] Renaming nabla variables in a term according to the order of
 *   traversal in the tree representation of the (normal form of the) term.
 *   This is a cheap way to force equivariant matching in tables.
 * Added by Tiu, 03 March 2011. *)

let rec rename term bindings n =
  let term = Norm.hnorm term in
  match Term.observe term with
    | Term.Var _ | Term.DB _ | Term.True | Term.False ->
        term, bindings, n
    | Term.NB i ->
        begin try
          let x,y = (List.find (fun (x,y) -> x=i) bindings) in
          Term.nabla y, bindings, n
        with
          | Not_found -> Term.nabla (n+1), (i,n+1)::bindings, n+1
        end
    | Term.Lam (i,t) ->
        let t,bindings,n = rename t bindings n in
        (Term.lambda i t),bindings,n
    | Term.Eq (t1,t2) ->
        let t1,bindings,n = rename t1 bindings n in
        let t2,bindings,n = rename t2 bindings n in
        Term.op_eq t1 t2,bindings,n
    | Term.And (t1,t2) ->
        let t1,bindings,n = rename t1 bindings n in
        let t2,bindings,n = rename t2 bindings n in
        Term.op_and  t1 t2,bindings,n
    | Term.Or (t1,t2) ->
        let t1,bindings,n = rename t1 bindings n in
        let t2,bindings,n = rename t2 bindings n in
        Term.op_or t1 t2,bindings,n
    | Term.Arrow (t1,t2) ->
        let t1,bindings,n = rename t1 bindings n in
        let t2,bindings,n = rename t2 bindings n in
        Term.op_arrow t1 t2,bindings,n
    | Term.Binder (b,i,t) ->
        let t,bindings,n = rename t bindings n in
        Term.binder b i t,bindings,n
    | Term.App (h,terms) ->
        let newterms,bds,n'=
          List.fold_left
            (fun (ts,bd,idx) t ->
               let t',bd',idx' = rename t bd idx
               in (t'::ts,bd',idx')
            )
            ([],bindings,n)
            (h::terms)
        in
        begin match List.rev newterms with
          | newh::newterms -> (Term.app newh newterms),bds,n'
          | _ -> assert false
        end
    | _ -> raise Cannot_table

let nb_rename terms =
  let newterms,_,_ =
    List.fold_left
      (fun (ts,bd,idx) t ->
         let t',bd',idx' = rename t bd idx
         in (t'::ts,bd',idx')
      )
      ([],[],0)
      terms
  in List.rev newterms


(* == UPDATE =============================================================== *)

(* TODO Some of these are tailrec, some waste this effort..
 *      Everything can be done tailrec using a zipper,
 *      and we'll get a flexible function allowing search and update
 *      in a single pass.
 * access : index -> term -> data option * (data -> index) * (() -> index)
 *                           found         update            delete          *)

let update ~allow_eigenvar index terms data =
  (* Update_pattern returns the list of catches and the alternative
   * corresponding to the former index in reverse order. *)
  let rec update_pattern bindings catches former_alt pattern term =
    match pattern, Term.observe (Norm.hnorm term) with
      | DB i, Term.DB j
      | NB i, Term.NB j when i = j ->
          (false, pattern, bindings, catches, former_alt)
      | True, Term.True | False, Term.False ->
          (false, pattern, bindings, catches, former_alt)
      | Cst (t,c), Term.Var c' when c==c' ->
          (false, pattern, bindings, catches, former_alt)
      | Var v, Term.Var ({Term.tag=Term.Eigen} as var) when allow_eigenvar ->
          (false, pattern, (v,var)::bindings, catches, former_alt)
      | Lam (i,pattern), Term.Lam (j,term) when i = j ->
          let (changed,pattern,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pattern term
          in
          (changed, Lam (i,pattern), bindings, catches, former_alt)
      | Eq (pat1,pat2), Term.Eq (t1,t2) ->
          let (changed1,pat1,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat1 t1
          in
          let (changed2,pat2,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat2 t2
          in
          (changed1 || changed2, Eq (pat1,pat2), bindings, catches, former_alt)
      | And (pat1,pat2), Term.And (t1,t2) ->
          let (changed1,pat1,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat1 t1
          in
          let (changed2,pat2,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat2 t2
          in
          (changed1 || changed2, And (pat1,pat2), bindings, catches, former_alt)
      | Or (pat1,pat2), Term.Or (t1,t2) ->
          let (changed1,pat1,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat1 t1
          in
          let (changed2,pat2,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat2 t2
          in
          (changed1 || changed2, Or (pat1,pat2), bindings, catches, former_alt)
      | Arrow (pat1,pat2), Term.Arrow (t1,t2) ->
          let (changed1,pat1,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat1 t1
          in
          let (changed2,pat2,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat2 t2
          in
          (changed1 || changed2, Arrow (pat1,pat2), bindings, catches, former_alt)
      | Binder (b1,n1,pat), Term.Binder (b2,n2,t) when b1=b2 && n1=n2 ->
          let (changed,pat,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pat t
          in
          (changed, Binder (b1,n1,pat), bindings, catches, former_alt)
      | App (i,patterns), Term.App (h,terms) when i = 1 + List.length terms ->
          let terms = h::terms in
          let (changed,patterns,bindings,catches,former_alt) =
            update_patterns bindings catches former_alt patterns terms
          in
          let patterns = List.rev patterns in
          assert (List.length patterns = i) ;
          (changed, App (i,patterns), bindings, catches, former_alt)
      | Hole,_ ->
          (false, Hole, bindings, term::catches, Hole::former_alt)
      | _ ->
          (true, Hole, bindings, term::catches, pattern::former_alt)

  and update_patterns bindings catches former_alt patterns terms =
    assert (List.length patterns = List.length terms) ;
    List.fold_left2
      (fun (changed,patterns,bindings,catches,former_alt) pattern term ->
         (* Go through one pattern, enrich catches and bindings,
          * and build the updated pattern. *)
         let (changed',pattern,bindings,catches,former_alt) =
           update_pattern bindings catches former_alt pattern term
         in
         changed'||changed,pattern::patterns,bindings,catches,former_alt)
      (false,[],bindings,catches,former_alt)
      patterns
      terms
  in

  let rec update_node bindings terms (patterns,children) =
    let changed,patterns,bindings,catches,former_alt =
      update_patterns bindings [] [] patterns terms
    in
    let patterns = List.rev patterns in
    let former_alt = List.rev former_alt in
    patterns,
    (if changed then
       (* The new patterns have some new holes, we separate the new and the
        * former terms by adding an intermediate index.
        * We need to compile the caught terms into patterns. *)
       match data with
         | Some data ->
             Refine [ create_node ~allow_eigenvar bindings catches data ;
                      former_alt, children ]
         | None -> raise Not_found
     else
       (* The terms were fully matched by the patterns,
        * the new [patterns] is the same as the former one,
        * the update gets propagated deeper without changing anything here. *)
       match children with
         | Refine index ->
             Refine (update_index bindings
                       (List.map Norm.hnorm (List.rev catches)) [] index)
         | Leaf map ->
             assert (catches = []) ;
             Leaf (update_leaf map bindings data))

  (* Update an index, i.e. an (unordered) list of alternative nodes. *)
  and update_index bindings terms index' = function
    | [] ->
        begin match data with
          | Some data ->
              (create_node ~allow_eigenvar
                 bindings (List.rev terms) data)::index'
          | None -> raise Not_found
        end
    | node::index ->
        if superficial_match (fst node) terms then
          (update_node bindings terms node)::index@index'
        else
          update_index bindings terms (node::index') index
  in
  (* update_index [] (List.map (Term.shared_copy) (nb_rename terms)) [] index *)
  if !eqvt_tbl then
    update_index [] (nb_rename terms) [] index
  else
    update_index [] (List.map Norm.hnorm terms) [] index

let add ?(allow_eigenvar=true) index terms data =
  update ~allow_eigenvar index terms (Some data)

(* == FIND ================================================================= *)

(* Filter a term through a pattern, raise Not_found on mismatch,
 * return the list of bindings and the reversed list of catches. *)


let rec filter bindings catches pattern term =
  match pattern, Term.observe (Norm.hnorm term) with
    | DB i, Term.DB j
    | NB i, Term.NB j when i=j -> bindings,catches
    | True, Term.True | False, Term.False -> bindings,catches
    | Cst (_,c), Term.Var c' when c==c' -> bindings,catches
    | Var v, Term.Var ({Term.tag=Term.Eigen} as var) ->
        (v,var)::bindings,catches
    | Lam (i,pattern), Term.Lam (j,term) when i=j ->
        filter bindings catches pattern term
    | Eq (pat1,pat2), Term.Eq (t1,t2) ->
        let bindings,catches = filter bindings catches pat1 t1 in
        filter bindings catches pat2 t2
    | And (pat1,pat2), Term.And (t1,t2) ->
        let bindings,catches = filter bindings catches pat1 t1 in
        filter bindings catches pat2 t2
    | Or (pat1,pat2), Term.Or (t1,t2) ->
        let bindings,catches = filter bindings catches pat1 t1 in
        filter bindings catches pat2 t2
    | Arrow (pat1,pat2), Term.Arrow (t1,t2) ->
        let bindings,catches = filter bindings catches pat1 t1 in
        filter bindings catches pat2 t2
    | Binder (b1,n1,pat), Term.Binder (b2,n2,t) when b1=b2 && n1=n2->
        filter bindings catches pat t
    | App (i,patterns), Term.App (h,l) when i = 1 + List.length l ->
        filter_several bindings catches patterns (h::l)
    | Hole,_ -> bindings,term::catches
    | _ -> raise Not_found

(* Same as [filter], returns the catches in reverse order. *)
and filter_several bindings catches patterns terms =
  List.fold_left2
    (fun (bindings,catches) pattern term ->
       filter bindings catches pattern term)
    (bindings,catches)
    patterns terms

let rec find bindings index terms =
  match index with
    | [] -> raise Not_found
    | (patterns,children)::index ->
        if superficial_match patterns terms then
          let bindings,catches = filter_several bindings [] patterns terms in
            match children with
              | Leaf map ->
                  assert (catches = []) ;
                  find_leaf map bindings
              | Refine index ->
                  find bindings index (List.map Norm.hnorm (List.rev catches))
        else
          find bindings index terms

let find index terms =
  let ts = if !eqvt_tbl then (nb_rename terms) else (List.map Norm.hnorm terms) in
  try Some (find [] index ts) with _ -> None

(* == FOLD ================================================================== *)

(* We use some kind of multi-locations zippers *)

module type MZ_t =
sig
  type t
  val empty : t
  val refine : t -> pattern list -> t
  val zip : Term.term array -> t -> Term.term list
end

module MZ : MZ_t =
struct

  type item =
    | ZVar    of int
    | ZCst    of Term.term * Term.var
    | ZDB     of int
    | ZNB     of int
    | ZTrue
    | ZFalse
    | ZEq
    | ZAnd
    | ZOr
    | ZArrow
    | ZBinder of Term.binder * int
    | ZLam    of int
    | ZApp    of int
    | ZHole

  type t = item list list

  let arity = function
    | ZVar _ | ZCst _ | ZDB _ | ZNB _ | ZTrue | ZFalse -> 0
    | ZEq _ | ZAnd _ | ZOr _ | ZArrow _ -> 2
    | ZApp n -> n
    | ZBinder _ | ZHole | ZLam _ -> 1

  let arity = function
    | [] -> assert false
    | row::_ -> List.fold_left (+) 0 (List.map arity row)

  let empty = []

  let compile_step pats =
    let row,subpats =
      List.fold_left
        (fun (row,subpats) -> function
           | DB i  ->  (ZDB i)::row, subpats
           | NB i  ->  (ZNB i)::row, subpats
           | Cst (t,c) -> (ZCst (t,c))::row, subpats
           | True -> ZTrue::row, subpats
           | False -> ZFalse::row, subpats
           | Var i -> (ZVar i)::row, subpats
           | Eq (p1,p2) -> ZEq::row, p2::p1::subpats
           | And (p1,p2) -> ZAnd::row, p2::p1::subpats
           | Or (p1,p2) -> ZOr::row, p2::p1::subpats
           | Arrow (p1,p2) -> ZArrow::row, p2::p1::subpats
           | Binder (b,n,p) -> (ZBinder (b,n))::row, p::subpats
           | App (n,l) -> (ZApp n)::row, List.rev_append l subpats
           | Lam (n,p) -> (ZLam n)::row, p::subpats
           | Hole -> ZHole::row, Hole::subpats)
        ([],[])
        pats
    in
    List.rev row,
    List.rev subpats

  let rec refine acc patterns =
    if List.for_all ((=) Hole) patterns then acc else
      let row,sub = compile_step patterns in
      refine (row::acc) sub

  let split_at_nth l n =
    let rec aux before l n = match l,n with
      | _,0 -> List.rev before,l
      | h::l,_ -> aux (h::before) l (n-1)
      | _ -> assert false
    in
    aux [] l n

  let zip table mz =
    let zip_step terms = function
      | ZVar i -> table.(i), terms
      | ZCst (t,_) -> t, terms
      | ZDB i  -> Term.db i, terms
      | ZNB i  -> Term.nabla i, terms
      | ZTrue -> Term.op_true, terms
      | ZFalse -> Term.op_false, terms
      | ZEq ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_eq t1 t2, terms
            | _ -> assert false
          end
      | ZAnd ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_and t1 t2, terms
            | _ -> assert false
          end
      | ZOr ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_or t1 t2, terms
            | _ -> assert false
          end
      | ZArrow ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_arrow t1 t2, terms
            | _ -> assert false
          end
      | ZBinder (b,n) ->
          begin match terms with
            | h::terms ->
                Term.binder b n h, terms
            | _ -> assert false
          end
      | ZApp n ->
          begin match split_at_nth terms n with
            | (h::tl),terms ->
                Term.app h tl, terms
            | _ -> assert false
          end
      | ZLam n ->
          begin match terms with
            | h::terms -> Term.lambda n h, terms
            | _ -> assert false
          end
      | ZHole ->
          begin match terms with
            | h::terms -> h, terms
            | _ -> assert false
          end
    in
    let rec zip terms row =
      let out,terms =
        List.fold_left
          (fun (out,terms) item ->
             let t,terms = zip_step terms item in
             t::out,terms)
          ([],terms)
          row
      in
      assert (terms = []) ;
      List.rev out
    in
    List.fold_left zip [] mz

end

let iter index f =
  let rec iter_children mz = function
    | Leaf map ->
        ConstraintsMap.iter
          (fun c v ->
             let table = Array.make (c.max_vid+1) (Term.db 0) in
             let l = ref [] in
             for i = 0 to Array.length c.eq - 1 do
               table.(c.vid.(i)) <-
                 if c.eq.(i) = i then
                   Term.fresh Term.Eigen ~ts:0 ~lts:0
                 else
                   table.(c.vid.(c.eq.(i))) ;
               if c.eq.(i) = i then
                 l := table.(c.vid.(i)) :: !l
             done ;
             let head = Term.fresh Term.Eigen ~ts:0 ~lts:0 in
             let t = Term.app head (MZ.zip table mz) in
             let l = List.rev !l in
             let t =
               List.fold_left
                 (fun t v -> Term.abstract v t)
                 t
                 l
             in
             f (Term.abstract head t) v)
          map
    | Refine i -> iter_index mz i

  and iter_node mz (patterns,children) =
    iter_children (MZ.refine mz patterns) children
  and iter_index mz = List.iter (iter_node mz) in

  iter_index MZ.empty index
