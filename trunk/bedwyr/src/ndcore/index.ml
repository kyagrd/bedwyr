(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2013 David Baelde, Alwen Tiu, Quentin Heath           *)
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

(* Option to turn on/off equivariant indexing. *)
let eqvt_index = ref true

(* In the tree, variables are identified by uniques numbers, which I'll call
 * the [VID] (variable id). We could get rid of that and rely only on the order
 * in which we meet the vars in the tree, but that would involve extra
 * care when changing an algorithm (insertion/lookup or fold).
 * So at the end of a branch we have a collection of variables with [VID]s,
 * and we want to store a constraint describing this collection, such that
 * two formulas satisfying the same rigid structure and map are indeed
 * logically equivalent.
 * We first get rid of [VID]s, which are not necessarily \[0,1,2..n\],
 * and renumber variables using [CID]s (constraint id) from 0 to n.
 * In the leaf we store:
 * - the maximum [VID]
 * - an array mapping [CID] to [VID]
 * In the constraint we store:
 * - an array describing variable equalities: to each variable (denoted by its
 *   [CID]) is associated the smallest (in term of [CID]) equal variable.
 * - the array mapping [CID]s to local timestamps. *)
type constraints = { eq      : int array ;
                     lts     : int array }

let dummy_var = Term.get_var (Term.fresh ~ts:(-1) ~lts:(-1) Term.Constant)

exception Found of int

let get_leaf bindings =
  let n = List.length bindings in
  (* Sorting might be a useless precautions since we always parse the index
   * in the same order, but it's not critical and I need the max anyway. *)
  let bindings = List.sort (fun (i,_) (j,_) -> compare j i) bindings in
  let max_vid = match bindings with (m,_)::_ -> m | _ -> 0 in
  let vid = Array.make n 0 in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let c = {
    eq      = Array.make n 0 ;
    lts     = Array.make n 0 }
  in
  let v = Array.make n dummy_var in
  let _ =
    List.fold_left
      (fun j (i,x) ->
         vid.(j) <- i ;
         c.lts.(j) <- x.Term.lts ;
         v.(j) <- x ;
         (* [c.eq.(j)] gets the least index which has an equal value *)
         c.eq.(j) <-
           (try
              for k = 0 to j do
                if v.(k) = x then raise (Found k)
              done ;
              assert false
            with Found k -> k) ;
         j+1)
      0 bindings
  in
  max_vid,vid,c

let get_constraints bindings =
  let _,_,constraints = get_leaf bindings in constraints

let get_vars max_vid vid c =
  let table = Array.make (max_vid+1) (Term.db 0) in
  let l = ref [] in
  for i = 0 to Array.length c.eq - 1 do
    table.(vid.(i)) <-
      (if c.eq.(i) = i then begin
         (* TODO use ~lts:(c.lts.(i)) *)
         let t = Term.fresh Term.Eigen ~ts:0 ~lts:0 in
           l := t :: !l ;
           t
       end else
         table.(vid.(c.eq.(i))))
  done ;
  table,(List.rev !l)

module ConstraintsOrdered = struct
  type t = constraints
  let compare = compare
end
module ConstraintsMap = Map.Make(ConstraintsOrdered)

let new_leaf bindings data =
  let map = ConstraintsMap.empty in
  let max_vid,vid,constraints = get_leaf bindings in
  max_vid,vid,ConstraintsMap.add constraints data map

let update_leaf (max_vid,vid,map) bindings data =
  let constraints = get_constraints bindings in
  let map = match data with
    | Some data -> ConstraintsMap.add constraints data map
    | None -> ConstraintsMap.remove constraints map
  in
  max_vid,vid,map

let find_leaf (_,_,map) bindings =
  let constraints = get_constraints bindings in
  try Some (ConstraintsMap.find constraints map)
  with Not_found -> None

let get_constraints_bis bindings =
  let n = List.length bindings in
  (* Sorting might be a useless precautions since we always parse the index
   * in the same order, but it's not critical and I need the max anyway. *)
  let bindings = List.sort (fun (i,_) (j,_) -> compare j i) bindings in
    (*
     *)
  let vid = Array.make n 0 in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let c = {
    eq      = Array.make n 0 ;
    lts     = Array.make n 0 }
  in
  let v = Array.make n (Term.db (-1)) in
  let _ =
    List.fold_left
      (fun j (i,t) ->
         vid.(j) <- i ;
         c.lts.(j) <-
           (match Term.observe t with
              | Term.Var v -> v.Term.lts
              | _ -> assert false) ;
         v.(j) <- t ;
         (* [c.eq.(j)] gets the least index which has an equal value *)
         c.eq.(j) <-
           (try
              for k = 0 to j do
                if Term.eq v.(k) t then raise (Found k)
              done ;
              assert false
            with Found k -> k) ;
         j+1)
      0 bindings
  in
  c

type match_status = Over | Exact | Under

let filter_leaf match_status (_,_,map) bindings f =
  match match_status with
    | Under ->
        assert false
    | _ ->
        let constraints = get_constraints_bis bindings in
        ConstraintsMap.iter
          (fun c d ->
             try
               Array.iteri
                 (fun i j ->
                    if (constraints.eq.(i) <> constraints.eq.(j))
                      || (c.lts.(i) <> constraints.lts.(i))
                    then raise (Found i))
                 c.eq ;
               (* if the term has equalities where the pattern does,
                * and has the same local timestamps,
                * then it is an instance of the pattern *)
               f d match_status
             with Found _ -> ())
          map


(* == Indexing ============================================================= *)

(*  Patterns allow universal (constant-like) variables,
 *  existential (instantiable) variables,
 *  and nabla variables as deBruijn indices. *)
type pattern =
  | QString of string
  | Nat    of int
  | DB     of int
  | NB     of int
  | UVar   of int
  | Cst    of Term.term * Term.var
  | EVar   of int
  | True
  | False
  | Binop  of Term.binop * pattern * pattern
  | Binder of Term.binder * int * pattern
  | Lam    of int * pattern
  | App    of int * pattern list (* Store the length of the list *)
  | Hole

type 'a t       = 'a children * 'a node list (* when on a Leaf, nodes=[] *)
and 'a children = Leaf of 'a leaf | Refine
and 'a leaf     = int * int array * 'a ConstraintsMap.t
and 'a node     = Node of (pattern list * 'a t)

(* Zipper used for an index traversal with on-the-fly adding
 * and strict matching. *)
type 'a path =
  | Top
  | Zip of 'a node list * pattern list * 'a node list   (* siblings and arc *)
    * 'a path                                           (* location *)

(* Zipper used for an index traversal with variable-aware matching. *)
type 'a path2 =
  | Top2
  | Zip2 of Term.term list                       (* requested term vector *)
    * (int * Term.term) list                      (* CID-term bindings *)
    * match_status                               (* ... *)
    * 'a node list * pattern list * 'a node list (* siblings and arc *)
    * 'a path2                                   (* location of our father *)

let empty = (Refine,[])

let rec z_top = function
  | index,Top -> index
  | index,Zip (older,patterns,younger,path) ->
      let index =
        Refine,(List.rev_append older ((Node (patterns,index))::younger))
      in
      z_top (index,path)

let rec z_top2 = function
  | index,Top2 -> index
  | index,Zip2 (_,_,_,older,patterns,younger,path) ->
      let index =
        Refine,(List.rev_append older ((Node (patterns,index))::younger))
      in
      z_top2 (index,path)

type zpattern =
  | ZQString of string
  | ZNat    of int
  | ZDB     of int
  | ZNB     of int
  | ZVar    of int
  | ZCst    of Term.term * Term.var
  | ZTrue
  | ZFalse
  | ZBinop  of Term.binop
  | ZBinder of Term.binder * int
  | ZLam    of int
  | ZApp    of int
  | ZHole

(* Asymetric zipper designed for an on-the-fly patternization of terms. *)
type pattern_path =
  | PTop
  | PZip of pattern list * zpattern * pattern list * Term.term list * pattern_path

let merge_pattern zpattern rev_patterns = match zpattern,rev_patterns with
  | ZQString s,[] -> QString s
  | ZNat i,[] -> Nat i
  | ZDB i,[]  -> DB i
  | ZNB i,[]  -> NB i
  | ZVar i,[] -> UVar i
  | ZCst (t,c),[] -> Cst (t,c)
  | ZTrue,[] -> True
  | ZFalse,[] -> False
  | ZBinop b,[p2;p1] ->
      Binop (b,p1,p2)
  | ZBinder (b,n),[p] ->
      Binder (b,n,p)
  | ZLam n,[p] ->
      Lam (n,p)
  | ZApp n,_ when n = List.length rev_patterns ->
      App (n,List.rev rev_patterns)
  | ZHole,[] -> Hole
  | _ -> assert false


exception Cannot_table

(* [create_node bindings terms data] compiles the terms into patterns
 * and associates them with a leaf containing the data. *)
let create_node ~switch_vars bindings terms data =
  let allow_universal = not switch_vars in
  (* TODO maybe bindings is always sorted,
   * or can easily be made that way *)
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
      | Term.QString s -> QString s,bindings
      | Term.Nat s -> Nat s,bindings
      | Term.Var ({Term.tag=Term.Eigen} as var)
          when (not switch_vars) & allow_universal ->
          let i,bindings = add bindings var in
          UVar i, bindings
      | Term.Var ({Term.tag=Term.Logic} as var)
          when switch_vars & allow_universal ->
          let i,bindings = add bindings var in
          UVar i, bindings
      | Term.Var ({Term.tag=Term.Constant} as v) ->
          Cst (Term.deref term,v), bindings
      | Term.DB i -> DB i, bindings
      | Term.NB i -> NB i, bindings
      | Term.True -> True, bindings
      | Term.False -> False, bindings
      | Term.Binop (b,t1,t2) ->
          let pat1,bindings = compile bindings t1 in
          let pat2,bindings = compile bindings t2 in
          Binop (b,pat1,pat2),bindings
      | Term.Binder (b,n,t) ->
          let pat,bindings = compile bindings t in
          Binder (b,n,pat),bindings
      | Term.Lam (i,t) ->
          let pat,bindings = compile bindings t in
          Lam (i,pat),bindings
      | Term.App (h,terms) ->
          let terms = h::terms in
          let patterns,bindings =
            List.fold_left
              (fun (pats,bds) t ->
                 let (p,bds) = compile bds t in
                 (p::pats,bds))
              ([],bindings)
              terms
          in
          App (List.length terms, List.rev patterns),bindings
      | Term.Susp _ -> raise Term.NonNormalTerm
      | _ -> raise Cannot_table
  in
  let patterns,bindings =
    List.fold_left
      (fun (pats,binds) term ->
         let pat,binds = compile binds term in
           pat::pats,binds)
      ([],bindings)
      (List.rev terms)
  in
  patterns,Leaf (new_leaf bindings data)

(* Expects a head-normalized term. *)
let superficial_match ~switch_vars patterns terms =
  let sub pat term =
    match pat, Term.observe term with
      | QString s1,Term.QString s2 -> s1=s2
      | Nat i,Term.Nat j
      | DB i, Term.DB j
      | NB i, Term.NB j -> i=j
      | UVar _, Term.Var {Term.tag=Term.Eigen} -> not switch_vars
      | UVar _, Term.Var {Term.tag=Term.Logic} -> switch_vars
      | Cst (_,v), Term.Var v' -> v==v'
      | EVar _,_ -> assert false
      | True, Term.True
      | False, Term.False -> true
      | Binop (b1,_,_), Term.Binop (b2,_,_) -> b1=b2
      | Binder (b1,n1,_), Term.Binder (b2,n2,_) -> b1=b2 && n1=n2
      | Lam (i,_), Term.Lam (j,_) -> i=j
      | App (i,_), Term.App (h,l) -> i = 1 + List.length l
      | Hole, _ -> true
      | _ -> false
  in
  List.for_all2 sub patterns terms

(* Sorts patterns directly contained in a list
 * according to their top-level symbol.
 * It uses hardcoded rankings for terms, binary operators
 * (the same that in Pprint, but hardcoded once more) and quantifiers.
 * TODO un-hardcode and share some code with Pprint.
 * A solution would be to take the binop and binder rankings as arguments
 * (defined in Pprint, where they belong), and to replace the ranking on terms,
 * which is actually a ranking on patterns and therefore cannot leave Index,
 * by an actual ranking on terms defined in Term
 * and used during the [update] stage. *)
let superficial_sort nodes =
  let rank = function
    | QString _ -> 0
    | Nat _ -> 1
    | DB _ -> 2
    | NB _ -> 3
    | UVar _ -> 4
    | Cst _ -> 5
    | EVar _ -> 6
    | True -> 7
    | False -> 8
    | Binop _ -> 9
    | Binder _ -> 10
    | Lam _ -> 11
    | App _ -> 12
    | Hole -> 13
  in
  let comp pat1 pat2 = match pat1,pat2 with
    | QString s1,QString s2 -> compare s1 s2
    | Nat i1,Nat i2 | DB i1,DB i2 | NB i1,NB i2
    | UVar i1,UVar i2 | EVar i1,EVar i2 -> compare i1 i2
    | Cst (t1,_),Cst (t2,_) -> compare (Term.get_name t1) (Term.get_name t2)
    | Binop (b1,_,_),Binop (b2,_,_) ->
        begin let priorities = function
          | Term.Eq -> 4
          | Term.And -> 3
          | Term.Or -> 2
          | Term.Arrow -> 1
        in
        compare (priorities b1) (priorities b2) end
    | Binder (b1,_,_),Binder (b2,_,_) ->
        begin let priorities = function
          | Term.Forall -> 3
          | Term.Exists -> 2
          | Term.Nabla -> 1
        in
        compare (priorities b1) (priorities b2) end
    | Lam (i1,_),Lam (i2,_)
    | App (i1,_),App (i2,_) -> compare i1 i2
    | _,_ -> compare (rank pat1) (rank pat2)
  in
  let multicomp (Node (l1,_)) (Node (l2,_)) =
    let rec aux = function
        | [],[] -> 0
        | [],_ | _,[] -> assert false
        | h1::l1,h2::l2 ->
            begin match comp h1 h2 with
              | 0 ->  aux (l1,l2)
              | n -> n
            end
    in
    aux (l1,l2)
  in
  List.sort multicomp nodes


(* == ACCESS =============================================================== *)

(* TODO Some of these are tailrec, some waste this effort... *)

(* Expects head-normalized terms. *)
let access ~switch_vars zipper terms =
  (* [access_patterns] filters a list of terms through a list of patterns,
   * returns a new pattern list (their pairwise GCDs),
   * the reversed list of catches (their respective remainders),
   * and the updated list of CID-var bindings.
   * XXX beware of switch_vars! XXX
   * Returns hnorm-ed terms. *)
  let access_patterns bindings patterns terms =
    let rec access_pattern
          (changed,bindings,rev_catches as accum)
          rev_patterns zipaterm pattern term patterns terms =
      let term = Norm.hnorm term in
      let accum,new_pattern,sub_patterns,sub_terms = match pattern, Term.observe term with
        | QString s1, Term.QString s2 when s1=s2 ->
            accum,ZQString s1,[],[]
        | Nat i, Term.Nat j when i = j ->
            accum,ZNat i,[],[]
        | DB i, Term.DB j when i = j ->
            accum,ZDB i,[],[]
        | NB i, Term.NB j when i = j ->
            accum,ZNB i,[],[]
        | UVar v, Term.Var ({Term.tag=Term.Eigen} as var)
            when (not switch_vars) & (not switch_vars) ->
            let bindings = (v,var)::bindings in
            (changed,bindings,rev_catches),ZVar v,[],[]
        | UVar v, Term.Var ({Term.tag=Term.Logic})
            when switch_vars & (not switch_vars) ->
            failwith "logic variable forbidden here"
        | Cst (t,c), Term.Var c' when c==c' ->
            accum,ZCst (t,c),[],[]
        | True, Term.True ->
            accum,ZTrue,[],[]
        | False, Term.False ->
            accum,ZFalse,[],[]
        | Binop (b1,p1,p2), Term.Binop (b2,t1,t2) when b1=b2 ->
            accum,ZBinop b1,[p1;p2],[t1;t2]
        | Binder (b1,n1,p), Term.Binder (b2,n2,t) when b1=b2 && n1=n2 ->
            accum,ZBinder (b1,n1),[p],[t]
        | Lam (i,p), Term.Lam (j,t) when i = j ->
            accum,ZLam i,[p],[t]
        | App (i,pats), Term.App (h,l) when i = 1 + List.length l ->
            assert (List.length pats = i) ;
            accum,ZApp i,pats,h::l
        | _ ->
            let changed = changed || (pattern<>Hole) in
            let rev_catches = (pattern,term)::rev_catches in
            (changed,bindings,rev_catches),ZHole,[],[]
      in
      let zipaterm = PZip (rev_patterns,new_pattern,patterns,terms,zipaterm) in
      aux accum ([],zipaterm,sub_patterns,sub_terms)
    and aux accum (rev_patterns,zipaterm,patterns,terms) = match patterns,terms with
      | [],[] ->
          begin match zipaterm with
            | PTop -> accum,List.rev rev_patterns
            | PZip (rev_patterns',zpattern,patterns,terms,zipaterm) ->
                assert (List.length patterns = List.length terms) ;
                let pattern = merge_pattern zpattern rev_patterns in
                aux accum (pattern::rev_patterns',zipaterm,patterns,terms)
          end
      | pattern::patterns,term::terms ->
          (* Go through one pattern, enrich catches and bindings,
           * and build the updated pattern. *)
          access_pattern accum rev_patterns zipaterm pattern term patterns terms
      | _ -> assert false
    in
    aux (false,bindings,[]) ([],PTop,patterns,terms)
  in
  (* Expects hnorm-ed terms. *)
  let rec access_node bindings terms path older_nodes nodes patterns index =
    let (changed,bindings,rev_catches),patterns =
      access_patterns bindings patterns terms
    in
    let path = Zip (older_nodes,patterns,nodes,path) in
    let sub_patterns,sub_terms =
      List.fold_left
        (fun (sub_patterns,sub_terms) (pattern,term) -> (pattern::sub_patterns,term::sub_terms))
        ([],[])
        rev_catches
    in
    if changed then
      (* The new patterns have some new holes, we separate the new and the
       * former terms by adding an intermediate index.
       * We need to compile the caught terms into patterns. *)
      (fun data ->
         let patterns,children =
           create_node ~switch_vars bindings sub_terms data
         in
         let newnode = Node (patterns,(children,[])) in
         let oldnode = Node (sub_patterns,index) in
         let index = Refine,[newnode ; oldnode] in
         z_top (index,path)),
      None
    else
      (* The terms were fully matched by the patterns,
       * the new [patterns] is the same as the former one,
       * the access gets propagated deeper without changing anything here. *)
      access_index bindings sub_terms (index,path)
  and access_nodes bindings terms path older_nodes = function
    | [] ->
        (fun data ->
           let patterns,children =
             create_node ~switch_vars bindings terms data
           in
           let index = children,[] in
           let path = Zip (older_nodes,patterns,[],path) in
           z_top (index,path)),
        None
    | (Node (patterns,index) as node)::nodes ->
        if superficial_match ~switch_vars patterns terms then
          access_node bindings terms path older_nodes nodes patterns index
        else
          access_nodes bindings terms path (node::older_nodes) nodes
  (* access an index, i.e. an (unordered) list of alternative nodes.
   * Expects hnorm-ed terms. *)
  and access_index bindings terms (index,path) = match terms,index with
    | [],(Leaf leaf,[]) ->
        (fun data ->
           let index = Leaf (update_leaf leaf bindings (Some data)),[] in
           z_top (index,path)),
        find_leaf leaf bindings
    | _,(Refine,nodes) ->
        access_nodes bindings terms path [] nodes
    | _ -> assert false
  in
  access_index [] terms zipper

let access ~switch_vars index terms =
  let terms =
    if !eqvt_index then (Norm.nb_rename terms) else (List.map Norm.hnorm terms)
  in
  let zipper = index,Top in
  let update,found = access ~switch_vars zipper terms in
  update,found

let filter ~switch_vars index terms f =
  let terms =
    if !eqvt_index then (Norm.nb_rename terms) else (List.map Norm.hnorm terms)
  in
  let zipper = index,Top2 in
  let filter_patterns bindings patterns terms match_status =
    let rec filter_pattern
          (match_status,bindings,rev_sub_terms as accum)
          pattern term patterns terms =
      let term = Norm.hnorm term in
      match pattern, Term.observe term with
        | QString s1, Term.QString s2 when s1=s2 ->
            aux accum (patterns,terms)
        | Nat i, Term.Nat j when i = j ->
            aux accum (patterns,terms)
        | DB i, Term.DB j when i = j ->
            aux accum (patterns,terms)
        | NB i, Term.NB j when i = j ->
            aux accum (patterns,terms)
        | UVar v, Term.Var ({Term.tag=Term.Eigen}) ->
            let accum = (match_status,(v,term)::bindings,rev_sub_terms) in
            aux accum (patterns,terms)
        | UVar v,Term.Var _ ->
            begin match match_status with
              | Under -> None
              | _ ->
                  let accum = (Over,(v,term)::bindings,rev_sub_terms) in
                  aux accum (patterns,terms)
            end
        | EVar _,_ -> assert false
        | Cst (_,c), Term.Var c' when c==c' ->
            aux accum (patterns,terms)
        | True, Term.True ->
            aux accum (patterns,terms)
        | False, Term.False ->
            aux accum (patterns,terms)
        | Binop (b1,p1,p2), Term.Binop (b2,t1,t2) when b1=b2 ->
            aux accum ((p1::p2::patterns),(t1::t2::terms))
        | Binder (b1,n1,p), Term.Binder (b2,n2,t) when b1=b2 && n1=n2 ->
            aux accum ((p::patterns),(t::terms))
        | Lam (i,p), Term.Lam (j,t) when i = j ->
            aux accum ((p::patterns),(t::terms))
        | App (i,pats), Term.App (h,l) when i = 1 + List.length l ->
            assert (List.length pats = i) ;
            aux accum (List.append pats patterns,List.append (h::l) terms)
        | Hole,_ ->
            let accum = (match_status,bindings,term::rev_sub_terms) in
            aux accum (patterns,terms)
        | _ -> None
    and aux accum (patterns,terms) = match patterns,terms with
      | [],[] -> Some accum
      | pattern::patterns,term::terms ->
          (* Go through one pattern, enrich bindings,
           * updates the matching status. *)
          filter_pattern accum pattern term patterns terms
      | _ -> assert false
    in
    aux (match_status,bindings,[]) (patterns,terms)
  in
  (* Expects hnorm-ed terms. *)
  let rec filter_node bindings terms match_status path older_nodes nodes patterns index =
    match filter_patterns bindings patterns terms match_status with
      | Some (ms,bd,rst) ->
          let path = Zip2 (terms,bindings,match_status,older_nodes,patterns,nodes,path) in
          filter_index bd (List.rev rst) ms (index,path)
      | None ->
          let node = Node (patterns,index) in
          filter_nodes bindings terms match_status path (node::older_nodes) nodes
  and filter_nodes bindings terms match_status path older_nodes = function
    | [] ->
        begin match path with
          | Top2 -> ()
          | Zip2 (terms',bindings',match_status',older',patterns',younger',path') ->
              let node = Node (patterns',(Refine,(List.rev older_nodes))) in
              filter_nodes bindings' terms' match_status' path' (node::older') younger'
        end
    | (Node (patterns,index))::nodes ->
        filter_node bindings terms match_status path older_nodes nodes patterns index
  (* access an index, i.e. an (unordered) list of alternative nodes.
   * Expects hnorm-ed terms. *)
  and filter_index bindings terms match_status (index,path) = match terms,index with
    | [],(Leaf leaf,[]) ->
        filter_leaf match_status leaf bindings f ;
        begin match path with
          | Top2 -> ()
          | Zip2 (terms',bindings',match_status',older',patterns',younger',path') ->
              let node = Node (patterns',index) in
              filter_nodes bindings' terms' match_status' path' (node::older') younger'
        end
    | _,(Refine,nodes) ->
        filter_nodes bindings terms match_status path [] nodes
    | _ -> assert false
  in
  filter_index [] terms Exact zipper


(* == FOLD ================================================================== *)

(* We use some kind of multi-locations zippers. *)

module type MZ_t =
sig
  type t
  val empty : t
  val refine : t -> pattern list -> t
  val zip : Term.term array -> t -> Term.term list
end

module MZ : MZ_t =
struct

  type t = zpattern list list

  let arity = function
    | ZBinop _ -> 2
    | ZBinder _ | ZLam _ | ZHole -> 1
    | ZApp n -> n
    | _ -> 0

  let arity = function
    | [] -> assert false
    | row::_ -> List.fold_left (+) 0 (List.map arity row)

  let empty = []

  let compile_step pats =
    let row,subpats =
      List.fold_left
        (fun (row,subpats) -> function
           | QString s -> (ZQString s)::row,subpats
           | Nat i -> (ZNat i)::row,subpats
           | DB i  ->  (ZDB i)::row, subpats
           | NB i  ->  (ZNB i)::row, subpats
           | UVar i | EVar i -> (ZVar i)::row, subpats
           | Cst (t,c) -> (ZCst (t,c))::row, subpats
           | True -> ZTrue::row, subpats
           | False -> ZFalse::row, subpats
           | Binop (b,p1,p2) -> (ZBinop b)::row, p2::p1::subpats
           | Binder (b,n,p) -> (ZBinder (b,n))::row, p::subpats
           | App (n,l) -> (ZApp n)::row, List.rev_append l subpats
           | Lam (n,p) -> (ZLam n)::row, p::subpats
           | Hole -> ZHole::row, Hole::subpats)
        ([],[])
        pats
    in
    List.rev row,List.rev subpats

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
      | ZQString s -> Term.qstring s,terms
      | ZNat i -> Term.nat i,terms
      | ZDB i  -> Term.db i, terms
      | ZNB i  -> Term.nabla i, terms
      | ZVar i -> table.(i), terms
      | ZCst (t,_) -> t, terms
      | ZTrue -> Term.op_true, terms
      | ZFalse -> Term.op_false, terms
      | ZBinop b ->
          begin match terms with
            | t1::t2::terms ->
                Term.op_binop b t1 t2, terms
            | _ -> assert false
          end
      | ZBinder (b,n) ->
          begin match terms with
            | h::terms ->
                Term.binder b n h, terms
            | _ -> assert false
          end
      | ZLam n ->
          begin match terms with
            | h::terms -> Term.lambda n h, terms
            | _ -> assert false
          end
      | ZApp n ->
          begin match split_at_nth terms n with
            | (h::tl),terms ->
                Term.app h tl, terms
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
          (fun (out,terms) zpattern ->
             let t,terms = zip_step terms zpattern in
             t::out,terms)
          ([],terms)
          row
      in
      assert (terms = []) ;
      List.rev out
    in
    List.fold_left zip [] mz

end

let fold f index y =
  let rec fold_node mz y (Node (patterns,index)) =
    fold_index (MZ.refine mz patterns) index y
  and fold_index mz index y = match index with
    | Leaf (max_vid,vid,map),[] ->
        ConstraintsMap.fold
          (fun c v y ->
             let table,l = (get_vars max_vid vid c) in
             let head = Term.fresh Term.Eigen ~ts:0 ~lts:0 in
             let t = Term.app head (MZ.zip table mz) in
             let t =
               List.fold_left
                 (fun t v -> Term.abstract v t)
                 t
                 l
             in
             f (Term.abstract head t) v y)
          map y
    | Refine,nodes -> List.fold_left (fold_node mz) y (superficial_sort nodes)
    | _ -> assert false
  in
  fold_index MZ.empty index y

let iter f x =
  fold (fun t v () -> f t v) x ()
