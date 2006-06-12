
(** {1 Constraint management}
  * Constraints are sets of equalities between eigenvariables represented
  * as integers. They are uniquely represented as arrays of integers. *)

type constraints = int array

let dummy_var = {Term.name="";Term.ts=0;Term.tag=Term.Constant}

exception Found of int

let get_constraints bindings =
  let n = List.length bindings in
  (* We prepare the constraints array,
   * and transform the [(int*var) list] into a more convenient [var array]. *)
  let a = Array.make n 0 in
  let v = Array.make n dummy_var in
    List.iter (fun (i,x) -> v.(i) <- x) bindings ;
    List.iter
      (fun (i,x) ->
         (* [a.(i)] gets the least index which has an equal value, or [i] *)
         a.(i) <-
           try
             for j = 0 to i do
               if v.(j) = x then raise (Found j)
             done ;
             assert false
           with
             | Found j -> j)
      bindings ;
    a

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

(** {1 Indexing} *)

(** Patterns allow eigenvariables and nabla variables as deBruijn indices. *)
type pattern =
  | DB    of int
  | Cst   of Term.id
  | Var of int
  | Lam   of int * pattern
  | App   of int * pattern list (* Store the length of the list *)
  | Hole

type 'a t        = 'a node list
and  'a node     = pattern list * 'a children
and  'a children = Refine of 'a t | Leaf of 'a ConstraintsMap.t

let empty = []

exception Cannot_table

let observe term = Term.observe (Norm.hnorm term)

(** [create_node bindings terms data] compiles the terms into patterns
  * and associates them a leaf containing the data.
  * Terms are expected to be reversed. *)
let create_node ~allow_eigenvar bindings terms data =
  let rec compile n bindings term = match observe term with
    | Term.DB i -> DB i, n, bindings
    | Term.Var {Term.tag=Term.Constant;Term.name=id} -> Cst id, n, bindings
    | Term.Var var when allow_eigenvar && var.Term.tag = Term.Eigen ->
        Var n, (n+1), (n,var)::bindings
    | Term.Lam (i,t) ->
        let pat,n,bindings = compile n bindings t in
          Lam (i,pat),n,bindings
    | Term.App (h,terms) ->
        let terms = h::terms in
        let patterns,n,bindings =
          List.fold_left
            (fun (pats,n,b) t ->
               let (p,n,b) = compile n b t in
                 (p::pats,n,b))
            ([],n,bindings)
            terms
        in
          App (List.length terms, List.rev patterns),n,bindings
    | _ -> raise Cannot_table
  in
  let patterns,_,bindings =
    List.fold_left
      (fun (pats,n,binds) term ->
         let pat,n,binds = compile n binds term in
           pat::pats,n,binds)
      ([],List.length bindings,bindings)
      terms
  in
    patterns, Leaf (new_leaf bindings data)

(* [superficial_match] expects a head-normalized term. *)
let superficial_match patterns terms =
  let sub (pat,term) = match pat, Term.observe term with
    | DB i, Term.DB j
    | Lam (i,_), Term.Lam (j,_) -> i=j
    | Cst i, Term.Var {Term.name=j;Term.tag=Term.Constant} -> i=j
    | Var _, Term.Var {Term.tag=Term.Eigen} -> true
    | App (i,_), Term.App (h,l) -> i = 1 + List.length l
    | Hole, _ -> true
    | _ -> false
  in
    List.for_all sub (List.map2 (fun a b -> a,b) patterns terms)

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
    match pattern, observe term with
      | DB i, Term.DB j when i = j ->
          (false, DB i, bindings, catches, former_alt)
      | Cst c, Term.Var {Term.name=c';Term.tag=Term.Constant} when c=c' ->
          (false, Cst c, bindings, catches, former_alt)
      | Var i, Term.Var var when allow_eigenvar && var.Term.tag=Term.Eigen ->
          (false, Var i, (i,var)::bindings, catches, former_alt)
      | App (i,patterns), Term.App (h,terms) when i = 1 + List.length terms ->
          let terms = h::terms in
          let (changed,patterns,bindings,catches,former_alt) =
            update_patterns bindings catches former_alt patterns terms
          in
          let patterns = List.rev patterns in
            assert (List.length patterns = i) ;
            (changed, App (i,patterns), bindings, catches, former_alt)
      | Lam (i,pattern), Term.Lam (j,term) when i = j ->
          let (changed,pattern,bindings,catches,former_alt) =
            update_pattern bindings catches former_alt pattern term
          in
            (changed, Lam (i,pattern), bindings, catches, former_alt)
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
      if changed then
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
              Leaf (update_leaf map bindings data)

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
    update_index [] (List.map Norm.hnorm terms) [] index

let add ~allow_eigenvar index terms data =
  update ~allow_eigenvar index terms (Some data)

(* == FIND ================================================================= *)

(* Filter a term through a pattern, raise Not_found on mismatch,
 * return the list of bindings and the reversed list of catches. *)
let rec filter bindings catches pattern term =
  match pattern, observe term with
    | DB i, Term.DB j ->
        if i=j then bindings,catches else raise Not_found
    | Cst i, Term.Var {Term.name=j;Term.tag=Term.Constant} ->
        if i=j then bindings,catches else raise Not_found
    | Var i, Term.Var var ->
        if var.Term.tag = Term.Eigen then
          (i,var)::bindings,catches
        else
          raise Not_found
    | Lam (i,pattern), Term.Lam (j,term) ->
        if i=j then
          filter bindings catches pattern term
        else
          raise Not_found
    | App (i,patterns), Term.App (h,l) ->
        if i = 1 + List.length l then
          filter_several bindings catches patterns (h::l)
        else
          raise Not_found
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
  try Some (find [] index (List.map Norm.hnorm terms)) with _ -> None
