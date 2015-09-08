(****************************************************************************)
(* Bedwyr -- higher-order pattern unification                               *)
(* Copyright (C) 2006 Gopalan Nadathur, Natalie Linnell, Axelle Ziegler     *)
(* Copyright (C) 2006,2007,2009,2010 David Baelde                           *)
(* Copyright (C) 2009 Zach Snow                                             *)
(* Copyright (C) 2011,2012 Quentin Heath                                    *)
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

type error =
  | OccursCheck
  | TypesMismatch
  | ConstClash of (Term.term * Term.term)

exception Error of error
exception NotLLambda of Term.term
exception IllegalVariable of Term.term

let not_ll x = raise (NotLLambda x)
let illegal_variable x = raise (IllegalVariable x)
let non_normal () = raise Term.NonNormalTerm
let raise_error e = raise (Error e)

module type Param =
sig
  val instantiatable : Term.tag
  val constant_like  : Term.tag
end

module Make (P:Param) =
struct

open P
open Term

let constant tag =
  tag = Constant || tag = constant_like
let variable tag =
  tag = instantiatable
let fresh = fresh instantiatable

(* Transform a term to represent substitutions under abstractions *)
let lift t n = match observe t with
  | QString _ | Nat _ | Var _ | NB _ | True | False -> t
  | DB i -> db (i+n)
  | _ -> susp t 0 n []

(* Transform a list of arguments to represent eta fluffing *)
let rec lift_args l n = match l,n with
  | [],0 -> []
  | [],n -> (db n)::lift_args [] (n-1)
  | (a::rargs),n -> (lift a n)::lift_args rargs n

(* [check_flex_args l fts flts] checks that a list of terms meets the LLambda
 * requirements for the arguments of a flex term whose timestamp and
 * local timestamp are [fts] and [flts].
 * @raise NotLLambda if the list doesn't satisfy the requirements *)
let rec check_flex_args l fts flts =
  (* Check whether a var doesn't appears in a list of terms *)
  let rec unique_var v = function
    | [] -> true
    | t::rargs  ->
        begin match observe t with
          | Var v' when v=v' -> false
          | _ -> unique_var v rargs
        end
  in
  (* Check whether a bound variable doesn't appears in a list of terms *)
  let rec unique_bv i = function
    | [] -> true
    | t::rargs ->
        begin match observe t with
          | DB j when i=j -> false
          | _ -> unique_bv i rargs
        end
  in
  (* Check whether a nabla variable doesn't appears in a list of terms *)
  let rec unique_nb i = function
    | [] -> true
    | t::tl ->
        begin match observe t with
          | NB j when i=j -> false
          | _ -> unique_nb i tl
        end
  in
  match l with
    | [] -> ()
    | t::q ->
        begin match observe t with
          | Var v when constant v.tag && v.ts>fts && unique_var v q ->
              check_flex_args q fts flts
          | DB i when unique_bv i q -> check_flex_args q fts flts
          | NB i when i>flts && unique_nb i q -> check_flex_args q fts flts
          | _ -> not_ll t
        end

(* Simple occurs-check and level check to allow unification in very
 * simple non-llambda cases (when [check_flex_args] fails).
 * [t] should be head-normalized.
 *
 * XXX Note that the level checks are useless on the left (this is in fact
 * true everywhere in this module) and that making them tighter on the right
 * can be dangerous. In a nutshell: this is very simple but suffices. *)
let can_bind v t =
  let rec aux n t =
    match observe t with
      | Var v' -> v' <> v && v'.ts <= v.ts && v'.lts <= v.lts
      | DB i -> i <= n
      | NB j -> j <= v.lts
      | Binop (_,x,y) -> aux n (Norm.hnorm x) && aux n (Norm.hnorm y)
      | Binder (_,n',t) -> aux (n+n') (Norm.hnorm t)
      | Lam (n',t) -> aux (n+n') t
      | App (h,ts) -> List.for_all (aux n) (h::List.map Norm.hnorm ts)
      | Susp _ -> non_normal ()
      | _ -> true
  in
  aux 0 t

(* [cindex c l n] return a nonzero index iff the constant [c]
 * appears in [l]; the index is the position from the right, representing
 * the DeBruijn index of the abstraction capturing the argument.
 * Arguments in the list are expected to be head-normalized. *)
let rec cindex c l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | Var c' when c=c' -> n
        | _ -> cindex c q (n-1)
      end

(* [bvindex bv l n] returns a nonzero index iff the db index [bv]
 * appears in [l]; the index is the position from the right, representing
 * the DeBruijn index of the abstraction capturing the argument.
 * Arguments in the list are expected to be head-normalized. *)
let rec bvindex i l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | DB j when i=j -> n
        | _ -> bvindex i q (n-1)
      end

(* [nbindex nv l n] returns a nonzero index iff the nb index [nv]
 * appears in [l]; the index is the position from the right, representing
 * the DeBruijn index of the abstraction capturing the argument.
 * Arguments in the list are expected to be head-normalized. *)
let rec nbindex i l n = match l with
  | [] -> 0
  | t::q ->
      begin match observe t with
        | NB j when i=j -> n
        | _ -> nbindex i q (n-1)
      end

(* Given a flexible term [v1 a11 ... a1n] and another term of the form
 * [... (v2 a21 ... a2m) ...] where [v1] and [v2] are distinct variables,
 * [ts1] and [ts2] being the timestamps associated with [v1] and [v2],
 * and [lev] being the number of abstractions under which [v2] appears
 * embedded in the second term,
 * [raise_and_invert ts1 ts2 [a11 .. a1n] [a21 .. a2m] lev]
 * return a triple consisting of:
 *
 * {ul
 * {li a truth value indicating whether a pruning or raising
 * substitution is needed for [v2],}
 * {li a list of terms [b1 ... bk] such that the term
 * [Lam ... Lam (... (v2' b1 ... bk) ...]
 * represents a unifying substitution for [v1] -- these terms
 * consist of constants from [a11 ... a1n] over which [v2] is
 * possibly raised and inversions of a pruned [a21 ... a2m], and}
 * {li the arguments [c1 ... ck] of a possible "raising" and pruning
 * substitution for [v2] matching the arguments [b1 ... bk] for
 * [v2'] in the second component.}}
 *
 * The composition of the arguments lists can be understood
 * qualitatively as follows:
 *
 * If [ts1 < ts2] then {ul{li the initial part of
 * [b1 ... bk] is the indices of constants from [a11 ... a1n] that do
 * not appear in [a21 ... a2m] and that have a timestamp less than or
 * equal to [ts2] (this corresponds to raising [v2]) and} {li the rest of
 * [b1 ... bk] are the indices (relative to the list a11 ... a1n) of
 * the constants in [a21 ... a2m] that appear in [a11 ... a1n] (these are
 * the arguments that must not be pruned).}} Correspondingly, the first
 * part of the list [c1 ... ck] are the constants from [a11 ... a1n] over
 * which [v2] is "raised" and the second part are the indices relative
 * to [a21 ... a2m] of the constants that are not pruned.
 *
 * If [ts1 >= ts2]
 * then each of [b1 ... bk] is either {ul{li a constant in [a21 ... a2m] that
 * does not appear in [a11 ... a1n] and which has a timestamp less than
 * [ts1] (this corresponds to first raising [v1] and then reducing the
 * substitution generated for [v1])} {li or it is the index, relative to
 * [a11 ... a1n], of the terms in [a21 ... a2m] that are in
 * [a11 ... a1n].}}
 * The list [c1 ... ck] in this case are simply the indices
 * relative to [a21 ... a2m] of the terms in [a21 ... a2m] that are
 * preserved (i.e. not pruned) in [b1 ... bk].
 *
 * This definition assumes that the [aij] are in
 * head-normal form and that [a1] and [a2] satisfies the LLambda
 * requirements. If [a2] does not satisfy these requirements, an
 * exception will be raised. *)
let raise_and_invert v1 v2 a1 a2 lev =
  let stamps = function {ts=ts;lts=lts} -> ts,lts in
  let ts1,lts1 = stamps v1 in
  let ts2,lts2 = stamps v2 in
  let l1 = List.length a1 in

  (* [raise_var args n] generates the collection of
   * constants in [args] that have a time stamp less than [ts2],
   * assuming [n] is the index for the abstraction corresponding
   * to the first term in [args]. In other words, constants which cannot
   * appear in [v2]'s body.
   * This serves to raise [v2] in the case where [ts1 < ts2]. The boolean
   * component of the returned triple tells if there is
   * any raising to be done. The terms in [args] are assumed to be
   * constants or de Bruijn indices or nabla indices, as head normalized
   * arguments satisfying the LLambda restriction. *)
  let rec raise_var l n = match l with
    | [] -> false,[],[]
    | t::tl ->
        begin match observe t with
          | Var {ts=ts} when ts<=ts2 ->
              let _,inds,consts = raise_var tl (n-1) in
              (true,(db (n+lev))::inds,t::consts)
          | NB j when j<=lts2 ->
              let _,inds,consts = raise_var tl (n-1) in
              (true,(db (n+lev))::inds,t::consts)
          | _ -> raise_var tl (n-1)
        end
  in

  (* [prune args n] "prunes" those items in [args] that are not
   * bound by an embedded abstraction and that do not appear in
   * [a1]. At the same time inverts the items that are not pruned
   * and that are not bound by an embedded abstraction; [n] is assumed to be
   * the length of [args] here and hence yields the index of the
   * leftmost argument position. This pruning computation is
   * relevant to the case when [ts1 < ts2]. The terms in [args]
   * are assumed to be constants or de Bruijn or nabla indices. *)
  let rec prune l n = match l,n with
    | [],0 -> false,[],[]
    | t::q,n ->
        begin match observe t with
          | Var v ->
              let pruned,inds1,inds2 = prune q (n-1) in
              begin match cindex v a1 l1 with
                | 0 -> (true,inds1,inds2)
                | j ->
                    (pruned,
                     (db (j+lev))::inds1,
                     (db n)::inds2)
              end
          | DB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
              if i <= lev then
                (pruned,t::inds1,(db n)::inds2)
              else begin match bvindex (i-lev) a1 l1 with
                | 0 -> (true,inds1,inds2)
                | j ->
                    (pruned,
                     (db (j+lev))::inds1,
                     (db n)::inds2)
              end
          | NB i ->
              let pruned,inds1,inds2 = prune q (n-1) in
              begin match nbindex i a1 l1 with
                | 0 -> (true,inds1,inds2)
                | j ->
                    (pruned,
                     (db (j+lev))::inds1,
                     (db n)::inds2)
              end
          | _ -> assert false
        end
    | _ -> assert false
  in

  (* Relevant to the case when [ts1 > ts2]. In this case,
   * [prune_and_raise args n] prunes those constants and de
   * Bruijn indices not bound by an embedded abstraction that do
   * not appear in [a1] and, in the case of constants, that have
   * a timestamp greater than [ts1]. These constants are preserved
   * via a raising of [v1].
   * As in prune, [n] is assumed to be the length of the list
   * args. The terms in [args] are assumed to be constants, nabla or
   * de Bruijn indices. *)
  let rec prune_and_raise l n = match l,n with
    | [],0 -> false,[],[]
    | a::q,n ->
        begin match observe a with
          | Var v ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
              if v.ts <= ts1 then
                (pruned,a::inds1,(db n)::inds2)
              else
                begin match cindex v a1 l1 with
                  | 0 -> (true,inds1,inds2)
                  | j ->
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                end
          | DB i ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
              if i <= lev then
                (pruned,a::inds1,(db n)::inds2)
              else begin match bvindex (i-lev) a1 l1 with
                | 0 -> (true,inds1,inds2)
                | j ->
                    (pruned,
                     (db (j+lev))::inds1,
                     (db n)::inds2)
              end
          | NB i ->
              let pruned,inds1,inds2 = prune_and_raise q (n-1) in
              if i <= lts1 then
                pruned,a::inds1,(db n)::inds2
              else
                begin match nbindex i a1 l1 with
                  | 0 -> (true,inds1,inds2)
                  | j ->
                      (pruned,
                       (db (j+lev))::inds1,
                       (db n)::inds2)
                end
          | _ -> assert false
        end
    | _ -> assert false
  in

  if ts1<ts2 || lts1<lts2 then
    let raised,args_r1,args_r2 = raise_var a1 l1 in
    let pruned,args_p1,args_p2 = prune a2 (List.length a2) in
    (raised||pruned,args_r1@args_p1,args_r2@args_p2)
  else
    prune_and_raise a2 (List.length a2)

(* Generating the arguments of a pruning substitution for the case
 * when trying to unify two flexible terms of the form (v t_1 ... t_n)
 * and lam ... lam (v s_1 ... s_m) where there are j abstractions at the
 * head of the second term. The first two arguments to prune_same_var
 * are the two lists of arguments, the third argument is j (i.e. the
 * number of abstractions at the head) and the last argument is n+j. It
 * is assumed that type consistency has been checked beforehand,
 * i.e. n+j is indeed equal to m and also that the two argument lists
 * are known to be of the form required for LLambda unification. The
 * computation essentially does the eta fluffing of the first term on
 * the fly (i.e. each t_i has to be lifted over j abstractions and and
 * j new arguments bound by these abstractions are added to the first
 * term). *)
let rec prune_same_var l1 l2 j bl = match l1,l2 with
  | [],[] -> []
  | [],t::q ->
      begin match observe t with
        | DB i when i=j -> (db bl)::(prune_same_var [] q (j-1) (bl-1))
        | _ -> prune_same_var [] q (j-1) (bl-1)
      end
  | t1::a1,t2::a2 ->
      begin match observe t1,observe t2 with
        | Var v1,Var v2 when v1==v2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | DB i1,DB i2 when i1+j=i2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | NB i1,NB i2 when i1=i2 ->
            (db bl)::(prune_same_var a1 a2 j (bl-1))
        | _ -> prune_same_var a1 a2 j (bl-1)
      end
  | _ -> assert false

(* [makesubst h1 t2 a1] unifies [App (h1,a1) = t2].
 * Given a term of the form [App (h1,a1)] where [h1] is a variable and
 * another term [t2], generate an LLambda substitution for [h1] if this is
 * possible, making whatever pruning and raising substitution that are
 * necessary to variables appearing within [t2].
 *
 * [t2] is assumed to be head-normalized.
 *
 * The unification computation is split into two parts, one that
 * examines the top level structure of [t2] and the other that descends
 * into its nested subparts. This organization is useful primarily
 * because [h1], the variable head of the first term can appear at the
 * toplevel in t2 without sacrificing unifiability but not in a nested
 * part.
 *
 * @raise NotLLambda in a non LLambda situation
 * @raise Error if there is a unification failure or a type mismatch
 * (if an a priori type checking has not been done) happens
 *)
let makesubst h1 t2 a1 =
  let n = List.length a1 in
  (* Check that h1 is a variable, get its timestamps *)
  let v1,ts1,lts1 = match observe h1 with
    | Var v when variable v.tag -> v,v.ts,v.lts
    | Susp _ -> non_normal ()
    | _ -> assert false
  in
  let a1 = List.map Norm.hnorm a1 in

  (* Generating a substitution term and performing raising and
   * pruning substitutions corresponding to a non top-level
   * (sub)term. In this case the variable being bound cannot appear
   * embedded inside the term. Exceptions can be raised if unification fails
   * or if LLambda conditions are found to be violated.
   * The incoming term should be head-normalized. *)
  let rec nested_subst c lev =
    match observe c with
      | Var v2 when variable v2.tag ->
          if eq c h1 then raise_error OccursCheck ;
          let (changed,a1',a2') = raise_and_invert v1 v2 a1 [] lev in
            if changed || not (lts1 >= v2.lts && ts1 >= v2.ts) then
              let h'= fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts) in
              bind c (app h' a2') ;
              app h' a1'
            else
              app c a1'
      | Var {tag=tag} when not (constant tag) -> illegal_variable c
      (* If [h1] can't depend on [c], [c] must belong to the argument list. *)
      | Var v when not (v.ts <= ts1 && v.lts <= lts1) ->
          begin match cindex v a1 n with
            | 0 -> raise_error OccursCheck
            | j -> db (j+lev)
          end
      | DB i when i>lev ->
          begin match bvindex (i-lev) a1 n with
            | 0 -> raise_error OccursCheck
            | j -> db (j+lev)
          end
      | NB i when i>lts1 ->
          begin match nbindex i a1 n with
            | 0 -> raise_error OccursCheck
            | j -> db (j+lev)
          end
      | Binop (b,x,y) ->
          op_binop b
            (nested_subst (Norm.hnorm x) lev)
            (nested_subst (Norm.hnorm y) lev)
      | Binder (b,n,t) ->
          binder b n
            (nested_subst (Norm.hnorm t) (lev+n))
      | Lam (n,t) ->
          lambda n (nested_subst t (lev+n))
      | App (h2,a2) ->
          begin match observe h2 with
            | Var v2 when variable v2.tag ->
                if eq h2 h1 then raise_error OccursCheck ;
                let a2 = List.map Norm.hnorm a2 in
                let ts2,lts2 = v2.ts,v2.lts in
                check_flex_args a2 ts2 lts2 ;
                let changed,a1',a2' = raise_and_invert v1 v2 a1 a2 lev in
                if changed then begin
                  let h' = fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 ts2) in
                  bind h2 (lambda (List.length a2) (app h' a2')) ;
                  app h' a1'
                end else if not (lts1 >= lts2 && ts1 >= ts2) then begin
                  let h' = fresh ~lts:(min lts1 v2.lts) ~ts:ts1 in
                  bind h2 h' ;
                  app h' a1'
                end else
                  app h2 a1'
            | Var {tag=tag} when not (constant tag) -> illegal_variable h2
            | Lam _ | App _ | Susp _ -> non_normal ()
            | _ ->
                app
                  (nested_subst h2 lev)
                  (List.map (fun x -> nested_subst (Norm.hnorm x) lev) a2)
          end
      | Susp _ -> non_normal ()
      (* If [h1] can depend on [c], the substitution is [c] itself,
       * and the llambda restriction ensures that this is the only solution. *)
      | _ -> c
  in

  (* Processing toplevel structure in generating a substitution.
   * First descend under abstractions. Then if the term is a
   * variable, generate the simple substitution. Alternatively, if
   * it is an application with the variable being bound as its head,
   * then generate the pruning substitution. In all other cases,
   * pass the task on to nested_subst. An optimization is possible
   * in the case that the term being examined has no outer
   * abstractions (i.e. lev = 0) and its head is a variable with a
   * time stamp greater than that of the variable being bound. In
   * this case it may be better to invoke raise_and_invert
   * directly with the order of the "terms" reversed.
   *
   * The incoming term should be head-normalized. *)
  let rec toplevel_subst t2 lev =
    match observe t2 with
      | Lam (n,t2) -> toplevel_subst t2 (lev+n)
      | Var v2 when variable v2.tag ->
          if h1=t2 then
            if n=0 && lev=0 then h1 else raise_error TypesMismatch
          else begin
            if not (lts1 >= v2.lts && ts1 >= v2.ts) then
              bind t2 (fresh ~lts:(min lts1 v2.lts) ~ts:(min ts1 v2.ts)) ;
            lambda (lev+n) t2
          end
      (* TODO the following seems harmless, and is sometimes useful..
      | Var v2 when not (constant v2.tag) && a1=[] ->
          lambda lev t2 (* [n] is 0 *)
         XXX shouldn't it rather be the following?
      | Var {tag=tag} when not (constant tag) -> illegal_variable h2
      *)
      | App (h2,a2) ->
          begin match observe h2 with
            | Var {ts=ts2;lts=lts2} when eq h1 h2 ->
                (* [h1] being instantiatable, no need to check it for [h2] *)
                let a2 = List.map Norm.hnorm a2 in
                check_flex_args a2 ts2 lts2 ;
                let bindlen = n+lev in
                if bindlen = List.length a2 then begin
                  let h1' = fresh ~lts:lts1 ~ts:ts1 in
                  let args = prune_same_var a1 a2 lev bindlen in
                  lambda bindlen (app h1' args)
                end else raise_error TypesMismatch
            | Susp _ -> non_normal ()
            | _ -> lambda (n+lev) (nested_subst t2 lev)
          end
      | Susp _ -> non_normal ()
      | _ -> lambda (n+lev) (nested_subst t2 lev)
  in

  try
    check_flex_args a1 ts1 lts1 ;
    toplevel_subst t2 0
  with (NotLLambda _) as e ->
        (* Not a pattern: try a very strict occurs-check to allow
         * simple cases of the form v1=t2. *)
    if a1 = [] && (can_bind v1 t2)
    then t2
    else raise e

(* Unifying the arguments of two rigid terms with the same head, these
 * arguments being given as lists. Exceptions are raised if
 * unification fails or if there are unequal numbers of arguments; the
 * latter will not arise if type checking has been done. *)
let rec unify_list l1 l2 =
  try List.iter2 (fun a1 a2 -> unify (Norm.hnorm a1) (Norm.hnorm a2)) l1 l2
  with Invalid_argument _ -> raise_error TypesMismatch

(* [unify_const_term cst t2] unifies the constant [cst] with [t2].
 * [t2] should be head-normalized,
 * different from an instantiable variable or an application.
 * If it is an abstraction, binders need to be equalized
 * and this becomes an application-term unification problem. *)
and unify_const_term cst t2 =
  if eq cst t2 then ()
  else match observe t2 with
    | Lam (n,t2) ->
        let a1 = lift_args [] n in
        unify_app_term cst a1 (app cst a1) t2
    | Susp _ -> non_normal ()
    | _ -> raise_error (ConstClash (cst,t2))

(* [unify_bv_term n1 t1 t2] unifies the bound variable [t1 = DB n1] with [t2].
 * [t2] should be head-normalized,
 * different from an instantiable variable or an application.
 * If it is an abstraction, binders need to be equalized
 * and this becomes an application-term unification problem. *)
and unify_bv_term n1 t1 t2 = match observe t2 with
  | DB n2 when n1=n2 -> ()
  | Lam (n,t2)  ->
      let t1' = lift t1 n in
      let a1 = lift_args [] n in
      unify_app_term t1' a1 (app t1' a1) t2
  | Susp _ -> non_normal ()
  | _ -> raise_error (ConstClash (t1,t2))

(* [unify_nv_term n1 t1 t2] unifies the nabla variable [t1 = NB n1] with [t2].
 * [t2] should be head-normalized,
 * different from an instantiable variable or an application.
 * If it is an abstraction, binders need to be equalized
 * and this becomes an application-term unification problem. *)
and unify_nv_term n1 t1 t2 = match observe t2 with
  | NB n2 when n1=n2 -> ()
  | Lam (n,t2) ->
      let a1 = lift_args [] n in
      unify_app_term t1 a1 (app t1 a1) t2
  | Susp _ -> non_normal ()
  | _ -> raise_error (ConstClash (t1,t2))

(* [unify_app_term h1 a1 t1 t2] solves [App h1 a1 = t2].
 * [h1] should be head-normalized.
 * [t1] should be the term decomposed as [App h1 a1].
 * [t2] should be head-normalized, different from an instantiable variable. *)
and unify_app_term h1 a1 t1 t2 = match observe h1,observe t2 with
  | Var {tag=tag},_ when variable tag -> bind h1 (makesubst h1 t2 a1)
  | Var {tag=tag},_ when not (constant tag) -> illegal_variable h1
  | Lam _,_ | App _,_ | Susp _,_ -> non_normal ()
  | _,Var {tag=tag} when variable tag -> assert false
  | _,Var {tag=tag} when not (constant tag) -> illegal_variable t2
  | _,Lam (n,t2) ->
      let h1' = lift h1 n in
      let a1' = lift_args a1 n in
      let t1' = app h1' a1' in
        unify_app_term h1' a1' t1' t2
  | h1',App (h2,a2) ->
      begin match h1',observe h2 with
        | _,Var {tag=tag} when variable tag -> bind h2 (makesubst h2 t1 a2)
        | _,Var {tag=tag} when not (constant tag) -> illegal_variable h2
        | _,Lam _ | _,App _ | _,Susp _ -> non_normal ()
        | Binop (b1,x1,y1),Binop (b2,x2,y2) when b1=b2 ->
            unify_list (x1::y1::a1) (x2::y2::a2)
        | Binder (b1,n1,x1),Binder (b2,n2,x2) when b1=b2 && n1=n2 ->
            unify_list (x1::a1) (x2::a2)
        | _,_ ->
            if eq h1 h2 then unify_list a1 a2
            else raise_error (ConstClash (h1,h2))
      end
  | _,Susp _ -> non_normal ()
  | _,_ -> raise_error (ConstClash (t1,t2))

(* Main unification procedure.
 *
 * Either succeeds and realizes the unification substitutions as side effects
 * or raises an exception to indicate nonunifiability or to signal
 * a case outside of the LLambda subset. When an exception is raised,
 * it is necessary to catch this and at least undo bindings for
 * variables made in the attempt to unify. This has not been included
 * in the code at present.
 *
 * This procedure assumes that the two terms it gets are in
 * head normal form and that there are no iterated
 * lambdas or applications at the top level. Any necessary adjustment
 * of binders through the eta rule is done on the fly. *)
and unify t1 t2 = match observe t1,observe t2 with
  | Var {tag=tag},_ when variable tag           -> bind t1 (makesubst t1 t2 [])
  | _,Var {tag=tag} when variable tag           -> bind t2 (makesubst t2 t1 [])
  | Var {tag=tag},_ when not (constant tag)     -> illegal_variable t1
  | _,Var {tag=tag} when not (constant tag)     -> illegal_variable t2
  | App (h1,a1),_                 -> unify_app_term h1 a1 t1 t2
  | _,App (h2,a2)                 -> unify_app_term h2 a2 t2 t1
  | QString _,_ | Nat _,_ | Var _,_
  | True,_ | False,_                            -> unify_const_term t1 t2
  | _,QString _ | _,Nat _ | _,Var _
  | _,True | _,False                            -> unify_const_term t2 t1
  | DB n,_                        -> unify_bv_term n t1 t2
  | _,DB n                        -> unify_bv_term n t2 t1
  | NB n,_                        -> unify_nv_term n t1 t2
  | _,NB n                        -> unify_nv_term n t2 t1
  | Binop (b1,x1,y1),Binop (b2,x2,y2) when b1=b2 ->
      unify (Norm.hnorm x1) (Norm.hnorm x2) ;
      unify (Norm.hnorm y1) (Norm.hnorm y2)
  | Binder (b1,n1,t1),Binder (b2,n2,t2) when b1=b2 && n1=n2 ->
      unify (Norm.hnorm t1) (Norm.hnorm t2)
  | Binop _,Binop _ | Binder _,Binder _         -> raise_error TypesMismatch
  | Lam (n1,t1),Lam(n2,t2)   ->
      if n1>n2 then
        unify (lambda (n1-n2) t1) t2
      else
        unify t1 (lambda (n2-n1) t2)
  | Susp _, _ | _, Susp _                       -> non_normal ()
  | _,_                                         -> raise_error TypesMismatch

let pattern_unify t1 t2 = unify (Norm.hnorm t1) (Norm.hnorm t2)

end
