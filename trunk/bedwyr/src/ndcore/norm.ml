(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006 Gopalan Nadathur, Natalie Linnell, Axelle Ziegler     *)
(* Copyright (C) 2006 Andrew Gacek                                          *)
(* Copyright (C) 2006,2007,2010 David Baelde                                *)
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

(* Term (beta-)normalization *)

(* Raise the substitution *)
let rec add_dummies env n m =
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Term.Dum (m+n'))::(add_dummies env n' m))

(* Make an environment appropriate to [n] lambda abstractions
 * applied to the arguments in [args]. Return the environment
 * together with any remaining lambda abstractions and arguments
 * (there can not be both abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e = match n,args with
    | 0,_ | _,[] -> e,n,args
    | _,hd::tl -> aux (n-1) tl (Term.Binding(hd, 0)::e)
  in
  aux n args []

(* Head normalization function.*)
let rec hnorm t =
  match Term.observe t with
    | Term.Lam (n,t) -> Term.lambda n (hnorm t)
    | Term.App (t,args) ->
        let t = hnorm t in
        begin match Term.observe t with
          | Term.Lam (n,t) ->
              let e, n', args' = make_env n args in
              let ol = List.length e in
              hnorm (Term.app (Term.susp (Term.lambda n' t) ol 0 e) args')
          | _ -> Term.app t args
        end
    | Term.Susp (t,ol,nl,e) ->
        let t = hnorm t in
        let susp x = Term.susp x ol nl e in
        begin match Term.observe t with
          | Term.DB i ->
              if i > ol then
                (* The index points to something outside the suspension *)
                Term.db (i-ol+nl)
              else
                (* The index has to be substituted for [e]'s [i]th element *)
                begin match List.nth e (i-1) with
                  | Term.Dum l -> Term.db (nl - l)
                  | Term.Binding (t,l) -> hnorm (Term.susp t 0 (nl-l) [])
                end
          | Term.Binop (b,t1,t2) -> Term.op_binop b (susp t1) (susp t2)
          | Term.Binder (b,n,t) ->
              Term.binder b n (hnorm (Term.susp t (ol+n) (nl+n)
                                           (add_dummies e n nl)))
          | Term.Lam (n,t) ->
              Term.lambda n (hnorm (Term.susp t (ol+n) (nl+n)
                                      (add_dummies e n nl)))
          | Term.App (t,args) ->
              hnorm (Term.app (susp t) (List.map susp args))
          | Term.Susp _ -> raise Term.NonNormalTerm
          | _ -> t
        end
    | _ -> t

(* Full normalization function.*)
let rec deep_norm t =
  let t = hnorm t in
  match Term.observe t with
    | Term.Binop (b,t1,t2) -> Term.op_binop b (deep_norm t1) (deep_norm t2)
    | Term.Binder (b,n,t) -> Term.binder b n (deep_norm t)
    | Term.Lam (n,t) -> Term.lambda n (deep_norm t)
    | Term.App (a,b) ->
        begin match Term.observe a with
          | Term.Binop _ | Term.Binder _ ->
              Term.app (deep_norm a) (List.map deep_norm b)
          | Term.Lam _ | Term.App _ | Term.Susp _ -> raise Term.NonNormalTerm
          | _ -> Term.app a (List.map deep_norm b)
        end
    | Term.Susp _ -> raise Term.NonNormalTerm
    | _ -> t

(* Rename nabla variables in terms according to the order of traversal
 * in the tree representation of the (normal form of the) term.
 * This is a cheap way to force equivariant matching in tables. *)
let nb_rename terms =
  let rec rename term bindings n =
    let term = hnorm term in
    match Term.observe term with
      | Term.NB i ->
          begin try (Term.nabla (List.assoc i bindings),bindings,n)
          with Not_found -> (Term.nabla (n+1),(i,n+1)::bindings,n+1)
          end
      | Term.Binop (b,t1,t2) ->
          let t1,bindings,n = rename t1 bindings n in
          let t2,bindings,n = rename t2 bindings n in
          Term.op_binop b t1 t2,bindings,n
      | Term.Binder (b,i,t) ->
          let t,bindings,n = rename t bindings n in
          Term.binder b i t,bindings,n
      | Term.Lam (i,t) ->
          let t,bindings,n = rename t bindings n in
          (Term.lambda i t),bindings,n
      | Term.App (h,terms) ->
          let newh,bindings,n = rename h bindings n in
          let newterms,bindings,n = multi_rename terms bindings n in
          Term.app newh newterms,bindings,n
      | Term.Susp _ -> raise Term.NonNormalTerm
      | _ -> term,bindings,n
  and multi_rename terms bindings n =
    let revnewterms,bindings,n =
      List.fold_left
        (fun (ts,bds,idx) t ->
           let t,bds,idx = rename t bds idx in
           (t::ts,bds,idx))
        ([],bindings,n)
        terms
    in
    List.rev revnewterms,bindings,n
  in
  let newterms,_,_ = multi_rename terms [] 0 in
  newterms
