(****************************************************************************)
(* An implementation of Higher-Order Pattern Unification                    *)
(* Copyright (C) 2006-2011 Nadathur, Linnell, Baelde, Ziegler, Gacek, Heath *)
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
  in aux n args []

(* Head normalization function.*)
let rec hnorm term =
  match Term.observe term with
    | Term.QString _ | Term.Nat _ | Term.Var _ | Term.DB _ | Term.NB _ | Term.True | Term.False
    | Term.Eq _ | Term.And _ | Term.Or _ | Term.Arrow _ | Term.Binder _ -> term
    | Term.Lam (n,t) -> Term.lambda n (hnorm t)
    | Term.App (t,args) ->
        let t = hnorm t in
        begin match Term.observe t with
          | Term.Lam (n,t) ->
              let e, n', args' = make_env n args in
              let ol = List.length e in
              if n' > 0
              then hnorm (Term.susp (Term.lambda n' t) ol 0 e)
              else hnorm (Term.app (Term.susp t ol 0 e) args')
          | _ -> Term.app t args
        end
    | Term.Susp (t,ol,nl,e) ->
        let t = hnorm t in
        let susp x = Term.susp x ol nl e in
        begin match Term.observe t with
          | Term.QString _ | Term.Nat _ | Term.Var _ | Term.NB _ | Term.True | Term.False -> t
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
          | Term.Eq (t1,t2) -> Term.op_eq (susp t1) (susp t2)
          | Term.And (t1,t2) -> Term.op_and (susp t1) (susp t2)
          | Term.Or (t1,t2) -> Term.op_or (susp t1) (susp t2)
          | Term.Arrow (t1,t2) -> Term.op_arrow (susp t1) (susp t2)
          | Term.Binder (b,n,t) ->
              Term.binder b n (hnorm (Term.susp t (ol+n) (nl+n)
                                           (add_dummies e n nl)))
          | Term.Lam (n,t) ->
              Term.lambda n (hnorm (Term.susp t (ol+n) (nl+n)
                                     (add_dummies e n nl)))
          | Term.App (t,args) ->
              hnorm (Term.app (susp t) (List.map susp args))
          | Term.Ptr _ | Term.Susp _ -> assert false
        end
    | Term.Ptr _ -> assert false

(* Full normalization function.*)
let rec deep_norm t =
  let t = hnorm t in
  match Term.observe t with
    | Term.QString _ | Term.Nat _ | Term.Var _ | Term.DB _ | Term.NB _ | Term.True | Term.False -> t
    | Term.Eq (t1,t2) -> Term.op_eq (deep_norm t1) (deep_norm t2)
    | Term.And (t1,t2) -> Term.op_and (deep_norm t1) (deep_norm t2)
    | Term.Or (t1,t2) -> Term.op_or (deep_norm t1) (deep_norm t2)
    | Term.Arrow (t1,t2) -> Term.op_arrow (deep_norm t1) (deep_norm t2)
    | Term.Binder (b,n,t) -> Term.binder b n (deep_norm t)
    | Term.Lam (n,t) -> Term.lambda n (deep_norm t)
    | Term.App (a,b) ->
        begin match Term.observe a with
          | Term.Var _ | Term.DB _ | Term.NB _ | Term.True | Term.False ->
              Term.app a (List.map deep_norm b)
          | _ -> Term.app (deep_norm a) (List.map deep_norm b)
        end
    | Term.Ptr _ | Term.Susp _ -> assert false
