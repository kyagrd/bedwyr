(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
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

(* (Lazy Head) Normalization *)

let rec make_explicit = function
  | t,0,0,[] -> t
  | t,ol,nl,e ->
      begin match Term.observe t with
        | Term.Lam (n,t) ->
            Term.lambda n
              (Term.susp t (ol+n) (nl+n) (Term.add_dummies e n nl))
        | _ -> assert false
      end

(** Lazy head normalisation.
  * The [whnf] flag tells to not normalize under abstractions. *)
let rec hn_lazy term ol nl e whnf =
  match Term.observe term with
    | Term.Const _
    | Term.Var _ -> (term,0,0,[])
    | Term.DB i ->
        if i>ol then
          (* The index used to point outside the original term,
           * it has to be updated *)
          (Term.db (i-ol+nl)),0,0,[]
        else
          (* The index has to to be substituted for [env]'s [i]th element. *)
          begin try match List.nth e (i-1) with
            | Term.Dum l -> (Term.db (nl-l)),0,0,[]
            | Term.Binding (t,l) -> 
                begin match Term.observe t with
                  | Term.Susp (t',ol',nl',e') ->
                      let s = hn_lazy t' ol' (nl'+nl-l) e' whnf in
                        (* if nl=l then Term.bind t (make_explicit s) ; *)
                        s
                  | x -> hn_lazy t 0 (nl-l) [] whnf
                end
          with
            | Failure "nth" -> assert false
          end
    | Term.Lam (n,t') ->
        if whnf then (term,ol,nl,e) else
          begin match
            (* Normalize the body. TODO Why not whnf ? *)
            if ol=0 && nl=0 then
              hn_lazy t' 0 0 [] false
            else
              hn_lazy
                t' (ol+n)
                (nl+n) (Term.add_dummies e n nl)
                false
          with
            | t',0,0,[] ->
                let abs = match Term.observe t' with
                  | Term.Lam (n',s) -> Term.lambda (n'+n) s
                  | _ -> Term.lambda n t'
                in
                  abs,0,0,[]
            | _ -> assert false (* whnf = false *)
          end
    | Term.App (t1,args) ->
        let argwrap =
          if ol=0 && nl=0
          then (fun x -> x)
          else (fun x -> Term.susp x ol nl e)
        in
        (* Compute the suspension ([refe] [args]),[fol],[fnl],[fe]
         * and normalize it lazily.
         * [nargs] is the length of [args] *)
        let rec contract_and_norm refe args fol fnl fe nargs =
          match Term.observe refe with
            | Term.Lam (n,t) ->
                (* Consume first [n] args and store them in the environment *)
                let rec arg2env n args e = match n with
                  | 0 -> (args,e)
                  | n ->
                      begin match args with
                        | [] -> ([],e)
                        | a::rargs ->
                            arg2env (n-1) rargs
                              ((Term.Binding ((argwrap a),fnl))::e)
                      end
                in
                let rargs,nenv = arg2env n args fe in
                  if n >= nargs then
                    (* All of the args were eaten *)
                    hn_lazy
                      (Term.lambda (n-nargs) t) (fol+nargs)
                      fnl nenv
                      whnf
                  else
                    (* [nargs-n] are remaining *)
                    let (t',ol',nl',e') =
                      hn_lazy t (fol+n) (fnl) (nenv) true
                    in
                      contract_and_norm t' rargs ol' nl' e' (nargs-n)
            | Term.App (t,args') ->
                (* Merge the two App, propagate suspension if needed *)
                if ol=0 && nl=0 then
                  (Term.app t (args'@args)),0,0,[]
                else
                  Term.app t
                    (args'@(List.map
                              (fun a -> Term.susp a ol nl e)
                              args)),0,0,[]
            | t -> 
                if ol=0 && nl=0 then
                  (Term.app refe args),0,0,[]
                else
                  (Term.app refe
                     (List.map
                        (fun a -> Term.susp a ol nl e)
                        args)),0,0,[]
        in

        (* Normalize the head, perform the application *)
        let (f,fol,fnl,fe) = hn_lazy t1 ol nl e true in
        let s = contract_and_norm f args fol fnl fe (List.length args) in
          s
          (* if ol=0 && nl=0 then
            let (t',ol',nl',e') = s in
              if ol'=0 && nl'=0 then Term.bind term t' ;
              s
          else
            s *)
    | Term.Susp (t,ol',nl',e') ->
        let s = hn_lazy t ol' nl' e' whnf in
          if ol=0 && nl=0 then s else
            hn_lazy (make_explicit s) ol nl e whnf
    | Term.Ptr t -> assert false (* deref *)

(** Head normalization function.
  * Note that iterated abstractions and applications are collected
  * at the top level. *)
let hnorm term = 
  match hn_lazy term 0 0 [] false with
    | hnterm,0,0,[] -> hnterm
    | _ -> assert false (* not whnf *)

let rec norm t = match Term.observe t with
  | Term.Var _
  | Term.Const _
  | Term.DB _ -> t
  | Term.Lam (n,t') -> Term.lambda n (norm t')
  | Term.App _ | Term.Susp _ ->
      let t = hnorm t in
      begin match Term.observe t with
        | Term.App (x,lt) -> Term.app (norm x) lt
        | _ -> norm t
      end
  | Term.Ptr _ -> assert false (* deref *)

(* TODO what's norm, hnorm ? difference ? *)
let rec deep_norm t =
  let t = norm t in
    match Term.observe t with
      | Term.Var _ | Term.Const _ | Term.DB _ -> t
      | Term.Lam (n,t) -> Term.lambda n (deep_norm t)
      | Term.App (a,b) ->
            begin match Term.observe a with
              | Term.Var _ | Term.Const _ | Term.DB _ ->
                    Term.app a (List.map deep_norm b)
              | _ -> deep_norm (Term.app (deep_norm a) (List.map deep_norm b))
            end
      | Term.Ptr _ | Term.Susp _ -> assert false
