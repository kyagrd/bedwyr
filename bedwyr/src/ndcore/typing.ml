(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2012 Quentin Heath                                         *)
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

open Type

type pos = Lexing.position * Lexing.position

(* Pre-terms *)

type preterm = rawpreterm
and rawpreterm =
  | QString of pos * string
  | Nat    of pos * int
  | FreeID of pos * string
  | PredConstID of pos * string
  | InternID of pos * string
  | True   of pos
  | False  of pos
  | Eq     of pos * preterm * preterm
  | And    of pos * preterm * preterm
  | Or     of pos * preterm * preterm
  | Arrow  of pos * preterm * preterm
  | Binder of pos * Term.binder * (pos * string * simple_type) list * preterm
  | Lam    of pos * (pos * string * simple_type) list * preterm
  | App    of pos * preterm * preterm list

let get_pos = function
  | QString (p,_) -> p
  | Nat (p,_) -> p
  | FreeID (p,_) -> p
  | PredConstID (p,_) -> p
  | InternID (p,_) -> p
  | True p -> p
  | False p -> p
  | Eq (p,_,_) -> p
  | And (p,_,_) -> p
  | Or (p,_,_) -> p
  | Arrow (p,_,_) -> p
  | Binder (p,_,_,_) -> p
  | Lam (p,_,_) -> p
  | App (p,_,_) -> p

let set_pos p = function
  | QString (_,s) -> QString (p,s)
  | Nat (_,s) -> Nat (p,s)
  | FreeID (_,s) -> FreeID (p,s)
  | PredConstID (_,s) -> PredConstID (p,s)
  | InternID (_,s) -> InternID (p,s)
  | True _ -> True p
  | False _ -> False p
  | Eq (_,t1,t2) -> Eq (p,t1,t2)
  | And (_,t1,t2) -> And (p,t1,t2)
  | Or (_,t1,t2) -> Or (p,t1,t2)
  | Arrow (_,t1,t2) -> Arrow (p,t1,t2)
  | Binder (_,b,l,t) -> Binder (p,b,l,t)
  | Lam (_,l,t) -> Lam (p,l,t)
  | App (_,hd,tl) -> App (p,hd,tl)


(* Creating pre-terms *)

let change_pos (p1,_) t (_,p2) = set_pos (p1,p2) t

let pre_qstring p s = QString (p,s)
let pre_nat p i = assert (i>=0) ; Nat (p,i)
let pre_freeid p s = FreeID (p,s)
let pre_predconstid p s = PredConstID (p,s)
let pre_internid p s = InternID (p,s)
let pre_true p = True p
let pre_false p = False p
let pre_eq p t1 t2 = Eq (p,t1,t2)
let pre_and p t1 t2 = And (p,t1,t2)
let pre_or p t1 t2 = Or (p,t1,t2)
let pre_arrow p t1 t2 = Arrow (p,t1,t2)

let pre_binder p b vars t = match vars,t with
  | [],_ -> t
  | _,Binder (_,b',vars',t) when b=b' -> Binder (p,b,vars@vars',t)
  | _,_ -> Binder (p,b,vars,t)

let pre_lambda p vars t = match vars,t with
  | [],_ -> t
  | _,Lam (_,vars',t) -> Lam (p,vars@vars',t)
  | _,_ -> Lam (p,vars,t)

let pre_app p hd args = if args = [] then hd else match hd with
  | App (_,hd,args') -> App (p,hd,args'@args)
  | _ -> App (p,hd,args)


(* kind checking *)
exception Type_kinding_error of pos * simple_kind * simple_kind

(* XXX all kind are assumed to be "*", so no real check is done here *)
let kind_check ty expected_kind atomic_kind =
  let check_eq ki expected_ki =
    if ki <> expected_ki
    then raise (Type_kinding_error ((Lexing.dummy_pos,Lexing.dummy_pos),expected_ki,ki))
  in
  let rec aux ty ki tykis (f,h,ho,p) = match ty with
    | Ty name ->
        (* XXX real position of the type? *)
        check_eq (atomic_kind ((Lexing.dummy_pos,Lexing.dummy_pos),name)) ki ;
        begin match tykis with
          | [] -> (false,h,ho,p)
          | (ty,ki)::tykis ->
              aux ty ki tykis (false,h,ho,p)
        end
    | Type.TProp ->
        check_eq KType ki ;
        begin match tykis with
          | [] -> (false,h,ho,true)
          | (ty,ki)::tykis ->
              aux ty ki tykis (false,h,true,p)
        end
    | Type.TString | Type.TNat ->
        check_eq KType ki ;
        begin match tykis with
          | [] -> (false,h,ho,p)
          | (ty,ki)::tykis ->
              aux ty ki tykis (false,h,ho,p)
        end
    | Type.TRArrow ([],ty) ->
        aux ty ki tykis (f,h,ho,p)
    | Type.TRArrow (ty::tys',ty') ->
        aux ty ki ((Type.TRArrow (tys',ty'),ki)::tykis) (false,h,ho,p)
    | Type.TVar _ ->
        (* TODO we need to remember the kinds of type variables! *)
        (*check_eq _ ki ;*)
        begin match tykis with
          | [] -> (f,true,ho,p)
          | (ty,ki)::tykis ->
              aux ty ki tykis (f,true,h,p)
        end
  in
  aux ty expected_kind [] (true,false,false,false) (* flex, hollow, higher order, propositional *)


(* type unifier type *)
module Unifier = Map.Make(struct type t = int let compare = compare end)
type type_unifier = simple_type Unifier.t

let iter = Unifier.iter

let global_unifier : simple_type Unifier.t ref = ref Unifier.empty

let ty_norm ?unifier ty =
  let u = match unifier with
    | None -> !global_unifier
    | Some u -> u
  in
  let rec aux = function
    | Ty _
    | TProp | TString | TNat as ty -> ty
    | TRArrow (tys,ty) ->
        TRArrow (List.map aux tys, aux ty)
    | TVar i as ty ->
        begin try
          let ty = Unifier.find i u in
          aux ty
        with
          | Not_found -> ty
        end
  in
  aux ty


(* type checking *)
exception Type_unification_error of simple_type * simple_type * simple_type Unifier.t
exception Term_typing_error of pos * simple_type * simple_type * simple_type Unifier.t
exception Var_typing_error of string option * pos option * simple_type

let occurs unifier i =
  let rec aux = function
    | Ty _
    | TProp | TString | TNat -> false
    | TRArrow (tys,ty) -> List.exists aux tys || aux ty
    | TVar j ->
        if i=j then true
        else begin try
          let ty = Unifier.find j unifier in
          aux ty
        with
          | Not_found -> false
        end
  in
  aux

(* TODO [unifier] needs to be GC-ed,
 * or at least we should avoid unnecessary chained references *)
let unify_constraint unifier ty1' ty2' =
  let rec aux u ty1 ty2 = match ty1,ty2 with
    | _,_ when ty1 = ty2 -> u
    | TRArrow ([],ty1),_ ->
        aux u ty1 ty2
    | _,TRArrow ([],ty2) ->
        aux u ty1 ty2
    | TVar i,_ when Unifier.mem i u ->
        let ty1 = Unifier.find i u in
        aux u ty1 ty2
    | _,TVar j when Unifier.mem j u ->
        let ty2 = Unifier.find j u in
        aux u ty1 ty2
    | TVar i,_ ->
        if occurs u i ty2
        then raise (Type_unification_error (ty1',ty2',unifier))
        else Unifier.add i ty2 u
    | _,TVar j ->
        if occurs u j ty1
        then raise (Type_unification_error (ty1',ty2',unifier))
        else Unifier.add j ty1 u
    | TRArrow (ty1::tys1,bty1),TRArrow (ty2::tys2,bty2) ->
        let u = aux u ty1 ty2 in
        aux u (TRArrow (tys1,bty1)) (TRArrow (tys2,bty2))
    | _ ->
        raise (Type_unification_error (ty1',ty2',unifier))
  in
  aux unifier ty1' ty2'

let build_abstraction_types arity =
  let rec aux tys ty = function
    | 0 -> tys, ty
    | a when a>0 ->
        aux ((fresh_tyvar ())::tys) ty (a-1)
    | _ -> assert (false)
  in
  aux [] (fresh_tyvar ()) arity

let type_check_and_translate pre_term expected_type typed_free_var normalize_types typed_declared_var typed_intern_var bound_var_type infer =
  let find_db s bvars =
    let rec aux n = function
      | [] -> None
      | (p,name,ty)::_ when name=s -> Some (Term.db n,ty)
      | _::bvars -> aux (n+1) bvars
    in
    aux 1 bvars
  in
  let rec aux pt exty bvars u =
    let p = get_pos pt in
    try match pt with
      | QString (p,s) ->
          let u = unify_constraint u exty TString in
          Term.qstring s,u
      | Nat (p,i) ->
          let u = unify_constraint u exty TNat in
          Term.nat i,u
      | FreeID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) ->
                let u = unify_constraint u exty ty in
                t,u
            | None ->
                let t,ty = typed_free_var (p,s) in
                let u = unify_constraint u exty ty in
                t,u
          end
      | PredConstID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) ->
                let u = unify_constraint u exty ty in
                t,u
            | None ->
                let t,ty = typed_declared_var (p,s) in
                let u = unify_constraint u exty ty in
                t,u
          end
      | InternID (p,s) ->
          let t,ty = typed_intern_var (p,s) in
          let u = unify_constraint u exty ty in
          t,u
      | True p ->
          let u = unify_constraint u exty TProp in
          Term.op_true,u
      | False p ->
          let u = unify_constraint u exty TProp in
          Term.op_false,u
      | Eq (p,pt1,pt2) ->
          let ty = fresh_tyvar () in
          let u = unify_constraint u exty TProp in
          let t1,u = aux pt1 ty bvars u in
          let t2,u = aux pt2 ty bvars u in
          Term.op_eq t1 t2,u
      | And (p,pt1,pt2) ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux pt1 TProp bvars u in
          let t2,u = aux pt2 TProp bvars u in
          Term.op_and t1 t2,u
      | Or (p,pt1,pt2) ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux pt1 TProp bvars u in
          let t2,u = aux pt2 TProp bvars u in
          Term.op_or t1 t2,u
      | Arrow (p,pt1,pt2) ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux pt1 TProp bvars u in
          let t2,u = aux pt2 TProp bvars u in
          Term.op_arrow t1 t2,u
      | Binder (p,b,vars,pt) ->
          let arity = List.length vars in
          let bvars = List.rev_append vars bvars in
          let _ = List.map bound_var_type vars in
          let u = unify_constraint u exty TProp in
          let t,u = aux pt TProp bvars u in
          List.iter
            (fun (p,_,ty) ->
               let ty = ty_norm ~unifier:u ty in
               let (_,_,higher_order,propositional) =
                 (* TODO replace this dummy atomic_kind by a no-op one *)
                 kind_check ty KType (fun _ -> KType)
               in
               if higher_order || propositional
               then raise (Var_typing_error (None,Some p,ty)))
            vars ;
          Term.binder b arity t,u
      | Lam (p,vars,pt) ->
          let arity = List.length vars in
          let bvars = List.rev_append vars bvars in
          let tys = List.map bound_var_type vars in
          let ty = fresh_tyvar () in
          let u = unify_constraint u exty (TRArrow (tys,ty)) in
          let t,u = aux pt ty bvars u in
          Term.lambda arity t,u
      | App (p,phd,pargs) ->
          let arity = List.length pargs in
          let tys,ty = build_abstraction_types arity in
          let u = unify_constraint u exty ty in
          let hd,u = aux phd (TRArrow (tys,ty)) bvars u in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux pt ty bvars u in u,t::args)
                         (u,[])
                         pargs
                         tys
          in
          Term.app hd (List.rev args),u
    with
      | Type_unification_error (ty1,ty2,unifier) ->
          raise (Term_typing_error (p,ty1,ty2,unifier))
  in
  let term,unifier = aux pre_term expected_type [] !global_unifier in
  normalize_types
    (fun v ty ->
       let ty = ty_norm ~unifier:unifier ty in
       let (_,_,higher_order,propositional) =
         (* TODO replace this dummy atomic_kind by a no-op one *)
         kind_check ty KType (fun _ -> KType)
       in
       if higher_order || propositional
       then raise (Var_typing_error (Some (Term.get_var_name v),None,ty)) ;
       ty) ;
  if infer then begin
    global_unifier := unifier ;
    term,expected_type
  end else begin
    term,(ty_norm ~unifier:unifier expected_type)
  end
