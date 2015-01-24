(****************************************************************************)
(* Parsing and type-checking for the Bedwyr prover                          *)
(* Copyright (C) 2012-2014 Quentin Heath, Alwen Tiu                         *)
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

(* Pre-terms and pre-AST, translation to terms and checking. *)

type pos = Lexing.position * Lexing.position
and pos' = pos

let dummy_pos = Lexing.dummy_pos,Lexing.dummy_pos
let dummy_pos' = dummy_pos

exception Illegal_string of char
exception Illegal_string_comment
exception Illegal_token of string * string
exception Unknown_command of string

exception Parse_error of pos * string * string

module I = struct
  type pos = pos'
  let dummy_pos = dummy_pos'
end
module Typing = Typing.Make (I)

type preterm = rawpreterm
and rawpreterm =
  | QString of pos * string
  | Nat    of pos * int
  | FreeBoundID of pos * string
  | PredConstBoundID of pos * string
  | InternID of pos * string
  | True   of pos
  | False  of pos
  | Eq     of pos * preterm * preterm
  | And    of pos * preterm * preterm
  | Or     of pos * preterm * preterm
  | Arrow  of pos * preterm * preterm
  | Binder of pos * Term.binder * (pos * string * Typing.ty) list * preterm
  | Lam    of pos * (pos * string * Typing.ty) list * preterm
  | App    of pos * preterm * preterm list

let get_pos = function
  | QString (p,_)
  | Nat (p,_)
  | FreeBoundID (p,_)
  | PredConstBoundID (p,_)
  | InternID (p,_)
  | True p
  | False p
  | Eq (p,_,_)
  | And (p,_,_)
  | Or (p,_,_)
  | Arrow (p,_,_)
  | Binder (p,_,_,_)
  | Lam (p,_,_)
  | App (p,_,_) -> p

let set_pos p = function
  | QString (_,s) -> QString (p,s)
  | Nat (_,s) -> Nat (p,s)
  | FreeBoundID (_,s) -> FreeBoundID (p,s)
  | PredConstBoundID (_,s) -> PredConstBoundID (p,s)
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

(* Pre-terms creation *)

let pre_qstring p s = QString (p,s)
let pre_nat p i = Nat (p,i)
let pre_freeid p s = FreeBoundID (p,s)
let pre_predconstid p s = PredConstBoundID (p,s)
let pre_internid p s = InternID (p,s)
let pre_true p = True p
let pre_false p = False p
let pre_eq p t1 t2 = Eq (p,t1,t2)
let pre_and p t1 t2 = And (p,t1,t2)
let pre_or p t1 t2 = Or (p,t1,t2)
let pre_arrow p t1 t2 = Arrow (p,t1,t2)

let pre_binder p b vars t =
  match vars,t with
    | [],_ -> t
    | _,Binder (_,b',vars',t) when b=b' -> Binder (p,b,vars@vars',t)
    | _,_ -> Binder (p,b,vars,t)

let pre_lambda p vars t =
  match vars,t with
    | [],_ -> t
    | _,Lam (_,vars',t) -> Lam (p,vars@vars',t)
    | _,_ -> Lam (p,vars,t)

let pre_app p hd args = if args = [] then hd else match hd with
  | App (_,hd,args') -> App (p,hd,args'@args)
  | _ -> App (p,hd,args)

(* Pre-terms manipulation *)

let change_pos (p1,_) t (_,p2) = set_pos (p1,p2) t

let free_args pre_term =
  let in_arg accum = function
    | FreeBoundID (_,"_") -> accum
    | FreeBoundID (_,s) -> s::accum
    | _ -> accum
  in
  let rec in_app = function
    | App (_,phd,pargs) ->
        List.rev_append (in_app phd) (List.fold_left in_arg [] pargs)
    | _ -> []
  in
  in_app pre_term


(* Input AST (.def file or toplevel) *)

exception Qed_error of pos

type flavour = Normal | Inductive | CoInductive

type command =
  | Exit
  | Help
  | Include             of string list
  | Reload
  | Session             of string list
  | Debug               of string option
  | Time                of string option
  | Equivariant         of string option
  | Freezing            of int
  | Saturation          of int
  | Env
  | Type_of             of preterm
  | Show_def            of pos * string
  | Show_table          of pos * string
  | Clear_tables
  | Clear_table         of pos * string
  | Save_table          of pos * string * string
  | Export              of string
  | Assert              of preterm
  | Assert_not          of preterm
  | Assert_raise        of preterm

type input =
  | KKind   of (pos * string) list * Typing.ki
  | TType   of (pos * string) list * Typing.ty
  | Def     of (flavour * pos * string * Typing.ty) list *
               (pos * preterm * preterm) list
  | Query   of preterm
  | Command of command
  | Theorem of (pos * string * preterm)
  | Qed     of (pos)

(* Pre-terms' type checking *)

exception Term_typing_error of pos * Typing.ty * Typing.ty * Typing.type_unifier

let type_check_and_translate
      ?stratum
      ~head
      ~free_args
      ~fold_free_types
      ~fresh_tyinst
      pre_term
      expected_type
      (typed_free_var,typed_declared_obj,typed_intern_pred,atomic_kind) =
  (* find the type corresponding to a De-Bruijn index *)
  let find_db s bvars =
    let rec aux n = function
      | [] -> None
      | (name,ty)::_ when name=s -> Some (Term.db n,ty)
      | _::bvars -> aux (n+1) bvars
    in
    aux 1 bvars
  in
  let rec aux ?(head=false) ~negative pt exty bvars u =
    let p = get_pos pt in
    try match pt with
      | QString (_,s) ->
          let u = Typing.unify_constraint u exty Typing.tstring in
          Term.qstring s,u
      | Nat (_,i) ->
          let u = Typing.unify_constraint u exty Typing.tnat in
          Term.nat i,u
      | FreeBoundID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) -> (* (upper-case) bound variable *)
                let u = Typing.unify_constraint u exty ty in
                t,u
            | None -> (* free variable *)
                let t,ty = typed_free_var (p,s) in
                let u = Typing.unify_constraint u exty ty in
                t,u
          end
      | PredConstBoundID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) -> (* (lower-case) bound variable *)
                let u = Typing.unify_constraint u exty ty in
                t,u
            | None -> (* declared object *)
                let forbidden_stratum = (if negative then stratum else None) in
                let t,ty =
                  typed_declared_obj
                    ~instantiate_type:(not head) ?forbidden_stratum (p,s)
                in
                let u = Typing.unify_constraint u exty ty in
                t,u
          end
      | InternID (p,s) ->
          let t,ty = typed_intern_pred (p,s) in
          let u = Typing.unify_constraint u exty ty in
          t,u
      | True _ ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          Term.op_true,u
      | False _ ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          Term.op_false,u
      | Eq (_,pt1,pt2) ->
          let ty = Typing.fresh_tyvar () in
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 ty bvars u in
          let t2,u = aux ~negative pt2 ty bvars u in
          Term.op_eq t1 t2,u
      | And (_,pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_and t1 t2,u
      | Or (_,pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_or t1 t2,u
      | Arrow (_,pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative:(not negative) pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_arrow t1 t2,u
      | Binder (_,b,vars,pt) ->
          let arity = List.length vars in
          let r_vars,bvars =
            List.fold_left
              (fun (r_vars,bvars) (p,name,ty) ->
                 let ty = fresh_tyinst ty in
                 ((p,ty)::r_vars,(name,ty)::bvars))
              ([],bvars)
              vars
          in
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t,u = aux ~negative pt Typing.tprop bvars u in
          List.iter
            (fun (p,ty) ->
               let ty = Typing.ty_norm ~unifier:u ty in
               let _ =
                 Typing.kind_check
                   ~obj:(Typing.QuantVar None) ~p ty ~atomic_kind
               in
               ())
            r_vars ;
          Term.binder b arity t,u
      | Lam (_,vars,pt) ->
          let arity = List.length vars in
          let bvars,r_tys =
            List.fold_left
              (fun (bvars,r_tys) (p,name,ty) ->
                 let ty = fresh_tyinst ty in
                 let _ = Typing.kind_check
                           ~obj:Typing.AbsVar ~p ty ~atomic_kind
                 in
                 ((name,ty)::bvars,ty::r_tys))
              (bvars,[])
              vars
          in
          let ty = Typing.fresh_tyvar () in
          let tys = List.rev r_tys in
          let u = Typing.unify_constraint u exty (Typing.ty_arrow tys ty) in
          let t,u = aux ~negative pt ty bvars u in
          Term.lambda arity t,u
      | App (_,phd,pargs) ->
          let arity = List.length pargs in
          let tys,ty = Typing.build_abstraction_types arity in
          let u = Typing.unify_constraint u exty ty in
          let hd,u = aux ~head ~negative phd (Typing.ty_arrow tys ty) bvars u in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux ~negative pt ty bvars u in u,t::args)
                         (u,[])
                         pargs
                         tys
          in
          Term.app hd (List.rev args),u
    with Typing.Type_unification_error (ty1,ty2,unifier) ->
      raise (Term_typing_error (p,ty1,ty2,unifier))
  in
  let term,unifier =
    aux ~head ~negative:false
      pre_term expected_type [] !Typing.global_unifier
  in
  Typing.global_unifier := unifier ;
  let p = get_pos pre_term in
  (* type-check free variables as quantified variables were, except if
   * they are bound to be abstracted *)
  let singletons = fold_free_types
    (fun v (ty,single_pos) singletons ->
       let n = Term.get_var_name v in
       let obj =
         if List.mem n free_args
         then Typing.AbsVar
         else (Typing.QuantVar (Some n))
       in
       let _ = Typing.kind_check ~obj ~p ty ~atomic_kind in
       match single_pos with
         | Some pos when n<>"_" -> (pos,n)::singletons
         | _ -> singletons)
    []
  in
  singletons,term
