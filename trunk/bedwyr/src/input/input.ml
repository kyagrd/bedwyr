(****************************************************************************)
(* Parsing and type-checking for the Bedwyr prover                          *)
(* Copyright (C) 2012-2015 Quentin Heath                                    *)
(* Copyright (C) 2013 Alwen Tiu                                             *)
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

exception Illegal_byte_sequence of char
exception Illegal_string_comment of pos
exception Illegal_token of string * string
exception Unknown_command of string
exception EOF_error of string
exception Empty_command
exception Empty_term
exception Parse_error of pos * string * string

module I = struct
  type pos = pos'
  let dummy_pos = dummy_pos'
end
module Typing = Typing.Make (I)

type preterm = pos * rawterm
and rawterm =
  | QString             of string
  | Nat                 of int
  | FreeBoundID         of string
  | PredConstBoundID    of string
  | InternID            of string
  | True
  | False
  | Eq                  of preterm * preterm
  | And                 of preterm * preterm
  | Or                  of preterm * preterm
  | Arrow               of preterm * preterm
  | Binder              of Term.binder * (pos * string * Typing.ty) list * preterm
  | Lam                 of (pos * string * Typing.ty) list * preterm
  | App                 of preterm * preterm * preterm list
  | Tuple               of preterm * preterm * preterm list

(* Pre-terms creation *)

let pre_qstring p s = p,QString s
let pre_nat p i = p,Nat i
let pre_freeid p s = p,FreeBoundID s
let pre_predconstid ?(infix=false) p s =
  let s = if infix then "("^s^")" else s in
  p,PredConstBoundID s
let pre_internid p s = p,InternID s
let pre_true p = p,True
let pre_false p = p,False
let pre_eq p t1 t2 = p,Eq (t1,t2)
let pre_and p t1 t2 = p,And (t1,t2)
let pre_or p t1 t2 = p,Or (t1,t2)
let pre_arrow p t1 t2 = p,Arrow (t1,t2)
let pre_binder p b vars t =
  match vars,t with
    | [],_ -> t
    | _,(_,Binder (b',vars',t)) when b=b' -> p,Binder (b,vars@vars',t)
    | _,_ -> p,Binder (b,vars,t)
let pre_lambda p vars t =
  match vars,t with
    | [],_ -> t
    | _,(_,Lam (vars',t)) -> p,Lam (vars@vars',t)
    | _,_ -> p,Lam (vars,t)
let pre_app p t ts =
  match t,List.rev ts with
    | hd,[] -> hd
    | (_,App (hd,arg,args1)),args2 -> p,App (hd,arg,args1@args2)
    | hd,arg::args -> p,App (hd,arg,args)
let pre_tuple p t1 t2 ts = p,Tuple (t1,t2,List.rev ts)

(* Pre-terms manipulation *)

let free_args pre_term =
  let in_arg accum = function
    | _,FreeBoundID "_" -> accum
    | _,FreeBoundID s -> s::accum
    | _ -> accum
  in
  let rec in_app = function
    | _,App (phd,parg,pargs) ->
        List.rev_append (in_app phd) (List.fold_left in_arg [] (parg::pargs))
    | _ -> []
  in
  in_app pre_term


(* Input AST *)

exception Qed_error of pos

type flavour = Normal | Inductive | CoInductive

module Command = struct
  type t =
    | Kind    of (pos * string) list * Typing.ki
    | Type    of (pos * string) list * Typing.ty
    | Def     of (flavour * pos * string * Typing.ty) list *
                 (pos * preterm * preterm) list
    | Theorem of (pos * string * preterm)
    | Qed     of pos
end

module MetaCommand = struct
  type t =
    | Exit
    | Help
    | Include       of string list
    | Reload
    | Session       of string list
    | Debug         of string option
    | Time          of string option
    | Equivariant   of string option
    | Freezing      of int
    | Saturation    of int
    | Env
    | Type_of       of preterm
    | Show_def      of pos * string
    | Show_table    of pos * string
    | Clear_tables
    | Clear_table   of pos * string
    | Save_table    of pos * string * string
    | Export        of string
    | Assert        of preterm
    | Assert_not    of preterm
    | Assert_raise  of preterm
end

type definition_mode =
  [
  | `Command            of Command.t
  | `MetaCommand        of MetaCommand.t
  ]

type toplevel =
  [
  | `Term               of pos * preterm
  | `MetaCommand        of MetaCommand.t
  ]

type term_mode =
  [
  | `Term               of pos * preterm
  ]

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
  let rec aux ?(head=false) ~negative (p,rt) exty bvars u =
    try match rt with
      | QString s ->
          let u = Typing.unify_constraint u exty Typing.tstring in
          Term.qstring s,u
      | Nat i ->
          let u = Typing.unify_constraint u exty Typing.tnat in
          Term.nat i,u
      | FreeBoundID s ->
          begin match find_db s bvars with
            | Some (t,ty) -> (* (upper-case) bound variable *)
                let u = Typing.unify_constraint u exty ty in
                t,u
            | None -> (* free variable *)
                let t,ty = typed_free_var (p,s) in
                let u = Typing.unify_constraint u exty ty in
                t,u
          end
      | PredConstBoundID s ->
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
      | InternID s ->
          let t,ty = typed_intern_pred (p,s) in
          let u = Typing.unify_constraint u exty ty in
          t,u
      | True ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          Term.op_true,u
      | False ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          Term.op_false,u
      | Eq (pt1,pt2) ->
          let ty = Typing.fresh_tyvar () in
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 ty bvars u in
          let t2,u = aux ~negative pt2 ty bvars u in
          Term.op_eq t1 t2,u
      | And (pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_and t1 t2,u
      | Or (pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_or t1 t2,u
      | Arrow (pt1,pt2) ->
          let u = Typing.unify_constraint u exty Typing.tprop in
          let t1,u = aux ~negative:(not negative) pt1 Typing.tprop bvars u in
          let t2,u = aux ~negative pt2 Typing.tprop bvars u in
          Term.op_arrow t1 t2,u
      | Binder (b,vars,pt) ->
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
      | Lam (vars,pt) ->
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
      | App (phd,parg,pargs) ->
          let tys = Typing.fresh_tyvars (1 + List.length pargs)
          and ty = Typing.fresh_tyvar () in
          let u = Typing.unify_constraint u exty ty in
          let hd,u = aux ~head ~negative phd (Typing.ty_arrow tys ty) bvars u in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux ~negative pt ty bvars u in u,t::args)
                         (u,[])
                         (parg::pargs)
                         tys
          in
          Term.app hd (List.rev args),u
      | Tuple (pt1,pt2,ptl) ->
          let ty1 = Typing.fresh_tyvar ()
          and ty2 = Typing.fresh_tyvar ()
          and tys = Typing.fresh_tyvars (List.length ptl) in
          let u = Typing.unify_constraint u exty (Typing.ttuple ty1 ty2 (List.rev tys)) in
          let hd = Term.tuple in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux ~negative pt ty bvars u in u,t::args)
                         (u,[])
                         (pt1::pt2::ptl)
                         (ty1::ty2::tys)
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
  let p,_ = pre_term in
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
