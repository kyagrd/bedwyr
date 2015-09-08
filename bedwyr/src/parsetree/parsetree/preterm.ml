(****************************************************************************)
(* Bedwyr -- concrete syntax tree to abstract syntax tree                   *)
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

module Term = Ndcore.Term
module Typing = Typing.Make (IO.Pos)

(* Pre-terms (CST) construction, checking, and translation to AST. *)

exception Empty_command
exception Empty_term
exception Parse_error of IO.Pos.t * string * string

type preterm = IO.Pos.t * rawterm
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
  | Binder              of Term.binder * (IO.Pos.t * string * Typing.Type.t) list * preterm
  | Lam                 of (IO.Pos.t * string * Typing.Type.t) list * preterm
  | App                 of preterm * preterm * preterm list
  | Tuple               of preterm * preterm * preterm list

let compare =
  let rec aux_vars = function
    | [],[] -> 0
    | (_,n1,ty1)::vars1,(_,n2,ty2)::vars2 ->
        let rn = compare n1 n2 in
        if rn <> 0 then rn
        else let rty = Typing.Type.compare ty1 ty2 in
        if rty <> 0 then rty
        else aux_vars (vars1,vars2)
    | [],_ -> -1
    | _,[] -> 1
  and aux_raw = function
    | Binder (b1,vars1,pt1),Binder (b2,vars2,pt2) ->
        let rb = compare b1 b2 in
        if rb <> 0 then rb
        else let rpt = aux (pt1,pt2) in
        if rpt <> 0 then rpt
        else aux_vars (vars1,vars2)
    | Binder _,_ -> 1
    | _,Binder _ -> -1
    | Lam (vars1,pt1),Lam (vars2,pt2) ->
        let rpt = aux (pt1,pt2) in
        if rpt <> 0 then rpt
        else aux_vars (vars1,vars2)
    | Lam _,_ -> 1
    | _,Lam _ -> -1
    | App (t1,t2,tl),App (u1,u2,ul) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else let r2 = aux (t2,u2) in
        if r2 <> 0 then r2
        else aux_list (tl,ul)
    | App _,_ -> 1
    | _,App _ -> -1
    | Tuple (t1,t2,tl),Tuple (u1,u2,ul) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else let r2 = aux (t2,u2) in
        if r2 <> 0 then r2
        else aux_list (tl,ul)
    | Tuple _,_ -> 1
    | _,Tuple _ -> -1
    | Arrow (t1,t2),Arrow (u1,u2) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else aux (t2,u2)
    | Arrow _,_ -> 1
    | _,Arrow _ -> -1
    | Or (t1,t2),Or (u1,u2) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else aux (t2,u2)
    | Or _,_ -> 1
    | _,Or _ -> -1
    | And (t1,t2),And (u1,u2) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else aux (t2,u2)
    | And _,_ -> 1
    | _,And _ -> -1
    | Eq (t1,t2),Eq (u1,u2) ->
        let r1 = aux (t1,u1) in
        if r1 <> 0 then r1
        else aux (t2,u2)
    | Eq _,_ -> 1
    | _,Eq _ -> -1
    | rt1,rt2 -> compare rt1 rt2
  and aux_list = function
    | [],[] -> 0
    | pt1::pts1,pt2::pts2 ->
        let r = aux (pt1,pt2) in
        if r <> 0 then r
        else aux_list (pts1,pts2)
    | [],_ -> -1
    | _,[] -> 1
  and aux = function
    | (_,rt1),(_,rt2) -> aux_raw (rt1,rt2)
  in
  fun pt1 pt2 -> aux (pt1,pt2)

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

exception Qed_error of IO.Pos.t

type flavour = Normal | Inductive | CoInductive

module Command = struct
  type t =
    | Kind    of (IO.Pos.t * string) list * Typing.Kind.t
    | Type    of (IO.Pos.t * string) list * Typing.Type.t
    | Def     of (flavour * IO.Pos.t * string * Typing.Type.t) list *
                 (IO.Pos.t * preterm * preterm) list
    | Theorem of (IO.Pos.t * string * preterm)
    | Qed     of IO.Pos.t
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
    | Show_def      of IO.Pos.t * string
    | Show_table    of IO.Pos.t * string
    | Clear_tables
    | Clear_table   of IO.Pos.t * string
    | Save_table    of IO.Pos.t * string * string
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
  | `Term               of IO.Pos.t * preterm
  | `MetaCommand        of MetaCommand.t
  ]

type term_mode =
  [
  | `Term               of IO.Pos.t * preterm
  ]


exception Term_typing_error of IO.Pos.t * Typing.Type.t * Typing.Type.t * Typing.Type.Unifier.u

let type_check_and_translate
      ?stratum
      ~head
      ~free_args
      ~free_types
      pre_term
      expected_type
      (typed_declared_obj,typed_intern_pred,kind_check) =
  (* return (and create if needed) a typed variable
   * corresponding to the name of a free variable *)
  let typed_free_var (p,name) =
    let was_free = Term.is_free name in
    let t = Term.atom ~tag:Term.Logic name in
    let v = Term.get_var t in
    try begin
      let ty,_ = Hashtbl.find free_types v in
      Hashtbl.replace free_types v (ty,None) ;
      t,ty
    end with Not_found ->
      let t,v =
        if was_free then t,v else begin
          (* the var existed prior to this type-checking process, so
           * let's re-create it as new *)
          Term.free name ;
          (* XXX in case we actually use this variable on day,
           * we should depend on the level to create an instantiable variable,
           * ie not always a Logic one (cf [Prover.System.mk_clause])*)
          let t = Term.atom ~tag:Term.Logic name in
          let v = Term.get_var t in
          t,v
        end
      in
      let ty = Typing.Type.fresh_var () in
      Hashtbl.replace free_types v (ty,Some p) ;
      t,ty
  (* find the type corresponding to a De-Bruijn index *)
  and find_db s bvars =
    if s="_" then None else
      let rec aux n = function
        | [] -> None
        | (name,ty)::_ when name=s -> Some (Term.db n,ty)
        | _::bvars -> aux (n+1) bvars
      in
      aux 1 bvars
  and instantiate_params = Typing.Type.instantiate_params () in
  let rec aux ?(head=false) ~negative (p,rt) exty bvars u =
    try match rt with
      | QString s ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.string in
          Term.qstring s,u
      | Nat i ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.nat in
          Term.nat i,u
      | FreeBoundID s ->
          begin match find_db s bvars with
            | Some (t,ty) -> (* (upper-case) bound variable *)
                let u = Typing.Type.Unifier.refine u exty ty in
                t,u
            | None -> (* free variable *)
                let t,ty = typed_free_var (p,s) in
                let u = Typing.Type.Unifier.refine u exty ty in
                t,u
          end
      | PredConstBoundID s ->
          begin match find_db s bvars with
            | Some (t,ty) -> (* (lower-case) bound variable *)
                let u = Typing.Type.Unifier.refine u exty ty in
                t,u
            | None -> (* declared object *)
                let forbidden_stratum = (if negative then stratum else None) in
                let t,ty =
                  typed_declared_obj
                    ~instantiate_type:(not head) ?forbidden_stratum (p,s)
                in
                let u = Typing.Type.Unifier.refine u exty ty in
                t,u
          end
      | InternID s ->
          let t,ty = typed_intern_pred (p,s) in
          let u = Typing.Type.Unifier.refine u exty ty in
          t,u
      | True ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          Term.op_true,u
      | False ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          Term.op_false,u
      | Eq (pt1,pt2) ->
          let ty = Typing.Type.fresh_var () in
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          let t1,u = aux ~negative pt1 ty bvars u in
          let t2,u = aux ~negative pt2 ty bvars u in
          Term.op_eq t1 t2,u
      | And (pt1,pt2) ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          let t1,u = aux ~negative pt1 Typing.Type.prop bvars u in
          let t2,u = aux ~negative pt2 Typing.Type.prop bvars u in
          Term.op_and t1 t2,u
      | Or (pt1,pt2) ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          let t1,u = aux ~negative pt1 Typing.Type.prop bvars u in
          let t2,u = aux ~negative pt2 Typing.Type.prop bvars u in
          Term.op_or t1 t2,u
      | Arrow (pt1,pt2) ->
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          let t1,u = aux ~negative:(not negative) pt1 Typing.Type.prop bvars u in
          let t2,u = aux ~negative pt2 Typing.Type.prop bvars u in
          Term.op_arrow t1 t2,u
      | Binder (b,vars,pt) ->
          let arity = List.length vars in
          let r_vars,bvars =
            List.fold_left
              (fun (r_vars,bvars) (p,name,ty) ->
                 let ty = instantiate_params ty in
                 ((p,ty)::r_vars,(name,ty)::bvars))
              ([],bvars)
              vars
          in
          let u = Typing.Type.Unifier.refine u exty Typing.Type.prop in
          let t,u = aux ~negative pt Typing.Type.prop bvars u in
          List.iter
            (fun (p,ty) ->
               let ty = Typing.Type.Unifier.norm ~unifier:u ty in
               let _ = kind_check ~obj:(Typing.QuantVar None) ~p ty in
               ())
            r_vars ;
          Term.binder b arity t,u
      | Lam (vars,pt) ->
          let arity = List.length vars in
          let bvars,r_tys =
            List.fold_left
              (fun (bvars,r_tys) (p,name,ty) ->
                 let ty = instantiate_params ty in
                 let _ = kind_check ~obj:Typing.AbsVar ~p ty in
                 ((name,ty)::bvars,ty::r_tys))
              (bvars,[])
              vars
          in
          let ty = Typing.Type.fresh_var () in
          let tys = List.rev r_tys in
          let u = Typing.Type.Unifier.refine u exty (Typing.Type.arrow tys ty) in
          let t,u = aux ~negative pt ty bvars u in
          Term.lambda arity t,u
      | App (phd,parg,pargs) ->
          let tys = Typing.Type.fresh_vars (1 + List.length pargs)
          and ty = Typing.Type.fresh_var () in
          let u = Typing.Type.Unifier.refine u exty ty in
          let hd,u = aux ~head ~negative phd (Typing.Type.arrow tys ty) bvars u in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux ~negative pt ty bvars u in u,t::args)
                         (u,[])
                         (parg::pargs)
                         tys
          in
          Term.app hd (List.rev args),u
      | Tuple (pt1,pt2,ptl) ->
          let ty1 = Typing.Type.fresh_var ()
          and ty2 = Typing.Type.fresh_var ()
          and tys = Typing.Type.fresh_vars (List.length ptl) in
          let u = Typing.Type.Unifier.refine u exty (Typing.Type.tuple ty1 ty2 (List.rev tys)) in
          let hd = Term.tuple in
          let u,args = List.fold_left2
                         (fun (u,args) pt ty ->
                            let t,u = aux ~negative pt ty bvars u in u,t::args)
                         (u,[])
                         (pt1::pt2::ptl)
                         (ty1::ty2::tys)
          in
          Term.app hd (List.rev args),u
    with Typing.Type.Unifier.Type_unification_error (ty1,ty2,unifier) ->
      raise (Term_typing_error (p,ty1,ty2,unifier))
  in
  let term,unifier =
    aux ~head ~negative:false
      pre_term expected_type [] !Typing.Type.Unifier.global_unifier
  in
  Typing.Type.Unifier.global_unifier := unifier ;
  let p,_ = pre_term in
  (* type-check free variables as quantified variables were, except if
   * they are bound to be abstracted *)
  let singletons =
    Hashtbl.fold
      (fun v (ty,unique_pos) singletons ->
         let n = Term.get_var_name v in
         let obj =
           if List.mem n free_args
           then Typing.AbsVar
           else (Typing.QuantVar (Some n))
         in
         let _ = kind_check ~obj ~p ty in
         match unique_pos with
           | Some pos when n<>"_" -> (pos,n)::singletons
           | _ -> singletons)
      free_types
      []
  in
  (List.sort (fun (p1,_) (p2,_) -> Pervasives.compare p2 p1) singletons),term
