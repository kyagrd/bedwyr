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

(* Kinds, types, unifying and pretty-printing. *)

module type INPUT = sig
  type pos
  val dummy_pos : pos
end

module type S = sig
  type pos
  val dummy_pos : pos

  type ki = Ki of ki list * ki_base
  and ki_base =
    | KType
  val ki_arrow : ki list -> ki -> ki
  val ktype : ki

  val pp_kind : Format.formatter -> ki -> unit
  val kind_to_string : ki ->string

  type ty = Ty of ty list * ty_base
  and ty_base =
    | TConst      of string
    | TProp
    | TString
    | TNat
    | TVar        of int
    | TParam      of int
  val ty_arrow : ty list -> ty -> ty
  val tconst : string -> ty
  val tprop : ty
  val tstring : ty
  val tnat : ty
  val tvar : int -> ty
  val tparam : int -> ty
  val fresh_tyvar : unit -> ty
  val fresh_typaram : unit -> ty
  val build_abstraction_types : int -> ty list * ty

  val pp_type : Format.formatter -> ty -> unit
  val type_to_string : ty -> string

  exception Type_kinding_error of pos * ki * ki
  val kind_check :
    ?atomic_kind:(pos * string -> ki) ->
    ty ->
    ki ->
    bool * bool * bool * bool

  type type_unifier
  val iter : (int -> ty -> unit) -> type_unifier -> unit
  val global_unifier : type_unifier ref
  val ty_norm : ?unifier:type_unifier -> ty -> ty
  val pp_type_norm :
    ?unifier:type_unifier -> Format.formatter -> ty -> unit
  val type_to_string_norm :
    ?unifier:type_unifier -> ty -> string

  exception Hollow_type of string
  val check_ground : string -> ty -> unit
  exception Type_unification_error of ty * ty * type_unifier
  val unify_constraint : type_unifier -> ty -> ty -> type_unifier
end

module Make (I : INPUT) = struct
  type pos = I.pos
  let dummy_pos = I.dummy_pos

  (* Utility to get a 'to_string' from a 'print'.
   * XXX factorize with the code in ndcore/Pprint? *)
  let formatter,do_formatter =
    let buf = Buffer.create 20 in
    let chan = Format.formatter_of_buffer buf in
      chan,
      (fun f ->
         assert (Buffer.length buf = 0) ;
         f () ;
         Format.pp_print_flush chan () ;
         assert (Buffer.length buf > 0) ;
         let s = Buffer.contents buf in
         Buffer.clear buf ;
         s)

  (* Kinds *)

  type ki = Ki of ki list * ki_base
  and ki_base =
    | KType

  let ktype = Ki ([],KType)
  let ki_arrow kis = function
    | Ki (kis',ki)        -> Ki (kis@kis',ki)

  let pp_kind chan ki =
    let rec aux par chan = function
      | Ki (ki::kis,ki_base) ->
          let print =
            if par then Format.fprintf chan "@[(%a -> %a)@]"
            else Format.fprintf chan "@[%a -> %a@]"
          in
          print (aux true) ki (aux false) (Ki (kis,ki_base))
      | Ki ([],KType) ->
          Format.fprintf chan "*"
    in
    Format.fprintf chan "@[%a@]" (aux false) ki

  let kind_to_string ki =
    do_formatter (fun () -> pp_kind formatter ki)

  (* Types *)

  type ty = Ty of ty list * ty_base
  and ty_base =
    | TConst      of string
    | TProp
    | TString
    | TNat
    | TVar        of int
    | TParam      of int

  let ty_arrow tys = function
    | Ty (tys',ty)        -> Ty (tys@tys',ty)
  let tconst name = Ty ([],TConst name)
  let tprop = Ty ([],TProp)
  let tstring = Ty ([],TString)
  let tnat = Ty ([],TNat)
  let tvar i = Ty ([],TVar i)
  let tparam i = Ty ([],TParam i)

  let fresh_tyvar =
    let count = ref 0 in
    fun () ->
      count := 1 + !count;
      tvar (!count)

  let fresh_typaram =
    let count = ref 0 in
    fun () ->
      count := 1 + !count;
      tparam (!count)

  let build_abstraction_types arity =
    let rec aux tys ty = function
      | 0 -> tys, ty
      | a when a>0 ->
          aux ((fresh_typaram ())::tys) ty (a-1)
      | _ -> assert (false)
    in
    aux [] (fresh_typaram ()) arity

  let pp_type chan ty =
    let rec aux par chan = function
      | Ty (ty::tys,ty_base) ->
          let print =
            if par then Format.fprintf chan "@[(%a -> %a)@]"
            else Format.fprintf chan "@[%a -> %a@]"
          in
          print (aux true) ty (aux false) (Ty (tys,ty_base))
      | Ty ([],TConst name) ->
          Format.fprintf chan "%s" name
      | Ty ([],TProp) ->
          Format.fprintf chan "prop"
      | Ty ([],TString) ->
          Format.fprintf chan "string"
      | Ty ([],TNat) ->
          Format.fprintf chan "nat"
      | Ty ([],TVar i) ->
          Format.fprintf chan "'%d" i
      | Ty ([],TParam i) ->
          Format.fprintf chan "?%d" i
    in
    Format.fprintf chan "@[%a@]" (aux false) ty

  let type_to_string ty =
    do_formatter (fun () -> pp_type formatter ty)

  (* Kind checking *)

  exception Type_kinding_error of pos * ki * ki

  (* XXX all kind are assumed to be "*" (KType),
   * so no real check is done here *)
  let kind_check ?(atomic_kind=(fun _ -> ktype)) ty expected_kind =
    let check_eq ki expected_ki =
      if ki <> expected_ki
      then raise (Type_kinding_error (dummy_pos,expected_ki,ki))
    in
    let rec aux ty ki =
      let Ty (tys,ty_base) = ty in
      let (f,h,p,ho) = (* flex, hollow, propositional, higher order *)
        List.fold_left
          (fun (_,h,_,ho) ty ->
             let (_,h',p',ho') = aux ty ki in
             (false,h || h',false,ho || p' || ho'))
          (true,false,false,false) tys
      in
      match ty_base with
        | TConst name ->
            (* XXX real position of the type? *)
            check_eq (atomic_kind (dummy_pos,name)) ki ;
            (false,h,false,ho)
        | TProp ->
            check_eq ktype ki ;
            (false,h,true,ho)
        | TString | TNat ->
            check_eq ktype ki ;
            (false,h,false,ho)
        | TVar _ ->
            (* TODO have a table of kinds of type variables
             * TODO also choose whether a variable can be propositional *)
            check_eq ktype ki ;
            (false,h,false,ho)
        | TParam _ ->
            (* XXX either ensure the input type is normalised,
             * or resolve the parameters here *)
            (f,true,false,ho)
    in
    aux ty expected_kind


  (* type unifier type *)
  module Unifier = Map.Make(struct type t = int let compare = compare end)
  type type_unifier = ty Unifier.t

  let iter = Unifier.iter

  let global_unifier : ty Unifier.t ref = ref Unifier.empty

  let ty_norm ?unifier ty =
    let u = match unifier with
      | None -> !global_unifier
      | Some u -> u
    in
    let rec aux = function
      | Ty (tys,ty_base) ->
          aux_base (List.map aux tys) ty_base
    and aux_base tys ty_base = match ty_base with
      | TConst _ | TProp | TString | TNat | TVar _ ->
          Ty (tys,ty_base)
      | TParam i ->
          try ty_arrow tys (aux (Unifier.find i u))
          with Not_found -> Ty (tys,ty_base)
    in
    aux ty

  let pp_type_norm ?unifier chan ty =
    let ty = match unifier with
      | None -> ty_norm ty
      | Some unifier -> ty_norm ~unifier ty
    in pp_type chan ty

  let type_to_string_norm ?unifier ty =
    let ty = match unifier with
      | None -> ty_norm ty
      | Some unifier -> ty_norm ~unifier ty
    in
    type_to_string ty

  exception Hollow_type of string

  let check_ground name ty =
    let _,hollow,_,_ =
      kind_check (ty_norm ty) ktype
    in
    if hollow then raise (Hollow_type name)

  let occurs unifier i ty =
    let rec aux = function
      | Ty (tys,ty_base) ->
          List.exists aux tys || aux_base ty_base
    and aux_base = function
      | TConst _ | TProp | TString | TNat | TVar _ -> false
      | TParam j ->
          if i=j then true
          else try aux (Unifier.find j unifier)
          with Not_found -> false
    in
    aux ty

  exception Type_unification_error of ty * ty * ty Unifier.t

  (* TODO [unifier] needs to be GC-ed,
   * or at least we should avoid unnecessary chained references *)
  let unify_constraint unifier ty1' ty2' =
    let rec aux u ty1 ty2 = match ty1,ty2 with
      | _ when ty1 = ty2 -> u
      | Ty (ty1::tys1,ty_base1),Ty (ty2::tys2,ty_base2) ->
          let u = aux u ty1 ty2 in
          aux u (Ty (tys1,ty_base1)) (Ty (tys2,ty_base2))
      | Ty ([],TParam i),_ when Unifier.mem i u ->
          let ty1 = Unifier.find i u in
          aux u ty1 ty2
      | _,Ty ([],TParam j) when Unifier.mem j u ->
          let ty2 = Unifier.find j u in
          aux u ty1 ty2
      | Ty ([],TParam i),_ ->
          if occurs u i ty2
          then raise (Type_unification_error (ty1',ty2',unifier))
          else Unifier.add i ty2 u
      | _,Ty ([],TParam j) ->
          if occurs u j ty1
          then raise (Type_unification_error (ty1',ty2',unifier))
          else Unifier.add j ty1 u
      | _ ->
          raise (Type_unification_error (ty1',ty2',unifier))
    in
    aux unifier ty1' ty2'
end
