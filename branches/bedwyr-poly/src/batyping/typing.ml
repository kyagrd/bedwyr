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

  type ki
  val ki_arrow : ki list -> ki -> ki
  val ktype : ki


  val pp_kind : Format.formatter -> ki -> unit
  val kind_to_string : ki ->string

  type ty
  val ty_arrow : ty list -> ty -> ty
  val tconst : string -> ty list -> ty
  val tprop : ty
  val tstring : ty
  val tnat : ty
  val tvar : int -> ty
  val tparam : int -> ty
  val fresh_tyvar : unit -> ty
  val get_tyvar : string -> ty
  val fresh_typaram : unit -> ty
  val fresh_tyinst : ty -> ty
  val build_abstraction_types : int -> ty list * ty

  val pp_type : Format.formatter -> ty -> unit
  val type_to_string : ty -> string

  exception Type_kinding_error of string * pos option * ki * ki
  val kind_check :
    ?p:pos ->
    ty ->
    atomic_kind:(pos * string -> ki) ->
    bool * bool * bool * bool

  type type_unifier
  val iter : (int -> ty -> unit) -> type_unifier -> unit
  val global_unifier : type_unifier ref
  val clear : unit -> unit
  val ty_norm : ?unifier:type_unifier -> ty -> ty
  val pp_type_norm :
    ?unifier:type_unifier -> Format.formatter -> ty -> unit
  val type_to_string_norm :
    ?unifier:type_unifier -> ty -> string

  exception Hollow_type of string
  val check_ground :
    string ->
    ty ->
    atomic_kind:(pos * string -> ki) ->
    unit
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

  let ktypes n =
    let rec aux tys m =
      if m > 0 then aux (ktype :: tys) (m-1)
      else Ki (tys,KType)
    in
    aux [] n

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
    | TConst      of string * (ty list) (* user-defined type constructors *)
    | TProp
    | TString
    | TNat
    | TVar        of int                (* type variables (for polymorphism) *)
    | TParam      of int                (* type parameters (for type inference) *)

  let ty_arrow tys = function
    | Ty (tys',ty)        -> Ty (tys@tys',ty)
  let tconst name args = Ty ([],TConst (name, args))
  let tprop = Ty ([],TProp)
  let tstring = Ty ([],TString)
  let tnat = Ty ([],TNat)
  let tvar i = Ty ([],TVar i)
  let tparam i = Ty ([],TParam i)

  let fresh_tyvar =
    let count = ref 0 in
    fun () ->
      incr count ;
      tvar (!count)

  let get_tyvar =
    let bindings = ref [] in
    fun s ->
      try List.assoc s !bindings
      with Not_found ->
        let ty = fresh_tyvar () in
        bindings := (s,ty) :: !bindings ; ty

  let fresh_typaram =
    let count = ref 0 in
    fun () ->
      incr count ;
      tparam (!count)

  (* Create a fresh instance of a polymorphic type.
   * All type variables are replaced with fresh type parameters. *)
  let fresh_tyinst ty =
    let bindings = ref [] in
    let rec aux accum = function
      | Ty (ty::tys,ty_base) ->
          aux ((aux [] ty)::accum) (Ty (tys,ty_base))
      | Ty ([],TConst (name,tys)) ->
          let tys = List.map (aux []) tys in
          Ty (List.rev accum,TConst (name,tys))
      | Ty ([],TVar i) ->
          let ty =
            try List.assoc i !bindings
            with Not_found ->
              let ty = fresh_typaram () in
              bindings := (i,ty) :: !bindings ; ty
          in
          ty_arrow (List.rev accum) ty
      | ty ->
          ty_arrow (List.rev accum) ty
    in
    aux [] ty

  let build_abstraction_types arity =
    let rec aux tys ty a =
      if a>0 then aux ((fresh_typaram ())::tys) ty (a-1)
      else tys,ty
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
      | Ty ([],TConst (name,tys)) ->
          let print =
            if par & List.length tys<>0
            then Format.fprintf chan "@[(%s%a)@]"
            else Format.fprintf chan "@[%s%a@]"
          in
          print name aux2 tys
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
    and aux2 chan =
      List.iter (fun ty -> Format.fprintf chan " %a" (aux true) ty)
    in
    Format.fprintf chan "@[%a@]" (aux false) ty

  let type_to_string ty =
    do_formatter (fun () -> pp_type formatter ty)

  (* Kind checking *)

  exception Type_kinding_error of string * pos option * ki * ki

  (* Run all kind of checks, and return
   * (f,h,p,ho) = (flex_head, hollow, propositional, higher order). *)
  let kind_check ?p ty ~atomic_kind =
    let rec aux ty =
      let Ty (tys,ty_base) = ty in
      let (h,ho) = List.fold_left aux2 (false,false) tys in
      match ty_base with
        | TConst (name,tys) ->
            (* XXX real position of the type? *)
            let Ki (kis,KType) = atomic_kind (dummy_pos,name) in
            let h,ho =
              try List.fold_left2 aux3 (h,ho) tys kis
              with Invalid_argument _ ->
                raise (Type_kinding_error
                         (name,p,
                          ktypes (List.length tys),Ki (kis,KType)))
            in
            (false,h,false,ho)
        | TProp -> (false,h,true,ho)
        | TString | TNat -> (false,h,false,ho)
        | TVar _ -> (false,h,false,ho)
        | TParam _ -> (true,true,false,ho)
    and aux2 (h,ho) ty =
      let (_,h',p',ho') = aux ty in
      (h || h',ho || p' || ho')
    and aux3 x ty ki =
      if ki<>ktype then assert false
      else aux2 x ty
    in
    aux ty
    (* aux (fresh_tyinst ty) *)


  (* type unifier type *)
  module Unifier = Map.Make(struct type t = int let compare = compare end)
  type type_unifier = ty Unifier.t

  let iter = Unifier.iter

  let global_unifier : ty Unifier.t ref = ref Unifier.empty

  let clear () =
    global_unifier := Unifier.empty

  let ty_norm ?(unifier=(!global_unifier)) ty =
    let rec aux = function
      | Ty (tys,ty_base) ->
          aux_base (List.map aux tys) ty_base
    and aux_base tys ty_base = match ty_base with
      | TProp | TString | TNat | TVar _ ->
          Ty (tys,ty_base)
      | TConst (name,tys1) ->
          Ty (tys,TConst (name,List.map aux tys1))
      | TParam i ->
          try ty_arrow tys (aux (Unifier.find i unifier))
          with Not_found -> Ty (tys,ty_base)
    in
    aux ty

  let kind_check ?p ty ~atomic_kind =
    kind_check ?p (ty_norm ty) ~atomic_kind

  let pp_type_norm ?unifier chan ty =
    let ty = ty_norm ?unifier ty in
    pp_type chan ty

  let type_to_string_norm ?unifier ty =
    let ty = ty_norm ?unifier ty in
    type_to_string ty

  exception Hollow_type of string

  let check_ground name ty ~atomic_kind =
    let _,hollow,_,_ =
      kind_check ty ~atomic_kind
    in
    if hollow then raise (Hollow_type name)

  let occurs unifier i ty =
    let rec aux = function
      | Ty (tys,ty_base) ->
          List.exists aux tys || aux_base ty_base
    and aux_base = function
      | TProp | TString | TNat | TVar _ -> false
      | TConst (_,tys) -> List.exists aux tys
      | TParam j ->
          if i=j then true
          else try aux (Unifier.find j unifier)
          with Not_found -> false
    in
    aux ty

  exception Type_unification_error of ty * ty * ty Unifier.t

  (* TODO [unifier] needs to be GC-ed,
   * or at least we should avoid unnecessary chained references,
   * for instance by soft-normaliying (leaving only the last
   * typaram) and removing the pure typarams from the unifier
   *)
  let unify_constraint unifier ty1' ty2' =
    let rec aux u ty1 ty2 = match ty1,ty2 with
      | _ when ty1 = ty2 -> u
      | Ty (ty1::tys1,ty_base1),Ty (ty2::tys2,ty_base2) ->
          let u = aux u ty1 ty2 in
          aux u (Ty (tys1,ty_base1)) (Ty (tys2,ty_base2))
      | Ty ([],TConst (name1,tys1)),Ty ([],TConst(name2,tys2)) ->
          if name1 = name2 then
            try List.fold_left2 aux u tys1 tys2
            with Invalid_argument _ ->
              raise (Type_unification_error (ty1',ty2',unifier))
          else
             raise (Type_unification_error (ty1',ty2',unifier))
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
