(****************************************************************************)
(* Bedwyr -- prenex polymorphic typing                                      *)
(* Copyright (C) 2011-2015 Quentin Heath                                    *)
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

(* Kinds, types; checking and pretty-printing. *)

module type POSITION = sig
  type t
  val dummy : t
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  type pos

  module Kind : sig
    type t
    val ktype : t
    val arrow : t list -> t -> t
    val pp : Format.formatter -> t -> unit
    val to_string : t -> string
  end

  module Type : sig
    type t
    val const : pos -> string -> t list -> t
    val tuple : t -> t -> t list -> t
    val prop : t
    val string : t
    val nat : t
    val param : int -> t
    val var : int -> t
    val arrow : t list -> t -> t
    val fresh_param : unit -> t
    val get_param : string -> t
    val fresh_var : unit -> t
    val instantiate_params : unit -> t -> t
    val fresh_vars : int -> t list
    val compare : t -> t -> int

    module Unifier : sig
      type u
      val iter : (int -> t -> unit) -> u -> unit
      val global_unifier : u ref
      val clear : unit -> unit

      exception Type_unification_error of t * t * u
      val refine : u -> t -> t -> u
      val norm : ?unifier:u -> t -> t
    end

    val get_pp :
      ?unifier:Unifier.u -> unit -> Format.formatter -> t -> unit
    val pp : Format.formatter -> t -> unit
    val get_to_string :
      ?unifier:Unifier.u -> unit -> t -> string
    val to_string : t -> string
  end

  exception Type_kinding_error of string * pos * Kind.t * Kind.t
  exception Invalid_pred_declaration of string * pos * Type.t
  exception Undefinite_type of string * pos * Type.t * int list
  exception Type_order_error of string option * pos * Type.t

  type obj =
    | Predicate of string
    | Constant of string
    | QuantVar of string option
    | AbsVar
  val kind_check :
    obj:obj ->
    p:pos ->
    Type.t ->
    get_kind:(pos * string -> Kind.t) ->
    int
end

module Make (Pos : POSITION) = struct
  type pos = Pos.t

  (* Utility to get a 'to_string' from a 'print'.
   * XXX factorize with the code in ndcore/Pprint? *)
  let string_of_formatter f =
    let buffer = Buffer.create 20 in
    let formatter = Format.formatter_of_buffer buffer in
    f formatter ;
    Format.pp_print_flush formatter () ;
    Buffer.contents buffer


  (* Kinds *)

  module Kind = struct
    type t = Ki of t list * ki_base
    and ki_base =
      | KType

    let ktype = Ki ([],KType)
    let arrow kis = function
      | Ki (kis',ki) -> Ki (kis@kis',ki)

    let ktypes n =
      let rec aux tys m =
        if m > 0 then aux (ktype :: tys) (m-1)
        else Ki (tys,KType)
      in
      aux [] n

    let pp chan ki =
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

    let to_string ki =
      string_of_formatter (fun formatter -> pp formatter ki)
  end


  (* Types *)

  module Type = struct
    type t = Ty of t list * ty_base
    and ty_base =
      | Const    of pos * string * (t list) (* user-defined type constructors *)
      | Tuple    of t * t * t list          (* predefined tuples constructors *)
      | Prop
      | String
      | Nat
      | Param    of int                     (* type parameters (for polymorphism) *)
      | Var      of int                     (* type variables (for inference) *)


    let const p name args = Ty ([],Const (p,name,List.rev args))
    let tuple arg1 arg2 args = Ty ([],Tuple (arg1,arg2,List.rev args))
    let prop = Ty ([],Prop)
    let string = Ty ([],String)
    let nat = Ty ([],Nat)
    let param i = Ty ([],Param i)
    let var i = Ty ([],Var i)
    let arrow tys (Ty (tys',ty)) = Ty (tys@tys',ty)

    let fresh_param =
      let count = ref 0 in
      fun () ->
        incr count ;
        param (!count)

    let get_param =
      let bindings = ref [] in
      fun s ->
        try List.assoc s !bindings
        with Not_found ->
          let ty = fresh_param () in
          bindings := (s,ty) :: !bindings ; ty

    let fresh_var =
      let count = ref 0 in
      fun () ->
        incr count ;
        var (!count)

    (* Create a fresh instance of a polymorphic type.
     * All type parameters are replaced with fresh type variables. *)
    let instantiate_params () =
      let bindings = ref [] in
      let rec aux accum = function
        | Ty (ty::tys,ty_base) ->
            aux ((aux [] ty)::accum) (Ty (tys,ty_base))
        | Ty ([],Const (p,name,tys)) ->
            let tys = List.map (aux []) tys in
            Ty (List.rev accum,Const (p,name,tys))
        | Ty ([],Tuple (ty1,ty2,tys)) ->
            let ty1 = aux [] ty1
            and ty2 = aux [] ty2
            and tys = List.map (aux []) tys in
            Ty (List.rev accum,Tuple (ty1,ty2,tys))
        | Ty ([],Param i) ->
            let ty =
              try List.assoc i !bindings
              with Not_found ->
                let ty = fresh_var () in
                bindings := (i,ty) :: !bindings ; ty
            in
            arrow (List.rev accum) ty
        | ty ->
            arrow (List.rev accum) ty
      in
      fun ty -> aux [] ty

    let fresh_vars =
      let rec aux tys a =
        if a>0 then aux ((fresh_var ())::tys) (a-1)
        else tys
      in
      aux []

    let compare =
      let rec aux_base = function
        | Prop,Prop | Nat,Nat | String,String -> 0
        | Prop,_ -> -1
        | _,Prop -> 1
        | Nat,_ -> -1
        | _,Nat -> 1
        | String,_ -> -1
        | _,String -> 1
        | Const (_,n1,l1),Const (_,n2,l2) ->
            let r = compare n1 n2 in
            if r <> 0 then r
            else aux_list (l1,l2)
        | Const _,_ -> -1
        | _,Const _ -> 1
        | Tuple (t1,t2,tl),Tuple (u1,u2,ul) ->
            let r1 = aux (t1,u1) in
            if r1 <> 0 then r1
            else let r2 = aux (t2,u2) in
            if r2 <> 0 then r2
            else aux_list (tl,ul)
        | Tuple _,_ -> -1
        | _,Tuple _ -> 1
        | Param p1,Param p2 -> compare p1 p2
        | Param _,_ -> -1
        | _,Param _ -> 1
        | Var v1,Var v2 -> compare v1 v2
      and aux_list = function
        | ty1::tys1,ty2::tys2 ->
            let r = aux (ty1,ty2) in
            if r <> 0 then r
            else aux_list (tys1,tys2)
        | [],[] -> 0
        | [],_ -> -1
        | _,[] -> 1
      and aux = function
        | Ty (tys1,ty_base1),Ty (tys2,ty_base2) ->
            let r = aux_base (ty_base1,ty_base2) in
            if r <> 0 then r
            else aux_list (List.rev tys1,List.rev tys2)
      in
      fun ty1 ty2 -> aux (ty1,ty2)

    let get_pp () =
      let string_of_param =
        let bindings = ref [] in
        let count = ref 0 in
        function i ->
          try List.assoc i !bindings
          with Not_found ->
            let s = String.make 1 (Char.chr (65 + (!count mod 26))) in
            let s = match !count / 26 with
              | 0 -> s
              | j -> s ^ string_of_int j
            in
            incr count ; bindings := (i,s) :: !bindings ; s
      in
      let string_of_var =
        let bindings = ref [] in
        let count = ref 0 in
        function i ->
          try List.assoc i !bindings
          with Not_found ->
            let s = "?" ^ string_of_int !count in
            incr count ; bindings := (i,s) :: !bindings ; s
      in
      let rec aux level chan = function
        | Ty (ty::tys,ty_base) ->
            let print =
              if level>0
              then Format.fprintf chan "@[(%a -> %a)@]"
              else Format.fprintf chan "@[%a -> %a@]"
            in
            print (aux 1) ty (aux 0) (Ty (tys,ty_base))
        | Ty ([],ty_base) ->
            begin match ty_base with
              | Const (_,name,tys) ->
                  let print =
                    if level>2
                    then Format.fprintf chan "@[(%s%a)@]"
                    else Format.fprintf chan "@[%s%a@]"
                  in
                  print name aux2 tys
              | Tuple (ty1,ty2,tys) ->
                  let print =
                    if level>1
                    then Format.fprintf chan "@[(%a%a)@]"
                    else Format.fprintf chan "@[%a%a@]"
                  in
                  print (aux 2) ty1 aux3 (ty2::tys)
              | Prop ->
                  Format.fprintf chan "prop"
              | String ->
                  Format.fprintf chan "string"
              | Nat ->
                  Format.fprintf chan "nat"
              | Param i ->
                  Format.fprintf chan "%s" (string_of_param i)
              | Var i ->
                  Format.fprintf chan "%s" (string_of_var i)
            end
      and aux2 chan =
        List.iter (fun ty -> Format.fprintf chan " %a" (aux 3) ty)
      and aux3 chan =
        List.iter (fun ty -> Format.fprintf chan " * %a" (aux 2) ty)
      in
      fun chan ty ->
        Format.fprintf chan "@[%a@]" (aux 0) ty

    (* type unifier *)
    module Unifier = struct
      module M = Map.Make(struct type t = int let compare = Pervasives.compare end)
      type u = t M.t

      let iter = M.iter

      let global_unifier : t M.t ref = ref M.empty

      let clear () =
        global_unifier := M.empty

      let occurs unifier i ty =
        let rec aux = function
          | Ty (tys,ty_base) ->
              List.exists aux tys || aux_base ty_base
        and aux_base = function
          | Prop | String | Nat | Param _ -> false
          | Const (_,_,tys) -> List.exists aux tys
          | Tuple (ty1,ty2,tys) -> aux ty1 || aux ty2 || List.exists aux tys
          | Var j ->
              if i=j then true
              else try aux (M.find j unifier)
              with Not_found -> false
        in
        aux ty

      exception Type_unification_error of t * t * u

      (* TODO [unifier] needs to be GC-ed,
       * or at least we should avoid unnecessary chained references,
       * for instance by soft-normaliying (leaving only the last
       * var) and removing the pure params from the unifier
       *)
      let refine unifier ty1' ty2' =
        let rec aux u ty1 ty2 = match ty1,ty2 with
          | _ when ty1 = ty2 -> u
          | Ty (ty1::tys1,ty_base1),Ty (ty2::tys2,ty_base2) ->
              let u = aux u ty1 ty2 in
              aux u (Ty (tys1,ty_base1)) (Ty (tys2,ty_base2))
          | Ty ([],Var i),_ when M.mem i u ->
              let ty1 = M.find i u in
              aux u ty1 ty2
          | _,Ty ([],Var j) when M.mem j u ->
              let ty2 = M.find j u in
              aux u ty1 ty2
          | Ty ([],Var i),_ ->
              if occurs u i ty2
              then raise (Type_unification_error (ty1',ty2',unifier))
              else M.add i ty2 u
          | _,Ty ([],Var j) ->
              if occurs u j ty1
              then raise (Type_unification_error (ty1',ty2',unifier))
              else M.add j ty1 u
          | Ty ([],ty_base1),Ty ([],ty_base2) ->
              begin match ty_base1,ty_base2 with
                | Const (_,name1,tys1),Const(_,name2,tys2) ->
                    if name1 = name2 then
                      try List.fold_left2 aux u tys1 tys2
                      with Invalid_argument _ ->
                        raise (Type_unification_error (ty1',ty2',unifier))
                    else
                       raise (Type_unification_error (ty1',ty2',unifier))
                | Tuple (ty11,ty21,tys1),Tuple (ty12,ty22,tys2) ->
                    begin try List.fold_left2 aux u
                                (ty11::ty21::tys1) (ty12::ty22::tys2)
                    with Invalid_argument _ ->
                      raise (Type_unification_error (ty1',ty2',unifier))
                    end
                | _ ->
                    raise (Type_unification_error (ty1',ty2',unifier))
              end
          | _ ->
              raise (Type_unification_error (ty1',ty2',unifier))
        in
        aux unifier ty1' ty2'

      let norm ?(unifier=(!global_unifier)) ty =
        let rec aux = function
          | Ty (tys,ty_base) ->
              aux_base (List.map aux tys) ty_base
        and aux_base tys ty_base = match ty_base with
          | Prop | String | Nat | Param _ ->
              Ty (tys,ty_base)
          | Const (p,name,tys1) ->
              Ty (tys,Const (p,name,List.map aux tys1))
          | Tuple (ty1,ty2,tys1) ->
              Ty (tys,Tuple (aux ty1,aux ty2,List.map aux tys1))
          | Var i ->
              try arrow tys (aux (M.find i unifier))
              with Not_found -> Ty (tys,ty_base)
        in
        aux ty
    end

    let get_pp ?unifier () =
      let pp = get_pp () in
      fun chan ty ->
        let ty = Unifier.norm ?unifier ty in
        pp chan ty

    let pp = get_pp ()

    let get_to_string ?unifier () =
      let pp = get_pp ?unifier () in
      fun ty -> string_of_formatter (fun formatter -> pp formatter ty)

    let to_string = get_to_string ()
  end

  (* Kind checking *)

  exception Type_kinding_error of string * pos * Kind.t * Kind.t
  exception Invalid_pred_declaration of string * pos * Type.t
  exception Undefinite_type of string * pos * Type.t * int list
  exception Type_order_error of string option * pos * Type.t

  type obj =
    | Predicate of string
    | Constant of string
    | QuantVar of string option
    | AbsVar

  (* Run all kind of checks, and return the arity. *)
  let kind_check =
    let module I = struct
      type t = int
      let compare = compare
    end in
    let module TypeParams = Set.Make (I) in
    fun ~obj ~p ty ~get_kind ->
      let rec aux ty =
        let Type.Ty (tys,ty_base) = ty in
        (* computes the number of source types, the set of their type
         * parameters, and whether they contain [prop] *)
        let (a,ho),tp1 = List.fold_left aux2 ((0,false),TypeParams.empty) tys in
        match ty_base with
          | Type.Const (p,name,tys) ->
              let Kind.Ki (kis,Kind.KType) as ki = get_kind (p,name) in
              let ho,tp2 =
                (* apply the head of the source type on its arguments *)
                try List.fold_left2 aux3 (ho,TypeParams.empty) tys kis
                with Invalid_argument _ ->
                  raise (Type_kinding_error
                           (name,p,
                            Kind.ktypes (List.length tys),ki))
              in
              (a,false,ho),(tp1,tp2)
          | Type.Tuple (ty1,ty2,tys) ->
              let ho,tp2 =
                List.fold_left aux4 (ho,TypeParams.empty) (ty1::ty2::tys)
              in
              (a,false,ho),(tp1,tp2)
          | Type.Prop -> (a,true,ho),(tp1,TypeParams.empty)
          | Type.String | Type.Nat -> (a,false,ho),(tp1,TypeParams.empty)
          | Type.Param i -> (a,false,ho),(tp1,TypeParams.singleton i)
          | Type.Var _ -> (a,false,ho),(tp1,TypeParams.empty)
      and aux2 ((a,ho),tp) ty =
        (* increment the number of source types and the set of type
         * parameters *)
        let ((_,pr',ho'),(tp1,tp2)) = aux ty in
        (a+1,ho || pr' || ho'),
        (TypeParams.union tp (TypeParams.union tp1 tp2))
      and aux3 (ho,tp) ty ki =
        (* increment the set of type parameters *)
        if ki<>Kind.ktype then assert false (* TODO raise something *)
        else let (_,ho),tp = aux2 ((0,ho),tp) ty in ho,tp
      and aux4 (ho,tp) ty =
        (* increment the set of type parameters *)
        let (_,ho),tp = aux2 ((0,ho),tp) ty in ho,tp
      in
      let (a,pr,ho),(tp1,tp2) = aux ty in
      match obj with
        | Predicate n ->
            if pr then a else
              (* the target type should be [prop] *)
              raise (Invalid_pred_declaration (n,p,ty))
        | Constant n ->
            if TypeParams.subset tp1 tp2 then a else
              (* the target type should contain all type parameters *)
              raise (Undefinite_type
                       (n,p,ty,TypeParams.elements
                                 (TypeParams.diff tp1 tp2)))
        | QuantVar n ->
            if ho || pr then
              (* LINC is a first-order logic *)
              raise (Type_order_error (n,p,ty))
            else a
        | AbsVar -> a

  let kind_check ~obj ~p ty ~get_kind =
    kind_check ~obj ~p (Type.Unifier.norm ty) ~get_kind
end
