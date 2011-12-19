(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2011 Quentin Heath                                         *)
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

(* Kinds and types *)

(* Kinds *)

type simple_kind =
  | KType
  | KRArrow of simple_kind' list * simple_kind'
and simple_kind' = simple_kind

let ki_arrow ty = function
  | KRArrow (tys,ty')   -> KRArrow (ty::tys,ty')
  | ty'                 -> KRArrow ([ty],ty')

(* Types *)

type simple_type =
  | Ty      of string
  | TProp
  | TString
  | TNat
  | TRArrow of simple_type' list * simple_type'
  | TVar    of int
and simple_type' = simple_type

let ty_arrow ty = function
  | TRArrow (tys,ty')   -> TRArrow (ty::tys,ty')
  | ty'                 -> TRArrow ([ty],ty')

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    count := 1 + !count;
    TVar !count
