(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2013 Quentin Heath                                         *)
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

module type INPUT = sig
  type son = Son of tag ref | Loop of tag ref | Cut of tag ref
  and tag =
      Proved of son list ref
    | Working of
        (son list ref * (bool ref * tag ref list ref * tag ref list ref))
    | Disproved of son list ref
    | Unset
  type t = tag ref Index.t ref
  val set_eqvt : bool -> unit
  val create : unit -> t
  val access :
    switch_vars:bool ->
    t ->
    Term.term list -> (tag ref -> bool) * tag ref option * (unit -> bool)
  val filter :
    switch_vars:bool -> t -> Term.term list -> bool option
  val nabla_abstract : Term.term -> Term.term
  val reset : t -> unit
  val iter : (Term.term -> tag -> unit) -> t -> unit
  val fold : (Term.term -> tag -> 'a -> 'a) -> t -> 'a -> 'a
  val print : Term.term -> t -> unit
  val fprint : out_channel -> Term.term -> t -> Input.Typing.ty -> unit
  val export : string -> (Term.term * t) list -> son list -> unit
end
