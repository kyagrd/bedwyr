(****************************************************************************)
(* Bedwyr -- level-0/1 proof search                                         *)
(* Copyright (C) 2005-2011 Baelde, Tiu, Ziegler, Gacek, Heath               *)
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

(** Bedwyr's core engine. *)

(** Raised when a Level-1 operator or predicate is used in level 0. *)
exception Level_inconsistency

(** Logic variable on the left. *)
exception Left_logic of Ndcore.Term.term

(** Raised when a instantiatable variable (eigen in level 0, logic in level 1)
  * is detected in a goal that is supposed to be ground. *)
exception Variable_leakage

(** Internal design of the prover has two levels, Zero and One. *)
type level =
  | Zero (** Logic vars are forbidden and eigen vars can be instantiated. *)
  | One (** Logic vars are instantiated and eigen vars are constants. *)

(** Maximum number of steps (theorem unfoldings) in backward chaining
  * (default: 0, no limit: -1). *)
val freezing_point : int ref

(** Maximum number of steps (theorem applications) in forward chaining
  * (default: 0, no limit: -1). *)
val saturation_pressure : int ref

(** Attempt to prove the goal [(nabla x_1..x_local . g)(S)] by
  * destructively instantiating it,
  * calling [success] on every success, and finishing with [failure]
  * which can be seen as a more usual continuation, typically
  * restoring modifications and backtracking.
  * [timestamp] must be the oldest timestamp in the goal.
  * @raise Level_inconsistency if an implication or a universal quantification
  * is given to the level-0 prover. *)
val prove :
  success:(int -> (unit -> 'a) -> 'a) ->
  failure:(unit -> 'a) ->
  timestamp:int -> local:int -> Ndcore.Term.term -> 'a
