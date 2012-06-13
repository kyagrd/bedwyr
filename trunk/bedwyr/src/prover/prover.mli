(****************************************************************************)
(* Bedwyr prover                                                            *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

(** Bedwyr's engine. *)

exception Level_inconsistency

(** Raised when a instantiatable variable (eigen in level 0, logic in level 1)
  * is detected in a goal that is supposed to be ground. *)
exception Variable_leakage

(** Raised when aborting search. *)
exception Abort_search

(** Internal design of the prover has two levels, Zero and One. *)
type level =
  | Zero (** Logic vars are forbidden and eigen vars can be instantiated. *)
  | One (** Logic vars are instantiated and eigen vars are constants. *)

(** Maximum number of theorem unfolding in backward chaining (-1: no limit). *)
val freezing_point : int ref

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
  level:level -> timestamp:int -> local:int -> Term.term -> 'a

(** Run the REPL, call [prove] on the queries,
  * and offer to print the solutions one by one. *)
val toplevel_prove : Term.term -> unit
