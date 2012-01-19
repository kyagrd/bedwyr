(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2011 David Baelde, Alwen Tiu                          *)
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

(** Implementation of an index structure used for tabling.
  *
  * An index represents a set of terms, in which eigenvariables may be allowed
  * but not logic variable -- since this requires suspensions.
  * The terms are abstracted over their eigenvars in the set.
  * For efficiency, the index lookup first parses the "rigid" structure of a
  * term in linear time, and extracts variables, and then takes care of the
  * equalities among these variables.
  *
  * Currently the Nabla indices are handled as part of the rigid structure of
  * terms, which means that weakening and swapping are not supported.
  * Later, the set of nabla variables could be extracted and simplified to an
  * essential representation just like eigenvariables.
  *
  * {1 Constraint management}
  * In the tree, variables are identified by uniques numbers, which I'll call
  * the [VID] (variable id). We could get rid of that and rely only on the order
  * in which we meet the vars in the tree, but that would involve extra
  * care when changing an algorithm (insertion/lookup or fold).
  * So at the end of a branch we have a collection of variables with [VID]s,
  * and we want to store a constraint describing this collection, such that
  * two formulas satisfying the same rigid structure and map are indeed
  * logically equivalent.
  * We first get rid of [VID]s, which are not necessarily \[0,1,2..n\], and renumber
  * variables using [CID]s (constraint id) from 0 to n. In the constraint we
  * store:
  * - the maximum [VID]
  * - an array mapping [CID] to [VID]
  * - an array describing variable equalities: to each variable (denoted by its
  *   [CID]) is associated the smallest (in term of [CID]) equal variable.
  * - the array mapping [CID]s to local timestamps. *)


(** Option to turn on/off equivariant tabling. *)
val eqvt_tbl : bool ref

(** {6 Indexing} *)

(** Type of an index of elements of type ['a]. *)
type 'a t
val empty  : 'a t

(** Eigen variable in level 0, or logic variable. *)
exception Cannot_table

(** {6 Update} *)

(**)
val add    : ?allow_eigenvar:bool -> 'a t -> Term.term list -> 'a -> 'a t

(** {6 Find} *)

(**)
val find   : 'a t -> Term.term list -> 'a option

(** {6 Fold} *)

(** Apply a function on each binding of index. *)
val iter   : 'a t -> (Term.term -> 'a -> unit) -> unit
