(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006-2013 Gacek, Baelde, Tiu, Heath                        *)
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

(** Goals tabling. *)

module O : sig
  type son =
    | Son of tag ref
    | Loop of tag ref
    | Cut of tag ref
  and tag =
    | Proved of (son list ref)
    | Working of ((son list ref) *
                  (bool ref * tag ref list ref * tag ref list ref))
    | Disproved of (son list ref)
    | Unset
  type t

  (** Turn on/off equivariant tabling. *)
  val set_eqvt : bool -> unit

  val create : unit -> t

  val access :
    switch_vars:bool ->
    t -> Term.term list ->
    (tag ref -> bool) * tag ref option * (unit -> bool)

  (** Abstract nabla variables in a term.
    * If equivariant tabling is used then use only nabla variables appearing in
    * the term. Otherwise, add vacuous nabla's as neccessary. *)
  val nabla_abstract : Term.term -> Term.term
  (** {e FIXME}
    * The maximum index of the nabla variables in the term determines the number
    * of nabla's needed to be added (in case of non-equivariant tabling).
    * For non-equivariant tabling, this use of maximum index will cause us
    * to miss vacuous nablas that appear inner most in a proved atomic goal.
    *
    * For example, if a query like [nabla x\ nabla y\ p x] succeeds,
    * then the table will only display [nabla x\ p x],
    * because the vacuous y is forgotten in the table.
    *
    * This behavior is strictly speaking unsound.
    * For example, if [p] is defined as {[p X := sigma Y\ (X = Y -> false)]}
    * that is, [p X] is true if there exists a term distinct from [X].
    * Assuming that the types are vacuous, then [nabla x\ p x]  is not provable
    * in Linc, but [nabla x\ nabla y\ p x] is.
    * Suppose the latter were proved by Bedwyr (currently it's impossible because
    * we can't yet handle logic variables on the left),
    * then the table will instead display [nabla x\ p x] as provable,
    * which is wrong.
    *
    * This unsoundness may never arise in the goals tabled by Bedwyr,
    * because to produce this behavior, it seems that we need unification
    * of logic variables on the left, which is not handled in Bedwyr anyway.
    * But it'd be good if this can be fixed,
    * if we want to be faithful to the Linc logic. *)

  (** Empty the table. *)
  val reset : t -> unit

  (** Apply a function to each element of a table. *)
  val iter : (Term.term -> tag -> unit) -> t -> unit

  (** Fold a table on an initial value with respect to a function. *)
  val fold : (Term.term -> tag -> 'a -> 'a) -> t -> 'a -> 'a

  (** Print a table to standard output.
    * Nabla variables are abstracted and explicitly quantified. *)
  val print : Term.term -> t -> unit

  (** Print a table to a file.
    * Nabla variables are abstracted and explicitly quantified. *)
  val fprint : out_channel -> Term.term -> t -> Input.Typing.ty -> unit

  (** Export the provided tables in an XML file. *)
  val export : string -> ((Term.term * t) list) -> unit
  (** XXX This currently crashes if [#clear_table] was used on any of those tables. *)
end
