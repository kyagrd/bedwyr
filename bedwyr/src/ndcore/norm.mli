(****************************************************************************)
(* Bedwyr -- non-destructive normalization of higher-order terms            *)
(* Copyright (C) 2006 Gopalan Nadathur, Natalie Linnell, Axelle Ziegler     *)
(* Copyright (C) 2006,2007,2010 David Baelde                                *)
(* Copyright (C) 2011,2012 Quentin Heath                                    *)
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

(** Term (beta-)normalization. *)

(** Head normalization. *)
val hnorm : Term.term -> Term.term
(** Suspensions are created for each (App (Lam .,.)) found in the head,
  * and then pushed down in the term. *)

(** Full normalization. *)
val deep_norm : Term.term -> Term.term
(** Head normalization is applied progressively until the suspensions
  * are applied on all (NB .) and removed. *)

(** Full normalization with on-the-fly nabla variables renaming. *)
val nb_rename : Term.term list -> Term.term list
(** Nabla variables are renamed according to the order of traversal
  * in the tree representation of the (normal form of the) term.
  * This is a cheap way to force equivariant matching in tables. *)
