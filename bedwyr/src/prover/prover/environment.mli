(****************************************************************************)
(* Bedwyr -- environment                                                    *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2015 Quentin Heath                                         *)
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

open Parsetree.Preterm.Typing

(** Predefined and internal predicates. *)
module Logic : sig
  (** {6 Non-logical extensions ({e EXPERIMENTAL})} *)

  (*
  val not : Ndcore.Term.term
  val ite : Ndcore.Term.term
  val abspred : Ndcore.Term.term
  val distinct : Ndcore.Term.term
  val assert_rigid : Ndcore.Term.term
  val abort_search : Ndcore.Term.term
  val cutpred : Ndcore.Term.term
  val check_eqvt : Ndcore.Term.term
   *)

  (** {[_not : prop -> prop]} Standard negation-as-failure, as in prolog. *)
  val var_not : Ndcore.Term.var

  (** {[_if : prop -> prop -> prop -> prop]} If-Then-Else:
    * [_if P Q R] is basically equivalent to [(P /\ Q) \/ (not(P) /\ R)].
    * The slight difference is that the second disjunct
    * will not be tried if P is successful. *)
  val var_ite : Ndcore.Term.var

  (** {[_abstract : A -> ((B -> A) -> A) -> A -> prop]}
    * [_abstract T Abs T'] assumes the logic variables in T are of type B,
    * abstracts them, applies the constructor Abs to each abstraction,
    * and unifies the result with T'.
    *
    * Example query:
    * {v ?= _abstract (pr X Y) abs T.
Solution found:
T = (abs (x1\ abs (x2\ pr x2 x1)))
Y = Y
X = X
More [y] ? y
No more solutions. v}
    *
    * {e WARNING}: Because [_abstract] can abstract any logic variables,
    * and because while the input files are type-checked,
    * the underlying abstract machine of bedwyr is untyped,
    * the abstraction produced by [_abstract] may not always respect
    * the type of the constructor Lam.
    *
    * For example, consider the above example.
    * If [pr] is of type [alpha -> beta -> gamma],
    * for some distinct types [alpha] and [beta],
    * then the above query will still succeed despite the fact that
    * [abs] is applied to terms of types [alpha -> gamma]
    * and [beta -> gamma]:
    * {v ?= #typeof pr.
pr : alpha -> beta -> gamma
?= #typeof abs.
abs : (beta -> gamma) -> gamma
?= #typeof _abstract.
_abstract : ?0 -> ((?1 -> ?0) -> ?0) -> ?0 -> prop
?= #typeof abs (x1\ abs (x2\ pr x2 x1)).
At line 4, bytes 30-31:
 Typing error: this term has type beta but is used as alpha. v}
    *
    * Hence type checking does not guarantee runtime type soundness
    * ("well typed programs don't go wrong").
    * A solution to this would be to make the bedwyr engine aware
    * of the type constraints,
    * so that it only abstracts variables of the correct types. *)
  val var_abspred : Ndcore.Term.var

  (** {[_distinct : prop -> prop]} Calling [_distinct P]
    * directs bedwyr to produce only distinct answer substitutions:
    * {v ?= true \/ true.
Yes.
More [y] ?
Yes.
More [y] ?
No more solutions.
?= _distinct (true \/ true).
Yes.
More [y] ?
No more solutions.
?= v} *)
  val var_distinct : Ndcore.Term.var

  (** {[_rigid : A -> prop]} This is a meta-level assertion predicate.
    * [_rigid X] will throw an assertion
    * (hence causes the prover to abort) if [X] is not a ground term. *)
  val var_assert_rigid : Ndcore.Term.var

  (** {[_abort : prop]} This predicate aborts the proof search
    * and returns to the toplevel query (if in interactive mode). *)
  val var_abort_search : Ndcore.Term.var

  (** {[_cut : prop -> prop]} Applying the predicate [_cut]
    * to a query removes the backtracking for that query.
    * That is, a query such as [cut P] will produce the first solution
    * (if any) to [P], and terminates. *)
  val var_cutpred : Ndcore.Term.var

  (** {[_eqvt : A -> A -> prop]}
    * This predicate checks that its arguments are
    * syntatically equivalent modulo renaming of nabla variables.
    *
    * For example:
    * {v ?= forall f, nabla x y, _eqvt (f x y) (f y x).
Yes.
More [y] ? y
No more solutions.
?= forall f, nabla x y, _eqvt (f x x) (f y y).
Yes.
More [y] ? y
No more solutions.
?= forall f, nabla x y, _eqvt (f x x) (f x y).
No. v} *)
  val var_check_eqvt : Ndcore.Term.var

  val internal_t : (Ndcore.Term.var,Type.t) Hashtbl.t
  val get_internal_type : Ndcore.Term.var -> Type.t

  (** {6 I/O extensions} *)

  (*
  val read : Ndcore.Term.term
  val fread : Ndcore.Term.term
  val fopen_in : Ndcore.Term.term
  val fclose_in : Ndcore.Term.term
  val print : Ndcore.Term.term
  val println : Ndcore.Term.term
  val printstr : Ndcore.Term.term
  val fprint : Ndcore.Term.term
  val fprintln : Ndcore.Term.term
  val fprintstr : Ndcore.Term.term
  val fopen_out : Ndcore.Term.term
  val fclose_out : Ndcore.Term.term
   *)

  (** {[read : A -> prop]} Parses the standard input and succeeds if the
    * result is a well-formed and well-typed term.
    * @see "" {!System.read} *)
  val var_read : Ndcore.Term.var

  (** {[fread : string -> A -> prop]} Parses the file specified in the
    * first argument and succeeds if the result is a well-formed and
    * well-typed term.
    * Fails if the file was not opened yet.
    * @see "" {!System.fread} *)
  val var_fread : Ndcore.Term.var

  (** {[fopen_in : string -> prop]} Open a file for reading.
    * @see "" {!System.fopen_in} *)
  val var_fopen_in : Ndcore.Term.var

  (** {[fclose_in : string -> prop]} Close an open file.
    * @see "" {!System.fclose_in} *)
  val var_fclose_in : Ndcore.Term.var

  (** {[print : A -> prop]} Print a term and succeeds.
    * @see "" {!System.print} *)
  val var_print : Ndcore.Term.var

  (** {[println : A -> prop]} [print] +  '\n'. *)
  val var_println : Ndcore.Term.var

  (** {[printstr : A -> prop]} Print a string (an actual [Ndcore.Term.QString])
    * unescaped, without quotation marks.
    * Fails if the argument is an unbound variable or a constant. *)
  val var_printstr : Ndcore.Term.var

  (** {[fprint : string -> A -> prop]} Print a term in the file
    * specified in the first argument and succeeds.
    * Fails if the file was not opened yet.
    * @see "" {!System.fprint} *)
  val var_fprint : Ndcore.Term.var

  (** {[fprintln : string -> A -> prop]} [println] in a file. *)
  val var_fprintln : Ndcore.Term.var

  (** {[var_fprintstr : string -> A -> prop]} [printstr] in a file. *)
  val var_fprintstr : Ndcore.Term.var

  (** {[fopen_out : string -> prop]} Open a file for writing.
    * @see "" {!System.fopen_out} *)
  val var_fopen_out : Ndcore.Term.var

  (** {[fclose_out : string -> prop]} Close an open file.
    * @see "" {!System.fclose_out} *)
  val var_fclose_out : Ndcore.Term.var

  (** Example:
    * {v ?= fopen_out "test.txt".
Yes.
More [y] ? y
No more solutions.
?= fprint "test.txt" "Test printing".
Yes.
More [y] ? y
No more solutions.
?= fclose_out "test.txt".
Yes.
More [y] ? y
No more solutions. v}
    * The file "test.txt" will contain the string "Test printing". *)

  val builtins_t : (Ndcore.Term.var,Type.t) Hashtbl.t
  val get_builtin : Ndcore.Term.var -> Type.t option
end

(** Inlined definition file containing common types, constants and
  * predicates that are purely logical (i.e. no side effects). *)
val stdlib : string


(** {6 Type declarations and access} *)

exception Invalid_type_declaration of string * IO.Pos.t * Kind.t * string


module Types : sig
  val save_state : unit -> int
  val restore_state : int -> unit
  val declare : IO.Pos.t * string -> Kind.t -> unit
  val iter : (Ndcore.Term.var -> Kind.t -> unit) -> unit
  val fold : (Ndcore.Term.var -> Kind.t -> 'a -> 'a) -> 'a -> 'a
  val clear : unit -> unit
end


(** {6 Constants and predicates declarations} *)

exception Stratification_error of string * IO.Pos.t
exception Invalid_declaration of
  string * string * IO.Pos.t * Type.t * string * Type.t
exception Invalid_flavour of
  string * IO.Pos.t * Parsetree.Preterm.flavour * Parsetree.Preterm.flavour


(** Tabling information: the table itself,
  * and some theorems for forward/backward chaining. *)
type tabling_info = { mutable theorem : Ndcore.Term.term; table : Table.t; }

(** Describe whether tabling is possible, and if so, how it is used. *)
type flavour =
    Normal
    (** only unfolding can be done *)
  | Inductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a failure *)
  | CoInductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a success *)

(** Predicate: tabling information if the flavours allows it,
  * stratum of the definition block,
  * definition and type. *)
type predicate = {
  flavour : flavour;
  stratum : int;
  mutable definition : Ndcore.Term.term;
  ty : Type.t;
}

module Objects : sig
  val get_pred : Ndcore.Term.var -> predicate option
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val declare_consts :
    (IO.Pos.t * string) list ->
    Type.t -> k:(unit -> int option) -> unit option

  (** Declare predicates.
    * @return the list of variables and types
    *  corresponding to those predicates *)
  val declare_preds :
    (Parsetree.Preterm.flavour * IO.Pos.t * string * Type.t)
    list -> k:(unit -> int option) -> int option
  val iter :
    (Ndcore.Term.var -> Type.t -> unit) ->
    (Ndcore.Term.var -> predicate -> unit) ->
    unit
  val fold :
    (Ndcore.Term.var -> Type.t -> 'a -> 'a) ->
    (Ndcore.Term.var -> predicate -> 'a -> 'a) ->
    'a -> 'a
  val clear : unit -> unit
end

val translate_term :
  ?stratum:int ->
  ?head:bool ->
  ?free_args:string list ->
  ?expected_type:Type.t ->
  ?free_types:(Ndcore.Term.var, Type.t * IO.Pos.t option) Hashtbl.t ->
  Parsetree.Preterm.preterm ->
  k:(unit ->
     (Type.t *
      (Ndcore.Term.var, Type.t * IO.Pos.t option) Hashtbl.t *
      ((IO.Pos.t * string) list * Ndcore.Term.term)) option) ->
  (Type.t *
   (Ndcore.Term.var, Type.t * IO.Pos.t option) Hashtbl.t *
   ((IO.Pos.t * string) list * Ndcore.Term.term)) option


(** {6 Definitions files} *)

module IncludedFiles : sig
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val apply_on_file : (Lexing.lexbuf -> 'a) -> string -> 'a option
  val clear : unit -> unit
end
