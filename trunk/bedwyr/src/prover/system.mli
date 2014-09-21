(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2013 Baelde, Tiu, Ziegler, Heath                      *)
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

(** System variables, predefined predicates,
  * definitions bulding and handling. *)

(** Predefined and internal predicates. *)
module Logic :
sig
  (** {6 Non-logical extensions ({e EXPERIMENTAL})} *)

  (** {[_not : prop -> prop]} Standard negation-as-failure, as in prolog. *)
  val var_not : Term.var

  (** {[_if : prop -> prop -> prop -> prop]} If-Then-Else:
    * [_if P Q R] is basically equivalent to [(P /\ Q) \/ (not(P) /\ R)].
    * The slight difference is that the second disjunct
    * will not be tried if P is successful. *)
  val var_ite : Term.var

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
  val var_abspred : Term.var

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
  val var_distinct : Term.var

  (** {[_rigid : A -> prop]} This is a meta-level assertion predicate.
    * [_rigid X] will throw an assertion
    * (hence causes the prover to abort) if [X] is not a ground term. *)
  val var_assert_rigid : Term.var

  (** {[_abort : prop]} This predicate aborts the proof search
    * and returns to the toplevel query (if in interactive mode). *)
  val var_abort_search : Term.var

  (** {[_cut : prop -> prop]} Applying the predicate [_cut]
    * to a query removes the backtracking for that query.
    * That is, a query such as [cut P] will produce the first solution
    * (if any) to [P], and terminates. *)
  val var_cutpred : Term.var

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
  val var_check_eqvt : Term.var

  (** {6 I/O extensions} *)

  (** {[print : A -> prop]} Print a term and succeeds (see {!IO.print}). *)
  val var_print : Term.var

  (** {[println : A -> prop]} [print] +  '\n'. *)
  val var_println : Term.var

  (** {[printstr : A -> prop]} Print a string (an actual [Term.QString])
    * unescaped, without quotation marks.
    * Fails if the argument is an unbound variable or a constant. *)
  val var_printstr : Term.var

  (** {[fprint : string -> A -> prop]} Print a term in the file
    * specified in the first argument and succeeds (see {!IO.fprint}).
    * Fails if the file was not opened yet. *)
  val var_fprint : Term.var

  (** {[fprintln : string -> A -> prop]} [println] in a file. *)
  val var_fprintln : Term.var

  (** {[var_fprintstr : string -> A -> prop]} [printstr] in a file. *)
  val var_fprintstr : Term.var

  (** {[fopen_out : string -> prop]} Open a file for writing
    * (see {!IO.open_user_file}). *)
  val var_fopen_out : Term.var

  (** {[fclose_out : string -> prop]} Close an open file
    * (see {!IO.close_user_file}). *)
  val var_fclose_out : Term.var

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
end

(** Simple debug flag, can be set dynamically from the logic program. *)
val debug : bool ref

(** Enables the display of computation times. *)
val time : bool ref

(** Root of the tree of tabled atoms. *)
val root_atoms : Table.O.son list ref

(** Enables the use of {!Table.O.filter}. *)
val use_filter : bool ref

(** {6 Type declarations} *)

exception Invalid_type_declaration of
  string * Input.pos * Input.Typing.ki * string
exception Missing_type of
  string * Input.pos
val declare_type : Input.pos * string -> Input.Typing.ki -> unit

(** {6 Constants and predicates declarations} *)

(** Tabling information: the table itself,
  * and some theorems for forward/backward chaining. *)
type tabling_info = { mutable theorem : Term.term ; table : Table.O.t }

(** Describe whether tabling is possible, and if so, how it is used. *)
type flavour = private
  | Normal
    (** only unfolding can be done *)
  | Inductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a failure *)
  | CoInductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a success *)

(** Predicate: tabling information if the flavours allows it,
  * stratum of the definition block,
  * definition and type. *)
type predicate = private
    { flavour           : flavour ;
      stratum           : int ;
      mutable definition: Term.term ;
      ty                : Input.Typing.ty }

exception Invalid_const_declaration of
  string * Input.pos * Input.Typing.ty * string
exception Invalid_flavour of
  string * Input.pos * Input.flavour * Input.flavour
exception Invalid_pred_declaration of
  string * Input.pos * Input.Typing.ty * string

val declare_const : Input.pos * string -> Input.Typing.ty -> unit

(** Declare predicates.
  * @return the list of variables and types
  *  corresponding to those predicates *)
val declare_preds :
  (Input.flavour * Input.pos * string * Input.Typing.ty) list -> int

(** {6 Clauses and queries construction} *)

exception Missing_declaration of string * Input.pos option
exception Stratification_error of string * Input.pos

(** Translate a pre-term, with typing and position information,
  * into a term, with variable sharing.
  * Type checking (or rather type inference) is done on the fly,
  * and no type information is kept in the terms from this point.
  * If the term isn't well typed, or has a type that isn't [prop],
  * an exception is raised and the global type unifier isn't updated. *)
val translate_query : Input.preterm -> Term.term

(** {6 Predicates definitions} *)

exception Inconsistent_definition of string * Input.pos * string

(** For each [(p,h,b)] of [c],
  * [add_clauses s c] adds the clause [h := b] to a definition,
  * as long as the var of the corresponding predicate has stratum [s]. *)
val add_clauses :
  int -> (Input.pos * Input.preterm * Input.preterm) list -> unit

(** {6 Theorem definitions} *)

exception Inconsistent_theorem of string * Input.pos * string

(** If possible, add the theorem to the tabling extended rules. *)
val add_theorem : (Input.pos * string * Input.preterm) -> unit

(** {6 Predicates accessors} *)

exception Missing_definition of string * Input.pos option
exception Missing_table of string * Input.pos option

(** Remove a definition. *)
val remove_def : Term.term -> unit

(** Get a predicate's tabling information and definition.
  * @raise Missing_declaration if [head_tm] is not an existing predicate
  *)
val get_flav_def : Term.term -> flavour * Term.term

(** Remove all tables. *)
val clear_tables : unit -> unit

(** Remove a table. *)
val clear_table : Input.pos * Term.term -> unit

(** {6 I/O} *)

(** Display all type and objects declarations. *)
val print_env : unit -> unit

(** Perform type checking on a pre-term and display the inferred type.
  * This can be used from the REPL to check the validity of a term
  * without messing with the future inference,
  * so the global type unifier is left unchanged
  * even if the term is well typed and of type [prop]. *)
val print_type_of : Input.preterm -> unit
(* TODO rewrite this comment once the new type system is merged *)

(** Display the body of a definition. *)
val show_def : Input.pos * Term.term -> unit

(** Display the content of a table. *)
val show_table : Input.pos * Term.term -> unit

(** Save the content of a table to a file.
  * The proved and disproved entries are stored as arguments
  * to the predicates [proved] and [disproved], respectively. *)
val save_table : Input.pos * Term.term -> string -> string -> unit

(** Export the current tables in an XML file.
  * Doesn't work between a call to [#clear_table] and the following call
  * to [#clear_tables]. *)
val export : string -> unit

(** {6 Misc} *)

(** User interruption. *)
exception Interrupt

(** Raised when aborting search. *)
exception Abort_search

(** Remove all definitions. *)
val reset_decls : unit -> unit

(** @return [true] if a user interruption was detected since the last call to
  * {!check_interrupt}, [false] otherwise. *)
val check_interrupt : unit -> bool
