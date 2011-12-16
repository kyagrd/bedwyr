(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2011 Baelde, Tiu, Ziegler, Heath                      *)
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

    (** {[_abstract : 'a -> (('b -> 'a) -> 'a) -> 'a -> prop]}
      * [_abstract T Abs T'] abstracts the logic variables in T of type 'b,
      * applies the constructor Abs to each abstraction,
      * and unify the result with T'.
      *
      * Example query:
      * {v ?= _abstract (pr X Y) abs T.
Solution found:
X = X
Y = Y
T = (abs (x1\ abs (x2\ pr x1 x2)))
More [y] ? y
No more solutions. v}
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
      * and [beta -> gamma].
      *
      * Hence type checking does not guarantee runtime type soundness
      * ("well typed programs don't go wrong").
      * A solution to this would be to make the bedwyr engine aware
      * of the type constraints,
      * so that it only abstracts variables of the correct types. *)
    val var_abspred : Term.var

    (** {[_distinct : prop -> prop]} Calling [_distinct P]
      * directs bedwyr to produce only distinct answer substitutions. *)
    val var_distinct : Term.var

    (** {[_rigid : 'a -> prop]} This is a meta-level assertion predicate.
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

    (** {[_eqvt : 'a -> 'a -> prop]}
      * This predicate checks that its arguments are
      * syntatically equivalent modulo renaming of nabla variables.
      *
      * For example:
      * {v ?= nabla x\ nabla y\ _eqvt (f x y) (f y x).
Yes.
More [y] ? y
No more solutions.
?= nabla x\ nabla y\ _eqvt (f x x) (f y y).
Yes.
More [y] ? y
No more solutions.
?= nabla x\ nabla y\ _eqvt (f x x) (f x y).
No. v} *)
    val var_check_eqvt : Term.var

    (** {6 I/O extensions} *)

    (** {[print : 'a -> prop]} Print a term and returns [true]. *)
    val var_print : Term.var

    (** {[println : 'a -> prop]} [print] +  '\n'. *)
    val var_println : Term.var

    (** {[fprint : string -> 'a -> prop]} Print a term in the file
      * specified in the first argument and returns [true].
      * Fails if the file was not opened yet. *)
    val var_fprint : Term.var

    (** {[fprintln : string -> 'a -> prop]} [fprint] +  '\n'. *)
    val var_fprintln : Term.var

    (** {[fopen_out : string -> prop]} Open a file for writing. *)
    val var_fopen_out : Term.var

    (** {[fclose_out : string -> prop]} Close an open file. *)
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
?= fclose "test.txt".
No definition found for fclose !
?= fclose_out "test.txt".
Yes.
More [y] ? y
No more solutions. v}
      * The file "test.txt" will contain the string "Test printing". *)
  end

(** Describes whether tabling is possible, and if so, how it is used. *)
type flavour =
    Normal (** only unfolding can be done *)
  | Inductive (** tabling is possible, and loop is a failure *)
  | CoInductive (** tabling is possible, and loop is a success *)
type command =
    Exit (** close all files and exit *)
  | Help (** display a short help message *)
  | Include of string list (** load a list of files *)
  | Reset (** clears the current session *)
  | Reload (** reload the current session *)
  | Session of string list (** load these files as the current session *)
  | Debug of string option (** turn debugging on/off (default off) *)
  | Time of string option (** turn timing on/off (default off) *)
  | Equivariant of string option (** turn equivariant tabling on/off (default on) *)
  | Show_table of Typing.pos * string (** displays the predicate's table *)
  | Clear_tables (** calls [clear_tables] *)
  | Clear_table of Typing.pos * string (** calls [clear_table] *)
  | Save_table of Typing.pos * string * string (** calls [save_table] *)
  | Assert of Typing.preterm (** checks whether a query succeeds *)
  | Assert_not of Typing.preterm (** checks whether a query fails *)
  | Assert_raise of Typing.preterm (** checks whether a query crashes *)
type input =
    KKind of (Typing.pos * string) list * Type.simple_kind (** type declaration *)
  | TType of (Typing.pos * string) list * Type.simple_type (** constant declaration *)
  | Def of (flavour * Typing.pos * string * Type.simple_type) list *
      (Typing.pos * Typing.preterm * Typing.preterm) list (** predicate declaration and definition *)
  | Query of Typing.preterm (** query (interactive mode) *)
  | Command of command (** meta-command (any mode) *)

(** Simple debug flag, can be set dynamically from the logic program. *)
val debug : bool ref

(** Enables the display of computation times. *)
val time : bool ref

val close_all_files : unit -> unit
val close_user_file : string -> unit
val get_user_file : string -> out_channel
val open_user_file : string -> out_channel

(** {6 Type declarations} *)

exception Invalid_type_declaration of string * Typing.pos *
            Type.simple_kind * string
val declare_type : Typing.pos * string -> Type.simple_kind -> unit

(** {6 Constants and predicates declarations} *)

exception Invalid_const_declaration of string * Typing.pos *
            Type.simple_type * string
exception Invalid_pred_declaration of string * Typing.pos *
            Type.simple_type * string
exception Invalid_bound_declaration of string * Typing.pos *
            Type.simple_type * string

val declare_const : Typing.pos * string -> Type.simple_type' -> unit

(** Declare a predicate.
  * @return a variable corresponding to this predicate *)
val create_def :
  flavour * Typing.pos * string * Type.simple_type' -> Term.var

(** {6 Typechecking, predicates definitions} *)

exception Missing_declaration of string * Typing.pos option
exception Inconsistent_definition of string * Typing.pos * string

(** Translate a pre-term, with typing and position information,
  * into a term, with variable sharing.
  * Type checking is done on the fly,
  * and no type information is kept in the terms from this point. *)
val translate_query : Typing.preterm -> Term.term

(** Add a clause to the definition of a declared predicate.
  * A list of the variables corresponding to the predicates
  * declared in the current definition block is given;
  * the predicate must match one of them.
  * @param new_predicates said list
  * *)
val add_clause :
  Term.var list -> Typing.pos * Typing.preterm * Typing.preterm -> unit

(** {6 Using definitions} *)

exception Arity_mismatch of Term.term * int

(** Remove all definitions. *)
val reset_defs : unit -> unit

(** Get a definition.
  * @param check_arity the expected arity of the predicate
  * @param head_tm the term corresponding to the predicate
  * @raise Missing_declaration if [head_tm] is not an existing predicate
  * @raise Arity_mismatch if [head_tm] exists but is not of arity [check_arity]
  *)
val get_def :
  check_arity:int ->
  Term.term -> flavour * Term.term * Table.t option * Type.simple_type'

(** Remove a definition. *)
val remove_def : Term.term -> unit

(** Display the content of a table. *)
val show_table : Typing.pos * Term.term -> unit

(** Remove all tables. *)
val clear_tables : unit -> unit

(** Remove a table. *)
val clear_table : Typing.pos * Term.term -> unit

(** Save the content of a table to a file.
  * The proved and disproved entries are stored as arguments
  * to the predicates [proved] and [disproved], respectively. *)
val save_table : Typing.pos * Term.term -> string -> unit
exception Interrupt

(** @return [true] if a user interruption was detected since the last call to
  * [check_interrupt], [false] otherwise. *)
val check_interrupt : unit -> bool
