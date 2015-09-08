(****************************************************************************)
(* Bedwyr -- environment                                                    *)
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

module Logic :
  sig
    val not : Term.term
    val ite : Term.term
    val abspred : Term.term
    val distinct : Term.term
    val assert_rigid : Term.term
    val abort_search : Term.term
    val cutpred : Term.term
    val check_eqvt : Term.term
    val var_not : Term.var
    val var_ite : Term.var
    val var_abspred : Term.var
    val var_distinct : Term.var
    val var_assert_rigid : Term.var
    val var_abort_search : Term.var
    val var_cutpred : Term.var
    val var_check_eqvt : Term.var
    val internal_t : (Term.var, Preterm.Typing.ty) Hashtbl.t
    val get_internal_type : Term.var -> Preterm.Typing.ty
    val read : Term.term
    val fread : Term.term
    val fopen_in : Term.term
    val fclose_in : Term.term
    val print : Term.term
    val println : Term.term
    val printstr : Term.term
    val fprint : Term.term
    val fprintln : Term.term
    val fprintstr : Term.term
    val fopen_out : Term.term
    val fclose_out : Term.term
    val var_read : Term.var
    val var_fread : Term.var
    val var_fopen_in : Term.var
    val var_fclose_in : Term.var
    val var_print : Term.var
    val var_println : Term.var
    val var_printstr : Term.var
    val var_fprint : Term.var
    val var_fprintln : Term.var
    val var_fprintstr : Term.var
    val var_fopen_out : Term.var
    val var_fclose_out : Term.var
    val builtins : (Term.var, Preterm.Typing.ty) Hashtbl.t
    val get_builtin : Term.var -> Preterm.Typing.ty option
  end

val stdlib : string


(** {6 Type declarations and access} *)

exception Invalid_type_declaration of string * Preterm.Pos.t * Preterm.Typing.ki * string


module Types : sig
  val save_state : unit -> int
  val restore_state : int -> unit
  val declare : Preterm.Pos.t * string -> Preterm.Typing.ki -> unit
  val iter : (Term.var -> Preterm.Typing.ki -> unit) -> unit
  val clear : unit -> unit
end


(** {6 Constants and predicates declarations} *)

exception Stratification_error of string * Preterm.Pos.t
exception Invalid_declaration of
  string * string * Preterm.Pos.t * Preterm.Typing.ty * string * Preterm.Typing.ty
exception Invalid_flavour of
  string * Preterm.Pos.t * Preterm.flavour * Preterm.flavour


(** Tabling information: the table itself,
  * and some theorems for forward/backward chaining. *)
type tabling_info = { mutable theorem : Term.term; table : Table.O.t; }

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
  mutable definition : Term.term;
  ty : Preterm.Typing.ty;
}

module Objects : sig
  val get_pred : Term.var -> predicate option
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val declare_consts :
    (Preterm.Typing.pos * string) list ->
    Preterm.Typing.ty -> k:(unit -> int option) -> unit option

  (** Declare predicates.
    * @return the list of variables and types
    *  corresponding to those predicates *)
  val declare_preds :
    (Preterm.flavour * Preterm.Typing.pos * string * Preterm.Typing.ty)
    list -> k:(unit -> int option) -> int option
  val iter :
    (Term.var -> Preterm.Typing.ty -> unit) ->
    (Term.var -> predicate -> unit) ->
    unit
  val fold :
    (Term.var -> Preterm.Typing.ty -> 'a -> 'a) ->
    (Term.var -> predicate -> 'a -> 'a) ->
    'a -> 'a
  val clear : unit -> unit
end

val translate_term :
  ?stratum:int ->
  ?head:bool ->
  ?free_args:string list ->
  ?expected_type:Preterm.Typing.ty ->
  ?free_types:(Term.var, Preterm.Typing.ty * Preterm.Pos.t option) Hashtbl.t ->
  Preterm.preterm ->
  k:(unit ->
     (Preterm.Typing.ty *
      (Term.var, Preterm.Typing.ty * Preterm.Pos.t option) Hashtbl.t *
      ((Preterm.Pos.t * string) list * Term.term))
     option) ->
  (Preterm.Typing.ty *
   (Term.var, Preterm.Typing.ty * Preterm.Pos.t option) Hashtbl.t *
   ((Preterm.Pos.t * string) list * Term.term))
  option


(** {6 Definitions files} *)

module IncludedFiles : sig
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val apply_on_file : (Lexing.lexbuf -> 'a) -> string -> 'a option
  val clear : unit -> unit
end
