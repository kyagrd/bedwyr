(****************************************************************************)
(* Bedwyr -- file input/output                                              *)
(* Copyright (C) 2012,2013,2015 Quentin Heath                               *)
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

(** File I/O utilities. *)

(** Wrapper around some [Sys_error]. *)
exception File_error of string * string * string


(** {6 Sanity wrappers} *)

(** Bedwyr working directory. *)
val bwd : string ref

(** Wether file access is allowed outside of {!!bwd} or not. *)
val chrooted : bool ref

(** Open a file for input and run a function on it, with default sanity
  * checks.
  * @param wrap Additional sanity wrapper allowing for conditional
  * input. *)
val run_in :
  wrap:((basename:string -> nice_path:string -> full_path:string -> 'a) ->
        (basename:string -> nice_path:string -> full_path:string -> 'b)) ->
  (?fname:string -> in_channel -> 'a) -> string ->
  'b

(** Open a file, with default sanity checks, and get its content. *)
val get_in : string -> string

(** Open a file for output and run a function on it, with default sanity
  * checks. *)
val run_out : (out_channel -> 'a) -> string -> 'a


(** {6 List of open files used for user predicate I/O} *)

module I : sig
  val get : string -> (in_channel * Lexing.lexbuf) option
  val add : string -> unit
  val remove : string -> in_channel -> unit
  val clear : unit -> unit
end

module O : sig
  val get : string -> (out_channel * Format.formatter) option
  val add : string -> unit
  val remove : string -> out_channel -> unit
  val clear : unit -> unit
end
