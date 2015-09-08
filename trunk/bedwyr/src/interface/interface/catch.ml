(****************************************************************************)
(* Bedwyr -- toplevel exception catching                                    *)
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

let solve ~p e =
  begin match e with
    (* Predicates *)
    | Prover.System.Missing_definition (n,p') ->
        IO.Output.eprintf ~p:(match p' with Some p -> p | None -> p)
          "Undefined predicate (%s was declared as a constant)."
          n

    (* HOPU *)
    | Ndcore.Unify.NotLLambda t ->
        IO.Output.eprintf ~p
          "LLambda unification prevented by %a."
          Ndcore.Pprint.pp_term t

    (* 0/1 *)
    | Prover.Proofsearch.Level_inconsistency ->
        IO.Output.eprintf ~p
          "This formula cannot be handled by the left prover!"
    | Prover.Proofsearch.Left_logic t ->
        IO.Output.eprintf ~p
          "Logic variable %a encountered on the left."
          Ndcore.Pprint.pp_term t

    (* Miscellaneous solver interruptions *)
    | Prover.System.Interrupt ->
        IO.Output.eprintf ~p
          "User interruption."
    | Prover.System.Abort_search ->
        IO.Output.eprintf ~p
          "Proof search aborted!"

    | e -> raise e
  end ;
  Prover.System.Status.ndcore () ;
  None

let meta_command ~p e =
  begin match e with
    (* Tables *)
    | Prover.System.Missing_table (n,p') ->
        IO.Output.eprintf ~p:(match p' with Some p -> p | None -> p)
          "No table (%s is neither inductive nor coinductive)."
          n
    | Prover.System.Uncleared_tables ->
        IO.Output.eprintf ~p
          "Unable to export tables (some have been cleared, \
            state might be inconsistent).@ Run #clear_tables to fix."

    (* Tests *)
    | Prover.System.Assertion_failed ->
        IO.Output.eprintf ~p
          "Assertion failed."

    (* Misc Bedwyr errors *)
    | Prover.System.Invalid_command ->
        IO.Output.eprintf ~p
          "Invalid meta-command, or wrong arguments."

    | e -> raise e
  end ;
  Prover.System.Status.solver () ;
  None

let io ?p e =
  begin match e with
    | IO.Files.File_error (s1,n,s2) ->
        IO.Output.eprintf ?p "Couldn't %s@ %S:@ %s." s1 n s2
    | e -> raise e
  end ;
  Prover.System.Status.bedwyr () ;
  None

(* Unhandled errors *)
let all ~p e =
  begin match e with
    | Failure s ->
        IO.Output.eprintf ~p
          "Error:@ %s"
          s
    | e ->
        IO.Output.eprintf ~p
          "Unexpected error:@ %s"
          (Printexc.to_string e)
  end ;
  Prover.System.Status.bedwyr () ;
  None
