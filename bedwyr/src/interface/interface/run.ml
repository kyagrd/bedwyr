(****************************************************************************)
(* Bedwyr -- interface                                                      *)
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


module Mode : sig
  val definition :
    include_file:(?test_limit:(int option) -> string -> Ndcore.Term.term list option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    Lexing.lexbuf -> Ndcore.Term.term option option option
  val toplevel : concise:bool ->
    include_file:(?test_limit:(int option) -> string -> Ndcore.Term.term list option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    Lexing.lexbuf -> unit option option
  val term :
    Lexing.lexbuf -> Ndcore.Term.term option option
end = struct
  let step ~read ~eval ~print lexbuf =
    try match read lexbuf with
      | None -> None
      | Some None -> Some None
      | Some (Some input) ->
          Some (eval ~print input ~p:(IO.Pos.of_lexbuf lexbuf ()))
    with e -> Some (Catch.all ~p:(IO.Pos.of_lexbuf lexbuf ()) e)

  let definition ~include_file ~reload ~test_limit lexbuf =
    let k _ =
      Prover.System.Status.input () ;
      None
    in
    let eval = Eval.definition ~include_file ~reload ~test_limit in
    step ~read:(Read.definition_mode ~k) ~eval ~print:ignore lexbuf

  let toplevel ~concise ~include_file ~reload ~test_limit lexbuf =
    let k _ =
      Prover.System.Status.input () ;
      None
    in
    let eval = Eval.toplevel ~concise ~include_file ~reload ~test_limit in
    step ~read:(Read.toplevel ~k) ~eval ~print:ignore lexbuf

  let term lexbuf =
    let k _ =
      Prover.System.Status.input () ;
      None
    in
    step ~read:(Read.term_mode ~k) ~eval:Eval.term ~print:ignore lexbuf
end

let () =
  Prover.System.read_term := begin
    let rec aux () =
      Format.printf " ?> %!" ;
      let lexbuf = Lexing.from_channel stdin in
      match Mode.term lexbuf with
        | None -> None
        | Some None -> aux ()
        | Some (Some term) -> Some term
    in
    fun () ->
      let restore =
        let namespace = Ndcore.Term.save_namespace () in
        Ndcore.Term.clear_namespace () ;
        fun () -> Ndcore.Term.restore_namespace namespace
      in
      let x =
        try aux () with e -> restore () ; raise e
      in
      restore () ;
      x
  end

let () =
  Prover.System.fread_term := begin
    fun lexbuf () ->
      match Mode.term lexbuf with
        | None -> None
        | Some x -> x
  end


(* 4 basic input styles *)

(* definition-mode step *)
let defs ?(test_limit=(!Prover.System.initial_test_limit)) ~include_file ~reload lexbuf =
  match Mode.definition ~include_file ~reload ~test_limit lexbuf with
    | None ->
        IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ()) "Empty command." ;
        Prover.System.Status.input () ;
        None
    | x -> x

(* definition-mode loop *)
let defl ?(test_limit=(!Prover.System.initial_test_limit)) ~include_file ~reload lexbuf =
  let rec aux accum error_less =
    match Mode.definition ~include_file ~reload ~test_limit lexbuf with
      | None -> if error_less then Some (List.rev accum) else None
      | Some None -> aux accum false
      | Some (Some None) -> aux accum error_less
      | Some (Some (Some term)) -> aux (term::accum) error_less
  in
  aux [] true

(* read-eval-print step *)
let reps ?(concise=true) ?(test_limit=(!Prover.System.initial_test_limit)) ~include_file ~reload lexbuf =
  match Mode.toplevel ~concise ~include_file ~reload ~test_limit lexbuf with
    | None ->
        IO.Output.eprintf ~p:(IO.Pos.of_lexbuf lexbuf ()) "Empty query." ;
        Prover.System.Status.input () ;
        None
    | Some None -> None
    | Some (Some ()) -> Some ()

(* read-eval-print loop *)
let repl ?(concise=false) ?(test_limit=(!Prover.System.initial_test_limit)) ~include_file ~reload lexbuf =
  let rec aux () =
    Format.printf "?= %!" ;
    Parsetree.Lexer.flush_input lexbuf ;
    match Mode.toplevel ~concise ~include_file ~reload ~test_limit lexbuf with
      | None -> Format.printf "@."
      | Some None -> aux ()
      | Some (Some ()) -> aux ()
  in
  aux ()


(* convenience wrappers *)

let run_file f path =
  try Some (Prover.Environment.IncludedFiles.apply_on_file f path)
  with e -> Catch.io e

let run_string f ?fname str =
  IO.Input.apply_on_string f ?fname str

let run_channel f ?fname chan =
  IO.Input.apply_on_channel f ?fname chan

(* public wrappers *)

let rec include_file ?test_limit name =
  match run_file (defl ?test_limit ~include_file ~reload) name with
    | None (* I/O error *)
    | Some (Some None) (* corrupted file *) -> None
    | Some None (* file already included *) -> Some []
    | Some (Some (Some assertions)) (* include success *) -> Some assertions

and reload ?(session=(!Prover.System.session)) () =
  Prover.System.reset () ;
  ignore (definitions_string ~fname:"Bedwyr::stdlib" Prover.Environment.stdlib) ;
  List.iter (function name -> ignore (include_file name)) session ;
  List.iter (function query -> ignore (definition_string query)) !Prover.System.definitions

and query_string str =
  run_string (reps ~include_file ~reload) str

and definition_string str =
  run_string (defs ~include_file ~reload) str

and definitions_string ?fname str =
  run_string (defl ~include_file ~reload) ?fname str

let queries_channel chan =
  run_channel (repl ~include_file ~reload) chan
