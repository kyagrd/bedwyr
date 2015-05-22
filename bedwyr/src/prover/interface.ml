(****************************************************************************)
(* Bedwyr prover                                                            *)
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

exception Uncleared_tables
exception Assertion_failed
exception Invalid_command

let help_msg =
  "Useful commands in query mode:\n\
  #help.                               Display this message.\n\
  #exit.                               Exit.\n\
  #debug [flag].                       Turn debugging [on]/off \
    (initially off).\n\
  #time [flag].                        Turn timing [on]/off (initially off).\n\
  #session \"file_1\" ... \"file_N\".      Load these files as the \
    current session.\n\
  #reload.                             Reload the current session.\n\
  #reset.                              Clears the current session.\n\
  #show_table [pred].                  Displays the predicate's table.\n\
  #save_table [pred] [file].           Save the predicate's table in a file.\n\
  #equivariant [flag].                 Turn equivariant tabling [on]/off \
    (initially on).\n\
  Or type in a formula to ask for its verification.\n\
  For more information (including commands relevant in definition mode),\n\
  see the user guide.\n\n"

module Status = struct
  let value = ref None

  let exit_with () =
    exit (match !value with
            | None -> 0
            | Some error_code -> error_code)
  and exit_if () =
    match !value with
      | None -> ()
      | Some error_code -> exit error_code
  and set error_code =
    if !value = None
    then value := Some error_code

  let input () = set 1
  let def () = set 2
  let ndcore () = set 3
  let solver () = set 4
  let bedwyr () = set 5
end

let reload : ((?session:(string list) -> unit -> unit) ref) = ref (fun ?session () -> ())
let include_file : ((test_limit:(int option) -> string -> unit) ref) =
  ref (fun ~test_limit:_ _ -> ())

let bool_of_flag = function
  | None | Some "on" | Some "true" -> true
  | Some "off" | Some "false" -> false
  | _ -> raise Invalid_command

(* XXX replace all lexbufes by positions, as we don't do
 * anything else, supposedly (proof skipping, maybe?) *)
module Catch = struct
  let check lexbuf =
    let k _ =
      Status.input () ;
      Some None
    in
    function
      (* Kind checking *)
      | System.Missing_type (n,_) ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Undeclared type %s."
            n
      | Input.Typing.Type_kinding_error (n,p,ki1,ki2) ->
          eprintf ~p ~k
            "Kinding error: the type constructor %s has kind %a@ \
              but is used as %a."
            n
            Input.Typing.pp_kind ki2
            Input.Typing.pp_kind ki1

      (* Type checking *)
      | System.Missing_declaration (n,p) ->
          eprintf ~p ~k
            "Undeclared object %s."
            n
      | Input.Term_typing_error (p,ty1,ty2,unifier) ->
          let pp_type = Input.Typing.get_pp_type ~unifier () in
          eprintf ~p ~k
            "Typing error: this term has type %a but is used as %a."
            pp_type ty2
            pp_type ty1
      | Input.Typing.Type_order_error (n,p,ty) ->
          begin match n with
            | Some n ->
                eprintf ~p ~k
                  "Typing error: cannot give free variable %s the type %a." n
                  (Input.Typing.get_pp_type ()) ty
            | None ->
                eprintf ~p ~k
                  "Typing error: cannot quantify over type %a."
                  (Input.Typing.get_pp_type ()) ty
          end
      | e -> raise e

  let command lexbuf =
    let k _ =
      Status.def () ;
      Some None
    in
    function
      (* Declarations *)
      | System.Invalid_type_declaration (n,p,ki,s) ->
          eprintf ~p ~k
            "Cannot declare type %s of kind %a:@ %s."
            n
            Input.Typing.pp_kind ki
            s
      | Input.Typing.Undefinite_type (n,p,ty,tp) ->
          let type_to_string = Input.Typing.get_type_to_string () in
          eprintf ~p ~k
            "Polymorphism error for %s: parameter%s %s@ of type %s@ \
              %s not transparant."
            n
            (if List.length tp > 1 then "s" else "")
            (String.concat ", "
               (List.map
                  (fun i -> Format.sprintf "%s"
                              (type_to_string (Input.Typing.tparam i))) tp))
            (type_to_string ty)
            (if List.length tp > 1 then "are" else "is")
      | System.Invalid_const_declaration (n,p,ty,s) ->
          eprintf ~p ~k
            "Cannot declare constant %s of type %a:@ %s."
            n
            (Input.Typing.get_pp_type ()) ty
            s
      | System.Invalid_pred_declaration (n,p,ty,s) ->
          eprintf ~p ~k
            "Cannot declare predicate %s of type %a:@ %s."
            n
            (Input.Typing.get_pp_type ()) ty
            s
      | Input.Typing.Invalid_pred_declaration (n,p,ty) ->
          eprintf ~p ~k
            "Cannot declare predicate %s of type %a:@ \
              target type must be %s."
            n
            (Input.Typing.get_pp_type ()) ty
            (Input.Typing.get_type_to_string () Input.Typing.tprop)
      | System.Invalid_flavour (n,p,gf,f) ->
          let string_of_flavour = function
            | Input.Normal -> assert false
            | Input.Inductive -> "Inductive"
            | Input.CoInductive -> "CoInductive"
          in
          eprintf ~p ~k
            "Cannot declare predicate %s of flavour %s:@ \
              this definition block is %s."
            n
            (string_of_flavour f)
            (string_of_flavour gf)

      (* Definitions *)
      | System.Stratification_error (n,p) ->
          eprintf ~p ~k
            "Inconsistent stratification:@ %s is forbidden here."
            n
      | System.Inconsistent_definition (n,p,s) ->
          eprintf ~p ~k
            "Inconsistent extension of definition for %s:@ %s."
            n
            s

      (* Theorems *)
      | System.Inconsistent_theorem (n,p,s) ->
          eprintf ~p ~k
            "Inconsistent theorem specification for %s:@ %s."
            n
            s

      (*
      | Input.Qed_error p ->
          eprintf ~p ~k
            "\"Qed.\" command used while not in proof mode."
       *)

      | e -> raise e

  let solve lexbuf =
    let k _ =
      Status.ndcore () ;
      Some None
    in
    function
      (* Predicates *)
      | System.Missing_definition (n,p) ->
          let p = match p with
            | Some p -> p | None -> position_lex lexbuf
          in
          eprintf ~p ~k
            "Undefined predicate (%s was declared as a constant)."
            n

      (* HOPU *)
      | Unify.NotLLambda t ->
          eprintf ~p:(position_lex lexbuf) ~k
            "LLambda unification prevented by %a."
            Pprint.pp_term t

      (* 0/1 *)
      | Prover.Level_inconsistency ->
          eprintf ~p:(position_lex lexbuf) ~k
            "This formula cannot be handled by the left prover!"
      | Prover.Left_logic t ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Logic variable %a encountered on the left."
            Pprint.pp_term t

      (* Miscellaneous solver interruptions *)
      | System.Interrupt ->
          eprintf ~p:(position_lex lexbuf) ~k
            "User interruption."
      | System.Abort_search ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Proof search aborted!"

      | e -> raise e

  let meta_command lexbuf =
    let k _ =
      Status.solver () ;
      Some None
    in
    function
      (* Tables *)
      | System.Missing_table (n,p) ->
          let p = match p with
            | Some p -> p | None -> position_lex lexbuf
          in
          eprintf ~p ~k
            "No table (%s is neither inductive nor coinductive)."
            n
      | Uncleared_tables ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Unable to export tables (some have been cleared, \
              state might be inconsistent).@ Run #clear_tables to fix."

      (* Tests *)
      | Assertion_failed ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Assertion failed."

      (* Misc Bedwyr errors *)
      | Invalid_command ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Invalid meta-command, or wrong arguments."

      | e -> raise e

  let io ?lexbuf =
    let k _ =
      Status.bedwyr () ;
      Some None
    in
    function
      | IO.File_error (s1,n,s2) ->
          (match lexbuf with
             | None -> eprintf ~k "Couldn't %s@ %S:@ %s."
             | Some l -> eprintf ~p:(position_lex l) ~k "Couldn't %s@ %S:@ %s.")
            s1 n s2
      | e -> raise e

  (* Unhandled errors *)
  let all lexbuf =
    let k _ =
      Status.bedwyr () ;
      Some None
    in
    function
      | Failure s ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Error:@ %s"
            s
      | e ->
          eprintf ~p:(position_lex lexbuf) ~k
            "Unexpected error:@ %s"
            (Printexc.to_string e)
end

module Eval : sig
  val definition : test_limit:(int option) ->
    print:('a -> unit) -> Input.definition_mode -> Lexing.lexbuf -> unit option
  val toplevel : test_limit:(int option) ->
    print:('a -> unit) -> Input.toplevel -> Lexing.lexbuf -> unit option
  val term : print:('a -> unit) -> Input.term_mode -> Lexing.lexbuf -> Term.term option
end = struct
  let set_reset () =
    let s = Term.save_state () in
    let ns = Term.save_namespace () in
    fun () -> Term.restore_state s ; Term.restore_namespace ns

  let command c =
    let vars = match c with
      | Input.Command.Kind (l, k) ->
          List.iter (fun s -> System.declare_type s k) l
      | Input.Command.Type (l, t) ->
          List.iter (fun s -> System.declare_const s t) l
      | Input.Command.Def (decls,defs) ->
          let stratum = System.declare_preds decls in
          let singletons = System.add_clauses stratum defs in
          List.iter
            (fun (p,n) -> wprintf ~p "%s is a singleton variable." n)
            (List.rev singletons)
      | Input.Command.Theorem thm ->
          System.add_theorem thm
      | Input.Command.Qed p -> raise (Input.Qed_error p)
    in
    ignore vars ;
    Some ()

  let query ~p ~print pre_query =
    let reset = set_reset () in
    try
      let query = System.translate_query pre_query in
      let s0 = Term.save_state () in
      let vars = List.map (fun t -> Pprint.term_to_string t, t)
                   (List.rev (Term.logic_vars [query])) in
      let found = ref false in
      let reset_time,time =
        let t0 = ref (Unix.gettimeofday ()) in
        (fun () -> t0 := Unix.gettimeofday ()),
        (fun () ->
           if !System.time
           then Format.printf "+ %.0fms@."
                  (1000. *. (Unix.gettimeofday () -. !t0)))
      in
      let show _ k =
        time () ;
        found := true ;
        if vars = [] then Format.printf "Yes.@." else
          Format.printf "Solution found:@." ;
        List.iter
          (fun (o,t) -> Format.printf " %s = %a@." o Pprint.pp_term t)
          vars ;
        Format.printf "More [y] ? %!" ;
        if
          try
            let l = input_line stdin in
            l = "" || l.[0] = 'y' || l.[0] = 'Y'
          with End_of_file -> false
        then begin
          reset_time () ;
          k ()
        end else begin
          Term.restore_state s0 ;
          Format.printf "Search stopped.@."
        end
      in
      let continue () =
        time () ;
        if !found then Format.printf "No more solutions.@."
        else Format.printf "No solution.@."
      in
      let result =
        Prover.prove ~local:0 ~timestamp:0 query
          ~success:show
          ~failure:continue
      in
      reset () ;
      Some result
    with e ->
      reset () ;
      raise e

  (* Execute meta-commands.
   * @raise Invalid_command if an argument is unexpected
   * (especially if a boolean flag is given something other than
   * "", "true", "on", "false" or "off")
   * @raise Assertion_failed if [#assert formula.], [#assert_not formula.]
   * or [#assert_raise formula.] fails *)
  let meta_command ~test_limit mc =
    let reset = Input.MetaCommand.(
      match mc with
        | Include _ | Reload | Session _ -> ignore
        | _ -> set_reset ())
    in
    try
      begin match mc with
        | Input.MetaCommand.Exit ->
            IO.close_io_files () ;
            Status.exit_with ()
        | Input.MetaCommand.Help -> Format.printf "%s" help_msg

        (* Session management *)
        | Input.MetaCommand.Include l -> List.iter (!include_file ~test_limit) l
        | Input.MetaCommand.Reload -> !reload ()
        | Input.MetaCommand.Session l -> !reload ~session:l ()

        (* Turn debugging on/off. *)
        | Input.MetaCommand.Debug value -> System.debug := (bool_of_flag value)

        (* Turn timing on/off. *)
        | Input.MetaCommand.Time value -> System.time := (bool_of_flag value)

        (* Tabling-related commands *)
        | Input.MetaCommand.Equivariant value ->
            Table.O.set_eqvt (bool_of_flag value)
        | Input.MetaCommand.Freezing temp -> Prover.freezing_point := temp
        | Input.MetaCommand.Saturation pressure ->
            Prover.saturation_pressure := pressure
        | Input.MetaCommand.Env -> System.print_env ()
        | Input.MetaCommand.Type_of pre_term -> System.print_type_of pre_term
        | Input.MetaCommand.Show_def (p,name) ->
            System.show_def (p,Term.atom ~tag:Term.Constant name)
        | Input.MetaCommand.Show_table (p,name) ->
            System.show_table (p,Term.atom ~tag:Term.Constant name)
        | Input.MetaCommand.Clear_tables ->
            System.clean_tables := true ;
            System.clear_tables ()
        | Input.MetaCommand.Clear_table (p,name) ->
            System.clean_tables := false ;
            System.clear_table (p,Term.atom ~tag:Term.Constant name)
        (* save the content of a table to a file. An exception is thrown if
         * file already exists. *)
        | Input.MetaCommand.Save_table (p,name,file) ->
            System.save_table (p,Term.atom ~tag:Term.Constant name) name file
        | Input.MetaCommand.Export name ->
            if !System.clean_tables
            then System.export name
            else raise Uncleared_tables

        (* Testing commands *)
        | Input.MetaCommand.Assert pre_query ->
            let query = System.translate_query pre_query in
            begin match test_limit with Some n when n <= 0 -> () | _ ->
              if !Status.value = None then begin
                Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
                  Pprint.pp_term query ;
                Prover.prove ~local:0 ~timestamp:0 query
                  ~success:(fun _ _ -> ())
                  ~failure:(fun () -> raise Assertion_failed)
              end
            end
        | Input.MetaCommand.Assert_not pre_query ->
            let query = System.translate_query pre_query in
            begin match test_limit with Some n when n <= 0 -> () | _ ->
              if !Status.value = None then begin
                Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
                  Pprint.pp_term query ;
                Prover.prove ~local:0 ~timestamp:0 query
                  ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
              end
            end
        | Input.MetaCommand.Assert_raise pre_query ->
            let query = System.translate_query pre_query in
            begin match test_limit with Some n when n <= 0 -> () | _ ->
              if !Status.value = None then begin
                Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@."
                  Pprint.pp_term query ;
                if try
                  Prover.prove ~local:0 ~timestamp:0 query
                    ~success:(fun _ _ -> true) ~failure:(fun _ -> true)
                with _ -> false
                then raise Assertion_failed
              end
            end
      end ;
      reset () ;
      Some ()
    with e ->
      reset () ;
      raise e

  let term ~p ~print pre_term =
    try Some (System.translate_term pre_term)
    with e -> raise e


  let definition ~test_limit ~print input lexbuf = match input with
    | `Command c ->
        command c
    | `MetaCommand mc ->
        meta_command ~test_limit mc

  let toplevel ~test_limit ~print input lexbuf = match input with
    | `Term (p,pre_query) ->
        query ~p ~print pre_query
    | `MetaCommand mc ->
        meta_command ~test_limit mc

  let term ~print input lexbuf = match input with
    | `Term (p,pre_term) ->
        term ~p ~print pre_term
end

module Mode : sig
  val definition : test_limit:(int option) -> Lexing.lexbuf -> (unit -> unit) -> unit
  val toplevel : test_limit:(int option) -> Lexing.lexbuf -> (unit -> unit) -> unit
  val term : Lexing.lexbuf -> (unit -> Term.term option) -> Term.term option
end = struct
  let step ~read ~eval ~print lexbuf =
    match read lexbuf with
      | None -> None
      | Some None -> Some None
      | Some (Some input) ->
          try Some ((eval ~print input) lexbuf)
          with e -> Catch.check lexbuf e

  let definition ~test_limit lexbuf cb =
    match
      try step ~read:Read.definition ~eval:(Eval.definition ~test_limit) ~print:ignore lexbuf
      with e -> try Catch.command lexbuf e
      with e -> try Catch.solve lexbuf e
      with e -> try Catch.meta_command lexbuf e
      with e -> try Catch.io ~lexbuf e
      with e -> Catch.all lexbuf e
    with
      | None -> cb ()
      | _ -> ()

  let toplevel ~test_limit lexbuf cb =
    match
      try step ~read:Read.toplevel ~eval:(Eval.toplevel ~test_limit) ~print:ignore lexbuf
      with e -> try Catch.solve lexbuf e
      with e -> try Catch.meta_command lexbuf e
      with e -> try Catch.io ~lexbuf e
      with e -> Catch.all lexbuf e
    with
      | None -> cb ()
      | _ -> ()

  let term lexbuf cb =
    match step ~read:Read.term ~eval:Eval.term ~print:ignore lexbuf with
      | None -> cb ()
      | Some None -> None
      | Some (Some term) -> Some term
end

let read_term () =
  let rec aux () =
    Format.printf " ?> %!" ;
    let lexbuf = Lexing.from_channel stdin in
    match Mode.term lexbuf (fun () -> raise End_of_file) with
      | None -> aux ()
      | Some term -> term
  in
  try Some (aux ()) with End_of_file -> None

let () = (System.read_term := read_term)

let fread_term lexbuf () =
  try Mode.term lexbuf (fun () -> raise End_of_file)
  with End_of_file -> None

let () = (System.fread_term := fread_term)

(* definition-mode step *)
let defs ~test_limit lexbuf =
  let cb () =
    let k _ =
      Status.input () ;
      None
    in
    ignore (eprintf ~p:(position_lex lexbuf) ~k "Empty command.")
  in
  Mode.definition ~test_limit lexbuf cb

(* definition-mode loop *)
let defl ~test_limit lexbuf =
  try while true do
    Mode.definition ~test_limit lexbuf (fun () -> raise End_of_file)
  done with End_of_file -> ()

(* read-eval-print step *)
let reps ~test_limit lexbuf =
  let cb () =
    let k _ =
      Status.input () ;
      None
    in
    ignore (eprintf ~p:(position_lex lexbuf) ~k "Empty query.")
  in
  Mode.toplevel ~test_limit lexbuf cb

(* read-eval-print loop *)
let repl ~test_limit lexbuf =
  try while true do
    Format.printf "?= %!" ;
    Lexer.flush_input lexbuf ;
    Mode.toplevel ~test_limit lexbuf (fun () -> raise End_of_file)
  done with End_of_file -> Format.printf "@."

(* TODO no meta-commands in defs? *)
