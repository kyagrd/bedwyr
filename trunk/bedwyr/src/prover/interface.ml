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

let session     = ref []
let definitions = ref []
let queries     = ref []
let test_limit  = ref (Some 0)

let incr_test_limit () =
  test_limit := match !test_limit with
    | Some n -> Some (n+1)
    | None -> None
let remove_test_limit () =
  test_limit := None
let decr_test_limit = function
  | Some n when n > 0 -> Some (n-1)
  | Some _ -> Some 0
  | None -> None

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

let bool_of_flag = function
  | None | Some "on" | Some "true" -> true
  | Some "off" | Some "false" -> false
  | _ -> raise Invalid_command

module Catch : sig
  val solve : p:Preterm.Pos.t -> exn -> 'a option
  val meta_command : p:Preterm.Pos.t -> exn -> 'a option
  val io : ?p:Preterm.Pos.t -> exn -> 'a option
  val all : p:Preterm.Pos.t -> exn -> 'a option
end = struct
  let solve ~p e =
    begin match e with
      (* Predicates *)
      | System.Missing_definition (n,p') ->
          Output.eprintf ~p:(match p' with Some p -> p | None -> p)
            "Undefined predicate (%s was declared as a constant)."
            n

      (* HOPU *)
      | Unify.NotLLambda t ->
          Output.eprintf ~p
            "LLambda unification prevented by %a."
            Pprint.pp_term t

      (* 0/1 *)
      | Prover.Level_inconsistency ->
          Output.eprintf ~p
            "This formula cannot be handled by the left prover!"
      | Prover.Left_logic t ->
          Output.eprintf ~p
            "Logic variable %a encountered on the left."
            Pprint.pp_term t

      (* Miscellaneous solver interruptions *)
      | System.Interrupt ->
          Output.eprintf ~p
            "User interruption."
      | System.Abort_search ->
          Output.eprintf ~p
            "Proof search aborted!"

      | e -> raise e
    end ;
    Status.ndcore () ;
    None

  let meta_command ~p e =
    begin match e with
      (* Tables *)
      | System.Missing_table (n,p') ->
          Output.eprintf ~p:(match p' with Some p -> p | None -> p)
            "No table (%s is neither inductive nor coinductive)."
            n
      | Uncleared_tables ->
          Output.eprintf ~p
            "Unable to export tables (some have been cleared, \
              state might be inconsistent).@ Run #clear_tables to fix."

      (* Tests *)
      | Assertion_failed ->
          Output.eprintf ~p
            "Assertion failed."

      (* Misc Bedwyr errors *)
      | Invalid_command ->
          Output.eprintf ~p
            "Invalid meta-command, or wrong arguments."

      | e -> raise e
    end ;
    Status.solver () ;
    None

  let io ?p e =
    begin match e with
      | IO.File_error (s1,n,s2) ->
          Output.eprintf ?p "Couldn't %s@ %S:@ %s." s1 n s2
      | e -> raise e
    end ;
    Status.bedwyr () ;
    None

  (* Unhandled errors *)
  let all ~p e =
    begin match e with
      | Failure s ->
          Output.eprintf ~p
            "Error:@ %s"
            s
      | e ->
          Output.eprintf ~p
            "Unexpected error:@ %s"
            (Printexc.to_string e)
    end ;
    Status.bedwyr () ;
    None
end


module Eval : sig
  val definition :
    include_file:(?test_limit:(int option) -> string -> unit option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    print:('a -> unit) -> Preterm.definition_mode -> p:Preterm.Pos.t ->
    unit option
  val toplevel : concise:bool ->
    include_file:(?test_limit:(int option) -> string -> unit option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    print:('a -> unit) -> Preterm.toplevel -> p:Preterm.Pos.t ->
    unit option
  val term :
    print:('a -> unit) -> Preterm.term_mode -> p:Preterm.Pos.t ->
    Term.term option
end = struct
  let set_reset () =
    let s = Term.save_state () in
    let ns = Term.save_namespace () in
    fun () -> Term.restore_state s ; Term.restore_namespace ns

  let command c =
    let k _ =
      Status.input () ;
      None
    in
    try match c with
      | Preterm.Command.Kind (l, k) ->
          List.iter (fun s -> Environment.Types.declare s k) l ;
          Some ()
      | Preterm.Command.Type (l, t) ->
          Environment.Objects.declare_consts l t ~k
      | Preterm.Command.Def (decls,defs) ->
          begin match Environment.Objects.declare_preds decls ~k with
            | Some stratum ->
                begin match System.add_clauses stratum defs ~k with
                  | Some singletons ->
                      List.iter
                        (fun (p,n) ->
                           Output.wprintf ~p "%s is a singleton variable." n)
                        (List.rev singletons) ;
                      Some ()
                  | None -> None
                end
            | None -> None
          end
      | Preterm.Command.Theorem thm ->
          System.add_theorem thm ~k
      | Preterm.Command.Qed p -> raise (Preterm.Qed_error p)
    with e -> begin match e with
      (* Declarations *)
      | Environment.Invalid_type_declaration (n,p,ki,s) ->
          Output.eprintf ~p
            "Cannot declare type %s of kind %a:@ %s."
            n
            Preterm.Typing.pp_kind ki
            s
      | Preterm.Typing.Undefinite_type (n,p,ty,tp) ->
          let type_to_string = Preterm.Typing.get_type_to_string () in
          Output.eprintf ~p
            "Polymorphism error for %s: parameter%s %s@ of type %s@ \
              %s not transparant."
            n
            (if List.length tp > 1 then "s" else "")
            (String.concat ", "
               (List.map
                  (fun i -> Format.sprintf "%s"
                              (type_to_string (Preterm.Typing.tparam i))) tp))
            (type_to_string ty)
            (if List.length tp > 1 then "are" else "is")
      | Environment.Invalid_declaration (t,n,p,ty1,s,ty2) ->
          Output.eprintf ~p
            "Cannot declare %s %s of type %a:@ %s of type %a."
            t n
            (Preterm.Typing.get_pp_type ()) ty1
            s
            (Preterm.Typing.get_pp_type ()) ty2
      | Preterm.Typing.Invalid_pred_declaration (n,p,ty) ->
          Output.eprintf ~p
            "Cannot declare predicate %s of type %a:@ \
              target type must be %s."
            n
            (Preterm.Typing.get_pp_type ()) ty
            (Preterm.Typing.get_type_to_string () Preterm.Typing.tprop)
      | Environment.Invalid_flavour (n,p,gf,f) ->
          let string_of_flavour = function
            | Preterm.Normal -> assert false
            | Preterm.Inductive -> "Inductive"
            | Preterm.CoInductive -> "CoInductive"
          in
          Output.eprintf ~p
            "Cannot declare predicate %s of flavour %s:@ \
              this definition block is %s."
            n
            (string_of_flavour f)
            (string_of_flavour gf)

      (* Definitions *)
      | Environment.Stratification_error (n,p) ->
          Output.eprintf ~p
            "Inconsistent stratification:@ %s is forbidden here."
            n
      | System.Inconsistent_definition (n,p,s) ->
          Output.eprintf ~p
            "Inconsistent extension of definition for %s:@ %s."
            n
            s

      (* Theorems *)
      | System.Inconsistent_theorem (n,p,s) ->
          Output.eprintf ~p
            "Inconsistent theorem specification for %s:@ %s."
            n
            s

      (*
      | Preterm.Qed_error p ->
          Output.eprintf ~p
            "\"Qed.\" command used while not in proof mode."
       *)

      | e -> raise e
    end ;
    Status.def () ;
    None

  let query ~p ~print ~concise pre_query =
    let k _ =
      Status.input () ;
      None
    in
    match System.translate_query pre_query ~k with
      | None -> None
      | Some query ->
          let reset = set_reset () in
          try
            let s0 = Term.save_state () in
            let vars =
              List.map
                (fun t -> Pprint.term_to_string t, t)
                (List.rev (Term.logic_vars [query]))
            in
            let number = ref 0 in
            let reset_time,time =
              let t0 = ref (Unix.gettimeofday ()) in
              (fun () -> t0 := Unix.gettimeofday ()),
              (fun () ->
                 if !System.time then
                   Output.printf ~nl:true "+ %.0fms"
                     (1000. *. (Unix.gettimeofday () -. !t0)))
            in
            let show _ k =
              time () ;
              incr number ;
              if vars = [] then Output.printf ~nl:true "Found a solution."
              else Output.printf ~nl:true "@[<v 1>Found a solution:%a@]"
                     Pprint.pp_env vars ;
              if concise || begin
                Output.printf "More [y] ? " ;
                try
                  let l = input_line stdin in
                  l = "" || l.[0] = 'y' || l.[0] = 'Y'
                with End_of_file -> false
              end then begin
                reset_time () ;
                k ()
              end else begin
                Term.restore_state s0 ;
                Output.printf ~nl:true "Search stopped."
              end
            in
            let continue () =
              time () ;
              if !number=0 then Output.printf ~nl:true "No solution."
              else Output.printf ~nl:true "No more solutions (found %d)." !number
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
            try Catch.io ~p e
            with e -> Catch.solve ~p e

  (* Execute meta-commands.
   * @raise Invalid_command if an argument is unexpected
   * (especially if a boolean flag is given something other than
   * "", "true", "on", "false" or "off")
   * @raise Assertion_failed if [#assert formula.], [#assert_not formula.]
   * or [#assert_raise formula.] fails *)
  let meta_command ~(include_file:(?test_limit:(int option) -> string -> unit option)) ~(reload:(?session:(string list) -> unit -> unit)) ~test_limit mc ~p =
    let k _ =
      Status.input () ;
      None
    in
    let reset = Preterm.MetaCommand.(
      match mc with
        | Include _ | Reload | Session _ -> ignore
        | _ -> set_reset ())
    in
    try
      let result = match mc with
        | Preterm.MetaCommand.Exit ->
            IO.close_io_files () ;
            exit 0
        | Preterm.MetaCommand.Help ->
            Format.printf "%s" help_msg ;
            Some ()

        (* Session management *)
        | Preterm.MetaCommand.Include files ->
            let f =
              include_file ~test_limit:(decr_test_limit test_limit)
            in
            List.fold_left
              (fun accum file -> match accum,f file with
                 | Some (),Some () -> Some ()
                 | _ -> None)
              (Some ())
              files
        | Preterm.MetaCommand.Reload ->
            Some (reload ())
        | Preterm.MetaCommand.Session session ->
            Some (reload ~session ())

        (* Turn debugging on/off. *)
        | Preterm.MetaCommand.Debug value ->
            Output.debug := (bool_of_flag value) ;
            Some ()

        (* Turn timing on/off. *)
        | Preterm.MetaCommand.Time value ->
            System.time := (bool_of_flag value) ;
            Some ()

        (* Tabling-related commands *)
        | Preterm.MetaCommand.Equivariant value ->
            Table.O.set_eqvt (bool_of_flag value) ;
            Some ()
        | Preterm.MetaCommand.Freezing temp ->
            Prover.freezing_point := temp ;
            Some ()
        | Preterm.MetaCommand.Saturation pressure ->
            Prover.saturation_pressure := pressure ;
            Some ()
        | Preterm.MetaCommand.Env ->
            System.print_env () ;
            Some ()
        | Preterm.MetaCommand.Type_of pre_term ->
            (* XXX *)
            ignore (System.print_type_of pre_term ~k) ;
            Some ()
        | Preterm.MetaCommand.Show_def (p,name) ->
            System.show_def (p,Term.atom ~tag:Term.Constant name) ;
            Some ()
        | Preterm.MetaCommand.Show_table (p,name) ->
            System.show_table (p,Term.atom ~tag:Term.Constant name) ;
            Some ()
        | Preterm.MetaCommand.Clear_tables ->
            System.clean_tables := true ;
            System.clear_tables () ;
            Some ()
        | Preterm.MetaCommand.Clear_table (p,name) ->
            System.clean_tables := false ;
            System.clear_table (p,Term.atom ~tag:Term.Constant name) ;
            Some ()
        (* save the content of a table to a file. An exception is thrown if
         * file already exists. *)
        | Preterm.MetaCommand.Save_table (p,name,file) ->
            System.save_table (p,Term.atom ~tag:Term.Constant name) name file ;
            Some ()
        | Preterm.MetaCommand.Export name ->
            begin if !System.clean_tables
            then System.export name
            else raise Uncleared_tables end ;
            Some ()

        (* Testing commands *)
        | Preterm.MetaCommand.Assert pre_query ->
            begin match System.translate_query pre_query ~k with
              | None -> None
              | Some query ->
                  begin match test_limit with Some n when n <= 0 -> () | _ ->
                    if !Status.value = None then begin
                      Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
                        Pprint.pp_term query ;
                      Prover.prove ~local:0 ~timestamp:0 query
                        ~success:(fun _ _ -> ())
                        ~failure:(fun () -> raise Assertion_failed)
                    end
                  end ;
                  Some ()
            end
        | Preterm.MetaCommand.Assert_not pre_query ->
            begin match System.translate_query pre_query ~k with
              | None -> None
              | Some query ->
                  begin match test_limit with Some n when n <= 0 -> () | _ ->
                    if !Status.value = None then begin
                      Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
                        Pprint.pp_term query ;
                      Prover.prove ~local:0 ~timestamp:0 query
                        ~success:(fun _ _ -> raise Assertion_failed) ~failure:ignore
                    end
                  end ;
                  Some ()
            end
        | Preterm.MetaCommand.Assert_raise pre_query ->
            begin match System.translate_query pre_query ~k with
              | None -> None
              | Some query ->
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
                  end ;
                  Some ()
            end
      in
      reset () ;
      result
    with e ->
      reset () ;
      try Catch.io ~p e
      with e -> try Catch.solve ~p e
      with e -> Catch.meta_command ~p e

  let term ~p ~print pre_term =
    let k _ =
      Status.input () ;
      None
    in
    try System.translate_term pre_term ~k
    with e -> raise e


  let definition ~include_file ~reload ~test_limit ~print input ~p = match input with
    | `Command c ->
        command c
    | `MetaCommand mc ->
        meta_command ~include_file ~reload ~test_limit mc ~p

  let toplevel ~concise ~include_file ~reload ~test_limit ~print input ~p = match input with
    | `Term (p,pre_query) ->
        query ~p ~print ~concise pre_query
    | `MetaCommand mc ->
        meta_command ~include_file ~reload ~test_limit mc ~p

  let term ~print input ~p = match input with
    | `Term (p,pre_term) ->
        term ~p ~print pre_term
end

module Mode : sig
  val definition :
    include_file:(?test_limit:(int option) -> string -> unit option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    Lexing.lexbuf -> unit option option
  val toplevel : concise:bool ->
    include_file:(?test_limit:(int option) -> string -> unit option) ->
    reload:(?session:(string list) -> unit -> unit) ->
    test_limit:(int option) ->
    Lexing.lexbuf -> unit option option
  val term :
    Lexing.lexbuf -> Term.term option option
end = struct
  let step ~read ~eval ~print lexbuf =
    try match read lexbuf with
      | None -> None
      | Some None -> Some None
      | Some (Some input) ->
          Some (eval ~print input ~p:(Preterm.Pos.of_lexbuf lexbuf ()))
    with e -> Some (Catch.all ~p:(Preterm.Pos.of_lexbuf lexbuf ()) e)

  let definition ~include_file ~reload ~test_limit lexbuf =
    let k _ =
      Status.input () ;
      None
    in
    let eval = Eval.definition ~include_file ~reload ~test_limit in
    step ~read:(Read.definition_mode ~k) ~eval ~print:ignore lexbuf

  let toplevel ~concise ~include_file ~reload ~test_limit lexbuf =
    let k _ =
      Status.input () ;
      None
    in
    let eval = Eval.toplevel ~concise ~include_file ~reload ~test_limit in
    step ~read:(Read.toplevel ~k) ~eval ~print:ignore lexbuf

  let term lexbuf =
    let k _ =
      Status.input () ;
      None
    in
    step ~read:(Read.term_mode ~k) ~eval:Eval.term ~print:ignore lexbuf
end

let () =
  System.read_term := begin
    let rec aux () =
      Format.printf " ?> %!" ;
      let lexbuf = Lexing.from_channel stdin in
      match Mode.term lexbuf with
        | None -> None
        | Some None -> aux ()
        | Some (Some term) -> Some term
    in
    fun () -> aux ()
  end

let () =
  System.fread_term := begin
    fun lexbuf () ->
      match Mode.term lexbuf with
        | None | Some None -> None
        | Some (Some term) -> Some term
  end


(* 4 basic input styles *)

(* definition-mode step *)
let defs ?(test_limit=(!test_limit)) ~include_file ~reload lexbuf =
  match Mode.definition ~include_file ~reload ~test_limit lexbuf with
    | None ->
        Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ()) "Empty command." ;
        Status.input () ;
        None
    | Some None -> Some None
    | Some (Some ()) -> Some (Some ())

(* definition-mode loop *)
let defl ?(test_limit=(!test_limit)) ~include_file ~reload lexbuf =
  let rec aux error_less =
    match Mode.definition ~include_file ~reload ~test_limit lexbuf with
      | None -> if error_less then Some () else None
      | Some None -> aux false
      | Some (Some ()) -> aux error_less
  in
  aux true

(* read-eval-print step *)
let reps ?(concise=true) ?(test_limit=(!test_limit)) ~include_file ~reload lexbuf =
  match Mode.toplevel ~concise ~include_file ~reload ~test_limit lexbuf with
    | None ->
        Output.eprintf ~p:(Preterm.Pos.of_lexbuf lexbuf ()) "Empty query." ;
        Status.input () ;
        None
    | Some None -> None
    | Some (Some ()) -> Some ()

(* read-eval-print loop *)
let repl ?(concise=false) ?(test_limit=(!test_limit)) ~include_file ~reload lexbuf =
  let rec aux () =
    Format.printf "?= %!" ;
    Lexer.flush_input lexbuf ;
    match Mode.toplevel ~concise ~include_file ~reload ~test_limit lexbuf with
      | None -> Format.printf "@."
      | Some None -> aux ()
      | Some (Some ()) -> aux ()
  in
  aux ()


(* convenience wrappers *)

let run_file f path =
  try Some (Environment.IncludedFiles.apply_on_file f path)
  with e -> Catch.io e

let run_string f ?fname str =
  Read.apply_on_string f ?fname str

let run_channel f ?fname chan =
  Read.apply_on_channel f ?fname chan

(* public wrappers *)

let rec include_file ?test_limit name =
  match run_file (defl ?test_limit ~include_file ~reload) name with
    | None (* I/O error *)
    | Some (Some None) (* corrupted file *) -> None
    | Some None (* file already included *)
    | Some (Some (Some ())) (* include success *) -> Some ()

and reload ?(session=(!session)) () =
  System.reset () ;
  ignore (run_definitions_string ~fname:"Bedwyr::stdlib" Environment.stdlib) ;
  List.iter (function name -> ignore (include_file name)) session ;
  List.iter (function query -> ignore (run_query_string query)) !definitions

and run_query_string str =
  run_string (reps ~include_file ~reload) str

and run_definitions_string ?fname str =
  run_string (defl ~include_file ~reload) ?fname str

let run_queries_channel chan =
  run_channel (repl ~include_file ~reload) chan
