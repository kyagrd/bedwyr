(****************************************************************************)
(* Bedwyr -- toplevel eval                                                  *)
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

let decr_test_limit = function
  | Some n when n > 0 -> Some (n-1)
  | Some _ -> Some 0
  | None -> None

let bool_of_flag = function
  | None | Some "on" | Some "true" -> true
  | Some "off" | Some "false" -> false
  | _ -> raise Prover.System.Invalid_command

let set_reset () =
  let s = Ndcore.Term.save_state () in
  let ns = Ndcore.Term.save_namespace () in
  fun () -> Ndcore.Term.restore_state s ; Ndcore.Term.restore_namespace ns

let apply_on_predicate ~k f (p,name) =
  match Prover.System.translate_term (Parsetree.Preterm.pre_predconstid p name) ~k with
    | None -> None
    | Some pred -> f (p,pred) ; Some None


(* Input types. *)

let command c =
  let open Parsetree.Preterm in
  let k _ =
    Prover.System.Status.input () ;
    None
  in
  try match c with
    | Command.Kind (l, k) ->
        List.iter (fun s -> Prover.Environment.Types.declare s k) l ;
        Some ()
    | Command.Type (l, t) ->
        Prover.Environment.Objects.declare_consts l t ~k
    | Command.Def (decls,defs) ->
        begin match Prover.Environment.Objects.declare_preds decls ~k with
          | Some stratum ->
              begin match Prover.System.add_clauses stratum defs ~k with
                | Some singletons ->
                    List.iter
                      (fun (p,n) ->
                         IO.Output.wprintf ~p "%s is a singleton variable." n)
                      (List.rev singletons) ;
                    Some ()
                | None -> None
              end
          | None -> None
        end
    | Command.Theorem thm ->
        Prover.System.add_theorem thm ~k
    | Command.Qed p -> raise (Qed_error p)
  with e -> begin match e with
    (* Declarations *)
    | Prover.Environment.Invalid_type_declaration (n,p,ki,s) ->
        IO.Output.eprintf ~p
          "Cannot declare type %s of kind %a:@ %s."
          n
          Typing.Kind.pp ki
          s
    | Typing.Undefinite_type (n,p,ty,tp) ->
        let type_to_string = Typing.Type.get_to_string () in
        IO.Output.eprintf ~p
          "Polymorphism error for %s: parameter%s %s@ of type %s@ \
            %s not transparant."
          n
          (if List.length tp > 1 then "s" else "")
          (String.concat ", "
             (List.map
                (fun i -> Format.sprintf "%s"
                            (type_to_string (Typing.Type.param i))) tp))
          (type_to_string ty)
          (if List.length tp > 1 then "are" else "is")
    | Prover.Environment.Invalid_declaration (t,n,p,ty1,s,ty2) ->
        IO.Output.eprintf ~p
          "Cannot declare %s %s of type %a:@ %s of type %a."
          t n
          Typing.Type.pp ty1
          s
          Typing.Type.pp ty2
    | Typing.Invalid_pred_declaration (n,p,ty) ->
        IO.Output.eprintf ~p
          "Cannot declare predicate %s of type %a:@ \
            target type must be %s."
          n
          (Typing.Type.pp) ty
          (Typing.Type.to_string Typing.Type.prop)
    | Prover.Environment.Invalid_flavour (n,p,gf,f) ->
        let string_of_flavour = function
          | Normal -> assert false
          | Inductive -> "Inductive"
          | CoInductive -> "CoInductive"
        in
        IO.Output.eprintf ~p
          "Cannot declare predicate %s of flavour %s:@ \
            this definition block is %s."
          n
          (string_of_flavour f)
          (string_of_flavour gf)

    (* Definitions *)
    | Prover.Environment.Stratification_error (n,p) ->
        IO.Output.eprintf ~p
          "Inconsistent stratification:@ %s is forbidden here."
          n
    | Prover.System.Inconsistent_definition (n,p,s) ->
        IO.Output.eprintf ~p
          "Inconsistent extension of definition for %s:@ %s."
          n
          s

    (* Theorems *)
    | Prover.System.Inconsistent_theorem (n,p,s) ->
        IO.Output.eprintf ~p
          "Inconsistent theorem specification for %s:@ %s."
          n
          s

    (*
    | Qed_error p ->
        IO.Output.eprintf ~p
          "\"Qed.\" command used while not in proof mode."
     *)

    | e -> raise e
  end ;
  Prover.System.Status.def () ;
  None

let query ~p ~print ~concise pre_query =
  let k _ =
    Prover.System.Status.input () ;
    None
  in
  match Prover.System.translate_query pre_query ~k with
    | None -> None
    | Some query ->
        let reset = set_reset () in
        try
          let s0 = Ndcore.Term.save_state () in
          let vars =
            List.map
              (fun t -> Ndcore.Pprint.term_to_string t, t)
              (List.rev (Ndcore.Term.logic_vars [query]))
          in
          let number = ref 0 in
          let reset_time,time =
            let t0 = ref (Unix.gettimeofday ()) in
            (fun () -> t0 := Unix.gettimeofday ()),
            (fun () ->
               if !Prover.System.time then
                 IO.Output.printf ~nl:true "+ %.0fms"
                   (1000. *. (Unix.gettimeofday () -. !t0)))
          in
          let show _ k =
            time () ;
            incr number ;
            if vars = [] then IO.Output.printf ~nl:true "Found a solution."
            else IO.Output.printf ~nl:true "@[<v 1>Found a solution:%a@]"
                   Ndcore.Pprint.pp_env vars ;
            if concise || begin
              IO.Output.printf "More [y] ? " ;
              try
                let l = input_line stdin in
                l = "" || l.[0] = 'y' || l.[0] = 'Y'
              with End_of_file -> false
            end then begin
              reset_time () ;
              k ()
            end else begin
              Ndcore.Term.restore_state s0 ;
              IO.Output.printf ~nl:true "Search stopped."
            end
          in
          let continue () =
            time () ;
            if !number=0 then IO.Output.printf ~nl:true "No solution."
            else IO.Output.printf ~nl:true "No more solutions (found %d)." !number
          in
          let result =
            Prover.Proofsearch.prove ~local:0 ~timestamp:0 query
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
 * @raise {!Prover.System.Invalid_command} if an argument is unexpected
 * (especially if a boolean flag is given something other than "",
 * "true", "on", "false" or "off")
 * @raise {!Prover.System.Assertion_failed} if [#assert formula.],
 * [#assert_not formula.] or [#assert_raise formula.] fails *)
let meta_command ~(include_file:(?test_limit:(int option) -> string -> Ndcore.Term.term list option)) ~(reload:(?session:(string list) -> unit -> unit)) ~test_limit mc ~p =
  let open Parsetree.Preterm in
  let k _ =
    Prover.System.Status.input () ;
    None
  in
  let reset = MetaCommand.(
    match mc with
      | Include _ | Reload | Session _ -> ignore
      | _ -> set_reset ())
  in
  try
    let result = match mc with
      | MetaCommand.Exit ->
          IO.Files.I.clear () ;
          IO.Files.O.clear () ;
          exit 0
      | MetaCommand.Help ->
          Format.printf "%s" help_msg ;
          Some None

      (* Session management *)
      | MetaCommand.Include files ->
          let f =
            include_file ~test_limit:(decr_test_limit test_limit)
          in
          List.fold_left
            (fun accum file -> match accum,f file with
               | Some None,Some _ -> Some None
               | _ -> None)
            (Some None)
            files
      | MetaCommand.Reload ->
          reload () ;
          Some None
      | MetaCommand.Session session ->
          reload ~session () ;
          Some None

      (* Turn debugging on/off. *)
      | MetaCommand.Debug value ->
          IO.Output.debug := (bool_of_flag value) ;
          Some None

      (* Turn timing on/off. *)
      | MetaCommand.Time value ->
          Prover.System.time := (bool_of_flag value) ;
          Some None

      (* Tabling-related commands *)
      | MetaCommand.Equivariant value ->
          Prover.Table.set_eqvt (bool_of_flag value) ;
          Some None
      | MetaCommand.Freezing temp ->
          Prover.Proofsearch.freezing_point := temp ;
          Some None
      | MetaCommand.Saturation pressure ->
          Prover.Proofsearch.saturation_pressure := pressure ;
          Some None
      | MetaCommand.Env ->
          Prover.System.print_env () ;
          Some None
      | MetaCommand.Type_of pre_term ->
          ignore (Prover.System.print_type_of pre_term ~k) ;
          Some None
      | MetaCommand.Show_def (p,name) ->
          apply_on_predicate ~k Prover.System.show_def (p,name)
      | MetaCommand.Show_table (p,name) ->
          apply_on_predicate ~k Prover.System.show_table (p,name)
      | MetaCommand.Clear_tables ->
          Prover.System.clean_tables := true ;
          Prover.System.clear_tables () ;
          Some None
      | MetaCommand.Clear_table (p,name) ->
          let f (p,pred) =
            Prover.System.clean_tables := false ;
            Prover.System.clear_table (p,pred)
          in
          apply_on_predicate ~k f (p,name)
      (* save the content of a table to a file. An exception is thrown if
       * file already exists. *)
      | MetaCommand.Save_table (p,name,file) ->
          let f (p,pred) =
            Prover.System.save_table (p,pred) name file
          in
          apply_on_predicate ~k f (p,name)
      | MetaCommand.Export name ->
          Prover.System.export name ;
          Some None

      (* Testing commands *)
      | MetaCommand.Assert pre_query ->
          begin match Prover.System.translate_query pre_query ~k with
            | None -> None
            | Some query ->
                begin match test_limit with Some n when n <= 0 -> () | _ ->
                  Format.eprintf "@[<hv 2>Checking that@ %a@,...@]@."
                    Ndcore.Pprint.pp_term query ;
                  Prover.Proofsearch.prove ~local:0 ~timestamp:0 query
                    ~success:(fun _ _ -> ())
                    ~failure:(fun () -> raise Prover.System.Assertion_failed)
                end ;
                Some (Some query)
          end
      | MetaCommand.Assert_not pre_query ->
          begin match Prover.System.translate_query pre_query ~k with
            | None -> None
            | Some query ->
                begin match test_limit with Some n when n <= 0 -> () | _ ->
                  Format.eprintf "@[<hv 2>Checking that@ %a@ is false...@]@."
                    Ndcore.Pprint.pp_term query ;
                  Prover.Proofsearch.prove ~local:0 ~timestamp:0 query
                    ~success:(fun _ _ -> raise Prover.System.Assertion_failed) ~failure:ignore
                end ;
                Some (Some query)
          end
      | MetaCommand.Assert_raise pre_query ->
          begin match Prover.System.translate_query pre_query ~k with
            | None -> None
            | Some query ->
                begin match test_limit with Some n when n <= 0 -> () | _ ->
                  Format.eprintf "@[<hv 2>Checking that@ %a@ causes an error...@]@."
                    Ndcore.Pprint.pp_term query ;
                  if try
                    Prover.Proofsearch.prove ~local:0 ~timestamp:0 query
                      ~success:(fun _ _ -> true) ~failure:(fun _ -> true)
                  with _ -> false
                  then raise Prover.System.Assertion_failed
                end ;
                Some None
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
    Prover.System.Status.input () ;
    None
  in
  try Prover.System.translate_term pre_term ~k
  with e -> raise e


(* Entry points. *)

let definition ~include_file ~reload ~test_limit ~print input ~p = match input with
  | `Command c ->
      begin match command c with
        | Some () -> Some None
        | None -> None
      end
  | `MetaCommand mc ->
      meta_command ~include_file ~reload ~test_limit mc ~p

let toplevel ~concise ~include_file ~reload ~test_limit ~print input ~p = match input with
  | `Term (p,pre_query) ->
      query ~p ~print ~concise pre_query
  | `MetaCommand mc ->
      begin match meta_command ~include_file ~reload ~test_limit mc ~p with
        | Some _ -> Some ()
        | None -> None
      end

let term ~print input ~p = match input with
  | `Term (p,pre_term) ->
      term ~p ~print pre_term
