(****************************************************************************)
(* Bedwyr -- high-level functions                                           *)
(* Copyright (C) 2006 Alwen Tiu, Axelle Ziegler, Andrew Gacek               *)
(* Copyright (C) 2006-2009 David Baelde                                     *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2011-2015 Quentin Heath                                    *)
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

let read_term = ref (fun () -> None)
let fread_term = ref (fun _ () -> None)
let time  = ref false
let root_atoms = ref []
let use_filter = ref false
let clean_tables = ref true



(* Clauses and queries construction *)


let translate_query pre_term ~k =
  match Environment.translate_term ~expected_type:Type.prop pre_term ~k with
    | Some (_,_,(_,term)) -> Some term
    | None -> None

(* Replace the params by fresh variables and
 * put the constraints on the parameters in the body:
 *     pred [params] := body
 *     d X X (f X Y) := g X Y Z
 * --> d X U V       := (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
 * --> d X U V       := exists Z Y, (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
 * --> d == \\\ Exists\\ #4=#5 /\ (#3=(f #5 #1) /\ (g #5 #1 #2))
 *)
let mk_clause pred params body =
  (* pred       d
   * params     [X;X;(f X Y)]
   * Create the prologue (new equalities added to the body) and the new
   * set of variables used as parameters.
   * A parameter can be left untouched if it's a variable which didn't
   * occur yet. *)
  let new_params,prologue =
    List.fold_left
      (fun (new_params,prologue) p ->
         match Ndcore.Term.observe p with
           | Ndcore.Term.Var {Ndcore.Term.tag=Ndcore.Term.Logic}
               when List.for_all (fun v -> v!=p) new_params ->
               p::new_params,prologue
           | _  ->
               let v = Ndcore.Term.fresh ~ts:0 ~lts:0 Ndcore.Term.Logic in
               (v::new_params,(Ndcore.Term.op_eq v p)::prologue))
      ([],[])
      params
  in
  (* new_params [V;U;X]
   * prologue   [V=(f X Y);U=X]
   * Add prologue to the body *)
  let body = if prologue = [] then body else
    List.fold_left
      (fun acc term -> Ndcore.Term.op_and term acc)
      body
      prologue
  in
  (* body       U=X /\ (V=(f X Y) /\ (g X Y Z))
   * Quantify existentially over the initial free variables. *)
  let body =
    List.fold_left
      (fun body v ->
         if List.exists (Ndcore.Term.eq v) new_params then body
         else Ndcore.Term.quantify Ndcore.Term.Exists v body)
      body
      (* XXX in case [body] wasn't created by [translate_term],
       * we should depend on the level to look for instantiable variables,
       * ie not always Logic ones (cf [translate_term]) *)
      (Ndcore.Term.logic_vars [body])
  in
  IO.Output.dprintf "%a := %a"
    Ndcore.Pprint.pp_term (Ndcore.Term.app pred (List.rev new_params))
    Ndcore.Pprint.pp_term body ;
  (* body       Exists\\ U=X /\ (V=(f X #1) /\ (g X #1 #2))
   * Finally, abstract over parameters *)
  let arity,body =
    if new_params = [] then 0,body else
      let body =
        List.fold_left (fun body v -> Ndcore.Term.abstract v body)
          body
          new_params
      in match Ndcore.Term.observe body with
        | Ndcore.Term.Lam (n,b) -> n,b
        | _ -> assert false
  in
  (* pred       d
   * arity      3
   * body       Exists\\ #4=#5 /\ (#3=(f #5 #1) /\ (g #5 #1 #2)) *)
  (pred, arity, body)


(* Predicates definitions *)

exception Inconsistent_definition of string * IO.Pos.t * string


let mk_def_clause p head body =
  let pred,params = match Ndcore.Term.observe head with
    | Ndcore.Term.Var ({Ndcore.Term.tag=Ndcore.Term.Constant}) -> head,[]
    | Ndcore.Term.App (pred,params) -> pred,params
    | _ -> raise (Inconsistent_definition
                    ("some predicate",p,"head term structure incorrect"))
  in
  mk_clause pred params body

(* returns the list of singleton variables of the clause *)
let add_def_clause stratum (p,pre_head,pre_body) ~k =
  let free_args = Parsetree.Preterm.free_args pre_head in
  (* XXX what about stratum in theorems? *)
  match
    Environment.translate_term ~expected_type:Type.prop ~stratum
      ~free_args ~head:true pre_head ~k
  with
    | Some (_,free_types,(_,head)) ->
        begin match
          Environment.translate_term ~expected_type:Type.prop ~stratum ~free_args
            ~free_types pre_body ~k
        with
          | Some (_,_,(singletons,body)) ->
              begin
                let pred,arity,body =
                  mk_def_clause p head body
                in
                let head_var = Ndcore.Term.get_var pred in
                let name = Ndcore.Term.get_name pred in
                let {Environment.stratum=stratum';Environment.definition=definition} as x =
                  match Environment.Objects.get_pred head_var with
                    | Some p -> p
                    | None ->
                        raise (Inconsistent_definition
                                 (name,p,"object declared as a constant"))
                in
                if stratum<>stratum' then
                  raise (Inconsistent_definition
                           (name,p,"predicate defined in anoter stratification block"))
                else let def =
                  match Ndcore.Term.observe definition with
                    | Ndcore.Term.Lam (a,b) when arity=a ->
                        Ndcore.Term.lambda a (Ndcore.Term.op_or b body)
                    | _ when arity=0 ->
                        Ndcore.Term.op_or definition body
                    | _ -> assert false
                in
                let def = Ndcore.Norm.hnorm def in
                x.Environment.definition <- def ;
                Some (List.rev singletons)
              end
          | None -> None
        end
    | None -> None

(* returns the list of singleton variables of the clause *)
let add_clauses stratum clauses ~k =
  List.fold_left
    (fun accum clause ->
       match accum,(add_def_clause stratum clause ~k ) with
         | Some singletons,Some new_singletons ->
             Some (List.rev_append new_singletons singletons)
         | _,_ -> None)
    (Some []) clauses


(* Theorem definitions *)

exception Inconsistent_theorem of string * IO.Pos.t * string


let mk_theorem_clauses (p,_) theorem =
  (* Check whether the theorem has the right structure. *)
  let clean_theorem theorem =
    let vars =
      let rec aux l = function
        | n when n <= 0 -> l
        (* XXX in case [translate_term] changes how it deals with free
         * variables, we should depend on the level to create an
         * instantiable variable, ie not always a Logic one (cf
         * [mk_clause] and [translate_term])*)
        | n -> aux ((Ndcore.Term.fresh ~ts:0 ~lts:0 Ndcore.Term.Logic)::l) (n-1)
      in
      aux []
    in
    let split head = match Ndcore.Term.observe head with
      | Ndcore.Term.Var ({Ndcore.Term.tag=Ndcore.Term.Constant}) -> head,[]
      | Ndcore.Term.App (pred,params) -> pred,params
      | _ -> raise (Inconsistent_theorem
                      ("some predicate",p,"head term structure incorrect"))
    in
    (* [newl] is a list of deep-normed theorem clauses
     * [oldl] is a list of theorems built with theorem clauses, /\ and -> *)
    let rec aux newl = function
      | [] -> newl
      | (hypothesis,theorem)::oldl ->
          let theorem = Ndcore.Norm.hnorm theorem in
          begin match Ndcore.Term.observe theorem with
            | Ndcore.Term.Binop (Ndcore.Term.Arrow,body,head) ->
                let body = Ndcore.Norm.deep_norm body in
                let hypothesis = Ndcore.Term.op_and body hypothesis in
                aux newl ((hypothesis,head)::oldl)
            | Ndcore.Term.Binder (Ndcore.Term.Forall,n,t) ->
                let t = Ndcore.Term.lambda n t in
                aux newl ((hypothesis,Ndcore.Term.app t (vars n))::oldl)
            | Ndcore.Term.Binop (Ndcore.Term.And,t1,t2) ->
                aux newl ((hypothesis,t1)::(hypothesis,t2)::oldl)
            | _ ->
                let head = Ndcore.Norm.deep_norm theorem in
                let pred,params = split head in
                aux ((pred,params,hypothesis)::newl) oldl
          end
    in
    aux [] [Ndcore.Term.op_true,theorem]
  in
  List.rev_map
    (fun (pred,params,body) -> mk_clause pred params body)
    (clean_theorem theorem)

let add_theorem_clause p (pred,arity,body) =
  let head_var = Ndcore.Term.get_var pred in
  let name = Ndcore.Term.get_name pred in
  let {Environment.flavour=flavour} =
    match Environment.Objects.get_pred head_var with
      | Some p -> p
      | None ->
          raise (Inconsistent_theorem
                   (name,p,"target object declared as a constant"))
  in
  match flavour with
    | Environment.Normal -> () (* XXX to crash or not to crash? *)
        (*raise (Inconsistent_theorem
                 (name,p,"predicate not tabled"))*)
    | Environment.Inductive ({Environment.theorem=theorem} as x)
    | Environment.CoInductive ({Environment.theorem=theorem} as x) ->
        let th =
          match Ndcore.Term.observe theorem with
            | Ndcore.Term.Lam (a,b) when arity=a ->
                Ndcore.Term.lambda a (Ndcore.Term.op_or b body)
            | _ when arity=0 ->
                Ndcore.Term.op_or theorem body
            | _ -> assert false
        in
        let th = Ndcore.Norm.hnorm th in
        x.Environment.theorem <- th

let add_theorem (p,n,pre_theorem) ~k =
  match Environment.translate_term ~expected_type:Type.prop pre_theorem ~k with
    | Some (_,_,(_,theorem)) ->
        let clauses = mk_theorem_clauses (p,n) theorem in
        List.iter (add_theorem_clause p) clauses ;
        Some ()
    | None -> None


(* Predicates accessors *)

exception Missing_definition of string * IO.Pos.t option
exception Missing_table of string * IO.Pos.t option


let get_name_pred ?pos head_tm =
  let head_var = Ndcore.Term.get_var head_tm in
  let name = Ndcore.Term.get_name head_tm in
  let {Environment.flavour=flavour;Environment.definition=definition;Environment.ty=ty} =
    match Environment.Objects.get_pred head_var with
      | Some p -> p
      | None -> raise (Missing_definition (name,pos))
  in
  name,flavour,definition,ty

let get_flav_def head_tm =
  let _,flavour,definition,_ = get_name_pred head_tm in
  flavour,definition

let get_def pos head_tm success =
  let _,_,definition,ty = get_name_pred ~pos head_tm in
  success definition ty

let get_table pos head_tm success =
  let name,flavour,_,ty = get_name_pred ~pos head_tm in
  match flavour with
    | Environment.Normal ->
        raise (Missing_table (name,Some pos))
    | Environment.Inductive {Environment.table=table} | Environment.CoInductive {Environment.table=table} ->
        success table ty

let clear_tables () =
  Environment.Objects.iter (fun _ _ -> ())
    (fun _ v -> match v with
       | {Environment.flavour=Environment.Inductive {Environment.table=table}}
       | {Environment.flavour=Environment.CoInductive {Environment.table=table}} ->
           Table.reset table
       | _ -> ())

let clear_table (p,head_tm) =
  get_table p head_tm (fun table _ -> Table.reset table)


(* Misc I/O *)

let print_env () =
  let print_types () =
    Format.printf "@[<v 3>*** Types ***" ;
    Environment.Types.iter
      (fun v k -> Format.printf "@,@[%s :@;<1 2>%a@]"
                    (Ndcore.Term.get_var_name v)
                    Kind.pp k) ;
    Format.printf "@]@."
  in
  let lc,lp =
    Environment.Objects.fold
      (fun k ty (lc,lp) ->
         (Ndcore.Term.get_var_name k,ty)::lc,lp)
      (fun k {Environment.flavour=f;ty=ty} (lc,lp) ->
         lc,(Ndcore.Term.get_var_name k,f,ty)::lp)
      ([],[])
  in
  let print_constants () =
    Format.printf "@[<v 3>*** Constants ***" ;
    List.iter
      (fun (n,ty) -> Format.printf "@,@[%s :@;<1 2>%a@]" n Type.pp ty)
      (List.sort (fun (x,_) (y,_) -> compare x y) lc) ;
    Format.printf "@]@."
  in
  let print_predicates () =
    let string_of_flavour = function
      | Environment.Normal -> "  "
      | Environment.Inductive _ -> "I "
      | Environment.CoInductive _ -> "C "
    in
    Format.printf "@[<v 1>*** Predicates ***" ;
    List.iter
      (fun (n,f,ty) -> Format.printf "@,@[%s%s :@;<1 4>%a@]"
                         (string_of_flavour f) n Type.pp ty)
      (List.sort (fun (x,_,_) (y,_,_) -> compare x y) lp) ;
    Format.printf "@]@."
  in
  print_types () ;
  print_constants () ;
  print_predicates ()

let print_type_of pre_term ~k =
  match Environment.translate_term pre_term ~k with
    | Some (ty,free_types,(_,t)) ->
        let pp_type = Type.get_pp () in
        Format.printf "@[<v 3>@[%a :@;<1 2>%a@]"
          Ndcore.Pprint.pp_term t
          pp_type ty ;
        let vars =
          Hashtbl.fold
            (fun v (ty,_) accum -> (Ndcore.Term.get_var_name v,ty)::accum)
            free_types
            []
        in
        List.iter
          (fun (n,ty) ->
             Format.printf "@,@[%s :@;<1 2>%a@]"
               n pp_type ty)
          (List.sort (fun (s1,_) (s2,_) -> compare s1 s2) vars) ;
        Format.printf "@]@." ;
        Some ()
    | None -> None

let show_def (p,head_tm) =
  get_def p head_tm
    (fun body _ -> Format.printf "%a@." Ndcore.Pprint.pp_term body)

let show_table (p,head_tm) =
  get_table p head_tm (fun table _ -> Table.print head_tm table)

let save_table (p,head_tm) name file =
  let aux channel =
    get_table p head_tm
      (fun table ty ->
         Table.fprint channel head_tm table ty)
  in
  IO.Files.run_out aux file

exception Uncleared_tables

let export file =
  if !clean_tables then begin
    let all_tables =
      Environment.(Objects.fold (fun _ _ l -> l)
                     (fun k v l -> match v with
                        | {flavour=Inductive {table=table}}
                        | {flavour=CoInductive {table=table}} ->
                            Ndcore.Term.(atom (get_var_name k),table) :: l
                        | _ -> l))
                     []
    in
    !Table.xml_export file all_tables !root_atoms
  end else raise Uncleared_tables

let translate_term pre_term ~k =
  (* TODO use the cert type here? *)
  match Environment.translate_term pre_term ~k with
    | Some (_,_,(_,term)) -> Some term
    | None -> None

let deactivated = ref false

let deactivate_io () =
  deactivated := true

let reactivate_io () =
  deactivated := false

(* Input predicates (stdin and file) *)

let read read_fun goals =
  if !deactivated then None
  else match goals with
    | [pattern] ->
        begin match read_fun () with
          | Some term -> Some (Ndcore.Term.op_eq pattern term)
          | None -> None
        end
    | _ -> assert false

let fopen_in goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.I.get name with
                | Some _ -> false
                | None -> IO.Files.I.add name ; true
              end
          | _ -> false
        end
    | _ -> assert false

let fread read_fun goals =
  if !deactivated then None
  else match goals with
    | [f;pattern] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.I.get name with
                | Some (_,l) ->
                    begin match read_fun l () with
                      | Some term -> Some (Ndcore.Term.op_eq pattern term)
                      | None -> None
                    end
                | None -> None
              end
          | _ -> None
        end
    | _ -> assert false

let fclose_in goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.I.get name with
                | Some (c,_) -> IO.Files.I.remove name c ; true
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false

(* Output predicates (stdout and file) *)

let print print_fun goals =
  if !deactivated then true
  else match goals with
    | [f] -> print_fun f
    | _ -> assert false

let fopen_out goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.O.get name with
                | Some _ -> false
                | None -> IO.Files.O.add name ; true
              end
          | _ -> false
        end
    | _ -> assert false

let fprint print_fun goals =
  if !deactivated then true
  else match goals with
    | [f;g] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.O.get name with
                | Some (_,f) -> print_fun f g
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false

let fclose_out goals =
  if !deactivated then true
  else match goals with
    | [f] ->
        begin match Ndcore.Term.observe f with
          | Ndcore.Term.QString name ->
              begin match IO.Files.O.get name with
                | Some (c,_) -> IO.Files.O.remove name c ; true
                | None -> false
              end
          | _ -> false
        end
    | _ -> assert false


(* Misc *)

exception Interrupt
exception Abort_search
exception Assertion_failed
exception Invalid_command


let get_reset () =
  let types_state = Environment.Types.save_state ()
  and objects_state = Environment.Objects.save_state ()
  and includedfiles_state = Environment.IncludedFiles.save_state () in
  fun () ->
    Environment.Types.restore_state types_state ;
    Environment.Objects.restore_state objects_state ;
    Environment.IncludedFiles.restore_state includedfiles_state

let reset () =
  Environment.Types.clear () ;
  Environment.Objects.clear () ;
  Environment.IncludedFiles.clear () ;
  Type.Unifier.clear ()

(* Handle user interruptions *)
let interrupt = ref false
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; true ) else false

let sanitize f clean =
  try f () ; clean ()
  with e -> clean () ; raise e

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

let initial_test_limit  = ref (Some 0)

let incr_test_limit () =
  initial_test_limit := match !initial_test_limit with
    | Some n -> Some (n+1)
    | None -> None
let remove_test_limit () =
  initial_test_limit := None

let session     = ref []
let definitions = ref []
let queries     = ref []
