(****************************************************************************)
(* Bedwyr -- base functions                                                 *)
(* Copyright (C) 2005-2015 Baelde, Tiu, Ziegler, Heath                      *)
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

module Ty = Preterm.Typing
module T = Table.O

let read_term = ref (fun () -> None)
let fread_term = ref (fun _ () -> None)
let time  = ref false
let root_atoms = ref []
let use_filter = ref false
let clean_tables = ref true



(* Clauses and queries construction *)


let translate_query pre_term ~k lexbuf =
  match Environment.translate_term ~expected_type:Ty.tprop pre_term ~k lexbuf with
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
         match Term.observe p with
           | Term.Var {Term.tag=Term.Logic}
               when List.for_all (fun v -> v!=p) new_params ->
               p::new_params,prologue
           | _  ->
               let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
               (v::new_params,(Term.op_eq v p)::prologue))
      ([],[])
      params
  in
  (* new_params [V;U;X]
   * prologue   [V=(f X Y);U=X]
   * Add prologue to the body *)
  let body = if prologue = [] then body else
    List.fold_left
      (fun acc term -> Term.op_and term acc)
      body
      prologue
  in
  (* body       U=X /\ (V=(f X Y) /\ (g X Y Z))
   * Quantify existentially over the initial free variables. *)
  let body =
    List.fold_left
      (fun body v ->
         if List.exists (Term.eq v) new_params then body
         else Term.quantify Term.Exists v body)
      body
      (* XXX in case [body] wasn't created by [translate_term],
       * we should depend on the level to look for instantiable variables,
       * ie not always Logic ones (cf [translate_term]) *)
      (Term.logic_vars [body])
  in
  Output.dprintf "%a := %a"
    Pprint.pp_term (Term.app pred (List.rev new_params))
    Pprint.pp_term body ;
  (* body       Exists\\ U=X /\ (V=(f X #1) /\ (g X #1 #2))
   * Finally, abstract over parameters *)
  let arity,body =
    if new_params = [] then 0,body else
      let body =
        List.fold_left (fun body v -> Term.abstract v body)
          body
          new_params
      in match Term.observe body with
        | Term.Lam (n,b) -> n,b
        | _ -> assert false
  in
  (* pred       d
   * arity      3
   * body       Exists\\ #4=#5 /\ (#3=(f #5 #1) /\ (g #5 #1 #2)) *)
  (pred, arity, body)


(* Predicates definitions *)

exception Inconsistent_definition of string * Preterm.Pos.t * string


let mk_def_clause p head body =
  let pred,params = match Term.observe head with
    | Term.Var ({Term.tag=Term.Constant}) -> head,[]
    | Term.App (pred,params) -> pred,params
    | _ -> raise (Inconsistent_definition
                    ("some predicate",p,"head term structure incorrect"))
  in
  mk_clause pred params body

(* returns the list of singleton variables of the clause *)
let add_def_clause stratum (p,pre_head,pre_body) ~k lexbuf =
  let free_args = Preterm.free_args pre_head in
  (* XXX what about stratum in theorems? *)
  match
    Environment.translate_term ~expected_type:Ty.tprop ~stratum ~free_args ~head:true
      pre_head ~k lexbuf
  with
    | Some (_,free_types,(_,head)) ->
        begin match
          Environment.translate_term ~expected_type:Ty.tprop ~stratum ~free_args
            ~free_types pre_body ~k lexbuf
        with
          | Some (_,_,(singletons,body)) ->
              begin
                let pred,arity,body =
                  mk_def_clause p head body
                in
                let head_var = Term.get_var pred in
                let name = Term.get_name pred in
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
                  match Term.observe definition with
                    | Term.Lam (a,b) when arity=a ->
                        Term.lambda a (Term.op_or b body)
                    | _ when arity=0 ->
                        Term.op_or definition body
                    | _ -> assert false
                in
                let def = Norm.hnorm def in
                x.Environment.definition <- def ;
                Some (List.rev singletons)
              end
          | None -> None
        end
    | None -> None

(* returns the list of singleton variables of the clause *)
let add_clauses stratum clauses ~k lexbuf =
  List.fold_left
    (fun accum clause ->
       match accum,(add_def_clause stratum clause ~k lexbuf) with
         | Some singletons,Some new_singletons ->
             Some (List.rev_append new_singletons singletons)
         | _,_ -> None)
    (Some []) clauses


(* Theorem definitions *)

exception Inconsistent_theorem of string * Preterm.Pos.t * string


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
        | n -> aux ((Term.fresh ~ts:0 ~lts:0 Term.Logic)::l) (n-1)
      in
      aux []
    in
    let split head = match Term.observe head with
      | Term.Var ({Term.tag=Term.Constant}) -> head,[]
      | Term.App (pred,params) -> pred,params
      | _ -> raise (Inconsistent_theorem
                      ("some predicate",p,"head term structure incorrect"))
    in
    (* [newl] is a list of deep-normed theorem clauses
     * [oldl] is a list of theorems built with theorem clauses, /\ and -> *)
    let rec aux newl = function
      | [] -> newl
      | (hypothesis,theorem)::oldl ->
          let theorem = Norm.hnorm theorem in
          begin match Term.observe theorem with
            | Term.Binop (Term.Arrow,body,head) ->
                let body = Norm.deep_norm body in
                let hypothesis = Term.op_and body hypothesis in
                aux newl ((hypothesis,head)::oldl)
            | Term.Binder (Term.Forall,n,t) ->
                let t = Term.lambda n t in
                aux newl ((hypothesis,Term.app t (vars n))::oldl)
            | Term.Binop (Term.And,t1,t2) ->
                aux newl ((hypothesis,t1)::(hypothesis,t2)::oldl)
            | _ ->
                let head = Norm.deep_norm theorem in
                let pred,params = split head in
                aux ((pred,params,hypothesis)::newl) oldl
          end
    in
    aux [] [Term.op_true,theorem]
  in
  List.rev_map
    (fun (pred,params,body) -> mk_clause pred params body)
    (clean_theorem theorem)

let add_theorem_clause p (pred,arity,body) =
  let head_var = Term.get_var pred in
  let name = Term.get_name pred in
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
          match Term.observe theorem with
            | Term.Lam (a,b) when arity=a ->
                Term.lambda a (Term.op_or b body)
            | _ when arity=0 ->
                Term.op_or theorem body
            | _ -> assert false
        in
        let th = Norm.hnorm th in
        x.Environment.theorem <- th

let add_theorem (p,n,pre_theorem) ~k lexbuf =
  match Environment.translate_term ~expected_type:Ty.tprop pre_theorem ~k lexbuf with
    | Some (_,_,(_,theorem)) ->
        let clauses = mk_theorem_clauses (p,n) theorem in
        List.iter (add_theorem_clause p) clauses ;
        Some ()
    | None -> None


(* Predicates accessors *)

exception Missing_definition of string * Preterm.Pos.t option
exception Missing_table of string * Preterm.Pos.t option


let get_name_pred ?pos head_tm =
  let head_var = Term.get_var head_tm in
  let name = Term.get_name head_tm in
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
           T.reset table
       | _ -> ())

let clear_table (p,head_tm) =
  get_table p head_tm (fun table _ -> T.reset table)


(* I/O *)

let print_env () =
  let print_types () =
    Format.printf "@[<v 3>*** Types ***" ;
    Environment.Types.iter
      (fun v k -> Format.printf "@,@[%s :@;<1 2>%a@]"
                    (Term.get_var_name v)
                    Ty.pp_kind k) ;
    Format.printf "@]@."
  in
  let lc,lp =
    Environment.Objects.fold
      (fun k ty (lc,lp) ->
         (Term.get_var_name k,ty)::lc,lp)
      (fun k {Environment.flavour=f;ty=ty} (lc,lp) ->
         lc,(Term.get_var_name k,f,ty)::lp)
      ([],[])
  in
  let print_constants () =
    Format.printf "@[<v 3>*** Constants ***" ;
    List.iter
      (fun (n,ty) -> Format.printf "@,@[%s :@;<1 2>%a@]"
                       n
                       (Ty.get_pp_type ()) ty)
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
                         (string_of_flavour f)
                         n
                         (Ty.get_pp_type ()) ty)
      (List.sort (fun (x,_,_) (y,_,_) -> compare x y) lp) ;
    Format.printf "@]@."
  in
  print_types () ;
  print_constants () ;
  print_predicates ()

let print_type_of pre_term ~k lexbuf =
  match Environment.translate_term pre_term ~k lexbuf with
    | Some (ty,free_types,(_,t)) ->
        let pp_type = Ty.get_pp_type () in
        Format.printf "@[<v 3>@[%a :@;<1 2>%a@]"
          Pprint.pp_term t
          pp_type ty ;
        let vars =
          Hashtbl.fold
            (fun v (ty,_) accum -> (Term.get_var_name v,ty)::accum)
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
    (fun body _ -> Format.printf "%a@." Pprint.pp_term body)

let show_table (p,head_tm) =
  get_table p head_tm (fun table _ -> T.print head_tm table)

let save_table (p,head_tm) name file =
  let aux channel =
    get_table p head_tm
      (fun table ty ->
         T.fprint channel head_tm table ty)
  in
  IO.run_out aux file

let export file =
  let all_tables =
    Environment.Objects.fold (fun _ _ l -> l)
      (fun k v l -> match v with
         | {Environment.flavour=Environment.Inductive {Environment.table=table}}
         | {Environment.flavour=Environment.CoInductive {Environment.table=table}} ->
             (Term.atom (Term.get_var_name k),table) :: l
         | _ -> l)
      []
  in
  T.export file all_tables !root_atoms

let translate_term pre_term ~k lexbuf =
  (* TODO use the cert type here? *)
  match Environment.translate_term pre_term ~k lexbuf with
    | Some (_,_,(_,term)) -> Some term
    | None -> None


(* Misc *)

exception Interrupt
exception Abort_search


let reset_decls () =
  Environment.Types.clear () ;
  Environment.Objects.clear ()

(* Handle user interruptions *)
let interrupt = ref false
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; true ) else false

let sanitize f clean =
  try f () ; clean ()
  with e -> clean () ; raise e
