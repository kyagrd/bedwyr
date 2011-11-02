(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
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

module Logic =
struct
  let eq      = Term.atom "="
  let andc    = Term.atom "/\\"
  let orc     = Term.atom "\\/"
  let imp     = Term.atom "=>"
  let truth   = Term.atom "true"
  let falsity = Term.atom "false"
  let forall  = Term.atom "forall"
  let exists  = Term.atom "exists"
  let nabla   = Term.atom "nabla"

  let not     = Term.atom "_not"
  let ite     = Term.atom "_if"
  let abspred = Term.atom "_abstract"
  let distinct = Term.atom "_distinct"
  let assert_rigid   = Term.atom "_rigid"
  let abort_search = Term.atom "_abort"
  let cutpred = Term.atom "_cut"
  let check_eqvt = Term.atom "_eqvt"

  let print   = Term.atom "print"
  let println = Term.atom "println"
  let fprint  = Term.atom "fprint"
  let fprintln = Term.atom "fprintln"
  let fopen_out = Term.atom "fopen_out"
  let fclose_out = Term.atom "fclose_out"
  let parse   = Term.atom "parse"
  let simp_parse = Term.atom "simp_parse"
  let on      = Term.atom "on"
  let off     = Term.atom "off"


  let var_eq      = Term.get_var eq
  let var_andc    = Term.get_var andc
  let var_orc     = Term.get_var orc
  let var_imp     = Term.get_var imp
  let var_truth   = Term.get_var truth
  let var_falsity = Term.get_var falsity
  let var_forall  = Term.get_var forall
  let var_exists  = Term.get_var exists
  let var_nabla   = Term.get_var nabla
  let var_not     = Term.get_var not
  let var_ite     = Term.get_var ite
  let var_abspred = Term.get_var abspred
  let var_distinct = Term.get_var distinct
  let var_assert_rigid = Term.get_var assert_rigid
  let var_abort_search = Term.get_var abort_search
  let var_cutpred = Term.get_var cutpred
  let var_check_eqvt = Term.get_var check_eqvt

  let var_print   = Term.get_var print
  let var_println  = Term.get_var println
  let var_fprint  = Term.get_var fprint
  let var_fprintln = Term.get_var fprintln
  let var_fopen_out = Term.get_var fopen_out
  let var_fclose_out = Term.get_var fclose_out
  let var_parse   = Term.get_var parse
  let var_simp_parse = Term.get_var simp_parse
  let var_on      = Term.get_var on
  let var_off     = Term.get_var off


  let _ =
    Pprint.set_infix [ ("=",  Pprint.Nonassoc) ;
                       ("/\\",  Pprint.Both) ;
                       ("\\/",  Pprint.Both) ;
                       ("=>", Pprint.Right) ;
                       ("->", Pprint.Right) ;
                       ("<-", Pprint.Left) ;
                       ("+",  Pprint.Both) ;
                       ("-",  Pprint.Left) ;
                       ("*",  Pprint.Both) ]
end

type defkind = Normal | Inductive | CoInductive

type input =
  | Kind    of string list * Type.simple_kind
  | Type    of string list * Type.simple_type
  | Typing  of defkind * Term.term * Type.simple_type option
  | Def     of Term.term * int * Term.term
  | Query   of Term.term
  | Command of string * Term.term list

(** A simple debug flag, which can be set dynamically from the logic program. *)

let debug = ref false
let time  = ref false
let typed = ref true

(* [AT:] list of open files *)

let user_files : (string, out_channel) Hashtbl.t =
  Hashtbl.create 50

let reset_user_files () = Hashtbl.clear user_files

let close_all_files () =
  Hashtbl.iter
    (fun n c ->
       try close_out c with | Sys_error e -> () )
    user_files ;
  reset_user_files ()

let close_user_file name =
  try
    let f = Hashtbl.find user_files name in
      close_out f ;
      Hashtbl.remove user_files name
  with
  | Sys_error e -> Hashtbl.remove user_files name
  | _ -> ()

let get_user_file name =
  Hashtbl.find user_files name

let open_user_file name =
  try
    Hashtbl.find user_files name
  with
  | Not_found ->
    (
      let fout = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 name in
          ignore (Hashtbl.add user_files name fout) ;
          fout
    )


(** Kind and type declaration *)

exception Forbidden_kind of Type.simple_kind * string
exception Multiple_type_declaration of string * string
(*exception Missing_type_declaration of string
 * TODO add in const_define_type and create_def*)
(*exception Forbidden_type of Type.simple_type * string
 * TODO add in const_define_type and create_def*)
exception Multiple_const_declaration of string * string
exception Missing_declaration of Term.term * (Term.term * Term.term) option


let type_kinds : (Term.var,Type.simple_kind) Hashtbl.t =
  Hashtbl.create 100

let type_define_kind name kind =
  let stype_var = Term.get_var (Term.atom name) in
  if Hashtbl.mem type_kinds stype_var
  then raise (Multiple_type_declaration (name,""))
  else if name = "prop"
  then raise (Multiple_type_declaration (name," (built-in type)"))
  else begin
    assert (name <> "");
    Hashtbl.add type_kinds stype_var kind
  end

let const_types : (Term.var,Type.simple_type) Hashtbl.t =
  Hashtbl.create 100

let const_define_type name ty =
  (*let built_in const =
    false
  in*)
  let const_var = Term.get_var (Term.atom name) in
  if Hashtbl.mem const_types const_var
  then raise (Multiple_const_declaration (name,""))
  (*else if build_in_const name
  then raise (Multiple_const_declaration (name,", built-in const"))*)
  else begin
    assert (name <> "");
    Hashtbl.add const_types const_var ty
  end


(** Definitions *)

exception Multiple_pred_declaration of Term.term
exception Missing_pred_declaration of Term.term
exception Inconsistent_definition of Term.term
exception Term_typing_error of Type.simple_type * Type.simple_type * Type.simple_type Type.Unifier.t * Term.term * Type.simple_type list
exception Clause_typing_error of Type.simple_type * Type.simple_type * Type.simple_type Type.Unifier.t * Term.term * Type.simple_type list * Term.term
exception Arity_mismatch of Term.term*int
exception Missing_definition of Term.term


let defs : (Term.var,(defkind*Term.term option*Table.t option*Type.simple_type)) Hashtbl.t =
  Hashtbl.create 100

let type_of_var v =
  try
    let _,_,_,ty = Hashtbl.find defs v in Some ty
  with
    | Not_found ->
        begin try
          Some (Hashtbl.find const_types v)
        with
          | Not_found -> None
        end

let type_of_term t = match Term.observe t with
  | Term.Var v ->
        type_of_var v
  (* XXX this case is not used,
   * and would need some unification to make sense *)
  | _ -> Some (Type.fresh_type())

let rec type_check_term term expected_type unifier db_types =
  try
    match Term.observe term with
      | Term.Var v ->
          begin match v with
            (* connectives *)
            | v when v = Logic.var_eq ->
                let ty = Type.fresh_type() in
                let ty = Type.TRArrow ([ty;ty],Type.TProp) in
                Type.unify_constraint unifier expected_type ty
            | v when v = Logic.var_andc || v = Logic.var_orc || v = Logic.var_imp ->
                let ty = Type.TRArrow ([Type.TProp;Type.TProp],Type.TProp) in
                Type.unify_constraint unifier expected_type ty
            | v when v = Logic.var_truth || v = Logic.var_falsity ->
                Type.unify_constraint unifier expected_type Type.TProp
            | v when v = Logic.var_forall || v = Logic.var_exists || v = Logic.var_nabla ->
                let ty = Type.fresh_type() in
                let ty = Type.TRArrow ([ty],Type.TProp) in
                let ty = Type.TRArrow ([ty],Type.TProp) in
                Type.unify_constraint unifier expected_type ty
            (* ? *)
            (*| v when v = Logic.var_not
            | v when v = Logic.var_ite
            | v when v = Logic.var_abspred
            | v when v = Logic.var_distinct
            | v when v = Logic.var_assert_rigid
            | v when v = Logic.var_abort_search
            | v when v = Logic.var_cutpred
            | v when v = Logic.var_check_eqvt ->
                raise (Type.Typing_error (Type.TProp,Type.TProp,unifier))*)
            (* misc *)
            | {Term.tag=Term.String} ->
                unifier
            | v when v = Logic.var_print ->
                let ty = Type.fresh_type() in
                let ty = Type.TRArrow ([ty],Type.TProp) in
                Type.unify_constraint unifier expected_type ty
            (*| v when v = Logic.var_println
            | v when v = Logic.var_fprint
            | v when v = Logic.var_fprintln
            | v when v = Logic.var_fopen_out
            | v when v = Logic.var_fclose_out
            | v when v = Logic.var_parse
            | v when v = Logic.var_simp_parse
            | v when v = Logic.var_on
            | v when v = Logic.var_off ->
                raise (Type.Typing_error (Type.TProp,Type.TProp,unifier))*)
            | _ ->
                begin match type_of_term term with
                  | None ->
                      raise (Missing_declaration (term,None))
                  | Some ty ->
                      Type.unify_constraint unifier expected_type ty
                end
          end
      | Term.DB i ->
          let ty = List.nth db_types (i-1) in
          Type.unify_constraint unifier expected_type ty
      (*| Term.NB i, Ty (_) -> true*)
      | Term.Lam (a,term) ->
          let tys,ty = Type.build_abstraction_types a in
          let unifier = Type.unify_constraint unifier expected_type (Type.TRArrow (tys,ty)) in
          let db_types = List.rev_append tys db_types in
          type_check_term term ty unifier db_types
      | Term.App (h,l) ->
          let arity = List.length l in
          let tys,ty = Type.build_abstraction_types arity in
          let unifier = Type.unify_constraint unifier expected_type ty in
          let unifier = type_check_term h (Type.TRArrow (tys,ty)) unifier db_types in
          List.fold_left2
            (fun u t ty -> type_check_term t ty u db_types)
            unifier
            l
            tys
      (*| Term.Susp _, Ty (_) -> true*)
      | _ ->
          failwith "Type checking aborted, unsupported term."
  with
    | Type.Type_unification_error (ty1,ty2,unifier) ->
        raise (Term_typing_error (ty1,ty2,unifier,term,db_types))

let type_check_clause arity body stype unifier =
  type_check_term (Term.lambda arity body) stype unifier []

let reset_defs () = Hashtbl.clear defs

let create_def kind head_tm stype =
  let head = Term.get_var head_tm in
  if Hashtbl.mem defs head then
    raise (Multiple_pred_declaration head_tm);
  (* Cleanup all tables.
   * Cleaning only this definition's table is _not_ enough, since other
   * definitions may rely on it.
   * TODO: make it optional to speedup huge definitions ? *)
  Hashtbl.iter
    (fun k v ->
       match v with
         | _,_,Some t,_ -> Table.reset t
         | _ -> ())
    defs ;
  let t = (if kind=Normal then None else Some (Table.create ())) in
  let stype = match stype with Some stype -> stype | None -> Type.fresh_type () in
  Hashtbl.add defs head (kind, None, t, stype)

let add_clause head_tm arity body =
  let head = Term.get_var head_tm in
  let k,b,t,st =
    try
      Hashtbl.find defs head
    with
      | Not_found -> raise (Missing_pred_declaration head_tm)
  in
  let () =
    try
      if !typed then
        Type.global_unifier := type_check_clause arity body st !Type.global_unifier
    with
      | Term_typing_error (ty1,ty2,unifier,term,db_types) ->
          raise (Clause_typing_error (ty1,ty2,unifier,term,db_types,head_tm))
      | Missing_declaration (term,None) ->
          raise (Missing_declaration (term,Some (head_tm,body)))
  in
  let b =
    match b with
      | None -> Term.lambda arity body
      | Some b ->
          begin match Term.observe b with
            | Term.Lam (a,b) when arity=a ->
                Term.lambda a (Term.app Logic.orc [b;body])
            | _ when arity=0 ->
                Term.app Logic.orc [b;body]
            | _ -> raise (Inconsistent_definition head_tm)
          end
  in
  let b = Norm.hnorm b in
  Hashtbl.replace defs head (k, Some b, t, st) ;
  if !debug then
    Format.printf "%a := %a\n" Pprint.pp_term head_tm Pprint.pp_term body

let get_def ?check_arity head_tm =
  let head = Term.get_var head_tm in
  try
    let k,b,t,st = Hashtbl.find defs head in
      match check_arity,b with
        | None, Some b | Some 0, Some b -> k,b,t,st
        | Some a, Some b ->
            begin match Term.observe b with
              | Term.Lam (n,_) when n=a -> k,b,t,st
              | _ -> raise (Arity_mismatch (head_tm,a))
            end
        | _ -> raise (Missing_definition head_tm)
  with
    | Not_found -> raise (Missing_pred_declaration head_tm)

let remove_def head_tm =
  let head = Term.get_var head_tm in
  Hashtbl.remove defs head

let show_table head =
  try
    let _,_,table,_ = Hashtbl.find defs (Term.get_var head) in
      match table with
        | Some table -> Table.print head table
        | None ->
            failwith ("No table defined for " ^ (Pprint.term_to_string head))
  with
    | Not_found -> raise (Missing_pred_declaration head)

let save_table head file =
   try
     let fout = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 file in
     try
       let _,_,table,_ = Hashtbl.find defs (Term.get_var head) in
         begin match table with
          | Some table -> Table.fprint fout head table
          | None ->
             failwith ("No table defined for " ^ (Pprint.term_to_string head))
         end ; close_out fout
     with | Not_found -> close_out fout ; raise (Missing_pred_declaration head)
  with
    | Sys_error e ->
       Printf.printf "Couldn't open file %s for writing! Make sure that the file doesn't already exist.\n" file

(* Common utils *)

let rec make_list f = function
  | 0 -> []
  | n -> (f n)::(make_list f (n-1))

(* Handle user interruptions *)

let interrupt = ref false
exception Interrupt
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; true ) else false
