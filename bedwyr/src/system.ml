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
  let not     = Term.atom ~tag:Term.Constant "_not"
  let ite     = Term.atom ~tag:Term.Constant "_if"
  let abspred = Term.atom ~tag:Term.Constant "_abstract"
  let distinct = Term.atom ~tag:Term.Constant "_distinct"
  let assert_rigid   = Term.atom ~tag:Term.Constant "_rigid"
  let abort_search = Term.atom ~tag:Term.Constant "_abort"
  let cutpred = Term.atom ~tag:Term.Constant "_cut"
  let check_eqvt = Term.atom ~tag:Term.Constant "_eqvt"

  let print   = Term.atom ~tag:Term.Constant "print"
  let println = Term.atom ~tag:Term.Constant "println"
  let fprint  = Term.atom ~tag:Term.Constant "fprint"
  let fprintln = Term.atom ~tag:Term.Constant "fprintln"
  let fopen_out = Term.atom ~tag:Term.Constant "fopen_out"
  let fclose_out = Term.atom ~tag:Term.Constant "fclose_out"
  let parse   = Term.atom ~tag:Term.Constant "parse"
  let simp_parse = Term.atom ~tag:Term.Constant "simp_parse"


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
end

type flavour = Normal | Inductive | CoInductive

type input =
  | KKind   of (Typing.pos * string) list * Type.simple_kind
  | TType   of (Typing.pos * string) list * Type.simple_type
  | Def     of (flavour * Typing.pos * string * Type.simple_type) list *
               (Typing.pos * Typing.term' * Typing.term') list
  | Query   of Typing.term'
  | Command of command
and command =
  | Exit
  | Help
  | Include             of string list
  | Reset
  | Reload
  | Session             of string list
  | Debug               of string option
  | Time                of string option
  | Equivariant         of string option
  | Show_table          of string
  | Clear_tables
  | Clear_table         of string
  | Save_table          of string * string
  | Assert              of Typing.term'
  | Assert_not          of Typing.term'
  | Assert_raise        of Typing.term'

(** A simple debug flag, which can be set dynamically from the logic program. *)

let debug = ref false
let time  = ref false

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


(** types declarations *)

exception Invalid_type_declaration of string * Typing.pos * Type.simple_kind * string


let type_kinds : (Term.var,Type.simple_kind) Hashtbl.t =
  Hashtbl.create 100

let declare_type (p,name) ki =
  assert (name <> "");
  match ki with
    | Type.KType ->
        let ty_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
        if Hashtbl.mem type_kinds ty_var
        then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
        else Hashtbl.add type_kinds ty_var ki
    | Type.KRArrow _ ->
        raise (Invalid_type_declaration (name,p,ki,"no type operators yet"))


(** constants and predicates declarations *)

exception Invalid_const_declaration of string * Typing.pos * Type.simple_type * string
exception Invalid_pred_declaration of string * Typing.pos * Type.simple_type * string


(* XXX all kind are assumed to be "*", so no real check is done here *)
let kind_check ~pred (name,p) ty =
  let rec aux is_target = function
    | Type.Ty name' as ty' ->
        assert (name' <> "");
        let type_var = Term.get_var (Term.atom ~tag:Term.Constant name') in
        if not (Hashtbl.mem type_kinds type_var) then
          if pred
          then raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "type %s was not declared" (Pprint.type_to_string None ty')))
          else raise (Invalid_const_declaration (name,p,ty,Format.sprintf "type %s was not declared" (Pprint.type_to_string None ty')))
        else if pred && is_target then
          raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "target type can only be %s" (Pprint.type_to_string None Type.TProp)))
        else true
    | Type.TProp ->
        if pred
        then is_target || raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "%s can only be a target type" (Pprint.type_to_string None Type.TProp)))
        else raise (Invalid_const_declaration (name,p,ty,Format.sprintf "%s can only be a target type for a predicate" (Pprint.type_to_string None Type.TProp)))
    | Type.TRArrow (tys,ty) -> List.for_all (aux false) tys && aux true ty
    | Type.TVar _ ->
        if pred
        then raise (Invalid_pred_declaration (name,p,ty,"no type variables yet"))
        else raise (Invalid_const_declaration (name,p,ty,"no type variables yet"))
  in
  aux true ty

let const_types : (Term.var,Type.simple_type) Hashtbl.t =
  Hashtbl.create 100

let defs : (Term.var,(flavour*Term.term option*Table.t option*Type.simple_type)) Hashtbl.t =
    Hashtbl.create 100

let declare_const (p,name) ty =
  assert (name <> "");
  let const_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem const_types const_var
  then raise (Invalid_const_declaration (name,p,ty,"constant already declared"))
  else if Hashtbl.mem defs const_var
  then raise (Invalid_const_declaration (name,p,ty,"name conflict with a declared predicate"))
  else if kind_check ~pred:false (name,p) ty
  then Hashtbl.add const_types const_var ty
  else raise (Invalid_const_declaration (name,p,ty,Format.sprintf "type is not of kind %s" (Pprint.kind_to_string Type.KType)))

let create_def (flavour,p,name,ty) =
  let head_tm = Term.atom ~tag:Term.Constant name in
  let head_var = Term.get_var head_tm in
  if Hashtbl.mem defs head_var
  then raise (Invalid_pred_declaration (name,p,ty,"predicate already declared"))
  else if Hashtbl.mem const_types head_var
  then raise (Invalid_pred_declaration (name,p,ty,"name conflict with a declared constant"))
  else if kind_check ~pred:true (name,p) ty
  then begin
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
    let t = (if flavour=Normal then None else Some (Table.create ())) in
    Hashtbl.add defs head_var (flavour, None, t, ty) ;
    head_var
  end else raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "type is not of kind %s" (Pprint.kind_to_string Type.KType)))


(** typechecking, predicates definitions *)

exception Missing_declaration of string
exception Inconsistent_definition of string * Typing.pos * string


let type_of_var (v,term) = match v with
  (* XXX ? *)
  (*| v when v = Logic.var_not
  | v when v = Logic.var_ite
  | v when v = Logic.var_abspred
  | v when v = Logic.var_distinct
  | v when v = Logic.var_assert_rigid
  | v when v = Logic.var_abort_search
  | v when v = Logic.var_cutpred
  | v when v = Logic.var_check_eqvt ->
      raise (Typing_error (TProp,TProp,unifier))*)
  | v when v = Logic.var_print ->
      let ty = Type.fresh_tyvar () in
      Type.TRArrow ([ty],Type.TProp)
  (*| v when v = Logic.var_println
  | v when v = Logic.var_fprint
  | v when v = Logic.var_fprintln
  | v when v = Logic.var_fopen_out
  | v when v = Logic.var_fclose_out
  | v when v = Logic.var_parse
  | v when v = Logic.var_simp_parse ->
      raise (Typing_error (TProp,TProp,unifier))*)
  | _ ->
      try let _,_,_,ty = Hashtbl.find defs v in ty
      with Not_found ->
        try Hashtbl.find const_types v
        with
          | Not_found ->
              let name = Term.get_name term in
              raise (Missing_declaration (name))

(* TODO try to include vars in type_of_var (eg create a fresh type for each),
 * and avoid this unnecessary existentially closure *)
let type_check_term ?vars term ty =
  let term = match vars with
    | None -> term
    | Some vars -> term
  in
  Typing.global_unifier := Typing.type_check_term term ty !Typing.global_unifier type_of_var

let type_check_clause arity body' ty =
  let body = Typing.translate body' in
  type_check_term (Term.lambda arity body) ty ;
  body

let type_check_query query' =
  let query = Typing.translate query' in
  type_check_term ~vars:(Term.logic_vars [query]) query Type.TProp ;
  query

let add_clause new_predicates (p,head_tm',body') =
  (* TODO
   * call Typing.mkdef,
   * raise an esception if head_tm' is invalid,
   * typecheck
   *)
  let ty = Type.TProp in
  let arity = 42 in

  let head_tm = type_check_query head_tm' in
  let body = type_check_clause arity body' ty in

  let head_var = Term.get_var head_tm in
  let name = Term.get_name head_tm in
  let f,b,t,ty =
    try Hashtbl.find defs head_var
    with Not_found -> raise (Inconsistent_definition (name,p,"predicate was not declared"))
  in
  if List.mem head_var new_predicates then begin
    let b =
      match b with
        | None -> Term.lambda arity body
        | Some b ->
            begin match Term.observe b with
              | Term.Lam (a,b) when arity=a ->
                  Term.lambda a (Term.op_or b body)
              | _ when arity=0 ->
                  Term.op_or b body
              | _ -> raise (Inconsistent_definition (name,p,Format.sprintf "predicate is not of arity %d" arity))
            end
    in
    let b = Norm.hnorm b in
    Hashtbl.replace defs head_var (f,Some b,t,ty) ;
    if !debug then
      Format.eprintf "%a := %a\n" Pprint.pp_term head_tm Pprint.pp_term body
  end else raise (Inconsistent_definition (name,p,"predicate declared in another block"))


(** using definitions *)

exception Arity_mismatch of Term.term * int


let reset_defs () = Hashtbl.clear defs

let get_def ?check_arity head_tm =
  let head_var = Term.get_var head_tm in
  try
    let k,b,t,st = Hashtbl.find defs head_var in
      match check_arity,b with
        | None,None | Some 0,None -> k,Term.op_false,t,st
        | Some a,None -> raise (Arity_mismatch (head_tm,a))
        | None,Some b | Some 0,Some b -> k,b,t,st
        | Some a,Some b ->
            begin match Term.observe b with
              | Term.Lam (n,_) when n=a -> k,b,t,st
              | _ -> raise (Arity_mismatch (head_tm,a))
            end
  with
    | Not_found ->
        let name = Term.get_name head_tm in
        raise (Missing_declaration (name))

let remove_def head_tm =
  let head_var = Term.get_var head_tm in
  Hashtbl.remove defs head_var

let show_table head_tm =
  try
    let _,_,table,_ = Hashtbl.find defs (Term.get_var head_tm) in
      match table with
        | Some table -> Table.print head_tm table
        | None ->
            failwith (Format.sprintf "No table defined for %s." (Pprint.term_to_string head_tm))
  with
    | Not_found ->
        let name = Term.get_name head_tm in
        raise (Missing_declaration (name))

let save_table head_tm file =
  try
    let fout = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o600 file in
    try
      let _,_,table,_ = Hashtbl.find defs (Term.get_var head_tm) in
      begin match table with
        | Some table -> Table.fprint fout head_tm table
        | None ->
            failwith (Format.sprintf "No table defined for %s." (Pprint.term_to_string head_tm))
      end ;
      close_out fout
    with
      | Not_found ->
          begin
            close_out fout ;
            let name = Term.get_name head_tm in
            raise (Missing_declaration (name))
          end
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
