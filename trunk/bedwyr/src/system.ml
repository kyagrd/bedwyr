(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2012 Baelde, Tiu, Ziegler, Heath                      *)
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
  let not               = Term.atom ~tag:Term.Constant "_not"
  let ite               = Term.atom ~tag:Term.Constant "_if"
  let abspred           = Term.atom ~tag:Term.Constant "_abstract"
  let distinct          = Term.atom ~tag:Term.Constant "_distinct"
  let assert_rigid      = Term.atom ~tag:Term.Constant "_rigid"
  let abort_search      = Term.atom ~tag:Term.Constant "_abort"
  let cutpred           = Term.atom ~tag:Term.Constant "_cut"
  let check_eqvt        = Term.atom ~tag:Term.Constant "_eqvt"

  let print             = Term.atom ~tag:Term.Constant "print"
  let println           = Term.atom ~tag:Term.Constant "println"
  (*let printty           = Term.atom ~tag:Term.Constant "printty"*)
  let fprint            = Term.atom ~tag:Term.Constant "fprint"
  let fprintln          = Term.atom ~tag:Term.Constant "fprintln"
  let fopen_out         = Term.atom ~tag:Term.Constant "fopen_out"
  let fclose_out        = Term.atom ~tag:Term.Constant "fclose_out"


  let var_not           = Term.get_var not
  let var_ite           = Term.get_var ite
  let var_abspred       = Term.get_var abspred
  let var_distinct      = Term.get_var distinct
  let var_assert_rigid  = Term.get_var assert_rigid
  let var_abort_search  = Term.get_var abort_search
  let var_cutpred       = Term.get_var cutpred
  let var_check_eqvt    = Term.get_var check_eqvt

  let var_print         = Term.get_var print
  let var_println       = Term.get_var println
  (*let var_printty       = Term.get_var printty*)
  let var_fprint        = Term.get_var fprint
  let var_fprintln      = Term.get_var fprintln
  let var_fopen_out     = Term.get_var fopen_out
  let var_fclose_out    = Term.get_var fclose_out
end

type flavour = Normal | Inductive | CoInductive
type command =
  | Exit
  | Help
  | Include             of string list
  | Reset
  | Reload
  | Session             of string list
  | Debug               of string option
  | Time                of string option
  | Equivariant         of string option
  | Env
  | Type_of             of Typing.preterm
  | Show_table          of Typing.pos * string
  | Clear_tables
  | Clear_table         of Typing.pos * string
  | Save_table          of Typing.pos * string * string
  | Assert              of Typing.preterm
  | Assert_not          of Typing.preterm
  | Assert_raise        of Typing.preterm

type input =
  | KKind   of (Typing.pos * string) list * Type.simple_kind
  | TType   of (Typing.pos * string) list * Type.simple_type
  | Def     of (flavour * Typing.pos * string * Type.simple_type) list *
               (Typing.pos * Typing.preterm * Typing.preterm) list
  | Query   of Typing.preterm
  | Command of command

let debug = ref false
let time  = ref false

(* list of open files *)
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


(* types declarations *)

exception Invalid_type_declaration of string * Typing.pos * Type.simple_kind * string


let type_kinds : (Term.var,Type.simple_kind) Hashtbl.t =
  Hashtbl.create 100

let declare_type (p,name) ki =
  let ty_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem type_kinds ty_var
  then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
  else match ki with
    | Type.KType ->
        Hashtbl.add type_kinds ty_var ki
    | Type.KRArrow _ ->
        raise (Invalid_type_declaration (name,p,ki,"no type operators yet"))


(* constants and predicates declarations *)

exception Missing_type of string * Typing.pos
exception Invalid_const_declaration of string * Typing.pos * Type.simple_type * string
exception Invalid_pred_declaration of string * Typing.pos * Type.simple_type * string
exception Invalid_bound_declaration of string * Typing.pos * Type.simple_type * string


let kind_check ?(expected_kind=Type.KType) ty =
  let kind (p,name) =
    let type_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    try Hashtbl.find type_kinds type_var
    with Not_found ->
      raise (Missing_type (name,p))
  in
  Typing.kind_check ty expected_kind kind

let const_types : (Term.var,Type.simple_type) Hashtbl.t =
  Hashtbl.create 100

let defs : (Term.var,(flavour*Term.term option*Table.t option*Type.simple_type)) Hashtbl.t =
    Hashtbl.create 100

let declare_const (p,name) ty =
  let const_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem const_types const_var
  then raise (Invalid_const_declaration (name,p,ty,"constant already declared"))
  else if Hashtbl.mem defs const_var
  then raise (Invalid_const_declaration (name,p,ty,"name conflict with a declared predicate"))
  else let _ = kind_check ty in
  Hashtbl.add const_types const_var ty

let create_def (flavour,p,name,ty) =
  let head_var = Term.get_var (Term.atom ~tag:Term.Constant name) in
  if Hashtbl.mem defs head_var
  then raise (Invalid_pred_declaration (name,p,ty,"predicate already declared"))
  else if Hashtbl.mem const_types head_var
  then raise (Invalid_pred_declaration (name,p,ty,"name conflict with a declared constant"))
  else let (_,_,_,propositional) = kind_check ty in
  if not propositional then
    raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "target type can only be %s" (Pprint.type_to_string Type.TProp)))
  else begin
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
  end


(* typechecking, predicates definitions *)

exception Missing_declaration of string * Typing.pos option
exception Inconsistent_definition of string * Typing.pos * string


let translate_term ?(infer=true) ?(expected_type=Type.TProp) pre_term free_types =
  (* return (and create if needed) a typed variable
   * corresponding to the name of a free variable *)
  let typed_free_var (_,name) =
    let was_free = Term.is_free name in
    let t = Term.atom ~tag:Term.Logic name in
    let v = Term.get_var t in
    try
      let ty = Hashtbl.find free_types v in
      t,ty
    with Not_found ->
      let t,v =
        if was_free then t,v else begin
          Term.free name ;
          let t = Term.atom ~tag:Term.Logic name in
          let v = Term.get_var t in
          t,v
        end
      in
      let ty = Type.fresh_tyvar () in
      Hashtbl.add free_types v ty ;
      t,ty
  in
  (* return a typed variable corresponding to the name
   * of a constant (predefined or not) or a predicate *)
  let typed_declared_var (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    try let _,_,_,ty = Hashtbl.find defs v in t,ty
    with Not_found ->
      try t,Hashtbl.find const_types v
      with Not_found ->
        let ty = match v with
          | v when v = Logic.var_print ->
              let ty = Type.fresh_tyvar () in
              Type.TRArrow ([ty],Type.TProp)
          | v when v = Logic.var_println ->
              let ty = Type.fresh_tyvar () in
              Type.TRArrow ([ty],Type.TProp)
          (*| v when v = Logic.var_printty ->
              let ty = Type.fresh_tyvar () in
              Type.TRArrow ([ty],Type.TProp)*)
          | v when v = Logic.var_fprint ->
              let ty = Type.fresh_tyvar () in
              Type.TRArrow ([Type.TString;ty],Type.TProp)
          | v when v = Logic.var_fprintln ->
              let ty = Type.fresh_tyvar () in
              Type.TRArrow ([Type.TString;ty],Type.TProp)
          | v when v = Logic.var_fopen_out ->
              Type.TRArrow ([Type.TString],Type.TProp)
          | v when v = Logic.var_fclose_out ->
              Type.TRArrow ([Type.TString],Type.TProp)
          | _ ->
              Term.free name ;
              raise (Missing_declaration (name,Some p))
        in t,ty
  in
  (* return a typed variable corresponding to the name
   * of an internal constant *)
  let typed_intern_var (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    let ty = match v with
      | v when v = Logic.var_not ->
          Type.TRArrow ([Type.TProp],Type.TProp)
      | v when v = Logic.var_ite ->
          Type.TRArrow ([Type.TProp;Type.TProp;Type.TProp],Type.TProp)
      | v when v = Logic.var_abspred ->
          let ty1 = Type.fresh_tyvar () in
          let ty2 = Type.TRArrow ([Type.TRArrow ([Type.fresh_tyvar ()],ty1)],ty1) in
          Type.TRArrow ([ty1;ty2;ty1],Type.TProp)
      | v when v = Logic.var_distinct ->
          Type.TRArrow ([Type.TProp],Type.TProp)
      | v when v = Logic.var_assert_rigid ->
          let ty = Type.fresh_tyvar () in
          Type.TRArrow ([ty],Type.TProp)
      | v when v = Logic.var_abort_search ->
          Type.TProp
      | v when v = Logic.var_cutpred ->
          Type.TRArrow ([Type.TProp],Type.TProp)
      | v when v = Logic.var_check_eqvt ->
          let ty = Type.fresh_tyvar () in
          Type.TRArrow ([ty;ty],Type.TProp)
      | _ ->
          Term.free name ;
          raise (Missing_declaration (name,Some p))
    in t,ty
  in
  (* return the type of the variable corresponding to an annotated ID *)
  let bound_var_type (p,name,ty) =
    let _ = kind_check ty in ty
  in
  Typing.type_check_and_translate pre_term expected_type typed_free_var typed_declared_var typed_intern_var bound_var_type infer

let translate_query pre_term =
  let free_types : (Term.var,Type.simple_type) Hashtbl.t =
    Hashtbl.create 10
  in
  let term,_ = translate_term pre_term free_types in term

let mk_clause p head body =
  (* Replace the params by fresh variables and
   * put the constraints on the parameters in the body:
   *     head          := body
   *     d X X (f X Y) := g X Y Z
   * --> d X U V       := (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
   * --> d X U V       := forall Z Y, (U = X) /\ ((V = (f X Y)) /\ (g X Y Z))
   * --> d == \\\ Exists\\ (4)=(5) /\ ((3)=(f (5) (1)) /\ (g (5) (1) (2)))
   *)
  let pred,params = match Term.observe head with
    | Term.Var ({Term.tag=Term.Constant}) -> head,[]
    | Term.App (pred,params) -> pred,params
    | _ -> raise (Inconsistent_definition ("an unknown predicate",p,"term structure incorrect"))
  in
  (* pred       pred
   * params     [X;X;(f X Y)]
   * Create the prolog (new equalities added to the body) and the new set
   * of variables used as parameters.
   * A parameter can be left untouched if it's a variable which didn't
   * occur yet. *)
  let new_params,prolog =
    List.fold_left
      (fun (new_params,prolog) p ->
         match Term.observe p with
           | Term.Var {Term.tag=Term.Logic}
               when List.for_all (fun v -> v!=p) new_params ->
               p::new_params,prolog
           | _  ->
               let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
               (v::new_params,(Term.op_eq v p)::prolog))
      ([],[])
      params
  in
  (* new_params [V;U;X]
   * prolog     [V=(f X Y);U=X]
   * Add prolog to the body *)
  let body = if prolog = [] then body else
    List.fold_left
      (fun acc term -> Term.op_and term acc)
      body
      prolog
  in
  (* body       U=X /\ (V=(f X Y) /\ (g X Y Z))
   * Quantify existentially over the initial free variables. *)
  let body =
    List.fold_left
      (fun body v ->
         if List.exists (Term.eq v) new_params then body
         else Term.quantify Term.Exists v body)
      body
      (Term.logic_vars [body])
  in
  if !debug then
    Format.eprintf "%a := %a@."
      Pprint.pp_term (Term.app pred (List.rev new_params))
      Pprint.pp_term body ;
  (* body       Exists\\ U=X /\ (V=(f X (1)) /\ (g X (1) (2)))
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
  (* pred       pred
   * arity      3
   * body       Exists\\ (4)=(5) /\ ((3)=(f (5) (1)) /\ (g (5) (1) (2))) *)
  (pred, arity, body)

let add_clause new_predicates (p,pre_head,pre_body) =
  let free_types : (Term.var,Type.simple_type) Hashtbl.t =
    Hashtbl.create 10
  in
  let head,_ = translate_term pre_head free_types in
  let body,_ = translate_term pre_body free_types in
  let head,arity,body =
    mk_clause p head body
  in
  let head_var = Term.get_var head in
  let name = Term.get_name head in
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
  end else raise (Inconsistent_definition (name,p,"predicate declared in another block"))


(* Using definitions *)

exception Arity_mismatch of Term.term * int


let reset_defs () = Hashtbl.clear defs

let get_def ~check_arity head_tm =
  let head_var = Term.get_var head_tm in
  try
    let k,b,t,st = Hashtbl.find defs head_var in
      match check_arity,b with
        (* XXX in the case of an empty definition (b = None),
         * we don't know the arity of the predicate,
         * so the actual value of the body returned should be
         * Lam (n,False) with an unknown n (actually, n may be known
         * via typechecking, but not with discretionary types and type
         * inference).
         * Therefore, so long as we allow empty definitions,
         * [check_arity] is made mandatory. *)
        | a,None -> k,Term.lambda a Term.op_false,t,st
        | 0,Some b->
            begin match Term.observe b with
              | Term.Lam (n,_) when n>0 ->
                  raise (Arity_mismatch (head_tm,0))
              | _ -> k,b,t,st
            end
        | a,Some b ->
            begin match Term.observe b with
              | Term.Lam (n,_) when n=a -> k,b,t,st
              | _ -> raise (Arity_mismatch (head_tm,a))
            end
  with
    | Not_found ->
        let name = Term.get_name head_tm in
        raise (Missing_declaration (name,None))

let remove_def head_tm =
  let head_var = Term.get_var head_tm in
  Hashtbl.remove defs head_var

let print_env () =
  let print_types () =
    Format.printf "@[<v 3>*** Types ***" ;
    Hashtbl.iter
      (fun v k -> Format.printf "@,@[%s :@;<1 2>%a@]"
                    (Term.get_var_name v)
                    Pprint.pp_kind k)
      type_kinds ;
    Format.printf "@]@."
  in
  let print_constants () =
    Format.printf "@[<v 3>*** Constants ***" ;
    Hashtbl.iter
      (fun v t -> Format.printf "@,@[%s :@;<1 2>%a@]"
                    (Term.get_var_name v)
                    (Pprint.pp_type_norm None) t)
      const_types ;
    Format.printf "@]@."
  in
  let print_predicates () =
    let string_of_flavour = function
      | Normal -> "  "
      | Inductive -> "I "
      | CoInductive -> "C "
    in
    Format.printf "@[<v 1>*** Predicates ***" ;
    Hashtbl.iter
      (fun v (f,_,_,ty) -> Format.printf "@,@[%s%s :@;<1 2>%a@]"
                            (string_of_flavour f)
                            (Term.get_var_name v)
                            (Pprint.pp_type_norm None) ty)
      defs  ;
    Format.printf "@]@."
  in
  print_types () ;
  print_constants ();
  print_predicates ()

let get_types pre_term =
  let free_types : (Term.var,Type.simple_type) Hashtbl.t =
    Hashtbl.create 10
  in
  let ty = Type.fresh_tyvar () in
  let _,ty = translate_term ~infer:false ~expected_type:ty pre_term free_types in
  ty

let print_type_of pre_term =
  let ty = get_types pre_term in
  Format.printf "%a@."
    Pprint.pp_type ty
  (*Pprint.pp_type Format.std_formatter ty*)

let show_table (p,head_tm) =
  try
    let _,_,table,_ = Hashtbl.find defs (Term.get_var head_tm) in
      match table with
        | Some table -> Table.print head_tm table
        | None ->
            failwith (Format.sprintf "No table defined for %s." (Pprint.term_to_string head_tm))
  with
    | Not_found ->
        let name = Term.get_name head_tm in
        raise (Missing_declaration (name,Some p))

let clear_tables () =
  Hashtbl.iter
    (fun _ v -> match v with
       | _,_,Some t,_ -> Table.reset t
       | _ -> ())
    defs

let clear_table (p,head_tm) =
  try
    let _,_,table,_ = Hashtbl.find defs (Term.get_var head_tm) in
      match table with
        | Some table -> Table.reset table
        | None ->
            failwith (Format.sprintf "No table defined for %s." (Pprint.term_to_string head_tm))
  with
    | Not_found ->
        let name = Term.get_name head_tm in
        raise (Missing_declaration (name,Some p))

let save_table (p,head_tm) file =
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
            raise (Missing_declaration (name,Some p))
          end
  with
    | Sys_error e ->
       Printf.printf "Couldn't open file %s for writing! Make sure that the file doesn't already exist.\n" file


(* Handle user interruptions *)

let interrupt = ref false
exception Interrupt
let _ =
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> interrupt := true))
let check_interrupt () =
  if !interrupt then ( interrupt := false ; true ) else false
