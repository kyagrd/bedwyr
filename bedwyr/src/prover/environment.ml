(****************************************************************************)
(* Bedwyr -- environment                                                    *)
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

(* TODO get the code from [Prover] here, so that internal/predefined
 * predicates are declared and defined in one single place
 * TODO add the word pervasive and remove some predecared/predefined *)
module Logic = struct
  let not               = Term.atom ~tag:Term.Constant "_not"
  let ite               = Term.atom ~tag:Term.Constant "_if"
  let abspred           = Term.atom ~tag:Term.Constant "_abstract"
  let distinct          = Term.atom ~tag:Term.Constant "_distinct"
  let assert_rigid      = Term.atom ~tag:Term.Constant "_rigid"
  let abort_search      = Term.atom ~tag:Term.Constant "_abort"
  let cutpred           = Term.atom ~tag:Term.Constant "_cut"
  let check_eqvt        = Term.atom ~tag:Term.Constant "_eqvt"

  let var_not           = Term.get_var not
  let var_ite           = Term.get_var ite
  let var_abspred       = Term.get_var abspred
  let var_distinct      = Term.get_var distinct
  let var_assert_rigid  = Term.get_var assert_rigid
  let var_abort_search  = Term.get_var abort_search
  let var_cutpred       = Term.get_var cutpred
  let var_check_eqvt    = Term.get_var check_eqvt

  let internal_t = Hashtbl.create 8
  let _ = Preterm.Typing.(List.iter
                            (fun (v,tys) -> Hashtbl.replace internal_t v (ty_arrow tys tprop))
                            [ (* Non-logical extensions *)
                              var_not,
                                [tprop] ;
                              var_ite,
                                [tprop;tprop;tprop] ;
                              var_abspred,
                                (let ty0 = tparam 0 in
                                 let ty1 = ty_arrow [ty_arrow [tparam 1] ty0] ty0 in
                                 [ty0;ty1;ty0]) ;
                              var_distinct,
                                [tprop] ;
                              var_assert_rigid,
                                [tparam 0] ;
                              var_abort_search,
                                [] ;
                              var_cutpred,
                                [tprop] ;
                              var_check_eqvt,
                                (let ty = tparam 0 in
                                 [ty;ty] ) ;
                            ])

  let get_internal_type v =
    Hashtbl.find internal_t v


  let read              = Term.atom ~tag:Term.Constant "read"
  let fread             = Term.atom ~tag:Term.Constant "fread"
  let fopen_in          = Term.atom ~tag:Term.Constant "fopen_in"
  let fclose_in         = Term.atom ~tag:Term.Constant "fclose_in"
  let print             = Term.atom ~tag:Term.Constant "print"
  let println           = Term.atom ~tag:Term.Constant "println"
  let printstr          = Term.atom ~tag:Term.Constant "printstr"
  let fprint            = Term.atom ~tag:Term.Constant "fprint"
  let fprintln          = Term.atom ~tag:Term.Constant "fprintln"
  let fprintstr         = Term.atom ~tag:Term.Constant "fprintstr"
  let fopen_out         = Term.atom ~tag:Term.Constant "fopen_out"
  let fclose_out        = Term.atom ~tag:Term.Constant "fclose_out"

  let var_read          = Term.get_var read
  let var_fread         = Term.get_var fread
  let var_fopen_in      = Term.get_var fopen_in
  let var_fclose_in     = Term.get_var fclose_in
  let var_print         = Term.get_var print
  let var_println       = Term.get_var println
  let var_printstr      = Term.get_var printstr
  let var_fprint        = Term.get_var fprint
  let var_fprintln      = Term.get_var fprintln
  let var_fprintstr     = Term.get_var fprintstr
  let var_fopen_out     = Term.get_var fopen_out
  let var_fclose_out    = Term.get_var fclose_out

  let builtins = Hashtbl.create 8
  let _ = Preterm.Typing.(List.iter
                            (fun (v,tys) -> Hashtbl.replace builtins v (ty_arrow tys tprop))
                            [ (* I/O extensions *)
                              var_read,       [tparam 0] ;
                              var_fread,      [tstring;tparam 0] ;
                              var_fopen_in,   [tstring] ;
                              var_fclose_in,  [tstring] ;
                              var_print,      [tparam 0] ;
                              var_println,    [tparam 0] ;
                              var_printstr,   [tstring] ;
                              var_fprint,     [tstring;tparam 0] ;
                              var_fprintln,   [tstring;tparam 0] ;
                              var_fprintstr,  [tstring;tstring] ;
                              var_fopen_out,  [tstring] ;
                              var_fclose_out, [tstring] ;
                            ])

  let get_builtin v =
    try Some (Hashtbl.find builtins v)
    with Not_found -> None
end


(** {6 Type declarations} *)
(* Types declarations *)

exception Invalid_type_declaration of string * Preterm.Pos.t * Preterm.Typing.ki * string
exception Missing_type of string * Preterm.Pos.t


module Types = struct
  let env : (Term.var,Preterm.Typing.ki) Hashtbl.t =
    Hashtbl.create 100

  let recent_keys = ref []

  let get_reset () =
    recent_keys := [] ;
    fun () ->
      List.iter
        (Hashtbl.remove env)
        !recent_keys ;
      recent_keys := []

  let declare (p,name) ki =
    let var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    if Hashtbl.mem env var
    then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
    else begin
      Hashtbl.replace env var ki ;
      recent_keys := var :: !recent_keys
    end

  let get_kind (p,name) =
    let var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    try Hashtbl.find env var
    with Not_found -> raise (Missing_type (name,p))

  let kind_check ~obj ~p ty =
    Preterm.Typing.kind_check ~obj ~p ty ~get_kind

  let iter f =
    Hashtbl.iter f env

  let clear () =
    Hashtbl.clear env
end

(** {6 ??} *)

exception Missing_declaration of string * Preterm.Pos.t
exception Stratification_error of string * Preterm.Pos.t

let catch ~k e =
  begin match e with
    (* Kind checking *)
    | Missing_type (n,p) ->
        Output.eprintf ~p
          "Undeclared type %s."
          n
    | Preterm.Typing.Type_kinding_error (n,p,ki1,ki2) ->
        Output.eprintf ~p
          "Kinding error: the type constructor %s has kind %a@ \
            but is used as %a."
          n
          Preterm.Typing.pp_kind ki2
          Preterm.Typing.pp_kind ki1

    (* Type checking *)
    | Missing_declaration (n,p) ->
        Output.eprintf ~p
          "Undeclared object %s."
          n
    | Preterm.Term_typing_error (p,ty1,ty2,unifier) ->
        let pp_type = Preterm.Typing.get_pp_type ~unifier () in
        Output.eprintf ~p
          "Typing error: this term has type %a but is used as %a."
          pp_type ty2
          pp_type ty1
    | Preterm.Typing.Type_order_error (n,p,ty) ->
        begin match n with
          | Some n ->
              Output.eprintf ~p
                "Typing error: cannot give free variable %s the type %a." n
                (Preterm.Typing.get_pp_type ()) ty
          | None ->
              Output.eprintf ~p
                "Typing error: cannot quantify over type %a."
                (Preterm.Typing.get_pp_type ()) ty
        end
    | e -> raise e
  end ;
  k ()

(** {6 Constants and predicates declarations} *)
(* Constants and predicates declarations *)

exception Invalid_declaration of
  string * string * Preterm.Pos.t * Preterm.Typing.ty * string * Preterm.Typing.ty
exception Invalid_flavour of
  string * Preterm.Pos.t * Preterm.flavour * Preterm.flavour


(** Tabling information: the table itself,
  * and some theorems for forward/backward chaining. *)
type tabling_info = { mutable theorem : Term.term ; table : Table.O.t }

(** Describe whether tabling is possible, and if so, how it is used. *)
type flavour = (* XXX private *)
  | Normal
    (** only unfolding can be done *)
  | Inductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a failure *)
  | CoInductive of tabling_info
    (** tabling is possible, and loop is (conditionally) a success *)

(** Predicate: tabling information if the flavours allows it,
  * stratum of the definition block,
  * definition and type. *)
type predicate = (* XXX private *)
    { flavour           : flavour ;
      stratum           : int ;
      mutable definition: Term.term ;
      ty                : Preterm.Typing.ty }
type object_declaration =
  | Constant of Preterm.Typing.ty
  | Predicate of predicate

let predicate flavour stratum definition ty =
  Predicate { flavour=flavour ;
              stratum=stratum ;
              definition=definition ;
              ty=ty }

(** {6 Constants and predicates declarations} *)
module Objects = struct
  let env : (Term.var,object_declaration) Hashtbl.t =
    Hashtbl.create 100

  let get_type v =
    try match Hashtbl.find env v with
      | Constant ty -> Some (None,ty)
      | Predicate {stratum=stratum;ty=ty} -> Some (Some stratum,ty)
    with Not_found -> None

  let get_pred v =
    match Hashtbl.find env v with
      | Constant _ -> None
      | Predicate x -> Some x

  let recent_keys = ref []

  let get_reset () =
    recent_keys := [] ;
    fun () ->
      List.iter
        (Hashtbl.remove env)
        !recent_keys ;
      recent_keys := []

  let declare_const (p,name) ty ~k =
    let var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    match get_type var with
      | Some (_,ty') ->
          raise (Invalid_declaration
                   ("constant",name,p,ty,
                    "name conflict with an object",ty'))
      | None ->
          begin match Logic.get_builtin var with
            | Some ty' ->
                raise (Invalid_declaration
                         ("constant",name,p,ty,
                          "name conflict with a built in predicate",ty'))
            | None ->
                begin match
                  try Some (Types.kind_check ~obj:(Preterm.Typing.Constant name) ~p ty)
                  with e -> catch ~k e
                with
                  | Some _ ->
                      recent_keys := var :: !recent_keys ;
                      Some (Hashtbl.replace env var (Constant ty))
                  | None -> None
                end
          end

  let declare_consts consts ty ~k =
    List.fold_left
      (fun result s ->
         match declare_const s ty ~k with
           | Some () -> result
           | None -> None)
      (Some ()) consts

  let create_def stratum ?(stratum_flavour=Preterm.Normal) (flavour,p,name,ty) ~k =
    let var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    match get_type var with
      | Some (_,ty') ->
          raise (Invalid_declaration
                   ("predicate",name,p,ty,
                    "name conflict with an object",ty'))
      | None ->
          begin match Logic.get_builtin var with
            | Some ty' ->
                raise (Invalid_declaration
                         ("predicate",name,p,ty,
                          "name conflict with a build in predicate",ty'))
            | None ->
                begin match
                  try Some (Types.kind_check ~obj:(Preterm.Typing.Predicate name) ~p ty)
                  with e -> catch ~k e
                with
                  | Some arity ->
                      recent_keys := var :: !recent_keys ;
                      let stratum_flavour,flavour = match stratum_flavour,flavour with
                        | _,Preterm.Normal -> stratum_flavour,Normal
                        | Preterm.Inductive,Preterm.CoInductive
                        | Preterm.CoInductive,Preterm.Inductive ->
                            raise (Invalid_flavour
                                     (name,p,stratum_flavour,flavour))
                        | _,Preterm.Inductive ->
                            flavour,
                            Inductive { theorem = Term.lambda arity Term.op_false ;
                                        table = Table.O.create () }
                        | _,Preterm.CoInductive ->
                            flavour,
                            CoInductive { theorem = Term.lambda arity Term.op_false ;
                                          table = Table.O.create () }
                      in
                      Hashtbl.replace env var
                        (predicate flavour stratum (Term.lambda arity Term.op_false) ty) ;
                      Some stratum_flavour
                  | None -> None
                end
          end

(** Declare predicates.
  * @return the list of variables and types
  *  corresponding to those predicates *)
  let declare_preds =
    let stratum = ref 0 in
    fun decls ~k ->
      incr stratum ;
      match
        List.fold_left
          (fun f decl ->
             match f with
               | Some flavour ->
                   create_def !stratum ~stratum_flavour:flavour decl ~k
               | None ->
                   (* XXX this is bullshit *)
                   ignore (create_def !stratum decl ~k) ;
                   None)
          (Some Preterm.Normal) decls
      with
        | Some _ -> Some !stratum
        | None -> None

  let iter f g =
    Hashtbl.iter
      (fun k v -> match v with
         | Constant c -> f k c
         | Predicate p -> g k p)
      env

  let fold f seed =
    Hashtbl.fold f env seed

  let fold f g seed =
    Hashtbl.fold
      (fun k v accum -> match v with
         | Constant c -> f k c accum
         | Predicate p -> g k p accum)
      env seed

  let clear () =
    Hashtbl.clear env
end

let get_reset () =
  let reset_types = Types.get_reset ()
  and reset_objects = Objects.get_reset () in
  fun () ->
    reset_types () ;
    reset_objects ()

let create_free_types : int -> (Term.var,(Preterm.Typing.ty*Preterm.Pos.t option)) Hashtbl.t =
  fun n -> Hashtbl.create n

let translate_term
      ?stratum
      ?(head=false)
      ?(free_args=[])
      ?(expected_type=Preterm.Typing.fresh_tyvar ())
      ?(free_types=create_free_types 10)
      pre_term ~k =
  let fresh_tyinst = Preterm.Typing.get_fresh_tyinst () in
  let fold_free_types f =
    Hashtbl.fold f free_types
  in
  (* return (and create if needed) a typed variable
   * corresponding to the name of a free variable *)
  let typed_free_var (p,name) =
    let was_free = Term.is_free name in
    let t = Term.atom ~tag:Term.Logic name in
    let v = Term.get_var t in
    try begin
      let ty,_ = Hashtbl.find free_types v in
      Hashtbl.replace free_types v (ty,None) ;
      t,ty
    end with Not_found ->
      let t,v =
        if was_free then t,v else begin
          Term.free name ;
          (* XXX in case we actually use this variable on day,
           * we should depend on the level to create an instantiable variable,
           * ie not always a Logic one (cf [mk_clause])*)
          let t = Term.atom ~tag:Term.Logic name in
          let v = Term.get_var t in
          t,v
        end
      in
      let ty = Preterm.Typing.fresh_tyvar () in
      Hashtbl.replace free_types v (ty,Some p) ;
      t,ty
  in
  (* return a typed variable corresponding to the name
   * of a constant or a predicate (built in or not) *)
  let typed_declared_obj ~instantiate_type ?forbidden_stratum (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    let ty =
      match Objects.get_type v with
        | Some (Some stratum,_) when forbidden_stratum=Some stratum ->
            Term.free name ;
            raise (Stratification_error (name,p))
        | Some (_,ty) -> ty
        | None ->
            begin
              match Logic.get_builtin v with
                | Some ty -> ty
                | None ->
                    Term.free name ;
                    raise (Missing_declaration (name,p))
            end
    in t,(if instantiate_type then Preterm.Typing.get_fresh_tyinst () ty else ty)
  in
  (* return a typed variable corresponding to the name
   * of an internal predicate *)
  let typed_intern_pred (p,name) =
    let t = Term.atom ~tag:Term.Constant name in
    let v = Term.get_var t in
    let ty =
      try Logic.get_internal_type v
      with Not_found ->
        begin
          Term.free name ;
          raise (Missing_declaration (name,p))
        end
    in t,Preterm.Typing.get_fresh_tyinst () ty
  in
  try Some (expected_type,
            free_types,
            Preterm.type_check_and_translate
              ?stratum
              ~head
              ~free_args
              ~fold_free_types
              ~fresh_tyinst
              pre_term
              expected_type
              (typed_free_var,typed_declared_obj,typed_intern_pred,Types.kind_check))
  with e -> catch ~k e
