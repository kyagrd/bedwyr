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

let stdlib = "\
Kind    list    type -> type.

Type    nil     list _.
Type    ::      A -> list A -> list A.

Define member : A -> list A -> prop by
  member X (X :: _) ;
  member X (_ :: L) := member X L.

%Define remove : A -> list A -> list A -> prop by
%  remove X (X :: L) L ;
%  remove X (Y :: L1) (Y :: L2) := remove X L1 L2.
%
%Define append : list A -> list A -> list A -> prop by
%  append nil L L ;
%  append (X :: L1) L2 (X :: L3) := append L1 L2 L3.
%
%Define least : (A -> A -> prop) -> list A -> A -> prop by
%  least _ (X :: nil) X ;
%  least Smaller (X :: Y :: L) Z :=
%    least Smaller (Y :: L) W /\\
%    ((Smaller X W /\\ Z = X) \\/ (Smaller W X /\\ Z = W)).
%
%Define sort : (A -> A -> prop) -> list A -> list A -> prop by
%  sort _ nil nil ;
%  sort Smaller L1 (X :: L2) := least Smaller L1 X /\\ remove X L1 L2.

Kind    option  type -> type.
Type    opnone  option A.
Type    opsome  A -> option A.
"


(* Type declarations. *)

exception Invalid_type_declaration of string * Preterm.Pos.t * Preterm.Typing.ki * string
exception Missing_type of string * Preterm.Pos.t


module Types : sig
  val save_state : unit -> int
  val restore_state : int -> unit
  val declare : Preterm.Pos.t * string -> Preterm.Typing.ki -> unit
  val get_kind : Preterm.Pos.t * string -> Preterm.Typing.ki
  val kind_check :
    obj:Preterm.Typing.obj ->
    p:Preterm.Typing.pos -> Preterm.Typing.ty -> int
  val iter : (Term.var -> Preterm.Typing.ki -> unit) -> unit
  val clear : unit -> unit
end = struct
  let env : (Term.var,Preterm.Typing.ki) Hashtbl.t =
    Hashtbl.create 100

  let keys = Stack.create ()

  let save_state () = Stack.length keys

  let restore_state n =
    for i=Stack.length keys downto n+1 do
      let key = Stack.pop keys in
      Hashtbl.remove env key
    done

  let declare (p,name) ki =
    let var = Term.get_var (Term.atom ~tag:Term.Constant name) in
    if Hashtbl.mem env var
    then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
    else begin
      let () = Stack.push var keys in
      Hashtbl.replace env var ki ;
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
    let () = Stack.clear keys in
    Hashtbl.clear env
end


(* Error handling. *)

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


(* Constants and predicates declarations. *)

exception Invalid_declaration of
  string * string * Preterm.Pos.t * Preterm.Typing.ty * string * Preterm.Typing.ty
exception Invalid_flavour of
  string * Preterm.Pos.t * Preterm.flavour * Preterm.flavour


type tabling_info = { mutable theorem : Term.term ; table : Table.O.t }

type flavour = (* XXX private *)
  | Normal
  | Inductive of tabling_info
  | CoInductive of tabling_info

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


(* Constants and predicates declarations. *)

module Objects : sig
  val get_type : Term.var -> (int option * Preterm.Typing.ty) option
  val get_pred : Term.var -> predicate option
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val declare_const :
    Preterm.Typing.pos * string ->
    Preterm.Typing.ty -> k:(unit -> int option) -> unit option
  val declare_consts :
    (Preterm.Typing.pos * string) list ->
    Preterm.Typing.ty -> k:(unit -> int option) -> unit option
  val create_def :
    int ->
    ?stratum_flavour:Preterm.flavour ->
    Preterm.flavour * Preterm.Typing.pos * string * Preterm.Typing.ty ->
    k:(unit -> int option) -> Preterm.flavour option
  val declare_preds :
    (Preterm.flavour * Preterm.Typing.pos * string * Preterm.Typing.ty)
    list -> k:(unit -> int option) -> int option
  val iter :
    (Term.var -> Preterm.Typing.ty -> unit) ->
    (Term.var -> predicate -> unit) ->
    unit
  val fold :
    (Term.var -> Preterm.Typing.ty -> 'a -> 'a) ->
    (Term.var -> predicate -> 'a -> 'a) ->
    'a -> 'a
  val clear : unit -> unit
end = struct
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

  let keys = Stack.create ()

  type state = int

  let save_state () = Stack.length keys

  let restore_state n =
    for i=Stack.length keys downto n+1 do
      let key = Stack.pop keys in
      Hashtbl.remove env key
    done

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
                      let () = Stack.push var keys in
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
                      let () = Stack.push var keys in
                      Hashtbl.replace env var
                        (predicate flavour stratum (Term.lambda arity Term.op_false) ty) ;
                      Some stratum_flavour
                  | None -> None
                end
          end

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

  let fold f g seed =
    Hashtbl.fold
      (fun k v accum -> match v with
         | Constant c -> f k c accum
         | Predicate p -> g k p accum)
      env seed

  let clear () =
    let () = Stack.clear keys in
    Hashtbl.clear env
end

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


(* Definitions files. *)

module IncludedFiles : sig
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val apply_on_file : (Lexing.lexbuf -> 'a) -> string -> 'a option
  val clear : unit -> unit
end = struct
  module M = Set.Make (struct type t = string let compare = compare end)

  let files = ref M.empty

  type state = M.t

  let save_state () = !files

  let restore_state f = files := f

  let apply_on_file f name =
    let wrap add ~basename ~nice_path ~full_path =
      if M.mem full_path !files then begin
        Output.wprintf "Skipping already included@ %S." nice_path ;
        None
      end else begin
        Output.wprintf "Now including@ %S." nice_path ;
        let result = add ~basename ~nice_path ~full_path in
        files := M.add full_path !files ;
        Some result
      end
    in
    IO.run_in ~wrap (Read.apply_on_channel f) name

  let clear () = files := M.empty
end
