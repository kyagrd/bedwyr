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

open Parsetree.Preterm.Typing

(* TODO get the code from [Prover] here, so that internal/predefined
 * predicates are declared and defined in one single place
 * TODO add the word pervasive and remove some predecared/predefined *)
module Logic = struct
  let not               = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_not"
  let ite               = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_if"
  let abspred           = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_abstract"
  let distinct          = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_distinct"
  let assert_rigid      = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_rigid"
  let abort_search      = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_abort"
  let cutpred           = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_cut"
  let check_eqvt        = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "_eqvt"

  let var_not           = Ndcore.Term.get_var not
  let var_ite           = Ndcore.Term.get_var ite
  let var_abspred       = Ndcore.Term.get_var abspred
  let var_distinct      = Ndcore.Term.get_var distinct
  let var_assert_rigid  = Ndcore.Term.get_var assert_rigid
  let var_abort_search  = Ndcore.Term.get_var abort_search
  let var_cutpred       = Ndcore.Term.get_var cutpred
  let var_check_eqvt    = Ndcore.Term.get_var check_eqvt

  let internal_t = Hashtbl.create 8
  let () =
    List.iter
      (fun (v,tys) -> Hashtbl.replace internal_t v (Type.arrow tys Type.prop))
      [ (* Non-logical extensions *)
        var_not,          [Type.prop] ;
        var_ite,          [Type.prop;Type.prop;Type.prop] ;
        var_abspred,
          (let ty0 = Type.param 0 in
           let ty1 = Type.arrow [Type.arrow [Type.param 1] ty0] ty0 in
           [ty0;ty1;ty0]) ;
        var_distinct,     [Type.prop] ;
        var_assert_rigid, [Type.param 0] ;
        var_abort_search, [] ;
        var_cutpred,      [Type.prop] ;
        var_check_eqvt,
          (let ty = Type.param 0 in
           [ty;ty] ) ;
      ]

  let get_internal_type v =
    Hashtbl.find internal_t v


  let read              = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "read"
  let fread             = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fread"
  let fopen_in          = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fopen_in"
  let fclose_in         = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fclose_in"
  let print             = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "print"
  let println           = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "println"
  let printstr          = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "printstr"
  let fprint            = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fprint"
  let fprintln          = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fprintln"
  let fprintstr         = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fprintstr"
  let fopen_out         = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fopen_out"
  let fclose_out        = Ndcore.Term.atom ~tag:Ndcore.Term.Constant "fclose_out"

  let var_read          = Ndcore.Term.get_var read
  let var_fread         = Ndcore.Term.get_var fread
  let var_fopen_in      = Ndcore.Term.get_var fopen_in
  let var_fclose_in     = Ndcore.Term.get_var fclose_in
  let var_print         = Ndcore.Term.get_var print
  let var_println       = Ndcore.Term.get_var println
  let var_printstr      = Ndcore.Term.get_var printstr
  let var_fprint        = Ndcore.Term.get_var fprint
  let var_fprintln      = Ndcore.Term.get_var fprintln
  let var_fprintstr     = Ndcore.Term.get_var fprintstr
  let var_fopen_out     = Ndcore.Term.get_var fopen_out
  let var_fclose_out    = Ndcore.Term.get_var fclose_out

  let builtins_t = Hashtbl.create 8
  let () =
    List.iter
      (fun (v,tys) -> Hashtbl.replace builtins_t v (Type.arrow tys Type.prop))
      [ (* I/O extensions *)
        var_read,       [Type.param 0] ;
        var_fread,      [Type.string;Type.param 0] ;
        var_fopen_in,   [Type.string] ;
        var_fclose_in,  [Type.string] ;
        var_print,      [Type.param 0] ;
        var_println,    [Type.param 0] ;
        var_printstr,   [Type.string] ;
        var_fprint,     [Type.string;Type.param 0] ;
        var_fprintln,   [Type.string;Type.param 0] ;
        var_fprintstr,  [Type.string;Type.string] ;
        var_fopen_out,  [Type.string] ;
        var_fclose_out, [Type.string] ;
      ]

  let get_builtin v =
    try Some (Hashtbl.find builtins_t v)
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


(* Error handling. *)

exception Missing_type of string * IO.Pos.t
exception Missing_declaration of string * IO.Pos.t


let catch ~k e =
  begin match e with
    (* Kind checking *)
    | Missing_type (n,p) ->
        IO.Output.eprintf ~p
          "Undeclared type %s."
          n
    | Type_kinding_error (n,p,ki1,ki2) ->
        IO.Output.eprintf ~p
          "Kinding error: the type constructor %s has kind %a@ \
            but is used as %a."
          n
          Kind.pp ki2
          Kind.pp ki1

    (* Type checking *)
    | Missing_declaration (n,p) ->
        IO.Output.eprintf ~p
          "Undeclared object %s."
          n
    | Parsetree.Preterm.Term_typing_error (p,ty1,ty2,unifier) ->
        let pp_type = Type.get_pp ~unifier () in
        IO.Output.eprintf ~p
          "Typing error: this term has type %a but is used as %a."
          pp_type ty2
          pp_type ty1
    | Type_order_error (n,p,ty) ->
        begin match n with
          | Some n ->
              IO.Output.eprintf ~p
                "Typing error: cannot give free variable %s the type %a." n
                Type.pp ty
          | None ->
              IO.Output.eprintf ~p
                "Typing error: cannot quantify over type %a."
                Type.pp ty
        end
    | e -> raise e
  end ;
  k ()


(* Type declarations and access. *)

exception Invalid_type_declaration of string * IO.Pos.t * Kind.t * string


module Types : sig
  val save_state : unit -> int
  val restore_state : int -> unit
  val declare : IO.Pos.t * string -> Kind.t -> unit
  val kind_check :
    obj:obj ->
    p:IO.Pos.t -> Type.t -> int
  val iter : (Ndcore.Term.var -> Kind.t -> unit) -> unit
  val fold : (Ndcore.Term.var -> Kind.t -> 'a -> 'a) -> 'a -> 'a
  val clear : unit -> unit
end = struct
  let env : (Ndcore.Term.var,Kind.t) Hashtbl.t =
    Hashtbl.create 100

  let keys = Stack.create ()

  let save_state () = Stack.length keys

  let restore_state n =
    for i=Stack.length keys downto n+1 do
      let key = Stack.pop keys in
      Hashtbl.remove env key
    done

  let declare (p,name) ki =
    let var = Ndcore.Term.(get_var (atom ~tag:Constant name)) in
    if Hashtbl.mem env var
    then raise (Invalid_type_declaration (name,p,ki,"type already declared"))
    else begin
      let () = Stack.push var keys in
      Hashtbl.replace env var ki ;
    end

  let get_kind (p,name) =
    let var = Ndcore.Term.(get_var (atom ~tag:Constant name)) in
    try Hashtbl.find env var
    with Not_found -> raise (Missing_type (name,p))

  let kind_check ~obj ~p ty =
    kind_check ~obj ~p ty ~get_kind

  let iter f =
    Hashtbl.iter f env

  let fold f seed =
    Hashtbl.fold f env seed

  let clear () =
    let () = Stack.clear keys in
    Hashtbl.clear env
end


(* Constants and predicates declarations. *)

exception Stratification_error of string * IO.Pos.t
exception Invalid_declaration of
  string * string * IO.Pos.t * Type.t * string * Type.t
exception Invalid_flavour of
  string * IO.Pos.t * Parsetree.Preterm.flavour * Parsetree.Preterm.flavour


type tabling_info = { mutable theorem : Ndcore.Term.term ; table : Table.t }

type flavour = (* XXX private *)
  | Normal
  | Inductive of tabling_info
  | CoInductive of tabling_info


type predicate = (* XXX private *)
    { flavour           : flavour ;
      stratum           : int ;
      mutable definition: Ndcore.Term.term ;
      ty                : Type.t }
type object_declaration =
  | Cons of Type.t
  | Pred of predicate

let predicate flavour stratum definition ty =
  Pred { flavour=flavour ;
              stratum=stratum ;
              definition=definition ;
              ty=ty }

module Objects : sig
  val get_type : Ndcore.Term.var -> (int option * Type.t) option
  val get_pred : Ndcore.Term.var -> predicate option
  type state
  val save_state : unit -> state
  val restore_state : state -> unit
  val declare_const :
    IO.Pos.t * string ->
    Type.t -> k:(unit -> int option) -> unit option
  val declare_consts :
    (IO.Pos.t * string) list ->
    Type.t -> k:(unit -> int option) -> unit option
  val create_def :
    int ->
    ?stratum_flavour:Parsetree.Preterm.flavour ->
    Parsetree.Preterm.flavour * IO.Pos.t * string * Type.t ->
    k:(unit -> int option) -> Parsetree.Preterm.flavour option
  val declare_preds :
    (Parsetree.Preterm.flavour * IO.Pos.t * string * Type.t)
    list -> k:(unit -> int option) -> int option
  val iter :
    (Ndcore.Term.var -> Type.t -> unit) ->
    (Ndcore.Term.var -> predicate -> unit) ->
    unit
  val fold :
    (Ndcore.Term.var -> Type.t -> 'a -> 'a) ->
    (Ndcore.Term.var -> predicate -> 'a -> 'a) ->
    'a -> 'a
  val clear : unit -> unit
end = struct
  let env : (Ndcore.Term.var,object_declaration) Hashtbl.t =
    Hashtbl.create 100

  let get_type v =
    try match Hashtbl.find env v with
      | Cons ty -> Some (None,ty)
      | Pred {stratum=stratum;ty=ty} -> Some (Some stratum,ty)
    with Not_found -> None

  let get_pred v =
    match Hashtbl.find env v with
      | Cons _ -> None
      | Pred x -> Some x

  let keys = Stack.create ()

  type state = int

  let save_state () = Stack.length keys

  let restore_state n =
    for i=Stack.length keys downto n+1 do
      let key = Stack.pop keys in
      Hashtbl.remove env key
    done

  let declare_const (p,name) ty ~k =
    let var = Ndcore.Term.get_var (Ndcore.Term.atom ~tag:Ndcore.Term.Constant name) in
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
                  try Some (Types.kind_check ~obj:(Constant name) ~p ty)
                  with e -> catch ~k e
                with
                  | Some _ ->
                      let () = Stack.push var keys in
                      Some (Hashtbl.replace env var (Cons ty))
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

  let create_def stratum ?(stratum_flavour=Parsetree.Preterm.Normal) (flavour,p,name,ty) ~k =
    let var = Ndcore.Term.get_var (Ndcore.Term.atom ~tag:Ndcore.Term.Constant name) in
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
                  try Some (Types.kind_check ~obj:(Predicate name) ~p ty)
                  with e -> catch ~k e
                with
                  | Some arity ->
                      let stratum_flavour,flavour = match stratum_flavour,flavour with
                        | _,Parsetree.Preterm.Normal -> stratum_flavour,Normal
                        | Parsetree.Preterm.Inductive,Parsetree.Preterm.CoInductive
                        | Parsetree.Preterm.CoInductive,Parsetree.Preterm.Inductive ->
                            raise (Invalid_flavour
                                     (name,p,stratum_flavour,flavour))
                        | _,Parsetree.Preterm.Inductive ->
                            flavour,
                            Inductive { theorem = Ndcore.Term.lambda arity Ndcore.Term.op_false ;
                                        table = Table.create () }
                        | _,Parsetree.Preterm.CoInductive ->
                            flavour,
                            CoInductive { theorem = Ndcore.Term.lambda arity Ndcore.Term.op_false ;
                                          table = Table.create () }
                      in
                      let () = Stack.push var keys in
                      Hashtbl.replace env var
                        (predicate flavour stratum (Ndcore.Term.lambda arity Ndcore.Term.op_false) ty) ;
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
          (Some Parsetree.Preterm.Normal) decls
      with
        | Some _ -> Some !stratum
        | None -> None

  let iter f g =
    Hashtbl.iter
      (fun k v -> match v with
         | Cons c -> f k c
         | Pred p -> g k p)
      env

  let fold f g seed =
    Hashtbl.fold
      (fun k v accum -> match v with
         | Cons c -> f k c accum
         | Pred p -> g k p accum)
      env seed

  let clear () =
    let () = Stack.clear keys in
    Hashtbl.clear env
end

let translate_term
      ?stratum
      ?(head=false)
      ?(free_args=[])
      ?(expected_type=Type.fresh_var ())
      ?(free_types=Hashtbl.create 10)
      pre_term ~k =
  (* return a typed variable corresponding to the name
   * of a constant or a predicate (built in or not) *)
  let typed_declared_obj ~instantiate_type ?forbidden_stratum (p,name) =
    let t = Ndcore.Term.atom ~tag:Ndcore.Term.Constant name in
    let v = Ndcore.Term.get_var t in
    let ty =
      match Objects.get_type v with
        | Some (Some stratum,_) when forbidden_stratum=Some stratum ->
            Ndcore.Term.free name ;
            raise (Stratification_error (name,p))
        | Some (_,ty) -> ty
        | None ->
            begin
              match Logic.get_builtin v with
                | Some ty -> ty
                | None ->
                    Ndcore.Term.free name ;
                    raise (Missing_declaration (name,p))
            end
    in t,(if instantiate_type then Type.instantiate_params () ty else ty)
  (* return a typed variable corresponding to the name
   * of an internal predicate *)
  and typed_intern_pred (p,name) =
    let t = Ndcore.Term.atom ~tag:Ndcore.Term.Constant name in
    let v = Ndcore.Term.get_var t in
    let ty =
      try Logic.get_internal_type v
      with Not_found ->
        begin
          Ndcore.Term.free name ;
          raise (Missing_declaration (name,p))
        end
    in t,Type.instantiate_params () ty
  and kind_check = Types.kind_check in
  try Some (expected_type,
            free_types,
            Parsetree.Preterm.type_check_and_translate
              ?stratum
              ~head
              ~free_args
              ~free_types
              pre_term
              expected_type
              (typed_declared_obj,typed_intern_pred,kind_check))
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
        IO.Output.wprintf "Skipping already included@ %S." nice_path ;
        None
      end else begin
        IO.Output.wprintf "Now including@ %S." nice_path ;
        let result = add ~basename ~nice_path ~full_path in
        files := M.add full_path !files ;
        Some result
      end
    in
    IO.Files.run_in ~wrap (IO.Input.apply_on_channel f) name

  let clear () = files := M.empty
end
