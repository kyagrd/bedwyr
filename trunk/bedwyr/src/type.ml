(* kinds *)
type simple_kind =
  | KRArrow of simple_kind' * simple_kind'
  | Ki of string
and simple_kind' = simple_kind


(* types *)
type simple_type =
  | TRArrow of simple_type' * simple_type'
  | Ty      of string
and simple_type' = simple_type

module NS = Map.Make(struct type t = string let compare = compare end)

let type_kinds : simple_kind NS.t ref = ref NS.empty

let type_define_kind name kind =
  if NS.mem name !type_kinds
  then failwith (Printf.sprintf "Duplicate definition of type \"%s\"!" name)
  (*else if name = "prop"
  then failwith ("Type \"%s\" not allowed here!" name)*)
  else begin
    assert (name <> "");
    type_kinds := NS.add name kind !type_kinds
  end

let type_atom name =
  if NS.mem name !type_kinds
  then Ty name
  else failwith (Printf.sprintf "Type \"%s\" not defined!" name)

let prop_atom name =
  if name <> "prop"
  then failwith (Printf.sprintf "A predicate's type must end with type \"prop\", not \"%s\"!" name)
  else Ty name


(* terms *)
(* [const_types] is like [System.defs], but for non-predicate constants *)
let const_types : (Term.var,simple_type) Hashtbl.t =
  Hashtbl.create 100

let const_define_type name ty =
  let const = Term.get_var (Term.atom name) in
  if Hashtbl.mem const_types const
  then failwith (Printf.sprintf "Duplicate definition of constant \"%s\"!" name)
  else Hashtbl.add const_types const ty
