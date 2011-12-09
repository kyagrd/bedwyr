(** kinds *)
type simple_kind =
  | KType
  | KRArrow of simple_kind' list * simple_kind'
and simple_kind' = simple_kind

let ki_arrow ty = function
  | KRArrow (tys,ty')   -> KRArrow (ty::tys,ty')
  | ty'                 -> KRArrow ([ty],ty')


(** types *)
type simple_type =
  | Ty      of string
  | TProp
  | TRArrow of simple_type' list * simple_type'
  | TVar    of int
and simple_type' = simple_type

let ty_arrow ty = function
  | TRArrow (tys,ty')   -> TRArrow (ty::tys,ty')
  | ty'                 -> TRArrow ([ty],ty')

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    count := 1 + !count;
    TVar !count
