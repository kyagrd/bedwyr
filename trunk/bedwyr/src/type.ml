(* kinds *)
type simple_kind =
  | KRArrow of simple_kind' * simple_kind'
  | Ki      of string
and simple_kind' = simple_kind

let pp_kind chan kind =
  let rec aux chan = function
    | KRArrow (k1,k2) ->
        Format.fprintf chan "@[(%a -> %a)@]" aux k1 aux k2
    | Ki name ->
        Format.fprintf chan "@[%s@]" name
  in
  Format.fprintf chan "@[%a@]" aux kind 


(* types *)
type simple_type =
  | Ty      of string
  | TRArrow of simple_type' list * simple_type'
  | TProp (* until we allow prop on the left of a '->' *)
  | TUndef  of int
and simple_type' = simple_type

let pp_type chan stype =
  let rec pp chan = function
    | Ty name ->
        Format.fprintf chan "@['%s'@]" name
    | TRArrow (ty1::tys,ty2) ->
        Format.fprintf chan "@[(%a -> %a)@]" pp ty1 pp (TRArrow (tys,ty2))
    | TRArrow ([],ty) ->
        pp chan ty
    | TProp ->
        Format.fprintf chan "@[prop@]"
    | TUndef i ->
        Format.fprintf chan "@[?%d@]" i
  in
  Format.fprintf chan "@[%a@]" pp stype

let pp_ltypes chan tys =
  let rec aux = function
    | [] -> Format.fprintf chan "]@]%!"
    | [ty] -> Format.fprintf chan " %a ]@]%!" pp_type ty
    | ty::tys -> Format.fprintf chan " %a ;" pp_type ty ; aux tys
  in
  Format.fprintf chan "@[[";
  aux tys

let arrow ty = function
  | TRArrow (tys,ty')   -> TRArrow (ty::tys,ty')
  | ty'                 -> TRArrow ([ty],ty')

let fresh_type =
  let n = ref 0 in
  fun () ->
    n := 1 + !n;
    TUndef !n

let atom = function
  | "_" -> fresh_type()
  | "prop" -> TProp
  | name -> Ty name

module Unifier = Map.Make(struct type t = int let compare = compare end)

let global_unifier : simple_type Unifier.t ref = ref Unifier.empty

let pp_type_deep unifier chan stype =
  let rec pp chan = function
    | Ty name ->
        Format.fprintf chan "@['%s'@]" name
    | TRArrow (ty1::tys,ty2) ->
        Format.fprintf chan "@[(%a -> %a)@]" pp ty1 pp (TRArrow (tys,ty2))
    | TRArrow ([],ty) ->
        pp chan ty
    | TProp ->
        Format.fprintf chan "@[prop@]"
    | TUndef i ->
        try
          let ty = Unifier.find i unifier in
          pp chan ty
        with
          | Not_found -> Format.fprintf chan "@[?%d@]" i
  in
  Format.fprintf chan "@[%a@]" pp stype

let pp_unifier chan unifier =
  Format.fprintf chan "@[{";
  Unifier.iter
    (fun i stype -> Format.fprintf chan "@[ %d : %a ;@]" i pp_type stype)
    unifier;
  Format.fprintf chan "}@]%!"


(* terms *)
exception Type_unification_error of simple_type * simple_type * simple_type Unifier.t

let occurs i =
  let rec aux = function
    | TUndef j when i=j -> true
    | TRArrow (tys,ty) -> List.exists aux tys || aux ty
    | _ -> false
  in
  aux

(* TODO [unifier] needs to be GC-ed,
 * or at least we should avoid unnecessary chained references *)
let rec unify_constraint unifier ty1 ty2 =
  try match ty1,ty2 with
    | _,_ when ty1 = ty2 -> unifier
    | TRArrow ([],ty1),_ ->
        unify_constraint unifier ty1 ty2
    | _,TRArrow ([],ty2) ->
        unify_constraint unifier ty1 ty2
    | TUndef i,_ ->
        begin
          try
            let ty1 = Unifier.find i unifier in
            unify_constraint unifier ty1 ty2
          with
            | Not_found ->
                if occurs i ty2
                then raise (Type_unification_error (ty1,ty2,unifier))
                else Unifier.add i ty2 unifier
        end
    | _,TUndef i ->
        begin
          try
            let ty2 = Unifier.find i unifier in
            unify_constraint unifier ty1 ty2
          with
            | Not_found ->
                if occurs i ty1
                then raise (Type_unification_error (ty1,ty2,unifier))
                else Unifier.add i ty1 unifier
        end
    | TRArrow (ty1::tys1,bty1),TRArrow (ty2::tys2,bty2) ->
        let unifier = unify_constraint unifier ty1 ty2 in
        unify_constraint unifier (TRArrow (tys1,bty1)) (TRArrow (tys2,bty2))
    | _ -> raise (Type_unification_error (ty1,ty2,unifier))
  with
    | Type_unification_error (_,_,unifier) ->
        raise (Type_unification_error (ty1,ty2,unifier))

let build_abstraction_types arity =
  let rec aux tys ty = function
    | 0 -> tys, ty
    | a when a>0 ->
        aux ((fresh_type())::tys) ty (a-1)
    | _ -> assert (false)
  in
  aux [] (fresh_type ()) arity
