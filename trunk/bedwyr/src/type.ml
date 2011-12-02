(* kinds *)
type simple_kind =
  | Ki      of string
  | KRArrow of simple_kind' list * simple_kind'
and simple_kind' = simple_kind

let pp_kind chan kind =
  let rec aux chan = function
    | Ki name ->
        Format.fprintf chan "@[%s@]" name
    | KRArrow (ki1::kis,ki2) ->
        Format.fprintf chan "@[(%a -> %a)@]" aux ki1 aux (KRArrow (kis,ki2))
    | KRArrow ([],ki) ->
        aux chan ki
  in
  Format.fprintf chan "@[%a@]" aux kind

let ki_arrow ty = function
  | KRArrow (tys,ty')   -> KRArrow (ty::tys,ty')
  | ty'                 -> KRArrow ([ty],ty')


(* types *)
type simple_type =
  | Ty      of string
  | TProp
  | TRArrow of simple_type' list * simple_type'
  | TVar    of int
and simple_type' = simple_type

module Unifier = Map.Make(struct type t = int let compare = compare end)

let global_unifier : simple_type Unifier.t ref = ref Unifier.empty

let ty_norm unifier ty =
  let rec aux = function
    | Ty _
    | TProp as ty -> ty
    | TRArrow (tys,ty) ->
        TRArrow (List.map aux tys, aux ty)
    | TVar i as ty ->
        begin try
          let ty = Unifier.find i unifier in
          aux ty
        with
          | Not_found -> ty
        end
  in
  aux ty

let pp_type unifier chan ty =
  let ty = match unifier with
    | None -> ty
    | Some unifier -> ty_norm unifier ty
  in
  let rec aux chan = function
    | Ty name ->
        Format.fprintf chan "@[%s@]" name
    | TProp ->
        Format.fprintf chan "@[prop@]"
    | TRArrow (ty1::tys,ty2) ->
        Format.fprintf chan "@[(%a -> %a)@]" aux ty1 aux (TRArrow (tys,ty2))
    | TRArrow ([],ty) ->
        aux chan ty
    | TVar i ->
        Format.fprintf chan "@[?%d@]" i
  in
  Format.fprintf chan "@[%a@]" aux ty

let pp_ltypes chan tys =
  let rec aux = function
    | [] -> Format.fprintf chan "]@]%!"
    | [ty] -> Format.fprintf chan " %a ]@]%!" (pp_type None) ty
    | ty::tys -> Format.fprintf chan " %a ;" (pp_type None) ty ; aux tys
  in
  Format.fprintf chan "@[[";
  aux tys

let ty_arrow ty = function
  | TRArrow (tys,ty')   -> TRArrow (ty::tys,ty')
  | ty'                 -> TRArrow ([ty],ty')

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    count := 1 + !count;
    TVar !count

let pp_unifier chan unifier =
  Format.fprintf chan "@[{";
  Unifier.iter
    (fun i ty -> Format.fprintf chan "@[ %d : %a ;@]" i (pp_type None) ty)
    unifier;
  Format.fprintf chan "}@]%!"


(* terms *)
exception Type_unification_error of simple_type * simple_type * simple_type Unifier.t

let occurs unifier i =
  let rec aux = function
    | Ty _
    | TProp -> false
    | TRArrow (tys,ty) -> List.exists aux tys || aux ty
    | TVar j ->
        if i=j then true
        else begin try
          let ty = Unifier.find j unifier in
          aux ty
        with
          | Not_found -> false
        end
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
    | TVar i,_ ->
        begin
          try
            let ty1 = Unifier.find i unifier in
            unify_constraint unifier ty1 ty2
          with
            | Not_found ->
                if occurs unifier i ty2
                then raise (Type_unification_error (ty1,ty2,unifier))
                else Unifier.add i ty2 unifier
        end
    | _,TVar j ->
        begin
          try
            let ty2 = Unifier.find j unifier in
            unify_constraint unifier ty1 ty2
          with
            | Not_found ->
                if occurs unifier j ty1
                then raise (Type_unification_error (ty1,ty2,unifier))
                else Unifier.add j ty1 unifier
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
        aux ((fresh_tyvar())::tys) ty (a-1)
    | _ -> assert (false)
  in
  aux [] (fresh_tyvar ()) arity
