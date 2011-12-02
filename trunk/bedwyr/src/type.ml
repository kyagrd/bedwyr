(** kinds *)
type simple_kind =
  | KType
  | KRArrow of simple_kind' list * simple_kind'
and simple_kind' = simple_kind

let ki_arrow ty = function
  | KRArrow (tys,ty')   -> KRArrow (ty::tys,ty')
  | ty'                 -> KRArrow ([ty],ty')


(** kind-checking *)
(*let kind_check is_predicate (name,p) ty =
  let rec aux is_target = function
    | Type.Ty name' as ty' ->
        assert (name' <> "");
        let type_var = Term.get_var (Term.atom name') in
        if not (Hashtbl.mem type_kinds type_var) then
          if is_predicate
          then raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "type %s was not declared" (Pprint.type_to_string None ty')))
          else raise (Invalid_const_declaration (name,p,ty,Format.sprintf "type %s was not declared" (Pprint.type_to_string None ty')))
        else if is_predicate && is_target then
          raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "target type can only be %s" (Pprint.type_to_string None Type.TProp)))
        else true
    | Type.TProp ->
        if is_predicate
        then is_target || raise (Invalid_pred_declaration (name,p,ty,Format.sprintf "%s can only be a target type" (Pprint.type_to_string None Type.TProp)))
        else raise (Invalid_const_declaration (name,p,ty,Format.sprintf "%s can only be a target type for a predicate" (Pprint.type_to_string None Type.TProp)))
    | Type.TRArrow (tys,ty) -> List.for_all (aux false) tys && aux true ty
    | Type.TVar _ ->
        if is_predicate
        then raise (Invalid_pred_declaration (name,p,ty,"no type variables yet"))
        else raise (Invalid_const_declaration (name,p,ty,"no type variables yet"))
  in
  aux true ty*)


(** types *)
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

let ty_arrow ty = function
  | TRArrow (tys,ty')   -> TRArrow (ty::tys,ty')
  | ty'                 -> TRArrow ([ty],ty')

let fresh_tyvar =
  let count = ref 0 in
  fun () ->
    count := 1 + !count;
    TVar !count


(** type-checking *)
exception Type_unification_error of simple_type * simple_type * simple_type Unifier.t
exception Term_typing_error of simple_type * simple_type * simple_type Unifier.t * Term.term

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
let unify_constraint unifier ty1' ty2' =
  let rec aux u ty1 ty2 = match ty1,ty2 with
    | _,_ when ty1 = ty2 -> u
    | TRArrow ([],ty1),_ ->
        aux u ty1 ty2
    | _,TRArrow ([],ty2) ->
        aux u ty1 ty2
    | TVar i,_ ->
        begin
          try
            let ty1 = Unifier.find i u in
            aux u ty1 ty2
          with
            | Not_found ->
                if occurs u i ty2
                then raise (Type_unification_error (ty1',ty2',u))
                else Unifier.add i ty2 u
        end
    | _,TVar j ->
        begin
          try
            let ty2 = Unifier.find j u in
            aux u ty1 ty2
          with
            | Not_found ->
                if occurs u j ty1
                then raise (Type_unification_error (ty1',ty2',u))
                else Unifier.add j ty1 u
        end
    | TRArrow (ty1::tys1,bty1),TRArrow (ty2::tys2,bty2) ->
        let u = aux u ty1 ty2 in
        aux u (TRArrow (tys1,bty1)) (TRArrow (tys2,bty2))
    | _ ->
        raise (Type_unification_error (ty1',ty2',u))
  in
  aux unifier ty1' ty2'

let build_abstraction_types arity =
  let rec aux tys ty = function
    | 0 -> tys, ty
    | a when a>0 ->
        aux ((fresh_tyvar ())::tys) ty (a-1)
    | _ -> assert (false)
  in
  aux [] (fresh_tyvar ()) arity

let type_check_term term expected_type unifier type_of_var =
  let rec aux term expected_type unifier db_types nb_types =
    try match Term.observe term with
      | Term.True | Term.False ->
          unify_constraint unifier expected_type TProp
      | Term.Eq (t1,t2) ->
          let ty = fresh_tyvar () in
          let unifier = aux t1 ty unifier db_types nb_types in
          let unifier = aux t2 ty unifier db_types nb_types in
          unify_constraint unifier expected_type TProp
      | Term.And (t1,t2) | Term.Or (t1,t2) | Term.Arrow (t1,t2) ->
          let unifier = aux t1 TProp unifier db_types nb_types in
          let unifier = aux t2 TProp unifier db_types nb_types in
          unify_constraint unifier expected_type TProp
      | Term.Binder (_,t) ->
          let ty = fresh_tyvar () in
          let ty = TRArrow ([ty],TProp) in
          let unifier = aux t ty unifier db_types nb_types in
          unify_constraint unifier expected_type TProp
      | Term.Var v -> (* TODO séparer les tags, refuser ce qui est Eigen
                       * (ce qui est Logic peut être une variable libre d'un
                       * assert), terminer avec juste les Constant *)
          begin match v with
            | {Term.tag=Term.String} ->
                unifier
            | _ ->
                unify_constraint unifier expected_type (type_of_var (v,term))
          end
      | Term.DB i ->
          let ty = List.nth db_types (i-1) in
          unify_constraint unifier expected_type ty
      (* XXX how to build nb_types?
      | Term.NB i ->
          let ty = List.nth nb_types (i-1) in
          unify_constraint unifier expected_type ty *)
      | Term.Lam (a,term) ->
          let tys,ty = build_abstraction_types a in
          let unifier = unify_constraint unifier expected_type (TRArrow (tys,ty)) in
          let db_types = List.rev_append tys db_types in
          aux term ty unifier db_types nb_types
      | Term.App (h,l) ->
          let arity = List.length l in
          let tys,ty = build_abstraction_types arity in
          let unifier = unify_constraint unifier expected_type ty in
          let unifier = aux h (TRArrow (tys,ty)) unifier db_types nb_types in
          List.fold_left2
            (fun u t ty -> aux t ty u db_types nb_types)
            unifier
            l
            tys
      (* XXX is term head-normalized?
      | Term.Susp _ -> assert false *)
      | _ ->
          failwith (Format.sprintf "Type checking aborted, unsupported term.")
    with
      | Type_unification_error (ty1,ty2,unifier) ->
          raise (Term_typing_error (ty1,ty2,unifier,term))
  in
  aux term expected_type unifier [] []
