open Type

(** trucs chelous *)

type pos = Lexing.position * Lexing.position
type term' = rawterm'
and rawterm' =
  | QString' of pos * string
  | UpperID of pos * string
  | LowerID of pos * string
  | InfixID of pos * string
  | True'   of pos
  | False'  of pos
  | Eq'     of pos * term' * term'
  | And'    of pos * term' * term'
  | Or'     of pos * term' * term'
  | Arrow'  of pos * term' * term'
  | Binder' of pos * Term.binder * (string * simple_type) list * term'
  | Lam'    of pos * (string * simple_type) list * term'
  | App'    of pos * term' * term' list

let change_pos (p1,_) t' (_,p2) = match t' with
  | QString' (_,s) -> QString' ((p1,p2),s)
  | UpperID (_,s) -> UpperID ((p1,p2),s)
  | LowerID (_,s) -> LowerID ((p1,p2),s)
  | InfixID (_,s) -> InfixID ((p1,p2),s)
  | True' _ -> True' (p1,p2)
  | False' _ -> False' (p1,p2)
  | Eq' (_,t1,t2) -> Eq' ((p1,p2),t1,t2)
  | And' (_,t1,t2) -> And' ((p1,p2),t1,t2)
  | Or' (_,t1,t2) -> Or' ((p1,p2),t1,t2)
  | Arrow' (_,t1,t2) -> Arrow' ((p1,p2),t1,t2)
  | Binder' (_,b,n,t) -> Binder' ((p1,p2),b,n,t)
  | Lam' (_,n,t) -> Lam' ((p1,p2),n,t)
  | App' (_,hd,tl) -> App' ((p1,p2),hd,tl)





(*  let mkdef head params body p =
    (* Replace the params by fresh variables and
     * put the constraints on the parameters in the body:
     * d (s X) X := body --> d Y X := (Y = s X) /\ body
     * As an input we get: [head] (d) [params] ([s X;X]) and [body]. *)

    (* Free the registered names that are bound in the definition clause.
     * If one doesn't do that, a logic variable [X] could be left
     * in the namespace, and persist from one query to another.
     * There shouldn't be any risk to actually free something that was
     * allocated before the parsing of that clause. *)
    let () =
      let v = Term.logic_vars (body::params) in
      List.iter (fun v -> Term.free (Term.get_name v)) v
    in

    (* Create the prolog (new equalities added to the body) and the new set
     * of variables used as parameters.
     * A parameter can be left untouched if it's a variable which didn't
     * occur yet. *)
    let new_params,prolog,old_params =
      List.fold_left
        (fun (new_params,prolog,old_params) p ->
           match Term.observe p with
             | Term.Var {Term.tag=Term.Logic}
                 when List.for_all (fun v -> v!=p) new_params ->
                 p::new_params,prolog,old_params
             | _  ->
                 let v = Term.fresh ~ts:0 ~lts:0 Term.Logic in
                 (v::new_params,(Term.op_eq v p)::prolog,p::old_params))
        ([],[],[])
        params
    in
    (* Add prolog to the body *)
    let body = if prolog = [] then body else
      List.fold_left
        (fun acc term -> Term.op_and term acc)
        body
        prolog
    in
    (* Quantify existentially over the initial free variables,
     * except for those that appeared only on the body
     * (they are not allowed) *)
    let body =
      Term.ex_close
        body
        (List.filter
           (fun v -> not (List.exists (Term.eq v) new_params))
           (Term.logic_vars old_params))
    in
    (* Finally, abstract over parameters *)
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
    (head, p, arity, body)*)


(** from pre-term to term *)
let translate =
  let rec find_db n s = function
    | [] -> None
    | hd::tl when hd=s -> Some (Term.db (n+1))
    | hd::tl -> find_db (n+1) s tl
  in
  let rec aux params = function
    | QString' (p,s) -> Term.qstring s
    | UpperID (p,s) ->
        begin match find_db 0 s params with
          | Some t -> t
          | None -> Term.atom ~tag:Term.Logic s
        end
    | LowerID (p,s) ->
        begin match find_db 0 s params with
          | Some t -> t
          | None -> Term.atom ~tag:Term.Constant s
        end
    | InfixID (p,s) -> Term.atom ~tag:Term.Constant s
    | True' p -> Term.op_true
    | False' p -> Term.op_false
    | Eq' (p,t1',t2') -> Term.op_eq (aux params t1') (aux params t2')
    | And' (p,t1',t2') -> Term.op_and (aux params t1') (aux params t2')
    | Or' (p,t1',t2') -> Term.op_or (aux params t1') (aux params t2')
    | Arrow' (p,t1',t2') -> Term.op_arrow (aux params t1') (aux params t2')
    | Binder' (p,b,l,t') ->
        Term.op_binder
          b
          (List.length l)
          (aux
             (List.rev_append (List.map fst l) params)
             t')
    | Lam' (p,l,t') ->
        Term.lambda
          (List.length l)
          (aux
             (List.rev_append (List.map fst l) params)
             t')
    | App' (p,hd',tl') -> Term.app (aux params hd') (List.map (aux params) tl')
  in aux []

let lambda' p tys t = match tys,t with
  | [],_ -> t
  | tys,Lam' (_,tys2,t2) -> Lam' (p,tys@tys2,t2)
  | tys,_ -> Lam' (p,tys,t)

let app' p a' b' = if b' = [] then a' else match a' with
  | App' (_,a',c') -> App' (p,a',c' @ b')
  | _ -> App' (p,a',b')


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


(** unifier *)
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
      | Term.Binder (_,n,t) ->
          let tys,_ = build_abstraction_types n in
          let unifier = unify_constraint unifier expected_type TProp in
          let db_types = List.rev_append tys db_types in
          aux term TProp unifier db_types nb_types
      | Term.QString _ -> unifier
      | Term.Var v -> (* TODO séparer les tags, refuser ce qui est Eigen
                       * (ce qui est Logic peut être une variable libre d'un
                       * assert), terminer avec juste les Constant *)
          begin match v with
            | {Term.tag=Term.Logic}
            | {Term.tag=Term.Eigen}
            | {Term.tag=Term.Constant} ->
                unify_constraint unifier expected_type (type_of_var (v,term))
          end
      | Term.DB i ->
          (* TODO handle Not_found, and not just with a fresh_tyvar()
           * (otherwise (DB 1 = (DB 1) (DB 1)) typechecks *)
          let ty = List.nth db_types (i-1) in
          unify_constraint unifier expected_type ty
      (* XXX how to build nb_types?
      | Term.NB i ->
          let ty = List.nth nb_types (i-1) in
          unify_constraint unifier expected_type ty *)
      | Term.Lam (n,term) ->
          let tys,ty = build_abstraction_types n in
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
