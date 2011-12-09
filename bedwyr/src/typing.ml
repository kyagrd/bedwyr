open Type

(** trucs chelous *)

type pos = Lexing.position * Lexing.position
type term' = rawterm'
and rawterm' =
  | QString of pos * string
  | FreeID of pos * string
  | PredConstID of pos * string
  | True   of pos
  | False  of pos
  | Eq     of pos * term' * term'
  | And    of pos * term' * term'
  | Or     of pos * term' * term'
  | Arrow  of pos * term' * term'
  | Binder of pos * Term.binder * (pos * string * simple_type) list * term'
  | Lam    of pos * (pos * string * simple_type) list * term'
  | App    of pos * term' * term' list

let get_pos = function
  | QString (p,_) -> p
  | FreeID (p,_) -> p
  | PredConstID (p,_) -> p
  | True p -> p
  | False p -> p
  | Eq (p,_,_) -> p
  | And (p,_,_) -> p
  | Or (p,_,_) -> p
  | Arrow (p,_,_) -> p
  | Binder (p,_,_,_) -> p
  | Lam (p,_,_) -> p
  | App (p,_,_) -> p

let set_pos p = function
  | QString (_,s) -> QString (p,s)
  | FreeID (_,s) -> FreeID (p,s)
  | PredConstID (_,s) -> PredConstID (p,s)
  | True _ -> True p
  | False _ -> False p
  | Eq (_,t1,t2) -> Eq (p,t1,t2)
  | And (_,t1,t2) -> And (p,t1,t2)
  | Or (_,t1,t2) -> Or (p,t1,t2)
  | Arrow (_,t1,t2) -> Arrow (p,t1,t2)
  | Binder (_,b,n,t) -> Binder (p,b,n,t)
  | Lam (_,n,t) -> Lam (p,n,t)
  | App (_,hd,tl) -> App (p,hd,tl)

let change_pos (p1,_) t' (_,p2) = set_pos (p1,p2) t'



let lambda' p vars t = match vars,t with
  | [],_ -> t
  | vars,Lam (_,vars2,t2) -> Lam (p,vars@vars2,t2)
  | vars,_ -> Lam (p,vars,t)

let app' p a' b' = if b' = [] then a' else match a' with
  | App (_,a',c') -> App (p,a',c' @ b')
  | _ -> App (p,a',b')


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
exception Term_typing_error of pos * simple_type * simple_type * simple_type Unifier.t

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
        begin try
          let ty1 = Unifier.find i u in
          aux u ty1 ty2
        with
          | Not_found ->
              if occurs u i ty2
              then raise (Type_unification_error (ty1',ty2',u))
              else Unifier.add i ty2 u
        end
    | _,TVar j ->
        begin try
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

let type_check_and_translate pre_term expected_type type_of_free type_of_id =
  let find_db s bvars =
    let rec aux n = function
      | [] -> None
      | (p,name,ty)::_ when name=s -> Some (Term.db n,ty)
      | _::bvars -> aux (n+1) bvars
    in
    aux 1 bvars
  in
  let rec aux pt exty bvars u =
    let p = get_pos pt in
    try match pt with
      | QString (p,s) -> Term.qstring s,u
      | FreeID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) ->
                let u = unify_constraint u exty ty in
                t,u
            | None ->
                let t,ty = type_of_free (p,s) in
                let u = unify_constraint u exty ty in
                t,u
          end
      | PredConstID (p,s) ->
          begin match find_db s bvars with
            | Some (t,ty) ->
                let u = unify_constraint u exty ty in
                t,u
            | None ->
                let t,ty = type_of_id (p,s) in
                let u = unify_constraint u exty ty in
                t,u
          end
      | True p ->
          let u = unify_constraint u exty TProp in
          Term.op_true,u
      | False p ->
          let u = unify_constraint u exty TProp in
          Term.op_false,u
      | Eq (p,t1',t2') ->
          let ty = fresh_tyvar () in
          let u = unify_constraint u exty TProp in
          let t1,u = aux t1' ty bvars u in
          let t2,u = aux t2' ty bvars u in
          Term.op_eq t1 t2,u
      | And (p,t1',t2') ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux t1' TProp bvars u in
          let t2,u = aux t2' TProp bvars u in
          Term.op_and t1 t2,u
      | Or (p,t1',t2') ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux t1' TProp bvars u in
          let t2,u = aux t2' TProp bvars u in
          Term.op_or t1 t2,u
      | Arrow (p,t1',t2') ->
          let u = unify_constraint u exty TProp in
          let t1,u = aux t1' TProp bvars u in
          let t2,u = aux t2' TProp bvars u in
          Term.op_arrow t1 t2,u
      | Binder (p,b,l,t') ->
          let arity = List.length l in
          let bvars = List.rev_append l bvars in
          let u = unify_constraint u exty TProp in
          let t,u = aux t' TProp bvars u in
          Term.binder b arity t,u
      | Lam (p,l,t') ->
          let arity = List.length l in
          let tys = List.map (fun (_,_,ty) -> ty) l in
          let ty = fresh_tyvar () in
          let bvars = List.rev_append l bvars in
          let u = unify_constraint u exty (TRArrow (tys,ty)) in
          let t,u = aux t' ty bvars u in
          Term.lambda arity t,u
      | App (p,hd',tl') ->
          let arity = List.length tl' in
          let tys,ty = build_abstraction_types arity in
          let u = unify_constraint u exty ty in
          let hd,u = aux hd' (TRArrow (tys,ty)) bvars u in
          let u,tl = List.fold_left2
                       (fun (u,tl) t' ty ->
                          let t,u = aux t' ty bvars u in u,t::tl)
                       (u,[])
                       tl'
                       tys
          in
          Term.app hd (List.rev tl),u
    with
      | Type_unification_error (ty1,ty2,unifier) ->
          raise (Term_typing_error (p,ty1,ty2,unifier))
  in
  let term,unifier = aux pre_term expected_type [] !global_unifier in
  global_unifier := unifier ;
  term
