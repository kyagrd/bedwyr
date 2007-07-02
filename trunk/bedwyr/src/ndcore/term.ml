(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2007 Nadathur, Linnell, Baelde, Ziegler               *)
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
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

(** Representation of higher-order terms. *)

type tag = Eigen | Constant | Logic

(** Physical equality is used to distinguish variables. *)
type var = {
  id  : int ; (* Only used for hashing *)
  tag : tag ;
  ts  : int ; (* Always zero for constants in Bedwyr *)
  lts : int
}

(** TODO ? phantom type for annotating term with what's inside
  * [ `Var ] term, etc... *)
type term = rawterm
and rawterm =
  | Var  of var (* Only when "observing" the term *)
  | DB   of int
  | NB   of int (* Nabla variables *)
  | Lam  of int * term
  | App  of term * term list
  | Susp of term * int * int * env
  | Ptr  of ptr
and ptr = in_ptr ref
and in_ptr = V of var | T of term
and env = envitem list
and envitem = Dum of int | Binding of term * int

(** Fast observational equality; no normalization is peformed. *)
let rec eq t1 t2 =
  match t1,t2 with
    (* Compare leafs *)
    | DB i1, DB i2
    | NB i1, NB i2 -> i1=i2
    | Ptr {contents=V v1}, Ptr {contents=V v2} -> v1==v2
    (* Ignore Ptr. It's an implementation artifact *)
    | _, Ptr {contents=T t2} -> eq t1 t2
    | Ptr {contents=T t1}, _ -> eq t1 t2
    (* Propagation *)
    | App (h1,l1), App (h2,l2) ->
        List.length l1 = List.length l2 &&
        List.fold_left2
          (fun test t1 t2 -> test && eq t1 t2)
          true (h1::l1) (h2::l2)
    | Lam (n,t1), Lam (m,t2) -> n = m && eq t1 t2
    | Var _, _ | _, Var _ -> assert false
    | Susp (t,ol,nl,e), Susp (tt,oll,nll,ee) ->
        ol = oll && nl = nll && eq t tt &&
          List.fold_left2
            (fun test e1 e2 ->
               test && match e1,e2 with
                 | Dum i, Dum j when i = j -> true
                 | Binding (t,i), Binding (tt,j) when i=j && eq t tt -> true
                 | _ -> false)
            true e ee
    | _ -> false

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var v
  | t -> t

let rec deref = function
  | Ptr {contents=T t} -> deref t
  | t -> t

(** {1 Binding a variable} *)

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing. *)

type state = int
let bind_stack = Stack.create ()
let bind_len = ref 0

let save_state () = !bind_len

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
      v := contents
  done ;
  bind_len := n

type subst = (ptr*in_ptr) list
type unsubst = subst

let bind v t =
  let dv = match deref v with
    | Ptr t -> t
    | _ -> assert false (* [v] should represent a variable *)
  in
  let dt = deref t in
    if match dt with Ptr r when r==dv -> false | _ -> true then begin
      Stack.push (dv,!dv) bind_stack ;
      dv := T dt ;
      incr bind_len
    end

exception Done

let get_subst state =
  let subst = ref [] in
  let count = ref (!bind_len-state) in
    assert (!count >= 0) ;
    try
      Stack.iter
        (fun (v,old) ->
           if !count = 0 then raise Done ;
           subst := (v,!v)::!subst ;
           decr count)
        bind_stack ;
      !subst
    with Done -> !subst

let apply_subst s = List.fold_left (fun sub (v,contents) ->
                                      let old = !v in
                                        v := contents ;
                                        (v,old)::sub) [] s
let undo_subst = List.iter (fun (s,old) -> s:=old)

(** {1 Abstract} *)

(* Add [n] abstractions. *)
let lambda n t =
  assert (n>=0) ;
  if n=0 then t else
    let rec aux n t =
      match deref t with
        | Lam (n',t') -> aux (n+n') t'
        | _ -> Lam (n,t)
    in
      aux n t

exception NonNormalTerm

(** [abstract var t] computes the abstraction of [t] over the variable [var]. *)
let abstract target t =
  let target =
    match observe target with
      | Var v -> v
      | App _ -> assert false
      | _ -> assert false
  in
  (* Recursively raise dB indices and abstract over [target]. *)
  let rec aux n t = match t with
    | NB i -> t
    | DB i -> if i>=n then DB (i+1) else t
    | App (h,ts) ->
        App ((aux n h), (List.map (aux n) ts))
    | Lam (m,s) -> Lam (m, aux (n+m) s)
    | Ptr {contents=T t} -> Ptr (ref (T (aux n t)))
    | Ptr {contents=V v} -> if v==target then DB n else t
    | Var _ -> assert false
    | Susp _ -> raise NonNormalTerm
  in
  lambda 1 (aux 1 t)

(** {1 Extract variables} *)

(** [get_vars test ts] computes the list of variables [v] occuring in
  * the list of normalized terms [ts] and which satisfy [test v]. *)
let get_vars test ts =
  let rec fv l t = match observe t with
    | Var v ->
        if test v && not (List.mem_assq v l) then ((v,t)::l) else l
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (n,t') -> fv l t'
    | NB _ | DB _ -> l
    | Susp _ -> assert false
    | Ptr _ -> assert false
  in
    List.map snd (List.fold_left fv [] ts)

(** Logic variables of [ts], assuming that they are normalized. *)
let logic_vars = get_vars (fun v -> v.tag = Logic)

(** Eigen variables of [ts], assuming that they are normalized. *)
let eigen_vars = get_vars (fun v -> v.tag = Eigen)

(** {1 Copying} *)

(** [copy ()] instantiates a copier, that copies terms,
  * preserving sharing inside the set of copied terms.
  * Input terms should be normalized. *)
let copy () =
  let tbl = Hashtbl.create 100 in
  let rec cp tm = match observe tm with
    | Var v ->
        begin try Hashtbl.find tbl v with
          | Not_found ->
              let x = Ptr (ref (V v)) in
                Hashtbl.add tbl v x ;
                x
        end
    | App (a,l) -> App (cp a, List.map cp l)
    | Lam (n,b) -> Lam (n, cp b)
    | NB i | DB i as x -> x
    | Susp _ | Ptr _ -> assert false
  in
    cp

(** {1 Generate and find variables} *)

(** [var_names] is used to attach a naming hint for the pretty printer
  * to variables, not only those built by the parser. It is designed to not
  * interfere with the GC. *)
module Hint = struct
  module M = Map.Make(struct type t = int let compare = compare end)
  let var_names = ref M.empty
  let add var name =
    var_names := M.add var.id name !var_names ;
    Gc.finalise (fun v -> var_names := M.remove v.id !var_names) var
  let find var =
    M.find var.id !var_names
end

let fresh_id =
  let c = ref 0 in
    fun () -> incr c ; !c

(** Generate a fresh variable. *)
let var ~tag ~ts ~lts = Ptr (ref (V {id=fresh_id();tag=tag;ts=ts;lts=lts}))

(** Generate a fresh variable, attach a naming hint to it. *)
let fresh ~name ~tag ~lts ~ts =
  let v = {id=fresh_id();tag=tag;ts=ts;lts=lts} in
    Hint.add v name ;
    Ptr (ref (V v))

module NS = Map.Make(struct type t = string let compare = compare end)
type namespace = term NS.t

(** [symbols] is used to obtain the exact same variable term for
  * representing all instances of that variable -- used by the parser. *)
let symbols = ref NS.empty

let save_namespace () = !symbols
let restore_namespace s = symbols := s

(** Get the unique variable attached to that name, preserving sharing.
  * The variable is created if it does not exist. *)
let get_var_by_name ~tag ~ts ~lts name =
  try
    NS.find name !symbols
  with
    | Not_found ->
        assert (name <> "") ;
        let lts = 0 in
        let t = fresh ~tag ~ts ~lts ~name in
          symbols := NS.add name t !symbols ;
          t

(* Same as [get_var_by_name] but infers the tag from the name and sets both
 * levels to 0. *)
let atom name =
  let tag = match name.[0] with
    | 'A'..'Z' -> Logic
    | _ -> Constant
  in
    get_var_by_name ~ts:0 ~lts:0 ~tag name

let get_var x = match observe x with
  | Var v -> v
  | App _ -> assert false
  | _ -> assert false

let get_hint var =
  Hint.find (get_var var)

(** Find an unique name for [v] (based on a naming hint if there is one)
  * and registers it in the symbols table. *)
let get_name var =
  let existing_name =
    NS.fold
      (fun key value x ->
         if eq value var then Some key else x)
      !symbols
      None
  in
    match existing_name with
      | Some n -> n
      | None ->
          let v = match observe var with Var v -> v | _ -> assert false in
          let prefix =
            try
              (* Get the naming hint. *)
              Hint.find v
            with
              | Not_found ->
                  begin match v.tag with
                    | Logic -> "H"
                    | Eigen -> "h"
                    | Constant -> "c"
                  end
          in
          let rec lookup suffix =
            let name =
              if suffix < 0 then prefix else prefix ^ string_of_int suffix
            in
              if NS.mem name !symbols then
                lookup (suffix+1)
              else begin
                symbols := NS.add name var !symbols ;
                name
              end
          in
            lookup (-1)

let dummy = let n = -1 in Ptr(ref(V { id=n;ts=n;lts=n;tag=Constant }))

(** [get_dummy_name prefix] finds a free name starting with [prefix] and
  * registers it. If [start] is not provided, the attempted suffixes will be
  * "", "0", "1", etc. If it is provided it will be used as the first suffix to
  * try. *)
let get_dummy_name ?(start=(-1)) prefix =
  let rec lookup suffix =
    let name =
      if suffix < 0 then prefix else prefix ^ string_of_int suffix
    in
      if NS.mem name !symbols then
        lookup (suffix+1)
      else begin
        symbols := NS.add name dummy !symbols ;
        name
      end
  in
    lookup start

(** List of [n] new dummy names, most recent first. *)
let get_dummy_names ?(start=(-1)) n prefix =
  let rec aux i =
    if i=0 then [] else
      let tl = aux (i-1) in
        (get_dummy_name ~start prefix)::tl
  in
    List.rev (aux n)

let is_free name =
  not (NS.mem name !symbols)

let free n =
  symbols := NS.remove n !symbols

(** {1 Convenience} *)

let string text = get_var_by_name ~tag:Constant ~lts:0 ~ts:0 text

let binop s a b = App ((atom s),[a;b])

let db n = DB n

let nabla n = NB n

let app a b = if b = [] then a else match observe a with
  | App(a,c) -> App (a,c @ b)
  | _ -> App (a,b)

let susp t ol nl e = Susp (t,ol,nl,e)

let get_nablas x =
  let rec nb l t = match observe t with
    | Var _ -> l
    | App (h,ts) -> List.fold_left nb (nb l h) ts
    | Lam (n,t') -> nb l t'
    | DB _ -> l
    | NB i -> if List.mem i l then l else i::l
    | Susp _ | Ptr _ -> assert false
  in
    nb [] x

module Notations =
struct
  let (%=) = eq
  let (!!) = observe
  let (//) = lambda
  let (^^) = app
end
