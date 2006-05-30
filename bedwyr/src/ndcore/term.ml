(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
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

(* Eigenvariables will be marked by [Ev] tag. *)
type tag = Unset | Ev

(* Terms. The use of references allow in-place normalization. *)
type term = rawterm ref
and rawterm = 
  | Const of string * int * tag
  | Var of string * int * tag
  | DB of int
  | Lam of int * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr
and ptr = term (* Hide this *)
and env = envitem list
and envitem = Dum of int | Binding of term * int

exception NonNormalTerm
exception NotValidTerm

(* Fast structural equality modulo Ptr.
 * Fast: try to use physical equality first.
 * Structural: no normalization peformed. *)
let rec eq t1 t2 =
  (* We do sharing, it may be worth trying physical equality first. *)
  if t1 == t2 then true else
    match !t1,!t2 with
      (* Compare leafs *)
      | DB _, DB _
      | Var _, Var _
      | Const _, Const _ -> t1 = t2
      (* Ignore Ptr. It's an implementation artifact *)
      | _, Ptr t2 -> eq t1 t2
      | Ptr t1, _ -> eq t1 t2
      (* Propagation *)
      | App (h1,l1), App (h2,l2) ->
          List.length l1 = List.length l2 &&
            List.fold_left2
              (fun test t1 t2 -> test && eq t1 t2)
              true (h1::l1) (h2::l2)
      | Lam (n,t1), Lam (m,t2) -> n = m && eq t1 t2
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

let rec deref t = match !t with
  | Ptr d -> deref d
  | _ -> t

let observe t = !(deref t)

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing. *)

type bind_state = int
let bind_stack = Stack.create ()
let bind_len = ref 0

let where () = Printf.printf "#%d\n" !bind_len

let save_state () = !bind_len

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
      v := contents
  done ;
  bind_len := n

type subst = (term*rawterm) list
type unsubst = subst

let bind v t =
  let dv = deref v in
  let dt = deref t in
    if dv != dt then begin
      Stack.push (dv,!dv) bind_stack ;
      dv := Ptr dt ;
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

(* Raise the substitution *)
let rec add_dummies env n m = 
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Dum (m+n'))::(add_dummies env n' m));;

(* Add [n] abstractions. *)
let rec lambda n t =
  let t = deref t in
    if n = 0 then t else
      match !t with
        | Lam (n',t') -> lambda (n+n') t'
        | _ -> ref (Lam (n,t))

(** We try to attach useful names to generated variables.
  * For that purpose we use prefixes like 'h' or 'x',
  * freshness is ensured by the suffix. During parsing, one must take care
  * to rename variables that could conflict with generated ones.
  * TODO choose a policy here.. use more prefixes depending on the type,
  * if typing is introduced ? *)

let prefix = "H"
let prefix_ev = "h"
let prefix_name = "x"

let getAbsName () = prefix_name

(** Generating a fresh variable with a given time stamp; the use of ref
  * ensures uniqueness. We should attach useful names as well, but this 
  * will do for the moment. 
  * I hide [varcount] cause resetting it hurts the consistency of the system. *)
let fresh =
  let varcount = ref 0 in
    fun () ->
      let i = !varcount in
        incr varcount ;
        i

let fresh_ev ts =
  let i = fresh () in
  let name = prefix_ev ^ (string_of_int i) in
    ref (Const (name,ts,Ev))

let fresh ts =
  let i = fresh () in
  let name = prefix ^ (string_of_int i) in
    ref (Var (name,ts,Unset))

(* Recursively raise dB indices and abstract over variables or constants
 * selected by [test]. *)
let abstract test =
  let rec aux n t = match !t with
    | Var (id',i,f)
    | Const (id',i,f) -> if test t id' then ref (DB n) else t
    | DB i -> t
    | App (h,ts) ->
        ref (App ((aux n h), (List.map (aux n) ts)))
    | Lam (m,s) -> ref (Lam (m, aux (n+m) s))
    | Ptr t -> ref (Ptr (aux n t))
    | Susp _ -> raise NonNormalTerm
  in aux

(** Abstract [t] over term [v]. *)
let abstract_var v t = lambda 1 (abstract (fun t id' -> t = v) 1 t)

(** Abstract [t] over constant or variable named [id]. *)
let abstract id t = lambda 1 (abstract (fun t id' -> id' = id) 1 t)

(** Free variables of [ts]. Bound variables are represented by DB indices. *)
let freevars ts =
  let rec fv l t = match observe t with
    | Var _ -> if List.mem t l then l else (t::l)
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (n,t') -> fv l t'
    | Const _ | DB _ -> l
    | Susp _ -> l (* TODO Looks like a gross approx ?! *)
    | Ptr _ -> assert false
  in
    List.fold_left fv [] ts

let eigenvars ts =
  let rec fv l t = match observe t with
    | Const (n,ts,Ev) -> if List.mem t l then l else (t::l)
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (n,t') -> fv l t'
    | Var _ | DB _ | Const _ -> l
    | Susp _ -> l (* TODO Looks like a gross approx ?! *)
    | Ptr _ -> assert false
  in
    List.fold_left fv [] ts

(** Utilities.
  * Easy creation of constants and variables, with sharing. *)

let tag_of_opt = function
  | Some Ev -> Ev
  | _ -> Unset

let const ?tag s n = ref (Const (s,n,tag_of_opt tag))
let var ?tag s n = ref (Var (s,n,tag_of_opt tag))

let tbl = Hashtbl.create 100
let reset_namespace () = Hashtbl.clear tbl
let reset_namespace_vars () =
  Hashtbl.iter
    (fun k v -> match !v with
       | Var _ -> Hashtbl.remove tbl k
       | _ -> ())
    tbl

let atom ?(ts=0) name =
  try
    Hashtbl.find tbl name
  with
    | Not_found ->
        assert (name <> "") ;
        let t =
          match name.[0] with
            | 'A'..'Z' -> var name ts
            | _ -> const name ts
        in
          Hashtbl.add tbl name t ;
          t

let string text = const text 0

let binop s a b = ref (App ((atom s),[a;b]))

let rec collapse_lam t = match !t with
  | Lam (n,t') ->
      begin match !(collapse_lam t') with 
        | Lam (m,u) -> ref (Lam (n+m,u))
        | _ -> t
      end
  | _ -> t

let db n = ref (DB n)
let app a b = if b = [] then a else ref (App (a,b))
let susp t ol nl e = ref (Susp (t,ol,nl,e))

module Notations =
struct
  let (%=) = eq
  let (!!) = observe
  let (//) = lambda
  let (^^) = app
end
