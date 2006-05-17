(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2006 David Baelde, Alwen Tiu, Axelle Ziegler               *)
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

exception Invalid_definition
exception Level_inconsistency

open Format
open System

(* Destructive flag swicth Ev <-> Logical *)

open Term

let iter_env f = List.iter (function
                             | Dum n -> ()
                             | Binding (t,n) -> f t)

let rec logical_to_ev t = match Term.observe t with
  | Var (n,ts,_) -> Term.bind t (Term.const ~tag:Term.Ev n ts)
  | Const _ | DB _ -> ()
  | App (h,l) -> List.iter logical_to_ev (h::l)
  | Lam (n,t) -> logical_to_ev t
  | Susp (t,_,_,e) -> logical_to_ev t ; iter_env logical_to_ev e
  | Ptr _ -> assert false

(* [t] is supposed to be fully normalized,
 * we need to check that logical variables in suspensions are not used anyway *)
let rec ev_to_logical t = match Term.observe t with
  | Const (n,ts,Ev) -> Term.bind t (Term.var ~tag:Term.Ev n ts)
  | Const _ | DB _ -> ()
  | Var (n,_,Ev) -> () (* Already switched *)
  | Var (n,_,_) -> failwith "Logical var on the left !"
  | App (h,l) -> List.iter ev_to_logical (h::l)
  | Lam (n,t) -> ev_to_logical t
  | Susp _
  | Ptr  _ -> assert false

(** Proof search *)

(* Internal design of the prover has two levels. *)
type level = Zero | One
let assert_level_one = function
  | One -> ()
  | Zero -> raise Level_inconsistency

(* Small definition to help having a tailrec prover *)
let unify a b =
  try Unify.pattern_unify a b ; true with Unify.Error _ -> false

(* Attemps to prove that the goal [(nabla x_1..x_local . g)(S)] by
 * destructively instantiating it,
 * calling [success] on every success, and finishing with [failure]
 * which can be seen as a more usual continuation, typically
 * restoring modifications and backtracking.
 * [timestamp] must be the oldest timestamp in the goal. *)
let rec prove ~success ~failure ~level ~timestamp ~local g =

  System.check_interrupt () ;

  let state = Term.save_state () in
  let failure () =
    if !debug then
      Format.printf "No (more) success for %a!\n%!" Pprint.pp_term g ;
    Term.restore_state state ;
    failure ()
  in
  let success k =
    if !debug then
      Format.printf "Success for           %a!\n%!" Pprint.pp_term g ;
    success k
  in

  let g = Norm.hnorm g in

  if !debug then
    printf "Proving %a...\n%!" Pprint.pp_term g ;

  let prove_atom d args =
    let kind,body = System.get_def ~check_arity:(List.length args) d in
      prove ~level ~timestamp ~local ~success ~failure (Term.app body args)
  in

  match Term.observe g with
  | Const (t,_,_) when t = "exit" -> exit 0
  | Const (t,_,_) when t = Logic.truth -> success failure
  | Const (t,_,_) when t = Logic.falsity -> failure ()
  | Const (d,_,_) -> prove_atom d []
  | App (hd,goals) ->
      let goals = List.map Norm.hnorm goals in
      begin match Term.observe hd with

        (* Solving an equality *)
        | Const (e,_,_) when e = Logic.eq && List.length goals = 2 ->
            if unify (List.hd goals) (List.hd (List.tl goals)) then
              success failure
            else
              failure ()

        (* Proving a conjunction *)
        | Const (a,_,_) when a = Logic.andc ->
            let rec conj failure = function
              | [] -> success failure
              | goal::goals ->
                  prove
                    ~local ~timestamp ~level
                    ~success:(fun k -> conj k goals)
                    ~failure
                    goal
            in
              conj failure goals

        (* Proving a disjunction *)
        | Const (o,_,_) when o = Logic.orc ->
            let rec alt = function
              | [] -> failure ()
              | g::goals ->
                  prove
                    ~level ~local ~timestamp
                    ~success
                    ~failure:(fun () -> alt goals)
                    g
            in
              alt goals

        (* Level 1: Implication *)
        | Const (i,_,_) when i = Logic.imp && List.length goals = 2 ->
            assert_level_one level ;
            let (a,b) = match goals with [a;b] -> a,b | _ -> assert false in
            (* The full normalization is useful for getting rid of logical
             * variables left in suspensions.  *)
            let a = Norm.deep_norm a in
            (* Solve [a] using level 0,
             * remind of the solution substitutions as slices of the bind stack,
             * then prove [b] at level 1 for every solution for [a],
             * thanks to the commutability between patches for [a] and [b],
             * one modifying eigenvars,
             * the other modifying logical variables. *)
            let state = save_state () in
            let ev_substs = ref [] in
            let store_subst k =
              (* We store the state in which we should leave the system
               * when calling [k].
               * The we complete the current solution with the reverse
               * flip of variables to eigenvariables, and we get sigma which
               * we store. *)
              let s = save_state () in
                logical_to_ev a ;
                ev_substs := (get_subst state)::!ev_substs ;
                restore_state s ;
                k ()
            in
            let rec prove_b failure = function
              | [] -> success failure
              | sigma::substs ->
                  (* We have to prove (b theta_0 sigma) *)
                  let unsig = ref (apply_subst sigma) in
                    prove ~level ~local ~timestamp b
                    ~success:(fun k ->
                                (* We found (b theta_0 sigma theta).
                                 * Temporarily remove sigma to
                                 * prove (b theta_0 theta) against other
                                 * sigmas in substs. *)
                                undo_subst !unsig ;
                                prove_b
                                  (fun () ->
                                     (* Put sigma back to call k
                                      * in the correct environment. *)
                                     unsig := apply_subst sigma ;
                                     k ())
                                  substs)
                    ~failure:(fun () ->
                                undo_subst !unsig ;
                                failure ())
            in
              ev_to_logical a ;
              prove ~level:Zero ~local ~timestamp a
                ~success:store_subst
                ~failure:(fun () ->
                            (* Undo ev_to_logical and prove b *)
                            restore_state state ;
                            prove_b failure !ev_substs)

        (* Level 1: Universal quantification *)
        | Const (forall,_,_) when forall = Logic.forall ->
            assert_level_one level ;
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (m,_) ->
                  let timestamp = timestamp + 1 in
                  let args = raise_eigenvars ~timestamp ~local m in
                  let goal = app goal args in
                    prove ~timestamp ~local ~level ~success ~failure goal
              | _ -> assert false
            end

        (* Local quantification *)
        | Const (nabla,_,_) when nabla = Logic.nabla ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (m,g) ->
                  let local = local + m in
                    prove ~timestamp ~local ~level ~success ~failure g
              | _ -> assert false
            end

        (* Existential quantification *)
        | Const (ex,_,_) when ex = Logic.exists ->
            let goal = match goals with
              | [g] -> g
              | _ -> assert false
            in begin match observe goal with
              | Lam (m,g) ->
                  prove ~timestamp ~local ~level ~success ~failure
                    (app goal (raise_vars ~timestamp ~local m))
              | _ -> assert false
            end

        (* Output *)
        | Const ("print",_,_) ->
            List.iter (fun t -> printf "%a\n%!" Pprint.pp_term t) goals ;
            success failure

        (* Check for definitions *)
        | Const (d,_,_) -> prove_atom d goals

        (* Invalid goal *)
        | _ ->
            printf "Invalid goal %a!" Pprint.pp_term g ;
            failure ()
      end

  (* Failure *)
  | _ ->
      printf "Invalid goal %a!" Pprint.pp_term g ;
      failure ()

let toplevel_prove g =
  let _ = Term.reset_namespace () in
  let s0 = Term.save_state () in
  let vars = List.map (fun t -> Pprint.term_to_string t, t)
               (List.rev (Term.freevars [g])) in
  let found = ref false in
  let show k =
    found := true ;
    if vars = [] then printf "True.\n" else
      printf "Solution found:\n" ;
    List.iter
      (fun (o,t) -> printf " %s = %a\n" o Pprint.pp_term t)
      vars ;
    printf "More [y] ? %!" ;
    let l = input_line stdin in
      if l = "" || l.[0] = 'y' || l.[0] = 'Y' then
        k ()
      else begin
        Term.restore_state s0 ;
        printf "Search stopped.\n"
      end
  in
    prove ~level:One ~local:0 ~timestamp:0 g
      ~success:show
      ~failure:(fun () ->
                  if !found then printf "No more solutions.\n"
                  else printf "Wrong.\n" ;
                  assert (s0 = Term.save_state ()))
