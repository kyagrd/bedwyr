(****************************************************************************)
(* Bedwyr -- level-0/1 proof search                                         *)
(* Copyright (C) 2006 Alwen Tiu, Axelle Ziegler, Andrew Gacek               *)
(* Copyright (C) 2006-2009 David Baelde                                     *)
(* Copyright (C) 2011 Alwen Tiu                                             *)
(* Copyright (C) 2011-2015 Quentin Heath                                    *)
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
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

exception Level_inconsistency

exception Left_logic of Ndcore.Term.term

exception Variable_leakage

open Environment
open System
open Ndcore.Term

(* Internal design of the prover has two levels, Zero and One.
 * On level One, logic vars are instantiated and eigenvars are constants.
 * On level Zero, logic vars are forbidden and eigenvars can be instantiated. *)
type level = Zero | One

let assert_level_one = function
  | One -> ()
  | Zero -> raise Level_inconsistency

let freezing_point = ref 0
let saturation_pressure = ref 0

type temperature = Unfrozen | Frozen of int

let unify =
  let module RightParams = struct
    let instantiatable = Logic
    let constant_like = Eigen
  end in
  let module Right = Ndcore.Unify.Make (RightParams) in

  let module LeftParams = struct
    let instantiatable = Eigen
    let constant_like = Constant
  end in
  let module Left = Ndcore.Unify.Make (LeftParams) in

  fun lvl a b ->
    try
      if lvl = Zero
      then Left.pattern_unify a b
      else Right.pattern_unify a b ;
      true
    with
      | Ndcore.Unify.Error _ -> false
      | Ndcore.Unify.IllegalVariable t -> raise (Left_logic t)

(* Tabling provides a way to cut some parts of the search,
 * but we should take care not to mistake shortcuts and disproving. *)

let dependency_stack = Stack.create ()

let clear_dependency_stack () =
  try
    while true do
      let s,_ = Stack.pop dependency_stack in s := Table.Unset
    done
  with Stack.Empty -> ()

exception Found
let mark_dependent_until =
  let add_dependencies status final_dependencies =
    try
      Stack.iter (fun (st,fi) ->
                    if st == status then raise Found else begin
                      fi := status :: !fi ;
                      final_dependencies := st :: !final_dependencies
                    end)
        dependency_stack ;
      assert false (* this can only be called on the tip of a loop *)
    with Found -> ()
  in
  let aux2 status (looping,final_influences,final_dependencies) =
    if !looping then
      (* this atom is the tip of a loop ;
       * we need to make the previous atoms depend on it *)
      add_dependencies status final_dependencies
    else ((* TODO prove that the second level of final influences
           * is included in the first *))
  in
  let aux status (looping,final_influences,final_dependencies) =
    if !looping then
      (* this atom is the tip of a loop ;
       * we need to make the previous atoms depend on it *)
      add_dependencies status final_dependencies
    else
      (* this atom is not a tip but depends upon some ;
       * we need to make the previous atoms depend on them *)
      List.iter
        (fun st -> match !st with
           | Table.Working (_,w) -> aux2 st w
           | _ -> assert false)
        !final_influences
  in
  aux

type 'a answer =
  | Known of ('a ref -> bool) * 'a ref * term * Table.t
  | Unknown of ('a ref -> bool) * term * Table.t
  | OffTopic


(* Attempt to prove the goal [(nabla x_1..x_local . g)(S)] by
 * destructively instantiating it,
 * calling [success] on every success, and finishing with [failure]
 * which can be seen as a more usual continuation, typically
 * restoring modifications and backtracking.
 * [timestamp] must be the oldest timestamp in the goal. *)
let rec prove sons
      temperatures depth
      ~success ~failure ~constraints ~level ~timestamp ~local g =

  if check_interrupt () then begin
    clear_dependency_stack () ;
    raise Interrupt
  end ;

  let g = Ndcore.Norm.hnorm g in
  let invalid_goal () =
    failwith (Format.sprintf "Invalid goal %s" (Ndcore.Pprint.term_to_string_full [] [] g))
  in

  (* Function to prove _distinct predicate *)
  let prove_distinct goals =
    let sol = ref [] in
    let match_list l1 l2 = List.for_all2 eq l1 l2 in
    let a = match goals with [a] -> a | _ -> invalid_goal () in
    let a = Ndcore.Norm.deep_norm a in
    let vars = if level = Zero then eigen_vars [a] else logic_vars [a] in
    prove sons
      temperatures (depth+1)
      ~level ~timestamp ~failure ~local a
      ~constraints
      ~success:(fun ts k ->
                  let tm_list = List.map shared_copy vars in
                  if List.exists (match_list tm_list) !sol then k () else begin
                    sol := tm_list :: !sol ;
                    success ts k
                  end)
  in

  (* Function to prove _abstract predicate *)
  let prove_abstract goals =
    let a,b,c = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
    let a = Ndcore.Norm.deep_norm a in
    let b = Ndcore.Norm.deep_norm b in
    let c = Ndcore.Norm.deep_norm c in
    let vars =
      if level = Zero then eigen_vars [a] else logic_vars [a]
    in
    let d =
      List.fold_left (fun t v -> app b [abstract_flex v t]) a vars
    in
    let g = op_eq c d in
    prove sons
      temperatures (depth+1)
      ~level ~success ~failure ~constraints ~timestamp ~local g
  in

  (* Function to prove _not predicate *)
  let prove_not goals =
    let a = match goals with [a] -> a | _ -> invalid_goal () in
    let a = Ndcore.Norm.deep_norm a in
    let state = save_state () in
    prove sons temperatures (depth+1) ~level ~timestamp ~local a
      ~constraints
      ~success:(fun ts k ->
                  restore_state state ;
                  failure ())
      ~failure:(fun () ->
                restore_state state ;
                success timestamp failure )
  in

  (* Function to prove _if predicate *)
  let prove_ite goals =
    let (a,b,c) = match goals with [a;b;c] -> a,b,c | _ -> invalid_goal () in
    let a = Ndcore.Norm.deep_norm a in
    let b = Ndcore.Norm.deep_norm b in
    let c = Ndcore.Norm.deep_norm c in
    let succeeded = ref false in
    let state = save_state () in
    prove sons temperatures (depth+1) ~level ~timestamp ~local a
      ~constraints
      ~success:(fun ts k ->
                  (*  restore_state state ; *)
                  (*  prove temperatures (depth+1) ~success ~failure ~level
                   *  ~timestamp ~local (op_and a b) *)
                  succeeded := true ;
                  prove sons
                    temperatures (depth+1)
                    ~success ~constraints ~level ~timestamp:ts ~local b ~failure:k)
      (* (fun () -> restore_state state ; failure()) *)
      ~failure:(fun () ->
                  restore_state state ;
                  if !succeeded then failure () else
                    prove sons
                      temperatures (depth+1)
                      ~success ~failure ~constraints ~level ~timestamp ~local c)
  in

  (* 2-step procedure (table, definition)
   * to prove a predicative atom *)
  let prove_atom d args (v,temperature,temperatures) =
    IO.Output.dprintf "[%s] Proving@ %a..."
      (match temperature with Frozen t -> string_of_int t | _ -> "+")
      Ndcore.Pprint.pp_term g ;
    let flavour,definition = get_flav_def d in
    (* first step, first sub-step: look at the table
     * (whether the atom is frozen or not is irrelevent at this point) *)
    let status = match flavour with
      | Normal -> OffTopic
      | Inductive {theorem=theorem;table=table}
      | CoInductive {theorem=theorem;table=table} ->
          let add,found,_ = Table.access ~switch_vars:(level=Zero) table args in
          match found with
            | Some c -> Known (add,c,theorem,table)
            | None -> Unknown (add,theorem,table)
    in
    match status with
      | OffTopic ->
          prove sons temperatures (depth+1)
            ~level ~timestamp ~local ~success ~failure ~constraints (app definition args)
      | Known (_,({contents=Table.Proved _} as status),_,_) ->
          IO.Output.dprintf "Goal (%a) proved using table." Ndcore.Pprint.pp_term g ;
          sons := Table.Cut status :: !sons ;
          success timestamp failure
      | Known (_,({contents=Table.Disproved _} as status),_,_) ->
          IO.Output.dprintf "Known disproved." ;
          sons := Table.Cut status :: !sons ;
          failure ()
      | Known (_,({contents=Table.Working (_,w)} as status),_,_) ->
          (* this is an unsure atom *)
          begin match temperature with
            | Frozen _ ->
                (* Unfortunately, a theorem is not a clause
                 * that we can add to a definition,
                 * since it doesn't respect the flavour.
                 * Therefore no loop-related feature is relevant,
                 * ie no marking.
                 * Moreover, this breaks the symmetry
                 * (theorems cannot handle negated atoms),
                 * so no success either. *)
                failure ()
            | Unfrozen ->
                let looping,_,_ = w in
                if !looping then begin
                  sons := Table.Loop status :: !sons
                end else begin
                  sons := Table.Cut status :: !sons
                end ;
                begin match flavour with
                  | Inductive _ ->
                      mark_dependent_until status w ;
                      failure ()
                  | CoInductive _ ->
                      mark_dependent_until status w ;
                      success timestamp failure
                  | _ -> assert false (* XXX plain loop detection or not? *)
                end
          end
      | Unknown (table_add,theorem,table)
      | Known (table_add,{contents=Table.Unset},theorem,table) ->
          match Table.filter ~switch_vars:(level=Zero) table args with
            | Some true ->
                success timestamp failure
            | Some false ->
                failure ()
            | None ->
          (* This handles the cases where nothing is in the table,
           * or Unset has been left, in which case the [Table.add]
           * will overwrite it. *)
          (* This is a generic function that works both for unfrozen proof
           * and backward chaining. *)
          let prove body success failure temperatures =
            let validate status final_influences result =
              let rec aux = function
                | [] -> ()
                | ([],_) :: l2 -> aux l2
                | ((st :: l1),st') :: l2 ->
                    begin match !st with
                      | Table.Working (sons',(_,fi,fd)) ->
                          let fi1,fi2 =
                            let rec rem l1 = function
                              | [] -> assert false
                              | hd::l2 ->
                                  if hd==st' then l1,l2 else rem (hd::l1) l2
                            in
                            rem [] !fi
                          in
                          if fi1=[] && fi2=[] then begin
                            st := result sons' ;
                            aux ((!fd,st) :: (l1,st') :: l2)
                          end else begin
                            fi := List.rev_append fi1 fi2 ;
                            aux ((l1,st') :: l2)
                          end
                      | _ -> assert false
                    end
              in
              (* we have to add a dumy dependency for the atom,
               * since [aux] decrements the number of dependencies *)
              let r = ref Table.Unset in
              final_influences := r :: !final_influences ;
              aux [[status],r]
            in
            let invalidate status result =
              let rec aux = function
                | [] -> ()
                | [] :: l2 -> aux l2
                | (st :: l1) :: l2 ->
                    begin match !st with
                      | Table.Working (_,(_,_,fd)) ->
                          st := Table.Unset ;
                          aux (!fd :: l1 :: l2)
                      | _ -> aux (l1 :: l2)
                    end
              in
              aux [[status]] ;
              status := result
            in
            let new_sons = ref [] in
            let process_success status final_influences =
              match temperature with
                | Frozen _ ->
                    (* Theorems cannot handle loops,
                     * so no (in)validation. *)
                    status := Table.Proved new_sons
                    (* TODO maybe remove this case, since final_dependencies
                     * and final_influences are empty anyway *)
                | Unfrozen ->
                    begin match flavour with
                      | Inductive _ ->
                          invalidate status (Table.Proved new_sons)
                      | CoInductive _ ->
                          validate status final_influences
                            (fun sons' -> Table.Proved sons')
                      | _ -> assert false
                    end
            in
            let process_failure status final_influences =
              match temperature with
                | Frozen _ ->
                    (* Theorems cannot handle negated atoms yet,
                     * so a failure means nothing. *)
                    status := Table.Unset
                    (* XXX (Frozen !freezing_point) never actually happens,
                     * instead the temperature is Unfrozen and the atom
                     * is incorrectly marked as Disproved,
                     * which is not a problem as long as the
                     * failure continuation calls for a standard proof search
                     * (which starts with resetting status to Working) *)
                | Unfrozen ->
                    begin match flavour with
                      | Inductive _ ->
                          validate status final_influences
                            (fun sons' -> Table.Disproved sons')
                      | CoInductive _ ->
                          invalidate status (Table.Disproved new_sons)
                      | _ -> assert false
                    end
            in
            let looping,final_influences,final_dependencies =
              (ref false,ref [],ref [])
            in
            let status =
              let w = looping,final_influences,final_dependencies in
              ref (Table.Working (new_sons,w))
            in
            let s0 = save_state () in
            let table_update_success ts _ =
              ignore (Stack.pop dependency_stack) ;
              looping := false ;
              process_success status final_influences ;
              (* Since we know that there is at most one success,
               * we ignore the failure continuation passed as argument
               * to [table_update_success] and directly jump to the
               * [failure] continuation. It _seems_ OK regarding the
               * cleanup handlers, which are just jumps to
               * previous states.
               * It is actually quite useful in examples/graph-alt.def,
               * and is required by the dependency_stack. *)
              let k () =
                success ts (fun () -> restore_state s0 ; failure ())
              in
              (* XXX Here be the Forward-Chaining XXX *)
              let saturate =
                match temperature with
                  | Frozen _ ->
                      (* XXX for now we don't forward-chain during
                       * backward chaining;
                       * if someday we do, we must skip "Working _"
                       * instead of failing on it *)
                      fun k -> k ()
                  | Unfrozen ->
                      (* [theorem] corresponds to the fact
                       * "forall X, theorem X -> p X" *)
                      let arity = List.length args in
                      let vars =
                        let rec aux l = function
                          | n when n <= 0 -> l
                          | n -> aux ((fresh
                                         ~lts:local
                                         Eigen
                                         ~ts:(timestamp + n))::l) (n-1)
                        in
                        aux [] arity
                      in
                      let timestamp = timestamp + arity in
                      let th_body = app theorem vars in
                      (* [store_subst] is nearly the same as for Arrow *)
                      let substs = ref [] in
                      let state = save_state () in
                      let store_subst ts k =
                        (* XXX check_variables? *)
                        substs := (get_subst state)::!substs ;
                        k ()
                      in
                      (* [make_copies] is nearly the same as for Arrow *)
                      let make_copies vs =
                        List.map
                          (fun sigma ->
                             let unsig = apply_subst sigma in
                             let newvars = List.map shared_copy vars in
                             undo_subst unsig ;
                             newvars)
                          vs
                      in
                      let rec fc k pressure = function
                        | [] -> k ()
                        | args::copies ->
                            IO.Output.dprintf "(%d) Tabling@ %a..."
                              pressure
                              Ndcore.Pprint.pp_term (app d args) ;
                            let k () = fc k pressure copies in
                            let status =
                              let add,found,_ =
                                Table.access
                                  ~switch_vars:(level=Zero) table args
                              in
                              match found with
                                | Some c -> Known (add,c,theorem,table)
                                | None -> Unknown (add,theorem,table)
                            in
                            match status with
                              | OffTopic -> k ()
                              | Known (_,{contents=Table.Proved _},_,_) ->
                                  IO.Output.dprintf
                                    "Goal (%a) already proved!"
                                    Ndcore.Pprint.pp_term (app d args) ;
                                  k ()
                              | Known (_,{contents=Table.Disproved _},_,_) ->
                                  failwith "did our theorem just prove false?"
                              | Known (_,{contents=Table.Working _},_,_) ->
                                  assert false
                              | Unknown (table_add,theorem,table)
                              | Known (table_add,{contents=Table.Unset},theorem,table) ->
                                  (* XXX what [sons] to use here? *)
                                  let status = ref (Table.Proved new_sons) in
                                  (* XXX switch_vars? *)
                                  if not (table_add status) then assert false ;
                                  IO.Output.dprintf
                                    "Goal (%a) proved using forward chaining."
                                    Ndcore.Pprint.pp_term (app d args) ;
                                  fc_step k pressure args
                      and fc_step k pressure args =
                        if pressure<>(!saturation_pressure) then begin
                          (* TODO replace this DFS by a BFS
                           * (or at least try whether it's more efficient
                           * memory-wise) *)
                          let pressure =
                            if pressure < !saturation_pressure
                            then pressure+1
                            else pressure
                          in
                          let failure () =
                            let copies = make_copies !substs in
                            substs := [] ;
                            fc k pressure copies
                          in
                          (* XXX for now we don't backward-chain during
                           * forward chaining;
                           * we must also use [args] at least once
                           * to improve performance *)
                          (* XXX check this sons! *)
                          prove new_sons ((v,Frozen 0)::temperatures)
                            (depth+1) ~local ~timestamp ~constraints
                            ~level:Zero ~success:store_subst ~failure th_body
                        end else k ()
                      in
                      fun k -> fc_step k 0 args
              in
              (* XXX There was the Forward-Chaining XXX *)
              saturate k
            in
            let table_update_failure () =
              begin match !status with
                | Table.Proved _ ->
                    (* This is just backtracking, we are seeing the tabling
                     * entry corresponding to a previous goal.
                     * Never happens if we skipped the success continuation. *)
                    assert false
                | Table.Working _ ->
                    ignore (Stack.pop dependency_stack) ;
                    looping := false ;
                    process_failure status final_influences
                | Table.Disproved _ | Table.Unset -> assert false
              end ;
              failure ()
            in
            if table_add status then begin
              (* TODO maybe do not add this when frozen *)
              Stack.push (status,final_influences) dependency_stack ;
              looping := true ;
              sons := Table.Son status :: !sons ;
              prove new_sons
                temperatures (depth+1)
                ~level ~local ~timestamp (app body args)
                ~constraints
                ~success:table_update_success
                ~failure:table_update_failure
            end else
              (* TODO so long as we can't table this atom,
               * there is probably no point in doing backward-chaining,
               * since we want to find an exhaustive list of solutions anyway,
               * and while we're at it, there is no point in table_add-ing
               * twice, part of this should be moved out of this local [prove]
               *)
              prove sons
                temperatures (depth+1)
                ~level ~local ~timestamp ~success ~failure ~constraints (app body args)
          in
          (* first step, second sub-step: freeze the atom if needed,
           * unfold the theorem *)
          let temp,success,failure =
            match temperature with
              | Frozen t ->
                  t,
                  (fun timestamp failure ->
                     IO.Output.dprintf
                       "Frozen goal (%a) proved using backward chaining."
                       Ndcore.Pprint.pp_term g ;
                     success timestamp failure),
                  failure
              | Unfrozen ->
                  !freezing_point,
                  (fun timestamp failure ->
                     IO.Output.dprintf
                       "Unfrozen goal (%a) proved using backward chaining."
                       Ndcore.Pprint.pp_term g ;
                     success timestamp failure),
                  (* second step: unfreeze the atom,
                   * unfold the definition *)
                  (fun () -> prove definition success failure temperatures)
          in
          if temp > 0 then
            prove theorem success failure ((v,Frozen (temp-1))::temperatures)
          else if temp = 0 then
            failure ()
          else
            prove theorem success failure ((v,Frozen (-1))::temperatures)
  in

  match observe g with
    | True -> success timestamp failure
    | False -> failure ()

    (* Abort search: throw an exception *)
    | Var v when v == Logic.var_abort_search ->  raise Abort_search

    | Var v ->
        let temperature,temperatures =
          try List.assq v temperatures,List.remove_assq v temperatures
          with Not_found -> Unfrozen,temperatures
        in
        prove_atom g [] (v,temperature,temperatures)

    (* Solving an equality *)
    | Binop (Eq,t1,t2) ->
        let state = save_state () in
        let failure () = restore_state state ; failure () in
        if unify level (Ndcore.Norm.hnorm t1) (Ndcore.Norm.hnorm t2) then
          success timestamp failure
        else
          failure ()

    (* Proving a conjunction *)
    | Binop (And,t1,t2) ->
        let rec conj ts failure = function
          | [] -> success ts failure
          | goal::goals ->
              prove sons temperatures (depth+1)
                ~local ~level ~timestamp
                ~success:(fun ts' k -> conj (max ts ts') k goals)
                ~failure
                ~constraints
                goal
        in
        conj timestamp failure [Ndcore.Norm.hnorm t1;Ndcore.Norm.hnorm t2]

    (* Proving a disjunction *)
    | Binop (Or,t1,t2) ->
        let rec alt = function
          | [] -> failure ()
          | g::goals ->
              prove sons temperatures (depth+1)
                ~level ~local ~success ~timestamp
                ~failure:(fun () -> alt goals)
                ~constraints
                g
        in
        alt [Ndcore.Norm.hnorm t1;Ndcore.Norm.hnorm t2]

    (* Level 1: Implication *)
    | Binop (Arrow,a,b) ->
        IO.Output.printf "constraints: " ;
        List.iter (fun t -> IO.Output.printf "%a ;" Ndcore.Pprint.pp_term t) constraints ;
        IO.Output.printf "\n" ;
        IO.Output.printf "here %a\n" Ndcore.Pprint.pp_term g ;
        let b = Ndcore.Norm.deep_norm b in
        let a = Ndcore.Norm.deep_norm a in
        begin match (level, observe a, observe b) with
        | (Zero, Binop(Eq,t1,t2), False) ->
          begin match (observe t1, observe t2) with
          | (x1, x2) ->
            IO.Output.printf "t1 %a\n" Ndcore.Pprint.pp_term t1 ;
            IO.Output.printf "t2 %a\n" Ndcore.Pprint.pp_term t2 ;
            if x1 = x2
            then failure ()
            else success timestamp failure (*
              prove sons temperatures (depth+1)
                ~level ~local ~timestamp ~success
                ~failure
                ~constraints:(op_binop Eq t1 t2::constraints)
                op_true (* TODO this is not right constraints are not passed to level 1 how can we do this?
                and how do we make sure x1 and x2 are vars *)
          | (t1o,t2o) ->
            IO.Output.printf "t1o %a\n" Ndcore.Pprint.pp_term t1 ;
            IO.Output.printf "t2o %a\n" Ndcore.Pprint.pp_term t2 ;
            assert_level_one level ;
            failure () *)
          end 
        | _ ->
          assert_level_one level ;
          let a = Ndcore.Norm.deep_norm a in
          let b = Ndcore.Norm.deep_norm b in
          let check_variables =
            let eigen = eigen_vars [a] in
            let logic = logic_vars [b] in
            let var v =
              match observe v with
                | Var v -> v
                | _ -> assert false
            in
            let max = (* maximum logic variable timestamp *)
              List.fold_left
                (fun m v -> max m (var v).ts) (-1) logic
            in
            let eigen = List.filter (fun v -> (var v).ts <= max) eigen in
            (* Check that all eigen-variables on which logic vars
             * can depend are instantiated to distinct eigenvars.
             * Then LLambda unifications will be preserved. *)
            let var v =
              match observe v with
                | Var v when v.tag = Eigen -> v
                | _ -> raise (Ndcore.Unify.NotLLambda v)
            in
            fun () ->
              (* This is called when some left solution has been
               * found. We check that everything is a variable. *)
              let eigen = List.map (fun v -> v,var v) eigen in
              let rec unicity = function
                | [] -> ()
                | (va,a)::tl ->
                    if List.exists (fun (_,b) -> a=b) tl then
                      raise (Ndcore.Unify.NotLLambda va) ;
                    unicity tl
              in
              unicity eigen
          in
          (* Solve [a] using level 0,
           * remind of the solution substitutions as slices of the bind stack,
           * then prove [b] at level 1 for every solution for [a],
           * thanks to the commutability between patches for [a] and [b],
           * one modifying eigenvars,
           * the other modifying logical variables. *)
          let substs = ref [] in
          let state = save_state () in
          let store_subst ts k =
            check_variables () ;
            (* We get sigma by comparing the current solution
             * with the state [k] will leave the system in,
             * and we store it. *)
            substs := (ts,
                       begin match observe a with
                             | Binop (Arrow,a1,a2)
                               when (match (observe a1,observe a2) with
                                     | (Binop (Eq,_,_), False) -> true
                                     | _                       -> false)
                                 -> [a1]
                             | _ -> []
                       end,
                       get_subst state)::!substs ;
            k ()
          in
          let make_copies vs g =
            List.map
              (fun (ts,cs,sigma) ->
               match cs with
               | [] ->
                 let unsig = apply_subst sigma in
                 let g = Ndcore.Norm.deep_norm g in
                 let newg = shared_copy g in
                 undo_subst unsig ;
                 (ts, newg)
               | (a1::_) ->
                 let unsig = apply_subst sigma in
                 let g = Ndcore.Norm.deep_norm g in
                 let newg = shared_copy g in
                 undo_subst unsig ;
              )
              vs
          in
          let rec prove_conj ts failure = function
            | [] -> success ts failure
            | (ts'',g)::gs ->
                prove sons
                  temperatures (depth+1)
                  ~level ~local ~timestamp:ts''
                  ~constraints
                  ~success:(fun ts' k -> prove_conj (max ts ts') k gs)
                  ~failure g
          in
          prove sons
            temperatures (depth+1)
            ~level:Zero ~local ~timestamp a
            ~constraints
            ~success:store_subst
            ~failure:(fun () ->
                        prove_conj timestamp failure
                          (make_copies !substs b))
        end
    (* Level 1: Universal quantification *)
    | Binder (Forall,n,goal) ->
        assert_level_one level ;
        let goal = lambda n goal in
        let vars =
          let rec aux l = function
            | n when n <= 0 -> l
            | n -> aux ((fresh ~lts:local Eigen ~ts:(timestamp + n))::l) (n-1)
          in
          aux [] n
        in
        let goal = app goal vars in
        prove sons
          temperatures (depth+1)
          ~local ~timestamp:(timestamp + n) ~level ~success ~failure ~constraints goal

    (* Local quantification *)
    | Binder (Nabla,n,goal) ->
        let goal = lambda n goal in
        let vars =
          let rec aux l = function
            | n when n <= 0 -> l
            | n -> aux ((nabla (local + n))::l) (n-1)
          in
          aux [] n
        in
        let goal = app goal vars in
        prove sons
          temperatures (depth+1)
          ~local:(local + n) ~timestamp ~level ~success ~failure ~constraints goal

    (* Existential quantification *)
    | Binder (Exists,n,goal) ->
        let goal = lambda n goal in
        let timestamp,vars = match level with
          | Zero ->
              let rec aux l = function
                | n when n <= 0 -> l
                | n -> aux ((fresh
                               ~lts:local Eigen ~ts:(timestamp + n))::l) (n-1)
              in
              timestamp + n,aux [] n
          | One ->
              let rec aux l = function
                | n when n <= 0 -> l
                | n -> aux ((fresh
                               ~lts:local Logic ~ts:timestamp)::l) (n-1)
              in
              timestamp,aux [] n
        in
        let goal = app goal vars in
        prove sons temperatures (depth+1) ~local ~timestamp ~level ~constraints
          ~success ~failure goal

    | App (hd,goals) ->
        let goals = List.map Ndcore.Norm.hnorm goals in
        begin match observe hd with
          (* Checking equivariance between terms *)
          | Var v when v == Logic.var_check_eqvt ->
              let a,b = match goals with [a;b] -> a,b | _ -> invalid_goal () in
              let a = Ndcore.Norm.deep_norm a in
              let b = Ndcore.Norm.deep_norm b in
              if (eqvt a b) then success timestamp failure else failure ()

          (* Proving a negation-as-failure *)
          | Var v when v == Logic.var_not ->
              prove_not goals

          (* Proving if-then-else *)
          | Var v when v == Logic.var_ite ->
              prove_ite goals

          (* Proving abstract-predicate *)
          | Var v when v == Logic.var_abspred ->
              prove_abstract goals

          (* Checking rigidity assumption *)
          | Var v when v == Logic.var_assert_rigid ->
             let a = match goals with [a] -> a | _ -> invalid_goal () in
             let a = Ndcore.Norm.deep_norm a in
             let vars =
               if level = Zero then eigen_vars [a] else logic_vars [a]
             in
             begin match vars with
               | [] -> success timestamp failure
               | _ -> raise Variable_leakage
             end

          (* proving cut predicate *)
          | Var v when v == Logic.var_cutpred ->
             let a = match goals with [a] -> a | _ -> invalid_goal () in
             let a = Ndcore.Norm.deep_norm a in
             let state = save_state () in
             prove sons
               temperatures (depth+1)
               ~level ~local ~timestamp ~failure a
               ~constraints
               ~success:(fun ts k -> success ts (fun () ->
                                                   restore_state state ;
                                                   failure ()) )

          (* Proving distinct-predicate *)
          | Var v when v == Logic.var_distinct ->
              prove_distinct goals

          (* Input *)
          | Var v when v == Logic.var_read ->
              let read_fun () = !System.read_term () in
              begin match System.read read_fun goals with
                | None -> failure ()
                | Some goal ->
                    prove sons
                      temperatures (depth+1)
                      ~level ~local ~timestamp ~failure ~success ~constraints
                      goal
              end

          | Var v when v == Logic.var_fread ->
              let read_fun lexbuf () = !System.fread_term lexbuf () in
              begin match System.fread read_fun goals with
                | None -> failure ()
                | Some goal ->
                    prove sons
                      temperatures (depth+1)
                      ~level ~local ~timestamp ~failure ~success ~constraints
                      goal
              end

          (* Opening file for input *)
          | Var v when v == Logic.var_fopen_in ->
              assert_level_one level ;
              if (System.fopen_in goals) then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fclose_in ->
              assert_level_one level ;
              if (System.fclose_in goals) then success timestamp failure
              else failure ()

          (* Output *)
          | Var v when v == Logic.var_print ->
              let print_fun t =
                IO.Output.printf "%a" Ndcore.Pprint.pp_term t ;
                true
              in
              if System.print print_fun goals
              then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_println ->
              let print_fun t =
                IO.Output.printf "%a@\n" Ndcore.Pprint.pp_term t ;
                true
              in
              if System.print print_fun goals
              then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_printstr ->
              let print_fun t = match observe t with
                | QString s -> IO.Output.printf "%s" s ; true
                | _ -> false
              in
              if System.print print_fun goals
              then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fprint ->
              let print_fun fmt t =
                IO.Output.fprintf ~formatter:fmt "%a" Ndcore.Pprint.pp_term t ;
                true
              in
              if System.fprint print_fun goals
              then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fprintln ->
              let print_fun fmt t =
                IO.Output.fprintf ~formatter:fmt "%a@\n" Ndcore.Pprint.pp_term t ;
                true
              in
              if System.fprint print_fun goals
              then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fprintstr ->
              let print_fun fmt t = match observe t with
                | QString s -> IO.Output.fprintf ~formatter:fmt "%s" s ; true
                | _ -> false
              in
              if System.fprint print_fun goals
              then success timestamp failure
              else failure ()

          (* Opening file for output *)
          | Var v when v == Logic.var_fopen_out ->
              assert_level_one level ;
              if (System.fopen_out goals) then success timestamp failure
              else failure ()

          | Var v when v == Logic.var_fclose_out ->
              assert_level_one level ;
              if (System.fclose_out goals) then success timestamp failure
              else failure ()

          (* Check for definitions *)
          | Var v ->
              let temperature,temperatures =
                try List.assq v temperatures,List.remove_assq v temperatures
                with Not_found -> Unfrozen,temperatures
              in
              prove_atom hd goals (v,temperature,temperatures)

          (* Invalid goal *)
          | Lam _ | App _ | Susp _ -> raise NonNormalTerm
          | _ -> invalid_goal ()
        end

    (* Failure *)
    | Susp _ -> raise NonNormalTerm
    | _ -> invalid_goal ()

(* Wrap prove with sanity checks. *)
let prove ~success ~failure ~constraints ~timestamp ~local g =
  let s0 = save_state () in
  let success ts k =
    assert (Stack.is_empty dependency_stack) ;
    success ts k
  in
  let failure () =
    assert (Stack.is_empty dependency_stack) ;
    assert (s0 = save_state ()) ;
    failure ()
  in
  try
    prove System.root_atoms
      [] 0
      ~success ~failure ~constraints ~level:One ~timestamp ~local g
  with e ->
    clear_dependency_stack () ;
    restore_state s0 ;
    raise e
