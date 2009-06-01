(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)
module Tacticals
  (Param : Firstordertypes.ParamSig)
  (FOT : Firstordertypes.TypesSig)
  (O : Output.Output) =
struct
  module FOA = Firstorderabsyn
  open FOT
  
  type tactic = (FOT.sequent, FOT.proof) Logic.tactic
  type tactical = (FOT.session, tactic) Logic.tactical

  (********************************************************************
  *Tacticals:
  ********************************************************************)
  
  (*  Constructs a module containing the 'generic' tacticals (like
      then, orelse, etc.) To do so we must generate a small signature
      containing the relevant types, because we can't pass the
      current module itself. *)    
  module FirstorderSig =
  struct
    type logic_session = FOT.session
    type logic_sequent = FOT.sequent
    type logic_proof = FOT.proof
  end  
  module G = Logic.GenericTacticals (FirstorderSig) (O)
  
  (********************************************************************
  *genericTacticals
  ********************************************************************)
  let genericTacticals = G.tacticals

  (********************************************************************
  *orElseTactical:
  * Exported for easy access in firstorder.ml; might be a bad idea.
  ********************************************************************)
  let orElseTactical t1 t2 =
    fun session args ->
      G.orElseTactical (t1 session args) (t2 session args)

  (********************************************************************
  *copyFormula:
  * Copies a formula's eigen variables. Used before performing eqL.
  ********************************************************************)
  let copyFormula ?(copier=(Term.copy_eigen () ~passive:false)) (Formula(i,f)) =
    let copyTerm t = copier t in
    let rec copyFormula () = FOA.mapFormula copyFormula copyTerm in
    (Formula(i,(copyFormula ()).FOA.polf f))

  (********************************************************************
  *handleNablas:
  * Given a formula found with a particular context level, makes it
  * into a formula at context level 0 by eliminating nablas via
  * abstraction.
  ********************************************************************)
  let rec handleNablas context f =
    let rec handle context f =
      if context = 0 then
        f
      else
        let (ann, _) = f in
        let v = Term.nabla context in
        let abstraction =
          FOA.AbstractionFormula(
            "invariant_n" ^ (string_of_int context),
            FOA.AbstractionBody(
              (FOA.abstractVarWithoutLambdas v).FOA.polf
                (handle (context - 1) f)))
        in
        (ann, FOA.QuantifiedFormula(FOA.Nabla, abstraction))
    in
    if Properties.getBool "firstorder.fix-nabla-induction" then
      (handle context f)
    else
      f

  (********************************************************************
  *makeProofBuilder ruleName ~b:bound_vars ~p:rule_params ~f:formula seq:
  * Makes a proof builder for a simple inference rule.  Given the name
  * of the inference rule ('rule'), constructs a function that takes a
  * list of the proofs (strings) of the arguments (arg1...argN) to the
  * inference rule and returns a proof of the rule that can be printed
  * in XML form easily.
  ********************************************************************)
  let makeProofBuilder name ?(b=[]) ?(p=[]) ?f seq = fun proofs ->
    { rule = name ; params = p ; bindings = b ; formula = f ; sequent = seq ;
      subs = proofs }

  (********************************************************************
  *findFormula:
  * Given a template and a list of formulas F, returns the first formula
  * that matches the template along with its context in F.
  ********************************************************************)
  let findFormula pattern formulas =
    let rec find front formulas =
      match formulas with
        [] ->
          let () = O.debug "Firstorder.findFormula: not found.\n" in
          None
      | (Formula(_,formula) as f)::fs ->
          if FOA.matchFormula pattern formula then
            let () =
              O.debug ("Firstorder.findFormula: found: " ^
                       (string_of_formula f ^ ".\n"))
            in
              Some(f, List.rev front, fs)
          else
            find (f::front) fs
    in
      find [] formulas

  (********************************************************************
  *matchLeft, matchRight:
  * Given a pattern and a sequent, finds the first element on the left
  * (or right) that matches the pattern, and returns a tuple with:
  *   the matching formula
  *   the before and after of the left or right
  *   the whole left
  *   the whole right
  ********************************************************************)
  let matchLeft pattern after sequent =
    let lhs = match after with Some a -> a | None -> sequent.lhs in
    let rhs = sequent.rhs in
    let result = findFormula pattern lhs in
    match result with
      Some(f,before,after) -> Some(f,before,after,lhs,rhs)
    | None -> None

  let matchRight pattern after sequent =
    let lhs = sequent.lhs in
    let rhs = match after with Some a -> a | None -> sequent.rhs in
    let result = findFormula pattern rhs in
    match result with
      Some(f,before,after) -> Some(f,before,after,lhs,rhs)
    | None -> None

  (********************************************************************
  *makeTactical:
  * Given a matcher and a tactic, creates a tactical that applies
  * the given tactic to the first formula in the sequent that matches
  * the tactic.  If the application fails, it finds the next formula.
  * If the application succeedes, the whole tactical succeeds. If none
  * match, it fails.
  ********************************************************************)
  let makeTactical name matcher tactic session =
    let tactic' = fun sequent sc fc ->
      let sc' ?b formula k s =
        sc s (makeProofBuilder name ~f:formula sequent) k
      in
      let rec fc' left right () =
        match (matcher right sequent) with
          Some(f, left', right', lhs, rhs) ->
            let left'' = left @ left' in
            let zip l = (left'' @ l @ right') in
            let fc'' () =
              fc' (left'' @ [f]) (Some right') ()
            in
              tactic session sequent f zip lhs rhs (sc' f) fc''
        | None ->
            fc ()
      in
        fc' [] None ()
    in
      G.makeTactical tactic'

  (********************************************************************
  *makeGeneralTactical:
  * Given the name of a tactic, a matcher constructor (either matchLeft or
  * matchRight), a default template for use if none is specified, and
  * a tactic, finds a formula to operate on using the matcher and applies
  * the tactic.
  *
  * The tactic passed to makeGeneralTactical should be a function that
  * takes the session, sequent, the matched formula, a zipper, the left
  * and right sides in their entirety, a success continuation that takes
  * a continue continuation (see logic.mli) and a list of new sequents,
  * and a failure continuation (see logic.mli).
  ********************************************************************)
  let makeGeneralTactical name (matchbuilder, default) tactic =
    fun session args ->
      (*  If no default template was specified and there is no argument
          template then bail. *)
      if default = "" && Listutils.empty args then
        (G.invalidArguments (name ^ ": incorrect number of arguments."))
      else
      
      let defaultPattern = parsePattern default in
      
      if Option.isSome defaultPattern then
        let defaultPattern = Option.get defaultPattern in
        match args with
            [] ->
              (makeTactical name (matchbuilder defaultPattern) tactic session)
          | Absyn.String(s)::[] ->
              let pattern = parsePattern s in
              if (Option.isSome pattern) then
                let pattern = Option.get pattern in
                if not (FOA.matchPattern defaultPattern pattern) then
                  G.invalidArguments
                    (name ^ ": pattern does not match default pattern")
                else
                  makeTactical name (matchbuilder pattern) tactic session
              else
                (G.invalidArguments (name ^ ": invalid pattern"))
          | _ -> (G.invalidArguments (name ^ ": incorrect number of arguments"))
      else
        (G.invalidArguments (name ^ ": invalid default pattern."))

  
  (********************************************************************
  *makeSimpleTactical:
  * Given the name of a tactic, a matcher constructor (either matchLeft or
  * matchRight), a default template for use if none is specified, and
  * a tactic, finds a formula to operate on using the matcher and applies
  * the tactic.
  *
  * The tactic passed to makeSimpleTactical should be a function that
  * takes the session, sequent, the matched formula, a zipper, the left
  * and right sides in their entirety, a success continuation that takes
  * a list of new sequents, and a failure continuation (see logic.mli).
  *
  * This function should be used only for simple inference rules as it
  * interacts subtly with backtracking by not allowing for a modified
  * continue continuation as makeGeneralTactical does.
  ********************************************************************)
  let makeSimpleTactical name (matchbuilder, defaulttemplate) tactic =
    let tactic' session seq f zip lhs rhs sc fc =
      tactic session seq f zip lhs rhs (sc fc) fc
    in
    makeGeneralTactical name (matchbuilder, defaulttemplate) tactic'
  
  (** {1 Rules of the logic} *)

  (** Utility for the atomic initial rule, looking for (p params) in some side
    * of a sequent. *)
  let atomicInit i p params sc fc =
    let rec attempts = function
      | [] -> fc ()
      | Formula(i',(_,FOA.ApplicationFormula(FOA.AtomicFormula p',params')))
        ::formulas ->
          if p=p' && (i.context=i'.context || not Param.strictNabla) then
            begin match FOA.unifyList FOA.rightUnify params params' with
              | FOA.UnifySucceeded bind ->
                  sc (fun () -> FOA.undoUnify bind ; attempts formulas)
              | FOA.UnifyFailed ->
                  attempts formulas
              | FOA.UnifyError s ->
                  if Properties.getBool "firstorder.debug" then
                    O.error (s ^ ".\n");
                  attempts formulas
            end
          else
            attempts formulas
      | _::formulas -> attempts formulas
    in
      attempts

  (* This is currently rather weak. Comparing the bodies will eventually be
   * needed, but implies using Term.eq for the leafs. *)
  let fixpointEq p p' = match p,p' with
    | FOA.FixpointFormula (f,name,_,_), FOA.FixpointFormula (f',name',_,_) ->
        f = f' && name = name'
    | _ -> false

  let fixpointInit i p params sc fc =
    let rec attempts = function
      | [] -> fc ()
      | Formula(i',(_,FOA.ApplicationFormula(p',params')))::formulas ->
          if fixpointEq p p' &&
             (i.context=i'.context || not Param.strictNabla) then
            begin match FOA.unifyList FOA.rightUnify params params' with
              | FOA.UnifySucceeded bind ->
                  sc (fun () -> FOA.undoUnify bind ; attempts formulas)
              | FOA.UnifyFailed ->
                  attempts formulas
              | FOA.UnifyError s ->
                  if Properties.getBool "firstorder.debug" then
                    O.error (s ^ ".\n");
                  attempts formulas
            end
          else
            attempts formulas
      | _::formulas -> attempts formulas
    in
    attempts

  (********************************************************************
  *abs_of_pred:
  * eta-expand (mu B) which is a predicate into (x..\ mu B x) which is
  * an abstraction.
  ********************************************************************)
  let abs_of_pred arity pol pred =
    let args' =
      Listutils.mapn
        (fun _ -> Term.fresh ~name:"*eta*" ~lts:0 ~ts:0 Term.Constant)
        arity
    in

    let f' = FOA.AbstractionBody(pol,FOA.ApplicationFormula(pred, args')) in


    List.fold_right (fun t -> (FOA.abstractVar t).FOA.abstf) args' f'

  (********************************************************************
  *unfoldFixpoint:
  ********************************************************************)
  let unfoldFixpoint rulename pol pred arity args mkseq sc fc =
    let body =
      match pred with
        | FOA.FixpointFormula (_,_,_,body) -> body
        | _ -> assert false
    in
    let abst = abs_of_pred arity pol pred in
    match (* body (mu body) *)
      (FOA.applyFixpoint abst).FOA.abstf body      
    with
     | Some p' ->
         begin match FOA.fullApply args p' with
           | Some mu' -> (* body (mu body) args *)
               sc rulename (mkseq mu')
           | _ ->
               O.impossible
                 "unable to apply arguments to fixpoint formula.\n" ;
               fc ()
         end
     | None ->
         O.impossible "definition has incorrect arity.\n" ;
         fc ()

  (** Given a body [b], and a (co)invariant [s] as a string, and parameters [t],
    * computes [s t], [s t'] and [b s t']. *)
  let fixpoint_St_St'_BSt' ~session ~lvl ~body ~argnames ~s ~t =
    let rec makeArgs lvl = function
      | [] -> (lvl, [])
      | a::aa ->
          let (lvl', a') = makeUniversalVar a lvl 0 in
          let (lvl'', aa') = makeArgs lvl' aa in
            (lvl'',  a'::aa')
    in
    let (lvl',t') = makeArgs lvl argnames in
      begin match
        FOA.fullApply t s, FOA.fullApply t' s,
        (FOA.applyFixpoint s).FOA.abstf body
      with
        | Some st, Some st', Some bs ->
            begin match FOA.fullApply t' bs with
              | Some bst' -> Some (st,lvl',st',bst')
              | None ->
                  O.impossible
                    "unable to apply arguments to B(S).\n";
                  None
            end
        | _ ->
            O.error "invariant has incorrect arity.\n";
            None
      end

  (********************************************************************
  *unfoldingProgresses:
  * Given a list of definition arguments (which consist of argument
  * names and booleans indicating whether the definition makes progress
  * on that argument) and a list of actual arguments (terms), returns
  * whether or not a rigid term is passed as an argument on which the
  * definition progresses.
  ********************************************************************)
  let unfoldingProgresses side =
    let rec rigid t = match Term.observe (Norm.hnorm t) with
      | Term.Lam (_,t) -> rigid t
      | Term.App (t,_) -> rigid t
      | Term.Var v when v.Term.tag = Term.Constant -> true
      | _ -> false
    in
      fun args params ->
        List.exists2
          (fun (_,b) p -> b = FOA.Progressing && rigid p)
          args params
        &&
        match side with
          | `Left ->
              let evars =
                Term.get_vars
                  (fun v -> v.Term.tag = Term.Logic)
                  params
              in
                evars = []
          | `Right -> true

  type internal_sc =
    ?k:(unit -> unit) -> ?b:(Term.term list) -> string -> sequent list -> unit

  let initial_progressing_bound = Some 10

  (** [intro] will be our do-it-all tactic: it takes a matcher, and applies
    * a rule with a matched formula as the active one.
    *
    * The only problem with that approach is that sometimes, there are several
    * choices for the same formula, e.g. with an additive disjunction or a fixed
    * point. The [arg] is there to specify these choices ("left"/"right").
    *
    * The focusing strategy will have to call it by passing a matcher that looks
    * for a focused or asynchronous, unfrozen formula. It will never pass any
    * [arg]. An example consequence is that [intro] should try both branches of
    * an additive disjunction if no [arg] is passed.
    *
    * The [intro] tactic will be conveniently wrapped in several specialized
    * tactics for the user, using [arg] to force choices. *)
  let intro side matcher session arg =
    (* Propagate the focused flag from f to its subformulas. Meant to be used as
     * part of the zipper. *)
    let propagate (super,_) (Formula(i,(sub,sf))) =
      let ann =
        (* TODO: Make sure that release doesn't break because we automatically
         * release here in case of a delay. Why not treat the delay there
         * anyway... because it would have been overwritten by a propagation. *)
        if super.FOA.control = FOA.Focused &&
          sub.FOA.control <> FOA.Delayed
        then
          { sub with FOA.control = FOA.Focused }
        else
          sub
      in
        Formula(i,(ann,sf))
    in
    (* Apply a rule with its active formula on the left hand-side. *)
    let left seq (Formula(i,f)) zip (sc:internal_sc) fc =
      let propagate = propagate f in
      let zip l = zip (List.map propagate l) in
      match f with
        | _,FOA.BinaryFormula (conn,l,r) ->
            begin match conn with
              | FOA.And ->
                  sc "and_l"
                    [{ seq with lhs = zip [Formula(i,l);Formula(i,r)] }]
              | FOA.Or ->
                  sc "or_l" [
                    { seq with lhs = zip [Formula(i,l)] };
                    { seq with lhs = zip [Formula(i,r)] }
                  ]
              | FOA.Imp ->
                  sc "imp_l" [
                    { seq with lhs = zip [] ; rhs =
                        let l = propagate (Formula (i,l)) in
                          if Param.intuitionistic then
                            [l]
                          else
                            l::seq.rhs } ;
                    { seq with lhs = zip [Formula(i,r)] }
                  ]
            end
        | _,FOA.QuantifiedFormula (FOA.Pi,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',var) = makeExistentialVar hint seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "pi_l" ~b:[var]
                      [{ seq with lvl=lvl' ; lhs = zip [Formula(i,f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula (FOA.Sigma,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',var) = makeUniversalVar hint seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "sigma_l" ~b:[var]
                      [{ seq with lvl=lvl' ; lhs = zip [Formula(i,f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula (FOA.Nabla,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',i',var) = makeNablaVar seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "nabla_l"
                      [{ seq with lvl=lvl' ;
                                  lhs = zip [Formula({ i with context = i'},
                                                     f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula _ -> assert false
        | _,FOA.EqualityFormula _ ->
            (* Copy the equality, then possibly instantiate its variables,
             * these instantiations will be taken into account when copying
             * the rest of the sequent. *)
            let copier = Term.copy_eigen () in
            let copy = List.map (copyFormula ~copier:(copier ~passive:true)) in
              begin match copyFormula ~copier (Formula(i,f)) with
                | Formula(_,(_,FOA.EqualityFormula(t1,t2))) ->
                    (* TODO fully normalize before extracting the vars *)
                    let checks_vars =
                      (* List of eigenvars which instantiation
                       * can silently break llambda unifications
                       * and violate timestamps. *)
                      let ts v =
                        match Term.observe v with
                          | Term.Var v -> v.Term.ts
                          | _ -> assert false
                      in
                      let eigen_id v =
                        match Term.observe v with
                          | Term.Var v when v.Term.tag=Term.Eigen -> v.Term.id
                          | _ -> raise Exit
                      in
                      let eigen =
                        (** Maximum timestamp for logic vars in the sequent. *)
                        let max_ts =
                          let logic =
                            Term.logic_vars
                              (List.concat
                                 (List.map
                                    (fun (Formula (_,f)) ->
                                       FOA.termsPolarized f)
                                    (seq.lhs@seq.rhs)))
                          in
                            List.fold_left max (-1) (List.map ts logic)
                        in
                          List.filter
                            (fun v -> ts v <= max_ts)
                            (Term.eigen_vars [t1;t2])
                      in
                        fun () ->
                          try
                            (* Check that eigen members are still eigenvars. *)
                            let eigen = List.map eigen_id eigen in
                            let rec unicity = function
                              | [] -> ()
                              | a::tl ->
                                if List.exists ((=) a) tl then raise Exit ;
                                unicity tl
                            in
                              unicity eigen ; true
                          with Exit -> false
                    in
                    begin match FOA.leftUnify t1 t2 with
                      | FOA.UnifyFailed ->
                          sc "eq_l" []
                      | FOA.UnifySucceeded bind ->
                          let fc () = FOA.undoUnify bind ; fc () in
                          if checks_vars () then
                            sc "eq_l" ~k:fc [{seq with lhs = copy (zip []) ;
                                                       rhs = copy seq.rhs }]
                          else begin
                            if Properties.getBool "firstorder.debug" then
                              O.error "Something nasty happened \
                                       in LLambda-land!\n" ;
                            fc ()
                          end
                      | FOA.UnifyError s ->
                          if Properties.getBool "firstorder.debug" then
                            O.error (s ^ ".\n");
                          fc ()
                    end
                | _ -> assert false
              end
        | pol,FOA.ApplicationFormula (p,args) ->
            let arity = List.length args in
            (* Induction steps consume the fixed point which makes it impossible
             * to do them infinitly many times.
             * On the other hand, fixed point unfoldings should be bounded.
             * We make a distinction between progressing and non-progressing
             * unfoldings: both can be done infinitely many times, but in
             * pratice, progressing unfoldings are "less dangerous" and "more
             * informative".
             * Before we used to consume a so-called async_bound for every
             * asynchronous unfolding, which was always progressing.
             * Now the progressing_bound is decreased for any progressing
             * unfolding while the normal bound is decreased otherwise. *)
            let unfoldFixpoint ruleName name args body argnames sc fc =
              let i,bound =
                if unfoldingProgresses `Left argnames args then
                  { i with
                        progressing_bound = updateBound i.progressing_bound },
                  seq.bound
                else
                  i, updateBound seq.bound
              in
              let pol =
                { pol with FOA.control =
                    if pol.FOA.control = FOA.Focused then
                      FOA.Normal
                    else
                      pol.FOA.control }
              in
              let seq = { seq with bound = bound } in
              let mkseq f =
                [{ seq with lhs = zip [Formula(i,f)] }]
              in
              if outOfBound seq.bound || outOfBound i.progressing_bound then
                fc ()
              else
                unfoldFixpoint ruleName pol p arity args mkseq sc fc
            in
            begin match p with
              | FOA.FixpointFormula (FOA.CoInductive,name,argnames,body) ->
                  assert (arity = List.length argnames) ;
                  (* This is synchronous. *)
                  begin match arg with
                    | Some "unfold" ->
                        unfoldFixpoint "nu_l" name args body argnames sc fc
                    | Some "init" ->
                        if pol.FOA.polarity = FOA.Positive then fc () else
                        fixpointInit i p args
                          (fun k -> sc "init_nu" [] ~k)
                          fc seq.rhs
                    | None ->
                        let fc () =
                          unfoldFixpoint "nu_l"
                            name args body argnames sc fc
                        in
                          if pol.FOA.polarity = FOA.Positive then fc () else
                            fixpointInit i p args
                              (fun k -> sc "init_nu" [] ~k)
                              fc
                              seq.rhs
                    | s -> assert false
                  end
              | FOA.FixpointFormula (FOA.Inductive,name,argnames,body) ->
                  let onlynames = List.map fst argnames in
                  assert (arity = List.length argnames) ;
                  (* This is asynchronous.
                   * If [arg] is "unfold", do mu_l, otherwise treat it as an
                   * invariant, otherwise infer an invariant. *)
                  begin match arg with
                    | Some "unfold" ->
                        unfoldFixpoint "mu_l" name args body argnames sc fc
                    | Some s ->
                        let s = parseInvariant session.definitions s in
                        if Option.isSome s then
                          let s = Option.get s in
                          begin match
                            fixpoint_St_St'_BSt'
                              ~session ~lvl:seq.lvl
                              ~body ~argnames:onlynames ~s ~t:args
                          with
                            | Some (st,lvl',st',bst') ->
                                let i' = { i with context = 0 } in
                                let st   = Formula(i,st) in
                                let st'  = Formula(i',st') in
                                let bst' = Formula(i',bst') in
                                let seqs =
                                  [{ seq with lhs = zip [st] } ;
                                  { seq with lvl = lvl' ;
                                             lhs = [bst'] ; rhs = [st'] }]
                                in
                                sc "induction" seqs
                            | None -> fc ()
                          end
                        else
                          fc ()
                    | None ->
                        if i.context <> 0 then
                          O.warning
                            "induction with non-empty generic context; \
                             use 'abstract' first for better results.\n";

                        let rhs =
                          (* ... |- H1,..,Hn becomes H1\/..\/Hn *)
                          let rec s = function
                            | [] -> assert false
                            | [Formula(i,f)] -> handleNablas i.context f
                            | (Formula(i,pf))::l -> 
                                { FOA.defaultAnnotation
                                  with FOA.polarity = FOA.Negative },
                                FOA.BinaryFormula
                                  (FOA.Or, handleNablas i.context pf, s l)
                          in s seq.rhs
                        in
                        let lrhs =
                          (* H1, ..., Hn |- rhs becomes H1 => .. => Hn => rhs *)
                          let rec s = function
                            | [] -> rhs
                            | Formula(i,f')::l -> 
                                let frozens =
                                  Properties.getString "firstorder.frozens"
                                in
                                if frozens = "ignore" &&
                                  (fst f').FOA.freezing = FOA.Frozen then
                                  (s l)
                                else
                                  let ann = 
                                    { FOA.defaultAnnotation with
                                      FOA.polarity = FOA.Negative }
                                  in
                                  let f'' =
                                    if frozens = "thaw" then
                                      FOA.changeAnnotation FOA.thaw f'
                                    else
                                      f'
                                  in
                                  handleNablas i.context
                                    (ann, FOA.BinaryFormula(FOA.Imp, f'', s l))
                          in
                          s (zip [])
                        in
                        let fresh n =
                          (* The details don't matter, we'll abstract that
                           * out soon enough. We only need that the fresh vars
                           * are not eigen. *)
                          Term.fresh ~name:n ~ts:0 ~lts:0 Term.Logic
                        in
                        let fv,eigenvars,elrhs =
                          (* Essentially form
                           *   fv1\..fvn\ fv1=arg1 => .. fvn=argn => lrhs.
                           * We avoid creating trivial equalities on eigenvars
                           * and keep track of those in [subst] instead. *)
                          let is_eigen x = match Term.observe x with
                            | Term.Var { Term.tag=Term.Eigen } -> true
                            | _ -> false
                          in
                          (* We need to copy eigenvars in our invariant
                           * since we'll perform substitutions on them. *)
                          let tm_copy = Term.copy_eigen () in
                          let rec add_equalities names args =
                            match names,args with
                              | [],[] -> [],lrhs 
                              | name::names,arg::args ->
                                  let fv,f = add_equalities names args in
                                  let v = fresh name in
                                    (* Eigenvars might have changed..
                                     * but then they would have been changed
                                     * into our fresh [fv] Logic variables.
                                     * So there's no need to apply the subst
                                     * (by copying) to check that the arg
                                     * is (still) an eigenvar. *)
                                    if i.context=0 && is_eigen arg then
                                      let arg = tm_copy ~passive:false arg in
                                        Term.bind arg v ;
                                        v::fv, f
                                    else
                                      v::fv,
                                      FOA.negativeFormula
                                        (FOA.BinaryFormula
                                           (FOA.Imp,
                                            handleNablas i.context
                                              (FOA.positiveFormula
                                                (FOA.EqualityFormula (v,arg))),
                                            f))
                              | _ -> assert false
                          in
                          let fv,f =
                            add_equalities onlynames (List.rev args)
                          in
                          (* Finally apply the substitutions everywhere. *)
                          let tm_copy = tm_copy ~passive:true in
                          let f =
                            let rec copyFormula () =
                              FOA.mapFormula copyFormula tm_copy
                            in
                              (copyFormula ()).FOA.polf f
                          in
                          let eigenvars =
                            (* We won't get the eigenvars
                             * that have been instantiated to the logic
                             * variables standing for the arguments [fv]. *)
                            Term.eigen_vars (FOA.termsPolarized f)
                          in
                            fv, eigenvars, f
                        in
                        (* Abstract universally over eigenvariables. *)
                        let aelrhs =
                          List.fold_left
                            (fun f v ->
                               FOA.negativeFormula
                                 (FOA.QuantifiedFormula
                                    (FOA.Pi, (FOA.abstractVar v).FOA.polf f)))
                            elrhs eigenvars
                        in
                        
                        (*  Thawing.  *)
                        let aelrhs' =
                          if Properties.getBool "firstorder.thawasync" then
                            modifyFormulaAnnotations unfreezeModifier aelrhs
                          else
                            aelrhs
                        in
                        
                        let aelrhs' =
                          if
                            Properties.getBool "firstorder.induction-unfold"
                          then
                            let f = FOA.ApplicationFormula (p,List.rev fv) in
                            let f = { FOA.defaultAnnotation with
                                        FOA.polarity = FOA.Positive ;
                                        FOA.freezing = FOA.Frozen },f in
                              FOA.positiveFormula
                                (FOA.BinaryFormula(FOA.And,f,aelrhs'))
                          else
                            aelrhs'
                        in
                        (* Abstract out the fv1..fvn. *)
                        let invariant =
                          List.fold_left
                            (fun f v -> (FOA.abstractVar v).FOA.abstf f)
                            (FOA.AbstractionBody aelrhs')
                            fv
                        in
                        let _,lvl',st',bst' =
                          Option.get (fixpoint_St_St'_BSt'
                                        ~session ~lvl:seq.lvl ~body
                                        ~argnames:onlynames
                                        ~s:invariant ~t:args)
                        in
                        let seq =
                          { seq with bound = updateBound seq.bound }
                        in
                        let i' =
                          { (* i with *) context = 0 ;
                            progressing_bound = initial_progressing_bound }
                        in
                        if outOfBound seq.bound then fc () else
                          let seq' = 
                            { seq with lvl = lvl' ;
                                 lhs = [Formula (i',bst')] ;
                                 rhs = [Formula (i',st')] }
                          in
                          (* TODO: check the other premise so the proof is complete
                           *  (in the proof builder, to save work).  *)
                          sc "induction" [seq']
                  end
              | FOA.AtomicFormula p ->
                  if p = "false" then sc "false" [] else (* TODO: false should be special *)
                  if p = "true" then
                    let seq' = { seq with lhs = zip [] } in
                    sc "true" [seq']
                  else
                  if pol.FOA.polarity = FOA.Positive then fc () else
                    atomicInit i p args (fun k -> sc "init" [] ~k) fc seq.rhs
              | FOA.DBFormula _ -> assert false
            end
    in

    (* Apply a rule with its active formula on the right hand-side. *)
    let right seq (Formula(i,f)) zip (sc:internal_sc) fc =
      let propagate = propagate f in
      let zip l = zip (List.map propagate l) in
      match f with
        | _,FOA.BinaryFormula (conn,l,r) ->
            begin match conn with
              | FOA.Or ->
                  if not Param.intuitionistic then
                    sc "or_r"
                      [{ seq with rhs = zip [Formula(i,l);Formula(i,r)] }]
                  else
                    let left  = { seq with rhs = [propagate (Formula(i,l))] } in
                    let right = { seq with rhs = [propagate (Formula(i,r))] } in
                      begin match arg with
                        | Some s when s <> "" ->
                            if s.[0] = 'l' then
                              sc "left" [left]
                            else
                              sc "right" [right]
                        | _ ->
                            sc "left" [left] ~k:(fun () -> sc "right" [right])
                      end
              | FOA.And ->
                  sc "and_r" [
                    { seq with rhs = zip [Formula(i,l)] };
                    { seq with rhs = zip [Formula(i,r)] }
                  ]
              | FOA.Imp ->
                  let l = propagate (Formula (i,l)) in
                  sc "imp_r" [ { seq with lhs = seq.lhs@[l] ;
                                          rhs = zip [Formula(i,r)] } ]
            end
        | _,FOA.QuantifiedFormula (FOA.Pi,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',var) = makeUniversalVar hint seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "pi_r" ~b:[var]
                      [{ seq with lvl=lvl' ; rhs = zip [Formula(i,f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula (FOA.Sigma,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',var) = makeExistentialVar hint seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "sigma_r" ~b:[var]
                      [{ seq with lvl=lvl' ; rhs = zip [Formula(i,f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula (FOA.Nabla,
              (FOA.AbstractionFormula(hint,FOA.AbstractionBody _) as f)) ->
            let (lvl',i',var) = makeNablaVar seq.lvl i.context in
              begin match FOA.fullApply [var] f with
                | Some f' ->
                    sc "nabla_r"
                      [{ seq with
                         lvl = lvl' ;
                         rhs = zip [Formula({ i with context = i'},f')] }]
                | _ -> fc ()
              end
        | _,FOA.QuantifiedFormula _ -> assert false
        | _,FOA.EqualityFormula (t1,t2) ->
            begin match FOA.rightUnify t1 t2 with
              | FOA.UnifySucceeded(bind) ->
                  let fc' () = FOA.undoUnify bind ; fc () in
                    sc "eq_r" ~k:fc' []
              | FOA.UnifyFailed -> fc ()
              | FOA.UnifyError(s) ->
                  if Properties.getBool "firstorder.debug" then
                    O.error (s ^ ".\n");
                  fc ()
            end
        | pol,FOA.ApplicationFormula (p,args) ->
            let arity = List.length args in
            (* TODO factor this out, I've cut/pasted too many times *)
            let unfoldFixpoint ruleName name args body argnames sc fc =
              let i,bound =
                if (unfoldingProgresses `Right argnames args) then
                  { i with
                        progressing_bound = updateBound i.progressing_bound },
                  seq.bound
                else
                  i, updateBound seq.bound
              in
              let pol =
                { pol with FOA.control =
                    if pol.FOA.control = FOA.Focused then
                      FOA.Normal
                    else
                      pol.FOA.control }
              in
              let seq = { seq with bound = bound } in
              let mkseq f =
                [{ seq with rhs = zip [Formula(i,f)] }]
              in
              if outOfBound seq.bound || outOfBound i.progressing_bound then
                fc ()
              else
                unfoldFixpoint ruleName pol p arity args mkseq sc fc
            in
            begin match p with
              | FOA.FixpointFormula (FOA.Inductive,name,argnames,body) ->
                  assert (arity = List.length argnames) ;
                  (* This is synchronous. *)
                  begin match arg with
                    | Some "unfold" ->
                        unfoldFixpoint "mu_r" name args body argnames sc fc
                    | Some "init" ->
                        if pol.FOA.polarity = FOA.Negative then fc () else
                        fixpointInit i p args
                          (fun k -> sc "init_mu" [] ~k)
                          fc seq.lhs
                    | None ->
                        let fc () =
                          unfoldFixpoint "mu_r"
                            name args body argnames sc fc
                        in
                          if pol.FOA.polarity = FOA.Negative then fc () else
                            fixpointInit i p args
                              (fun k -> sc "init_mu" [] ~k)
                              fc
                              seq.lhs
                    | s -> O.error "Invalid parameter." ; fc ()
                  end
              | FOA.FixpointFormula (FOA.CoInductive,name,argnames,body) ->
                  let onlynames = List.map fst argnames in
                  assert (arity = List.length argnames) ;
                  (* This is asynchronous.
                   * If [arg] is "unfold", do nu_r, otherwise treat it as an
                   * invariant, otherwise infer an invariant. *)
                  begin match arg with
                    | Some "unfold" ->
                        unfoldFixpoint "nu_r" name args body argnames sc fc
                    | Some s ->
                        let s = parseInvariant session.definitions s in
                        if Option.isSome s then
                          let s = Option.get s in
                          begin match
                            fixpoint_St_St'_BSt'
                              ~session ~lvl:seq.lvl
                              ~body ~argnames:onlynames ~s ~t:args
                          with
                            | Some (st,lvl',st',bst') ->
                                let i'   = { i with context = 0 } in
                                let st   = Formula(i,st) in
                                let st'  = Formula(i',st') in
                                let bst' = Formula(i',bst') in
                                let seqs =
                                  [{ seq with rhs = zip [st] } ;
                                  { seq with lvl = lvl' ;
                                             lhs = [st'] ; rhs = [bst'] }]
                                in
                                sc "induction" seqs
                            | None -> fc ()
                          end
                        else
                          fc ()
                    | None ->
                        if i.context <> 0 then
                          O.warning
                            "induction or coinduction with non-zero \
                             generic contexts; \
                             use 'abstract' first to avoid this problem.\n";
                        
                        let fresh n =
                          Term.fresh ~name:n ~ts:0 ~lts:0 Term.Eigen
                        in
                        (* For now, don't treat the right hand-side,
                         * it is useless in the intuitionistic case,
                         * and requires some care for classical logic:
                         * the rhs would have to be negated and put in a big
                         * conjunction in the co-invariant. But the negation is
                         * badly written as A=>false. *)
                        let lrhs =
                          (* Conjunction of the left hand-side. *)
                          let rec s = function
                            | [] ->
                                { FOA.defaultAnnotation with
                                    FOA.polarity = FOA.Positive },
                                FOA.ApplicationFormula
                                  (FOA.AtomicFormula "true", [])
                            | [Formula(i,f)] -> handleNablas i.context f
                            | Formula(i,f)::l ->
                               { FOA.defaultAnnotation with
                                   FOA.polarity = FOA.Positive },
                               FOA.BinaryFormula
                                 (FOA.And, handleNablas i.context f, s l)
                          in
                          s seq.lhs
                        in
                        let fv,elrhs =
                          (* Essentially form
                           * fv1\..fvn\ fv1=arg1 /\ .. fvn=argn /\ lrhs *)
                          let rec e lan la =
                            match lan,la with
                              | [],[] -> [],lrhs 
                              | an::lan,a::la ->
                                  let lv,f = e lan la in
                                  let v = fresh an in
                                    v::lv,
                                    FOA.positiveFormula
                                      (FOA.BinaryFormula
                                         (FOA.And,
                                          handleNablas i.context
                                            (FOA.positiveFormula
                                              (FOA.EqualityFormula (v,a))),
                                          f))
                              |_ -> assert false
                          in
                            e onlynames (List.rev args)
                        in
                        (* Abstract existentially over eigenvariables. *)
                        let getenv =
                          Term.eigen_vars ((FOA.termsPolarized lrhs)@args)
                        in
                        let aelrhs =
                          List.fold_left
                            (fun f v ->
                               FOA.positiveFormula
                                 (FOA.QuantifiedFormula
                                    (FOA.Sigma,
                                     (FOA.abstractVar v).FOA.polf f)))
                            elrhs getenv
                        in
                        (*  Thawing.  *)
                        let aelrhs' =
                          if Properties.getBool "firstorder.thawasync" then
                            modifyFormulaAnnotations unfreezeModifier aelrhs
                          else
                            aelrhs
                        in
                        
                        let aelrhs' =
                          if Properties.getBool "firstorder.coinduction-unfold" then
                            let f = FOA.ApplicationFormula (p,List.rev fv) in
                            let f = { FOA.defaultAnnotation with
                                        FOA.polarity = FOA.Negative ;
                                        FOA.freezing = FOA.Frozen },f in
                              FOA.positiveFormula
                                (FOA.BinaryFormula(FOA.Or,f,aelrhs'))
                          else
                            aelrhs'
                        in
                        (* Abstract out the fv1..fvn. *)
                        let invariant =
                          List.fold_left
                            (fun f v -> (FOA.abstractVar v).FOA.abstf f)
                            (FOA.AbstractionBody aelrhs')
                            fv
                        in
                        let _,lvl',st',bst' =
                          Option.get (fixpoint_St_St'_BSt'
                                        ~session ~lvl:seq.lvl ~body
                                        ~argnames:onlynames
                                        ~s:invariant ~t:args)
                        in
                        let seq =
                          { seq with bound = updateBound seq.bound }
                        in
                        let i' =
                          { (* i with *) context = 0 ;
                            progressing_bound = initial_progressing_bound }
                        in
                          if outOfBound seq.bound then fc () else
                            (*  TODO: check the other premise.  *)
                            sc "coinduction"
                              [{ seq with lvl = lvl' ;
                                 lhs = [Formula(i',st')] ;
                                 rhs = [Formula(i',bst')] }]
                  end
              | FOA.AtomicFormula p ->
                  if p = "true" then sc "true" [] else  (*  TODO: true should be special. *)
                  if pol.FOA.polarity = FOA.Negative then fc () else
                  atomicInit i p args (fun k -> sc "init" [] ~k) fc seq.lhs
              | FOA.DBFormula _ -> assert false
            end
    in

    (* Wrap up: try to find a matched formula, apply a rule on it. *)
    let tactic formTac get_hs = fun sequent sc fc ->
      let rec parse before after =
        match matcher after with
          | None -> fc ()
          | Some (f,before',after) ->
              let before = before @ before' in
              let zip l = before @ l @ after in
              let parse_more () = parse (before @ [f]) after in
                formTac
                  sequent f zip
                  (fun ?(k=parse_more) ?b name sequents ->
                     sc sequents (makeProofBuilder name ?b ~f sequent) k)
                  parse_more
      in
      parse [] (get_hs sequent)
    in
    let left  = tactic left  (fun s -> s.lhs) in
    let right = tactic right (fun s -> s.rhs) in
    match side with
      | `Any -> G.orElseTactical (G.makeTactical left) (G.makeTactical right)
      | `Left -> G.makeTactical left
      | `Right -> G.makeTactical right

  (** Utility for creating matchers easily. TODO: get rid of that, and only
    * use patterns. *)
  let make_matcher test formulas =
    let rec aux acc = function
      | f::tl -> if test f then Some (f,List.rev acc,tl) else aux (f::acc) tl
      | [] -> None
    in
    aux [] formulas

  (* Easy wrapper for tactics without arguments. *)
  let specialize ?arg side default_matcher session args =
    match args with
      | [Absyn.String s] ->
          begin match parsePattern s with
            | Some pattern ->
                intro
                  side (findFormula pattern)
                  session arg
            | None ->
                O.error "invalid pattern" ; fun s sc fc -> fc ()
          end
      | [] -> intro side default_matcher session arg
      | _ ->
          O.error "too many arguments" ; fun s sc fc -> fc ()

  (* Even more wrapping: pass a pattern instead of a matcher.. *)
  let patternTac ?arg side defaultPattern session args =
    match parsePattern defaultPattern with
      | Some (pattern) ->
          specialize ?arg side (findFormula pattern) session args
      | None -> assert false

  (* {1 Specialized basic manual tactics} *)

  let orLeft  = patternTac `Right "_;_" ~arg:"left"
  let orRight = patternTac `Right "_;_" ~arg:"right"
  let orR   = patternTac `Right "_;_" (* tries both in intuitionistic mode *)
  let orL   = patternTac `Left  "_;_"

  let andL = patternTac `Left  "_,_"
  let andR = patternTac `Right "_,_"
  let impL = patternTac `Left  "_=>_"
  let impR = patternTac `Right "_=>_"
  let eqL  = patternTac `Left  "_=_"
  let eqR  = patternTac `Right "_=_"
  let piL  = patternTac `Left  "pi _"
  let piR  = patternTac `Right "pi _"
  let sigmaL = patternTac `Left  "sigma _"
  let sigmaR = patternTac `Right "sigma _"
  let nablaL = patternTac `Left  "nabla _"
  let nablaR = patternTac `Right "nabla _"
  let trueR  = patternTac `Right "true"
  let falseL = patternTac `Left  "false"
  let muL = patternTac `Left  "mu _" ~arg:"unfold"
  let muR = patternTac `Right "mu _" ~arg:"unfold"
  let nuL = patternTac `Left  "nu _" ~arg:"unfold"
  let nuR = patternTac `Right "nu _" ~arg:"unfold"

  let caseTactical session args =
    match args with
        []
      | [Absyn.String(_)] ->
          G.thenTactical
            (muL session args)
            (G.thenTactical
              (G.repeatTactical (orL session []))
              (G.repeatTactical (sigmaL session [])))
      | _ -> G.invalidArguments "case"

  let introsTactical session args =
    match args with
        [] ->
          (G.thenTactical
            (G.repeatTactical (piR session []))
            (G.repeatTactical (impR session [])))
      | _ -> G.invalidArguments "intros"

  let inductionTactical session = function
    | [] -> patternTac `Left "mu _" session []
    | [Absyn.String i] -> patternTac `Left "mu _" ~arg:i session []
    | [Absyn.String i; Absyn.String p] -> patternTac `Left p ~arg:i session []
    | _ -> (fun _ _ fc -> O.error "Invalid arguments.\n" ; fc ())

  let coinductionTactical session = function
    | [] -> patternTac `Right "nu _" session []
    | [Absyn.String i] -> patternTac `Right "nu _" ~arg:i session []
    | [Absyn.String i; Absyn.String p] -> patternTac `Right p ~arg:i session []
    | _ -> (fun _ _ fc -> O.error "Invalid arguments.\n" ; fc ())

  let axiom_atom =
    specialize `Any
      (make_matcher
         (function
            | Formula(_,(_,FOA.ApplicationFormula ((FOA.AtomicFormula _),_))) ->
                true
            | _ -> false))
      ~arg:"init"

  let axiom_mu =
    specialize `Right
      (make_matcher
         (function
            | Formula(_,
                (_,FOA.ApplicationFormula
                    ((FOA.FixpointFormula (FOA.Inductive,_,_,_)),_))) -> true
            | _ -> false))
      ~arg:"init"

  let axiom_nu =
    specialize `Left
      (make_matcher
         (function
            | Formula(_,
                (_,FOA.ApplicationFormula
                    ((FOA.FixpointFormula (FOA.CoInductive,_,_,_)),_))) -> true
            | _ -> false))
      ~arg:"init"
  let axiom s a =
    G.orElseTactical (axiom_atom s a)
      (G.orElseTactical (axiom_mu s a) (axiom_nu s a))

  (** {1 Structural rules} *)

  let contractL =
    let tactic session seq f zip lhs rhs sc fc =
      sc [{seq with lhs = zip [f;f]}]
    in
      makeSimpleTactical "contract_l" (matchLeft, "_") tactic

  let contractR =
    let tactic session seq f zip lhs rhs sc fc =
      sc [{seq with rhs = zip [f;f]}]
    in
      makeSimpleTactical "contract_r" (matchRight, "_") tactic

  let weakL =
    let tactic session seq f zip lhs rhs sc fc =
      sc [{ seq with lhs = zip [] }]
    in
      makeSimpleTactical "weak_l" (matchLeft, "_") tactic

  let weakR =
    let tactic session seq f zip lhs rhs sc fc =
      sc [{ seq with rhs = zip [] }]
    in
      makeSimpleTactical "weak_r" (matchRight, "_") tactic

  let weakTactical session args =
    G.orElseTactical (weakL session args) (weakR session args)

  let contractTactical session args =
    G.orElseTactical (contractL session args) (contractR session args)

  (********************************************************************
  *rotateL, rotateR:
  * Rotate the current sequents to the left or right to change the
  * 'active' sequent (as most rules work on the first sequent only).
  * These don't really have a meaning in the logic.
  ********************************************************************)
  let rotateL session params seqs success failure =
    match seqs with
      | { lhs = [] } :: _ -> failure ()
      | ({ lhs = l::ltl } as seq)::tl ->
          success [{ seq with lhs = ltl@[l] }] tl (fun p -> p) failure
      | [] -> assert false

  let rotateR session params seqs success failure =
    match seqs with
      | ({ rhs = [] })::_ -> failure ()
      | ({ rhs = l::rtl } as seq)::tl ->
          success [{ seq with rhs = rtl@[l] }] tl (fun p -> p) failure
      | [] -> assert false

  (** {1 Meta-rules} *)

  (********************************************************************
  *forceTactical:
  * Toplevel tactical to force unification between two terms.  Note
  * that all that this does is attempt unification; if you specify
  * terms that don't exist in the sequent it could still easily succeed.
  ********************************************************************)
  let forceTactical session args =
    let unifier seqstring term =
      let seqterm = parseTerm seqstring in
      let unterm = parseTerm term in
      if Option.isSome seqterm && Option.isSome unterm then
        let seqterm = Option.get seqterm in
        let unterm = Option.get unterm in

        (* pretactic: simply unifies the two terms. *)
        let pretactic = fun seq sc fc ->
          let result = FOA.rightUnify seqterm unterm in
          match result with
              FOA.UnifySucceeded(s) ->
                let fc' () =
                  (FOA.undoUnify s;
                  fc ())
                in
                let pb = List.hd in
                sc [seq] pb fc'
            | FOA.UnifyFailed -> fc ()
            | FOA.UnifyError(s) ->
                if Properties.getBool "firstorder.debug" then
                  O.error (s ^ ".\n");
                fc ()
        in
        G.makeTactical pretactic
      else
        (if Option.isNone seqterm then O.error "invalid sequent term.\n"
        else ();
        if Option.isNone unterm then O.error "invalid unification term.\n"
        else ();
        G.failureTactical)
    in
    match args with
      | Absyn.String(seqstring)::Absyn.String(term)::[] ->
          unifier seqstring term
      | _ -> (G.invalidArguments "force")

  (********************************************************************
  *cutTactical:
  * Toplevel tactical to cut an arbitrary formula.  Handles both
  * classical and intuitionistic cuts.
  ********************************************************************)
  let cutTactical session args =
    match args with
      | Absyn.String(s)::[] ->
          let f = parseFormula session.definitions s in
            begin match f with
              | None -> O.error "unable to parse lemma.\n" ; G.failureTactical
              | Some f ->
                  let pretactic = fun sequent sc fc ->
                    let f' = makeFormula f in
                    let pb = makeProofBuilder "cut" ~p:["formula",s] sequent in

                    (*  Classical vs. intuitionistic cut  *)
                    let rhs' =
                      if Param.intuitionistic then
                        [f']
                      else
                        sequent.rhs @ [f']
                    in
                    
                    let s1 = { sequent with rhs = rhs' } in
                    let s2 = { sequent with lhs = sequent.lhs @ [f'] } in
                    sc [s1; s2] pb fc
                  in
                    G.makeTactical pretactic
            end
      | _ -> G.invalidArguments "cut"
        
  (** {1 Simplifying strategy}
    * Apply all non-branching invertible rules.
    * Handling units (true/false) requires to work on atoms on both sides. *)
  let simplify_matcher_l = (* TODO use annotations more ? *)
    make_matcher
      (fun (Formula(i,(_,f))) ->
         match f with
           | FOA.BinaryFormula (FOA.And,_,_)
           | FOA.QuantifiedFormula ((FOA.Nabla|FOA.Sigma),_)
           | FOA.EqualityFormula _
           | FOA.ApplicationFormula ((FOA.AtomicFormula _),_) -> true
           | _ -> false)

  let simplify_matcher_r =
    make_matcher
      (fun (Formula(i,(_,f))) ->
         match f with
           | FOA.QuantifiedFormula ((FOA.Nabla|FOA.Pi),_)
           | FOA.BinaryFormula (FOA.Imp,_,_)
           | FOA.EqualityFormula _
           | FOA.ApplicationFormula ((FOA.AtomicFormula _),_) -> true
           | FOA.BinaryFormula (FOA.Or,_,_) -> not Param.intuitionistic
           | _ -> false)

  let simplifyTactical session args = match args with
    | [] ->
        G.repeatTactical
          (G.orElseTactical
            (intro `Left  simplify_matcher_l session None)
            (intro `Right simplify_matcher_r session None))
    | _ -> G.invalidArguments "simplify"

  (** {1 Nabla elimination}
    * The abstract tactic implements the reduction of nabla to liftings. *)
  let abstractTactical session args =
    let rec n_downto_1 = function
      | 0 -> []
      | n -> n :: n_downto_1 (n-1)
    in
    let abstract seq =
      (* Compute the nabla-normal form of every formula in the sequent.
       * it may be more convenient to be able to target a specific one. *)
      let abstract (Formula(i,form)) =
        let tv = List.map Term.nabla (n_downto_1 i.context) in
        let form = (FOA.eliminateNablas tv).FOA.polf form in
        Formula({ i with context = 0 },form)
      in
        { seq with lhs = List.map abstract seq.lhs ;
                   rhs = List.map abstract seq.rhs }
    in
    fun seqs sc fc ->
      match seqs with
        | s::tl -> sc [abstract s] tl (fun proofs -> proofs) fc
        | _ -> fc ()

  (** {1 Debugging} *)
  (********************************************************************
  *examineTactical:
  * Print the AST of the current sequent and succeed.
  ********************************************************************)
  let examineTactical session args = match args with
    | [] ->
        fun sequents sc fc ->
          let seq = List.hd sequents in
          let lhs =
            String.concat "\n  " (List.map string_of_formula_ast seq.lhs)
          in
          let rhs =
            String.concat "\n  " (List.map string_of_formula_ast seq.rhs)
          in
            O.output
              (Printf.sprintf
                 "Sequent AST:\n  %s\n----------------------------\n  %s\n"
                 lhs rhs) ;
            sc [] sequents Logic.idProofBuilder fc
    | _ -> G.invalidArguments "examine"

  (********************************************************************
  *examinePatternTactical:
  * Print the AST of the given pattern and succeed.
  ********************************************************************)
  let examinePatternTactical session args = match args with
    | [Absyn.String(s)] ->
        let p = parsePattern s in
        if Option.isNone p then
          G.invalidArguments "examine"
        else
          fun sequents sc fc ->
            O.output
              (Printf.sprintf "Pattern: %s.\n"
                 (FOA.string_of_pattern_ast (Option.get p))) ;
            sc [] sequents Logic.idProofBuilder fc
    | _ -> G.invalidArguments "examine"

  (********************************************************************
  *cutThenTactical, cutRepeatTactical:
  * Similar to then and repeat, but backtracking only happens over the
  * whole tactical, not over individual tactics within the tactical.
  * The restorer is needed to handle the 'big' backtrack at the end, as
  * the regular functionality (handled by success and failure
  * continuations) isn't invoked.  The point of these tacticals is
  * purely efficiency concerns.
  ********************************************************************)
  let cutThenTactical, cutRepeatTactical =
    let restorer () =
      let s = Term.save_state () in
      fun () -> Term.restore_state s
    in
      G.cutThenTactical restorer,
      G.cutRepeatTactical restorer

  (** {1 Focusing strategy} *)

  (********************************************************************
  *Focusing Strategy:
  * Focusing proceeds as follows:
  *   1. Asynchronous phase:
  *       Here you repeatedly apply asynchronous rules.  Once there
  *       are no more to apply, you move to the freezing phase via the
  *       success continuation.
  *   2. Freezing phase:
  *       Here you make the choice of either freezing or performing
  *       induction on each mu/nu formula.  First, everything gets
  *       frozen.  If this fails, one formula is unfrozen and induction
  *       is tried on it.  If this fails, another is unfrozen (leaving
  *       the previously unfrozen mu/nu unfrozen) and induction is
  *       tried, and so on, until all atoms have been tried.  The
  *       success continuation points to the synchronous phase.
  *   3. Synchronous phase:
  *       Here you run a synchronous phase by first focusing on
  *       something and then repeatedly applying sync_step.  Once
  *       there's nothing left with focus on it, the success continuation
  *       sends you back to the asynchronous phase.
  ********************************************************************)
  
  (** AtomicFormula includes the units (true/false).
    * The Negative polarity is actually never used, and the whole polarity
    * design is too weak as the polarity is set only at toplevel and not on
    * subformulas.
    * Hence, the "polarity" of mu/nu is currently fixed to resp. pos/neg. *)
  
  (** Why we don't use the existing building blocks (then, or, etc.):
    * The problem is that this model hides some information. The asynchronous
    * phase, in presence of fixed points, can produce several alternative lists
    * of subgoals, which might easily have the first goal in common.
    * Using iterate, if you notice that the first goal is impossible, you can
    * just ask async for more data, and get the second alternative, which might
    * have the same impossible first goal.
    * An example of that is (nat x => nat y): the first possibility is to freeze
    * (nat x), all the others produce a subgoal (x=0 => nat y) which is
    * impossible. *)

  (** In automatic mode, intro doesn't really need a session. *)
  let automaticIntro session side matcher = intro side matcher session None

  let isFixpoint = function
    | FOA.ApplicationFormula ((FOA.FixpointFormula _),_) -> true
    | _ -> false

  (** The decide rule focuses on a synchronous formula.
    * This tactic takes a single sequent and its successes are single sequents
    * too.
    * The freeze tactic works the same way, even though it has nothing to do
    * with decide. *)  

  (*  matcher: helper to make a matcher.  *)
  let matcher fl = make_matcher (fun (Formula(i,f)) -> fl f)
  
  (* Find a formula on the right satisfying fr,
  * succeed with the sequent resulting of the application of focus to it.
  * On failure, if b, keep searching on the left with tac_l and fl. *)
  let rec tac_r before after seq sc (fc : unit -> unit) focuser fl fr b =
    match matcher fr after with
      | Some (f,before',after) ->
          let before = before @ before' in
            if Properties.getBool "firstorder.proofsearchdebug" then
              (* TODO this also shows up for the freezing tac *)
              Format.printf "%s@[<hov 2>Focus right@ %s@]\n%!"
                (String.make
                   (match seq.bound with Some b -> max 0 b | None -> 0)
                   ' ')
                (string_of_formula f) ;
            sc
              [{ seq with rhs = before @ [ focuser f ] @ after }]
              (fun () -> tac_r (before@[f]) after seq sc fc focuser fl fr b)
      | None ->
          if b then
            tac_l [] seq.lhs seq sc fc focuser fl fr false
          else
            (fc : unit -> unit) ()

  and tac_l before after seq sc (fc : unit -> unit) focuser fl fr b =
    match matcher fl after with
      | Some (f,before',after) ->
          let before = before @ before' in
          if Properties.getBool "firstorder.proofsearchdebug" then
            Format.printf "%s@[<hov 2>Focus left@ %s@]\n%!"
              (String.make
                 (match seq.bound with Some b -> max 0 b | None -> 0)
                 ' ')
              (string_of_formula f) ;
          sc
            [{ seq with lhs = before @ [ focuser f ] @ after }]
            (fun () -> tac_l (before@[f]) after seq sc fc focuser fl fr b)
      | None ->
          if b then
            tac_r [] seq.rhs seq sc (fc : unit -> unit) focuser fl fr false
          else
            (fc : unit -> unit) ()

  (********************************************************************
  *focusTactic:
  * Builds a tactic that focuses on something.
  ********************************************************************)
  let rec focusTactic session =
    let (pretactic : (sequent, proof) Logic.pretactic) = fun seq sc fc ->
      let pb proofs = 
        let proof = List.hd proofs in
        {proof with params = ("focus", "true")::(proof.params)}
      in
      let sc s k = sc s pb k in
      tac_l
        [] seq.lhs seq sc fc 
        focusFormula
        (fun (a,_) -> a.FOA.control<>FOA.Focused &&
                      a.FOA.polarity=FOA.Negative)
        (fun (a,_) -> a.FOA.control<>FOA.Focused &&
                      a.FOA.polarity=FOA.Positive)
        true
    in
    (G.makeTactical pretactic)

  (********************************************************************
  *focusRightTactic:
  * A tactic for manually focusing on something on the right.
  ********************************************************************)
  and focusRightTactic = fun seq sc fc ->
    tac_r
      [] seq.rhs seq sc fc focusFormula
      (fun (a,_) -> a.FOA.control<>FOA.Focused &&
                    a.FOA.polarity=FOA.Negative)
      (fun (a,_) -> a.FOA.control<>FOA.Focused &&
                    a.FOA.polarity=FOA.Positive)
      true

  (********************************************************************
  *freezeLeftTactic:
  * A tactic for manually freezing something on the left.
  ********************************************************************)
  and freezeLeftTactic = fun seq sc fc ->
    tac_l
      [] seq.lhs seq sc fc freezeFormula
      (fun (a,f) -> a.FOA.freezing=FOA.Unfrozen && isFixpoint f)
      (fun (a,f) -> a.FOA.freezing=FOA.Unfrozen && isFixpoint f)
      true

  (********************************************************************
  *unfocus:
  * The reaction rule removes the focus from an asynchronous formula.
  ********************************************************************)
  and unfocus =
    let matcher_l =
      make_matcher
        (fun (Formula(i,(a,f))) ->
           a.FOA.control=FOA.Focused && a.FOA.polarity=FOA.Positive)
    in
    let matcher_r =
      make_matcher
        (fun (Formula(i,(a,f))) ->
           a.FOA.control=FOA.Focused && a.FOA.polarity=FOA.Negative)
    in
    let unfocus (Formula(i,(a,f))) =
      Formula (i,({ a with FOA.control = FOA.Normal },f))
    in
      (fun seq ->
         match matcher_l seq.lhs with
           | Some (f,before,after) ->
               if Properties.getBool "firstorder.proofsearchdebug" then
               Printf.printf "%sRelease left %s\n%!"
                 (String.make
                    (match seq.bound with Some b -> max 0 b | None -> 0) ' ')
                 (string_of_formula f)
                 (* (xml_of_sequent seq) *);
               Some { seq with lhs = before @ [ unfocus f ] @ after }
           | None ->
               begin match matcher_r seq.rhs with
                 | Some (f,before,after) ->
                     if Properties.getBool "firstorder.proofsearchdebug" then
                     Printf.printf "%sRelease right %s\n%!"
                       (String.make
                          (match seq.bound with Some b -> max 0 b | None -> 0)
                          ' ')
                       (string_of_formula f)
                       (* (xml_of_sequent seq) *) ;
                     Some { seq with rhs = before @ [ unfocus f ] @ after }
                 | None -> None
               end)

  (********************************************************************
  *finite:
  * Introduces 'finite' async connectives, i.e. those that can be
  * introduced eagerly without backtrack.  For the fixed points (mu on
  * the left, nu on the right) there is a choice of "opening" or
  * "freezing", over which backtrack should be possible.
  ********************************************************************)
  and finite session =
    cutRepeatTactical
      (G.orElseListTactical
         [ automaticIntro session `Left
             (make_matcher
               (fun (Formula(i,(a,f))) ->
                  not (isFixpoint f || a.FOA.polarity=FOA.Negative))) ;
           automaticIntro session `Right
             (make_matcher
               (fun (Formula(i,(a,f))) ->
                  not (isFixpoint f || a.FOA.polarity=FOA.Positive))) ;
           intro `Left
             (make_matcher
                (function
                   | Formula(i,(({FOA.freezing=FOA.Unfrozen} as a),
                       (FOA.ApplicationFormula(
                          FOA.FixpointFormula(
                            FOA.Inductive,_,argnames,_),args) as f)))
                     when unfoldingProgresses `Left argnames args ->
                       if Properties.getBool "firstorder.proofsearchdebug" then
                         Format.printf "%s@[<hov 2>Unfold left@ %s@]\n%!"
                           ""
                           (string_of_formula (Formula(i,(a,f)))) ;
                       true
                   | _ -> false))
             session (Some "unfold") ;
           intro `Right
             (make_matcher
                (function
                   | Formula(i,(({FOA.freezing=FOA.Unfrozen} as a),
                       (FOA.ApplicationFormula(
                          FOA.FixpointFormula(
                            FOA.CoInductive,_,argnames,_),args) as f)))
                     when unfoldingProgresses `Right argnames args ->
                       if Properties.getBool "firstorder.proofsearchdebug" then
                         Format.printf "%s@[<hov 2>Unfold right@ %s@]\n%!"
                           ""
                           (string_of_formula (Formula(i,(a,f)))) ;
                       true
                   | _ -> false))
             session (Some "unfold")
         ])

  (* TODO: note that the treatment of fixed points is not based on polarities
   * but the roles of mu/nu are hardcoded. *)
  and match_inductable =
    make_matcher
      (fun (Formula(i,(a,f))) ->
         match f with
           | FOA.ApplicationFormula
              (FOA.FixpointFormula (FOA.Inductive,_,_,_), _) ->
              a.FOA.freezing = FOA.Unfrozen
           | _ -> false)
  
  and match_coinductable =
    make_matcher
      (fun (Formula(i,(a,f))) ->
         match f with
           | FOA.ApplicationFormula
              (FOA.FixpointFormula (FOA.CoInductive,_,_,_), _) ->
              a.FOA.freezing = FOA.Unfrozen
           | _ -> false)

  (** Apply a rule on the focused formula if it is synchronous. *)
  and sync_step session =
    let body =
      (G.orElseTactical
        (automaticIntro session `Left
          (make_matcher
             (fun (Formula(i,(a,f))) ->
               a.FOA.control=FOA.Focused && a.FOA.polarity=FOA.Negative)))
        (automaticIntro session `Right
          (make_matcher
             (fun (Formula(i,(a,f))) ->
               a.FOA.control=FOA.Focused && a.FOA.polarity=FOA.Positive))))
    in
    body

  (********************************************************************
  *introduceLemmas:
  * Essentially takes all of the lemmas and adds them to the context,
  * with some options to make it less terrible:
  *   Strip non-atomics or not.
  *   Freeze lemmas or not.
  *   Freeze hypotheses/conclusion or not.
  ********************************************************************)
  and introduceLemmas session =
    let get s d = Properties.getDefault Properties.getBool s d in
    let strip = get "firstorder.lemmas.strip-atomic" false in
    let freezeLemmas = get "firstorder.lemmas.freeze-lemmas" false in
    let freezeSequent = get "firstorder.lemmas.freeze-sequent" false in

    (*  strip: Strip nonatomic formulas from a list of formulas.  *)
    let strip s =
      let atomic f =
        match f with
            Formula(_, (_,FOA.ApplicationFormula(_))) -> true
          | _ -> false
      in
      if strip then
        (List.filter atomic s)
      else
        s
    in
    
    (*  freezeAll: freeze all formulas in a list. *)
    let freezeAll fs =
      let freezer arg =
        match arg with
          ann, FOA.ApplicationFormula(_) -> freezeModifier arg
        | _ -> idModifier arg
      in
      List.map
        (fun (Formula(i,f)) ->
          Formula(i,
            modifyFormulaAnnotations
              (composeModifiers freezer unfocusModifier) f))
        fs
    in

    let freezeLemmas lemmas =
      if freezeLemmas then
        freezeAll lemmas
      else
        lemmas
    in
    let freezeSequent seq =
      if freezeSequent then
        freezeAll seq
      else
        seq
    in
    
    (*  The list of lemmas, with nablas removed.  *)
    let lemmas =
      List.map 
        (fun (_,f,_) -> makeFormula ((FOA.eliminateNablas []).FOA.polf f))
        session.lemmas
    in
    let pretactic = fun seq sc fc ->
      let postLemmaBound = updateBound seq.bound in
      let lhs' = strip seq.lhs in
      let rhs' = strip seq.rhs in
      if Listutils.empty rhs' then
        fc ()
      else
        let () = O.debug "Introducing lemmas.\n" in
        let seq' =
          {seq with
            lhs = List.append (freezeLemmas lemmas) (freezeSequent lhs');
            rhs = freezeSequent rhs';
            lemma_bound = updateBound seq.lemma_bound;
            bound = postLemmaBound}
        in
        (*  TODO: add in the proofs of all of the lemmas. *)
        let make pb = fun proofs ->
          { rule = "introduce_lemmas" ;
            params = [] ;
            bindings = [] ;
            formula = None ;
            sequent = seq ;
            subs = (pb proofs) }
        in
        
        (*  NOTE: Might not be right... see old way below.  *)
        (*
        focusTactic session [seq']
          (fun newSeqs oldSeqs pb k ->
            let sc' ns os pb k = sc ns (make pb) k in
            syncTactical session newSeqs sc' k)
          fc
        *)
        fullAsync session [seq']
          (fun ns os pb k ->
            assert (Listutils.empty ns) ;
            sc ns (make pb) k)
          fc
    in
    G.makeTactical pretactic

  (** Focused proof-search, starting with the async phase. *)
  (********************************************************************
  *fullAsync:
  * The start of the asynchronous phase, just resets the asynchronous
  * bound, runs the asynchronous phase, and then runs the freezing
  * phase.
  ********************************************************************)
  and fullAsync session s sc fc =
    cutThenTactical (finite session) (freeze session) s sc fc

  (* Freeze the first available asynchronous fixed point,
   * takes care of unfoldings and re-calling fullAsync when needed. *)
  (********************************************************************
  *freeze:
  * The freezing phase.  Finds an inductable and tries to do induction
  * or coinduction on it.  If it succeeds it continues with the
  * asynchronous phase; if it can't find one it proceeds to the
  * synchronous phase.
  ********************************************************************)
  and freeze session sequents sc fc =
(* TODO this is simply fullAsync *)
    let async = cutThenTactical (finite session) (freeze session) in
    let seq = match sequents with [seq] -> seq | _ -> assert false in
      match match_inductable seq.lhs with
       | Some (Formula(i,(a,f)), before, after) ->
           (* Unfolding might sometimes yield simpler proofs,
            * but trying it everytime seems costly...
            * TODO: a way of getting a quasi-unfolding for free inside the
            * induction is to bundle a frozen version of the fixed point
            * with the invariant *)
           G.orElseTactical
             (fun _ sc fc ->
                if Properties.getBool "firstorder.proofsearchdebug" then
                  Format.printf "%s@[<hov 2>Freeze@ %s@]\n%!"
                    (String.make
                       (match seq.bound with Some b -> max 0 b | None -> 0)
                       ' ')
                    (string_of_formula (Formula(i,(FOA.freeze a,f))));
                freeze session
                  [{seq with lhs =
                               before@[Formula(i,(FOA.freeze a,f))]@after }]
                  sc fc)
          (fun _ -> G.orElseTactical
             (cutThenTactical
                (* The cut is needed here so that auto_intro doesn't try
                 * to induct on another Mu on the left. *)
                (fun _ sc fc ->
                   if Properties.getBool "firstorder.proofsearchdebug" then
                     Format.printf "%s@[<hov 2>Induction@ %s@]\n%!"
                       (String.make
                          (match seq.bound with Some b -> max 0 b | None -> 0)
                          ' ')
                       (string_of_formula (Formula(i,(a,f)))) ;
                   automaticIntro session `Left match_inductable [seq] sc fc)
                async)
             (cutThenTactical
                (* The cut is needed here so that auto_intro doesn't try
                 * to unfold another Mu on the left. *)
                (fun _ sc fc ->
                   if Properties.getBool "firstorder.proofsearchdebug" then
                     Format.printf "%s@[<hov 2>Unfold@ %s@]\n%!"
                       (String.make
                          (match seq.bound with Some b -> max 0 b | None -> 0)
                          ' ')
                       (string_of_formula (Formula(i,(a,f)))) ;
                   intro `Left match_inductable session (Some "unfold") [seq]
                     sc fc)
                async)
             [])
             [(* No arguments *)] sc fc
       | None ->
           begin match match_coinductable seq.rhs with
             | Some (Formula(i,(a,f)), before, after) ->
                 G.orElseTactical
                   (fun _ ->
                      freeze session
                        [{seq with
                          rhs = before@[Formula(i,(FOA.freeze a,f))]@after }])
                   (cutThenTactical
                     (fun _ ->
                        automaticIntro session `Right match_coinductable [seq])
                     async)
                   (* TODO unfold *)
                   [(*no args*)] sc fc
             | None ->
                 (* Don't wait to collect all results of the async phase,
                  * check each immediately. *)
                 fullSync session seq sc fc
           end

  (********************************************************************
  *asyncTactical:
  * Just performs a single round of finite, for manual use outside "prove".
  * The bounds have to be set before, cause they won't be installed
  * by the rest of the prove tactic.
  ********************************************************************)
  and asyncTactical session args =
    G.thenTactical
      (setBoundTactical session args)
      (G.thenTactical (finite session) clearBounds)

  (** Complete focused proof-search starting with a decide rule. *)
  (********************************************************************
  *fullSync:
  * First thaws all formulas in the sequent if the corresponding
  * property is set.  Then either introduces lemmas if that property
  * is set followed by focusing on a formula, or just focuses on a
  * formula immediately.
  ********************************************************************)
  and fullSync session seq sc fc =
    let focuser () =
      focusTactic session [seq]
        (fun newSeqs oldSeqs pb k -> syncTactical session newSeqs sc k)
        fc
    in
    if Properties.getBool "firstorder.lemmas" then
      if outOfBound seq.lemma_bound then
        focuser ()
      else if Listutils.empty (session.lemmas) then
        (O.debug "No lemmas to try.\n";
        focuser ())
      else
        introduceLemmas session [seq] sc focuser
    else
      focuser ()

  (********************************************************************
  *syncTactical:
  * Toplevel tactical that repeatedly calls sync_step until it fails.
  * Once it fails it unfocuses and begins the asynchronous phase again.
  *
  * NOTE: This is not exported; if it is, it could mess up the bounds
  * set on the sequents.
  ********************************************************************)
  and syncTactical session seqs sc fc =
    assert (List.length seqs = 1) ;
    sync_step session seqs
      (fun n o b k ->
         G.iterateTactical
           (syncTactical session)
           (List.append n o) (* succeeds on n@o=[] *)
           (fun n' o' b' k' ->
              assert (n'=[] && o'=[]) ; (* syncTactical is a complete tactic *)
              sc [] [] (fun l -> b (b' l)) k') (* expect l = [] *)
           k)
      (fun () ->
         match unfocus (List.hd seqs) with
           | Some seq -> fullAsync session [seq] sc fc
           | None -> fc ()) (* TODO: that might be broken with delays *)

  (********************************************************************
  *setBound:
  * Sets the synchronous and lemma bounds.
  ********************************************************************)
  and setBound session syncBound lemmaBound =
    let set (Formula (i,f)) =
      Formula ({ i with progressing_bound = initial_progressing_bound },f)
    in
    fun seqs sc fc ->
      match seqs with
       | (seq::tl) ->
          let seq' =
            [{seq with
                bound = Some syncBound;
                lemma_bound = Some lemmaBound;
                lhs = List.map set seq.lhs ;
                rhs = List.map set seq.rhs }]
          in
          sc seq' tl (fun proofs -> proofs) fc
       | [] -> fc ()
  
  (********************************************************************
  *clearBounds:
  * Clears all bounds to None on the given sequents, and succeeds with
  * all of them as the new sequents.  Doesn't mess with the proof
  * builder, as we hide extra-logical things like bounds in the proof.
  ********************************************************************)
  and clearBounds =
    let unset (Formula (i,f)) =
      Formula ({ i with progressing_bound = None },f)
    in
    fun seqs sc fc ->
      let clear seq =
        { seq with bound = None; lemma_bound = None ;
           lhs = List.map unset seq.lhs ; rhs = List.map unset seq.rhs }
      in
      sc (List.map clear seqs) [] (fun proofs -> proofs) fc

  (********************************************************************
  *setBoundTactical:
  * Toplevel interface to setBound.
  ********************************************************************)
  and setBoundTactical session args =
    let lemmaBound = Properties.getInt "firstorder.lemmas.bound" in
    let syncBound = (Properties.getInt "firstorder.defaultbound") in
    match args with
        [Absyn.String s] ->
          setBound session (stringToIntDefault s 0) lemmaBound
      | [(Absyn.String s1); (Absyn.String s2)] ->
          setBound session (stringToIntDefault s1 0) (stringToIntDefault s2 0)
      | [] -> setBound session syncBound lemmaBound
      | _ -> G.invalidArguments "set_bound"
  
  (*******************************************************************
  *iterativeDeepeningProveTactical:
  * Iterative deepening.  Takes a lower and upper bound; you can
  * therefore simulate the old prove tactical by doing prove("n", "n").
  * We _must_ abstract out generic quantifications first: because it
  * brings more expressivity but also because the automation does not
  * take the generic contexts into account at many places, and it would
  * thus do meaningless and error-prone things.
  ********************************************************************)
  and iterativeDeepeningProveTactical session args =
    let abstractAsync =
      G.thenTactical (abstractTactical session []) (fullAsync session)
    in
    let lemmaBound = Properties.getInt "firstorder.lemmas.bound" in
    let rec construct i max =
      if i = max then
        (G.thenTactical (setBound session max lemmaBound) abstractAsync)
      else
        (G.orElseTactical
          (G.thenTactical (setBound session i lemmaBound) abstractAsync)
          (construct (i + 1) max))
    in
    match args with
        [Absyn.String(s)] ->
          let maxBound = stringToIntDefault s 0 in
          construct 0 (max maxBound 0)
      | [Absyn.String(s);Absyn.String(s')] ->
          let minBound = stringToIntDefault s 0 in
          let maxBound = stringToIntDefault s' 0 in
          construct (min maxBound minBound) (max minBound maxBound)
      | [] ->
          construct 0 (max (Properties.getInt "firstorder.defaultbound") 0)
      | _ -> G.invalidArguments "prove"

  let unfocusTactic =
    G.makeTactical
      (fun seq sc fc ->
         match unfocus seq with
           | Some s -> sc [s] List.hd fc
           | None -> fc ())

  let unfocusTactical =
    fun _ _ -> unfocusTactic

  (********************************************************************
  *cutLemmaTactical:
  * Searches the list of lemmas and adds the lemma of the given name
  * to the hypotheses.  Additionally modifies the proof builder to insert
  * the proof of the lemma in the appropriate place.
  ********************************************************************)
  let cutLemmaTactical session args = match args with
      Absyn.String(s)::[] ->
        (try
          let (_,formula,proof) =
            List.find (fun (s',_,_) -> s = s') session.lemmas
          in
          let formula' = makeFormula formula in
          let pretactic = fun sequent sc fc ->
            let seq = { sequent with lhs = sequent.lhs @ [formula'] } in
            let pb = fun proofs ->
              { rule = "cut_lemma" ;
              params = ["lemma", s] ;
              bindings = [] ;
              formula = Some formula' ;
              sequent = seq ;
              subs = proof::proofs }
            in
            sc [seq] pb fc
          in
          (G.makeTactical pretactic)
        with
          Not_found -> (O.error "undefined lemma.\n" ; G.failureTactical))
    | _ -> G.invalidArguments "cut_lemma"

  (********************************************************************
  *applyTactical:
  * Applies the lemma of the given name by focusing on the lemma,
  * repeating 'sync', and finally releasing focus.  It also tweaks the
  * proof builder in the same way as cutLemmaTactical.
  ********************************************************************)
  let applyTactical session args =
    let apply lemma reduce =
      (*  select: given a formula, do something to it (we don't know
          what yet, so we don't do anything; options include negating
          some things, freezing others, etc.), and focus on it. *)
      let select formula =
        let tf x = x in
        let rec ff () =
          let f' = FOA.mapFormula ff tf in
          {f' with
            FOA.polf = fun (ann, f) ->
              (ann, (ff ()).FOA.formf f)}
        in
        let (annotation, newFormula) = (ff ()).FOA.polf formula in
        ({annotation with FOA.control = FOA.Focused}, newFormula)
      in
      
      (try
        let (_,formula,proof) =
          List.find (fun (s',_,_) -> lemma = s') session.lemmas
        in
        let formula = (FOA.eliminateNablas []).FOA.polf formula in
        let formula' = makeFormula (select formula) in
        let pretactic = fun sequent sc fc ->
          let seq = { sequent with lhs = sequent.lhs @ [formula'] } in
          let pb = fun proofs ->
            { rule = "apply" ;
            params = [] ; (* ["lemma", lemma] ; *)
            bindings = [] ;
            formula = Some formula' ;
            sequent = seq ;
            subs = proof::proofs }
          in
          sc [seq] pb fc
        in
        let tac = (G.makeTactical pretactic) in
        if reduce then
          (G.thenTactical
            tac
            (G.thenTactical
              (G.repeatTactical (sync_step session))
              (G.tryTactical unfocusTactic)))
        else
          tac
      with
        Not_found -> (O.error "undefined lemma.\n" ; G.failureTactical))
    in
    match args with
      [Absyn.String(s)] -> apply s true
    | [Absyn.String(s); Absyn.String(mode)] ->
        if mode = "reduce" then
          apply s true
        else if mode = "simple" then
          apply s false
        else
          G.invalidArguments "apply"
    | _ -> G.invalidArguments "apply"

  let applyTactical s a =
    G.thenTactical (abstractTactical s []) (applyTactical s a)

  (********************************************************************
  *admitTactical:
  * A tactical that proves everything! It just kills the current
  * sequent; only useful when testing or experimenting, or when you
  * know that the current sequent can be proved and you don't want
  * to bother.
  ********************************************************************)
  let admitTactical session args =
    match args with
        [] ->
          (G.admitTactical (fun seq ->
            {rule="admit"; 
            formula=None;
            sequent=seq;
            params=[];
            bindings=[];
            subs=[]}))
      | _ -> G.invalidArguments "admit"

  let focusTactical session args =
    match args with
        [] -> focusTactic session
      | _ -> G.invalidArguments "focus"

  let focusRightTactical session args =
    match args with
        [] ->
          G.makeTactical
            (fun seq sc fc ->
              focusRightTactic seq (fun s k -> sc s List.hd k) fc)
      | _ -> G.invalidArguments "freeze_r"
    
  let freezeTactical session args =
    match args with
        [] ->
          G.makeTactical
            (fun seq sc fc ->
              freezeLeftTactic seq (fun s k -> sc s List.hd k) fc)
      | _ -> G.invalidArguments "freeze"

  let syncStepTactical session args =
    match args with
        [] -> sync_step session
      | _ -> G.invalidArguments "sync"

end
