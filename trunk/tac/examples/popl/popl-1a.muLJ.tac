#include "popl-1a.mod".

#lemma sub_refl "pi l\t\ closed l t => sub l t t".
prove.

#tactical bind_absurd then(
    find("bind _ _ _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _")),
    repeat(weak_l("cut _ _")),
    prove("1")).
#tactical instantiate then(repeat(sigma), repeat(then(and_r, try(eq_r)))).
#tactical sub_bind_trans then(mu_r,left,left,right).
#tactical sub_arrow then(mu_r,left,right).
#tactical sub_all then(mu_r,right).

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false)".

#define "permute c c' :=
  (pi x\t\ bind x t c => bind x t c'),
  (pi x\t\ bind x t c' => bind x t c)".

#define "cut {c} {x} := pi a\b\ sub c a x => sub c x b => sub c a b".
#define "coinductive gcut {x} :=
  (pi c\ context c => cut c x),
  (nabla y\ gcut x)".

#define "narrowing {c} {t} :=
  pi s\t1\t2\ sub c s t =>
    nabla x\ context (cons (pair x t) c) =>
      sub (cons (pair x t) c) (t1 x) (t2 x) =>
        sub (cons (pair x s) c) (t1 x) (t2 x)".
#define "coinductive gnarrowing {t} :=
  (pi c\ context c => narrowing c t),
  (nabla y\ gnarrowing t)".

% SIMPLE STRUCTURAL LEMMAS.

#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
prove.

% The simpler form is also useful.
#lemma context_w0
  "pi c\ context c => nabla a\ context c".
prove.

#lemma gcut_cut "pi x\ gcut x => pi c\ context c => cut c x".
prove.

#lemma gcut_w "pi x\ gcut x => nabla a\ gcut x".
prove.

#lemma lift_gcut_cut "nabla a\ pi x\ gcut x => pi c\ context c => cut c x".
prove.

#lemma lift_gcut_w "nabla b\ pi x\ gcut x => nabla a\ gcut x".
abstract.
simplify.
coinduction.
  then(and_r,simplify).
    then(nu_l,and_l,weak_l,nu_l,and_l,weak_l("#2")).
    admit. % TODO we need generic exchange on cut.
    prove.

% Check wether (nabla a\ gcut x) => gcut x,
% which involves (nabla a\ cut x) => cut x.

#lemma gnarrowing_narrowing
   "pi x\ gnarrowing x => pi c\ context c => narrowing c x".
prove.

#lemma lift_gnarrowing_narrowing
  "nabla a\ pi x\ gnarrowing x => pi c\ context c => narrowing c x".
prove.

#lemma bind_w
  "pi x\t\c\ bind x t c => pi t'\ nabla n\ bind x t (cons (pair n t') c)".
intros.
induction.
cases.
  prove.
  pi_l.
  abstract.
  force("T'", "t'0").
  prove.

#lemma bind_s
  "pi c\x'\t'\ (nabla n\ bind (x' n) (t' n) c) =>
    sigma x\t\ x' = (a\ x), t' = (a\ t), bind x t c".
prove.

#lemma permute_w
  "pi c\ta\tb\c'\
    (nabla a\ permute (c' a) (cons (pair a ta) c)) =>
    (nabla b\a\ permute (cons (pair b tb) (c' a))
                        (cons (pair b tb) (cons (pair a ta) c)))".
admit.

#lemma sub_w
  "pi c\a\b\ sub c a b => pi t\ nabla x\ sub (cons (pair x t) c) a b".
simplify.
induction(
   "c\a\b\ nabla x\ pi c'\ permute c' (cons (pair x t) c) => sub c' a b").
then(nabla, pi_l).
force("C'","(n1\ cons (pair n1 t) c)").
prove.
cases.
  % Top.
  prove.
  % Bind_refl.
  apply("bind_w").
  then(mu_l("lift_permute _ _"),mu_r,prove).
  % Bind_trans.
  abstract.
  apply("#2","_").
  apply("bind_w").
  then(mu_l("lift_permute _ _"),sub_bind_trans,prove).
  % Arrow.
  abstract.
  apply("#1","_").
  apply("#2","_").
  prove.
  % All.
  abstract.
  apply("#1","_").
  then(sub_all,instantiate).
    axiom.
    weak_l.
    apply("permute_w").
    intros("#1").
admit.
admit.

% ESSENTIAL CASES FOR CUT.

#set "firstorder.induction-unfold" "true".
#lemma sub_arrow
  "pi a\b\x\y\c\ context c => cut c a => cut c b =>
    sub c x (arrow a b) => sub c (arrow a b) y =>
      sub c x y".
intros.
induction("auto", "sub c x (arrow a b)").
and_r.
  % induction target.
  prove.
  
  % inductive case.
  then(simplify,cases).
    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
    sub_bind_trans.
    prove.

    % sub - arrow.
    weak_l("#2").
    weak_l("#3").
    cases("#6").
      % sub - top.
      prove.

      % sub - bind reflexive.
      bind_absurd.

      %sub - bind transitive.
      bind_absurd.

      % sub - arrow.
      repeat(mu_l("cut _ _")).
      sub_arrow.
      prove.

#lemma sub_all
  "pi c\a\b\a'\b'\x\ context c => cut c a => narrowing c a =>
    (nabla x\ cut (cons (pair x a') c) (b x)) =>
    sub c x (all a b) => sub c (all a b) (all a' b') =>
      sub c x (all a' b')".
intros.
induction("auto", "sub c x (all a b)").
and_r.
  % induction target.
  prove.

  % inductive case.
  then(simplify,cases).

    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
    sub_bind_trans.
    instantiate.
    axiom.
    apply("#3", eq_r, axiom, axiom, axiom, prove, axiom).
    axiom.

    % sub - all.
    weak_l("#2"). % unusable hypothesis.
    weak_l("#3"). % unusable hypothesis.
    cases("#7").
      % sub - bind reflexive.
      bind_absurd.

      % sub - bind transitive.
      bind_absurd.

      % sub - all.
      then(mu_r, right).
      instantiate.
        mu_l("#4").
        apply("#4", axiom, axiom).
        axiom.

        nabla_r.
        mu_l("#5").
        apply("#5", axiom).
        nabla_l.
        apply("#5", then(apply("context_w"), axiom), axiom).
        mu_l("#6").
        apply("#6", axiom, axiom).
        axiom.

% MAIN LEMMA FOR CUT.

% The outer induction on the type will provide us
% (generalized) cut and narrowing for immediate subtypes.
#define "outer_inv g x :=
   (x = top);
   (sigma t\ bind x t g);
   (sigma a\b\
      x = (arrow a b),
      (context g => gcut a, gnarrowing a),
      (context g => gcut b, gnarrowing b));
   (sigma a\b\
      x = (all a b),
      (context g => gcut a, gnarrowing a),
      (nabla x\ context (cons (pair x a) g) => gcut (b x), gnarrowing (b x)))".

#lemma outer_inv_w
   "pi c\x\ outer_inv c x => nabla a\ outer_inv c x".
simplify.
admit.

#lemma cut_hered
  "pi ct\x\ outer_inv ct x => context ct => pi c\ context c => cut c x".
intros.
then(mu_r,intros).
induction("auto","sub _ _ x1").
and.
  % Induction target.
  prove.
  % Invariance.
  cases.
    % top.
    weak_l("outer_inv _ _").
    prove.

    % bind (reflexive).
    weak_l("outer_inv _ _").
    prove.

    % bind (transitive).
    apply("#3","_","_","_").
    sub_bind_trans.
    prove.

    % arrow.
    weak_l("#2").
    weak_l("#3").
% BUG, kills a goal    andthen(cases("outer_inv _ _"),bind_absurd).
    cases("outer_inv _ _").
    bind_absurd.
    apply("#3", axiom).
    apply("#4", axiom).
    simplify.
    repeat(weak_l("gnarrowing _")).
    weak_l("context ct3").
% BUG same    andthen(apply("gcut_cut"),axiom,weak_l("gcut _")).
%    andthen(apply("gcut_cut"),axiom,weak_l("gcut _")).
    apply("gcut_cut").
      axiom.
    weak_l("gcut _").
    apply("gcut_cut").
      axiom.
    weak_l("gcut _").
    cut("sub context9 (arrow s11 s21) (arrow a6 b8)").
      then(sub_arrow,instantiate,axiom).
    cut_lemma("sub_arrow").
    apply("#8", "_", "cut _ a6", "cut _ b8", "_", "_").
    axiom.

    % all.
    weak_l("#2").
    weak_l("#3").
    cases("outer_inv _ _").
    bind_absurd.

     apply("#3", axiom).
     apply("#4", then(apply("context_w"), axiom)).
     simplify.
     weak_l("context ct4").
     cut("cut context10 a7").
       admit.
     cut("narrowing context10 a7").
       admit.
     weak_l("gcut _").
     weak_l("gnarrowing _").

     cases("sub _ (all _ _) _").
       prove.
       bind_absurd.
       bind_absurd.

       cut_lemma("sub_all").
       apply("#10", axiom, axiom, axiom).
admit.

#set "firstorder.induction-unfold" "false".

#theorem sub_dual
  "pi g\t\ context g => type g t => gcut t, gnarrowing t".
intros.
induction("auto", "type _ _").
cut("outer_inv a00 a10").
prove.
weak_l.
intros.
% Narrowing uses cut at the current type, so we prove it first.
cut("gcut a10").

  % Generalized transitivity.
  coinduction("auto", "gcut _").
  and_r.

    % Transitivity.
    cut_lemma("cut_hered").
    prove.

    % Show that the ingredients of the proof of cut
    % admit generic weakening, which gives us gcut.
    simplify.
    instantiate.
    weak_l("#2").
    apply("outer_inv_w").
    axiom.
    apply("context_w0").
    axiom.

  and.
  axiom.

  % Generalized narrowing.
  coinduction.
  and.

  % Narrowing.
  simplify.
  then(mu_r, intros).
  abstract.

  weak_l("outer_inv _ _").
  weak_l("context a02").
  weak_l("lift_context _").
  induction("g\u\v\ nabla x\ pi c\s\t\
     context c => sub c s t => gcut t =>
     permute (g x) (cons (pair x t) c) =>
       sub (cons (pair x s) c) (u x) (v x)",
    "lift_sub _ _ _").
  % apply("#4",axiom,axiom,axiom).
  % prove.
admit.

  % Invariance.
  abstract.
  cases.
    % top.
    then(repeat(weak_l),prove).

    % bind reflexive.
    then(weak_l("#2"),weak_l("#2"),weak_l("#2")).
    prove.

    % bind transitive.
    apply("#2", axiom,axiom,axiom,axiom).
    then(mu_l("lift_permute _ _"),and_l,apply("#6","_")).
    weak_l.
    weak_l("#6").
    cases("lift_bind _ _ _").
      % Bind-trans on the narrowed variable.
      then(sub_bind_trans,instantiate).
      prove.
      cut("nabla x2\ context (cons (pair x2 (s'2 x2)) (c'4 x2))").
      then(weak_l,repeat(weak_l("#2")),prove).
      % apply("context_w").
      % apply("gcut_w").
      %   axiom.
      nu_l("lift_gcut _").
      and_l.
      weak_l("lift_context _").
      abstract.
      apply("#3","_").
      weak_l("lift_lift_gcut _").
%      weak_l("gcut _").
%      apply("sub_w").
%      weak_l("sub _ _ _").
%      weak_l("context _").
      cut("nabla x2\ sub (cons (pair x2 (s'2 x2)) (c'4 x2)) (s'2 x2) (t'3 x2)").
      admit.
      then(abstract,mu_l("lift_cut _ _"),repeat(freeze),prove).
      % Bind-trans on another variable.
      sub_bind_trans.
      instantiate.
      then(mu_r,right,instantiate,axiom).
      axiom.
      
    % arrow.
    apply("#1", axiom,axiom,axiom,axiom).
    apply("#2", axiom,axiom,axiom,axiom).
    repeat(weak_l("#3")).
    prove.

    % all.
    apply("#1", axiom,axiom,axiom,axiom).
    then(sub_all,instantiate).
    axiom.
    pi_l.
    force("C''","(x2\ (x3\ (cons (pair x2 (t1'0 x3)) (c'3 x3))))").
%    apply("#2",
%      then(apply("lift_context_w"),axiom),
%      then(apply("lift_sub_w"),axiom),
%      then(apply("lift_gcut_w"),axiom)).
    intros("#2").
    admit.
    intros("#2").
      force("T''","(x2\(x3\ t'7 x3))").
      force("S''","(x2\(x3\ s'4 x3))").
      admit.
    intros("#2").
      admit.
    intros("#2").
      then(weak_l,weak_l,weak_l,weak_l).
      admit.
    weak_l.
    repeat(weak_l("#2")).
  % need to reorder.
  admit.
    
  % The ingredients of proving narrowing admit weakening.
  simplify.
  instantiate.
  apply("outer_inv_w").
  axiom.
  apply("context_w0").
  axiom.
  apply("gcut_w").
  axiom.

% Qed.
