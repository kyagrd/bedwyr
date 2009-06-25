#include "popl-1a.mod".

#lemma sub_refl "pi l\t\ closed l t => sub l t t".
prove.

#tactical bind_absurd then(
    find("bind _ _ _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _")),
    repeat(weak_l("outer_inv _ _")),
    repeat(weak_l("cut _ _")),
    prove("1")).
#tactical instantiate then(repeat(sigma), repeat(then(and_r, try(eq_r)))).
#tactical sub_bind_refl then(mu_r,left,left,left,right).
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

% #lemma lift_context_w
%   "nabla n\ pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
% prove.
% Not quite a lifting, has exchange too.
#lemma lift_context_w
  "pi c\ pi t\ nabla n\ context (c n) =>
     nabla x\ context (cons (pair n (t x)) (c x))".
prove.

#lemma context_s "pi c\ (nabla a\ context c) => context c".
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

% Lifting a theorem always yields a theorem as long as no atoms are used.
% Often, the same proof script works, but in some cases like here extra
% steps have to be taken, notably involving generic exchange.
#lemma lift_gcut_w "nabla b\ pi x\ gcut x => nabla a\ gcut x".
admit.

#lemma lift_gcut_wx "pi x\ nabla a\ gcut (x a) => nabla b\ gcut (x b)".
admit.

#lemma gnarrowing_narrowing
   "pi x\ gnarrowing x => pi c\ context c => narrowing c x".
prove.

#lemma gnarrowing_w "pi x\ gnarrowing x => nabla a\ gnarrowing x".
prove.

#lemma lift_gnarrowing_narrowing
  "nabla a\ pi x\ gnarrowing x => pi c\ context c => narrowing c x".
prove.

#lemma lift_gnarrowing_w
  "nabla b\ pi x\ gnarrowing x => nabla a\ gnarrowing x".
admit.

#lemma lift_gnarrowing_wx
  "pi x\ nabla a\ gnarrowing (x a) => nabla b\ gnarrowing (x b)".
admit.

#lemma bind_w "pi x\t\c\ bind x t c => nabla a\ bind x t c".
prove.

#lemma bind_ctxt_w
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
  "pi c\c'\ permute c c' => nabla a\ permute c c'".
simplify.
then(mu_l,mu_r).
% TODO use andthen when fixed.
then(and_l,and_r).
  weak_l("#2").
  then(cut_lemma("bind_w"),cut_lemma("bind_s"),prove).
  weak_l("#1").
  then(cut_lemma("bind_w"),cut_lemma("bind_s"),prove).

#lemma permute_weakening
  "pi c\ta\tb\c'\
    (nabla a\ permute (c' a) (cons (pair a ta) c)) =>
    (nabla b\a\ permute (cons (pair b tb) (c' a))
                        (cons (pair b tb) (cons (pair a ta) c)))".
admit.

#lemma lift_permute_weakening
  "pi c\c'\t\t'\
 nabla x\ permute (c x) (cons (pair x (t x)) (c' x)) =>
  nabla y\ permute (cons (pair x (t' y)) (c y))
                   (cons (pair y (t y)) (cons (pair x (t' y)) (c' y)))".
admit.

#lemma sub_w "pi c\s\t\ sub c s t => nabla x\ sub c s t".
intros.
abstract.
induction.
cases.
  % Top.
  prove.
  % Bind_refl.
  sub_bind_refl.
  instantiate.
  force("U'", "(x\ u)").
  apply("bind_w").
  axiom.
  % Bind_trans.
  then(mu_r, left, left, right).
  instantiate.
    force("U'0", "(x\ u0)").
    apply("bind_w").
    axiom.
  prove.
  % Arrow.
  prove.
  % All.
  prove.
% Qed.

#lemma sub_ctxt_inclusion
  "pi c\a\b\ sub c a b =>
    pi c'\ (pi x\t\ bind x t c => bind x t c') => sub c' a b".
simplify.
induction.
cases.
  % Top.
  prove.
  % Bind_refl.
  then(sub_bind_refl,prove).
  % Bind_trans.
  then(sub_bind_trans,prove).
  % Arrow.
  intros("#1").
    then(weak_l,prove).
  intros("#2").
    then(weak_l,prove).
  prove.
  % All.
  abstract.
  intros("#1").
    then(weak_l,prove).
  then(sub_all,instantiate).
    axiom.
    weak_l.
    intros("#1").
      force("C''","(x1\ cons (pair x1 t10) c'4)").
      cut_lemma("bind_w").
      cut_lemma("bind_s").
      prove.
    axiom.
% Qed.

#lemma lift_sub_ctxt_inclusion "nabla n\
  pi c\a\b\ sub c a b =>
    pi c'\ (pi x\t\ bind x t c => bind x t c') => sub c' a b".
admit.

#lemma lift_lift_sub_ctxt_inclusion "nabla n\m\
  pi c\a\b\ sub c a b =>
    pi c'\ (pi x\t\ bind x t c => bind x t c') => sub c' a b".
admit.

#lemma sub_weakening
  "pi c\a\b\ sub c a b => pi t\ nabla x\ sub (cons (pair x t) c) a b".
simplify.
cut("nabla n\ pi x\t\ bind x t c => bind x t (cons (pair n t) c)"). 
then(weak_l,prove).
cut_lemma("lift_sub_ctxt_inclusion").
apply("sub_w").
weak_l("sub _ _ _").
prove.
% Qed.

% Not only a lifting, has exchange too.
#lemma lift_sub_weakening
  "pi c\a\b\t\
    nabla n\ sub (c n) (a n) (b n) =>
     nabla x\ sub (cons (pair n (t x)) (c x)) (a x) (b x)".
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
      then(sub_all,instantiate).
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
cases.
cases("#1").
  % Top.
  prove.
  % Bind.
  then(mu_r,left,left,right).
  apply("bind_w").
    prove.
  % Arrow.
  then(mu_r,left,right,instantiate,simplify).
  apply("context_s").
  apply("#1","_").
  repeat(weak_l("#2")).
  then(simplify,and_r).
    then(apply("gcut_w"),axiom).
    then(apply("gnarrowing_w"),axiom).
  apply("context_s").
  weak_l.
  apply("#1","_").
  repeat(weak_l("#2")).
  then(simplify,and_r).
    then(apply("gcut_w"),axiom).
    then(apply("gnarrowing_w"),axiom).
  % All.
  then(mu_r,right,instantiate,simplify).
  apply("context_s").
  apply("#1","_").
  repeat(weak_l("#2")).
  then(simplify,and_r).
    then(apply("gcut_w"),axiom).
    then(apply("gnarrowing_w"),axiom).
  weak_l.
  cut("nabla n\m\ context c0").
    weak_l.
    prove.
  imp_l.
    then(weak_l,prove).
  repeat(weak_l("#2")).
  then(and_r,simplify).
    then(apply("lift_gcut_wx"),axiom).
    then(apply("lift_gnarrowing_wx"),axiom).
% Qed.

#lemma cut_hered
  "pi ct\x\ outer_inv ct x => context ct => pi c\ context c => cut c x".
intros.
then(mu_r,intros).
induction("auto","sub _ _ x1").
and.
  % Induction target.
  then(mu_r,prove("0")).
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
    % TODO andthen(cases("outer_inv _ _"),bind_absurd).
    cases("outer_inv _ _").
    bind_absurd.
    apply("#3", axiom).
    apply("#4", axiom).
    simplify.
    repeat(weak_l("gnarrowing _")).
    weak_l("context ct3").
    % TODO same bug: andthen(apply("gcut_cut"),axiom,weak_l("gcut _")).
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
    cases("sub _ (all _ _) _").
      prove.
      bind_absurd.
      bind_absurd.
    cut("sub context14 (all s12 s22) (all s13 s23)").
    then(sub_all,instantiate,simplify,axiom).
    cut("sub context14 (all s13 s23) (all t17 t27)").
    then(sub_all,instantiate,simplify,axiom).
    then(weak_l("sub _ _ _"),weak_l("sub _ _ _"),
         weak_l("sub _ _ _"),weak_l("sub _ _ _")).
    cases("outer_inv _ _").
      bind_absurd.
    apply("#1", axiom).
    apply("#2", then(apply("context_w"), axiom)).
    simplify.
    weak_l("#4").
    weak_l("context ct4").
    apply("gcut_cut").
      axiom.
    apply("gnarrowing_narrowing").
      axiom.
    weak_l("gcut _").
    weak_l("gnarrowing _").
    apply("context_w").
    apply("lift_gcut_cut").
      axiom.
     weak_l("lift_context _").
     weak_l("lift_gcut _").
     cut_lemma("sub_all").
     abstract.
     apply("#7", axiom,axiom,axiom,axiom,axiom,axiom).
     axiom.

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
  
  % Invariant => goal.
  abstract.
  apply("#4",
     then(apply("context_w0"),axiom),
     then(apply("sub_w"),axiom),
     then(apply("gcut_w"),axiom)).
  intros("#4").
    then(repeat(weak_l),prove).
  axiom.

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
      weak_l("lift_context _").
      apply("lift_gcut_cut").
        axiom.
        weak_l("lift_gcut _").
      cut("nabla n\ sub (cons (pair n (s'2 n)) (c'4 n)) (s'2 n) (t'3 n)").
      cut_lemma("lift_sub_ctxt_inclusion").
      abstract.
      intros("#5").
        % TODO wtf?
        force("C'","c'4").
        force("A'","s'2").
        force("B'","t'3").
        axiom.
      intros("#5").
        force("C''","(x2\ cons (pair x2 (s'2 x2)) (c'4 x2))").
        then(repeat(weak_l),prove).
      axiom.
      weak_l("#2").
      weak_l("lift_context _").
      prove.

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
    repeat(pi_l).
    force("T''","(x2\(x3\ t'7 x3))").
    force("C''0","(x2\ (x3\ (cons (pair x2 (t1'0 x3)) (c'3 x3))))").
    apply("#2",
      then(apply("lift_context_w"),axiom)).
    imp_l.
      then(weak_l,apply("lift_sub_weakening"),axiom).
    imp_l.
      apply("lift_gcut_w").
      axiom.
      % TODO that should be an axiom but gcut has been unfolded.
      then(repeat(weak_l("mu _")),prove).
    apply("#2",then(apply("lift_permute_weakening"),axiom)).
    weak_l.
    repeat(weak_l("#2")).
    apply("lift_lift_sub_ctxt_inclusion").
    force("C'''",
     "(x2\(x3\ cons (pair x2 (t1'0 x3))
                (cons (pair x3 (s'4 x3)) (c'3 x3))))").
    then(weak_l,prove).
    axiom.

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

