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

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false)".

#define "cut {c} {x} := pi a\b\ sub c a x => sub c x b => sub c a b".

#define "narrowing {c} {t} :=
  pi s\t1\t2\ sub c s t =>
    nabla x\ context (cons (pair x t) c) =>
      sub (cons (pair x t) c) (t1 x) (t2 x) =>
        sub (cons (pair x s) c) (t1 x) (t2 x)".

#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
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
  simplify.
  cases.
    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
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
      then(mu_r, left, right).  % unfold the arrow case.
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
  simplify.
  cases.
    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
    then(mu_r, left, left, right).
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

#set "firstorder.induction-unfold" "false".

#theorem sub_dual
  "pi g\t\ context g => type g t => 
    ((pi c\ context c => cut c t), (pi c\ context c => narrowing c t))".
intros.
induction("auto", "type _ _").
intros.
and_r.

  % Transitivity.
  intros.
  then(mu_r, intros).
  #set "firstorder.induction-unfold" "true".
  induction("auto", "sub c a a1").
  and_r.
    prove.
  cases.
    % top.
    prove.

    % bind (reflexive).
    prove.

    % bind (transitive).
    intros("#3").
      force("A0", "a03").
      repeat(weak_l("#4")).
      repeat(weak_l("mu _")).
      cases.
        prove.
        prove.
        then(left, right, instantiate).
          weak_l("#2").
          prove.
          weak_l.
          prove.
        then(right, instantiate).
          weak_l("#2").
          prove.
          weak_l.
          prove.
    weak_l("#4").
    then(mu_r, left, left, right).
    prove.
    
    % arrow.  
    weak_l("#2").
    weak_l("#3").
    cases.
      bind_absurd.
      apply("#3", axiom).
      apply("#4", axiom).
      simplify.
      repeat(then(pi_l, imp_l, try(axiom("context h5")))).
      cut("sub h5 (arrow h6 h7) (arrow h26 h27)").
        then(mu_r, left, right).
        prove.
      cut_lemma("sub_arrow").
      apply("#11", "context h5", "cut _ h26", "cut _ h27", "_", "_").
      axiom.

    % all.
    weak_l("#2").
    weak_l("#3").
    cases.
      bind_absurd.
 
      apply("#3", axiom).
      apply("#4", then(apply("context_w"), axiom)).
      simplify.
      weak_l("context h36").
      cases("#8").
        prove.
        bind_absurd.
        bind_absurd.

        cut_lemma("sub_all").
        apply("#3", axiom).
        apply("#4", axiom).
        apply("#10", axiom, axiom, axiom).
        intros("#10").
          force("A'", "h46").
          force("B0", "h50").
          intros("#5").
            apply("context_w").
            force("C", "(x\ cons (pair x T) h45)").
            axiom.
          prove.
        cut("sub h45 (all h51 h50) (all h46 h47)").
          then(mu_r, right).
          prove.
        cut("sub h45 (all h9 h10) (all h51 h50)").
          then(mu_r, right).
          prove.
        apply("#10", axiom, axiom).
        axiom.

  % Narrowing.
  intros.
  then(mu_r, simplify).
  abstract.
  induction("auto", "lift_sub _ _ _").
  and_r.
    prove.
  cases.

    % top.
    prove.

    % bind reflexive.
    prove.

    % bind transitive.
    admit.

    % arrow (long); this used to prove...
    weak_l("#5").
    apply("#2", eq_r, eq_r, eq_r, id).
      prove.
    apply("#4", eq_r, eq_r, eq_r, id).
      prove.
    weak_l("context a09").
    apply("#2", id).
      force("T0", "s3").
      force("C0", "h60").
      admit
    apply("#2", axiom, axiom).
    apply("#4", id).
      force("T1", "s3").
      force("C1", "h60").
      admit.
    apply("#4", axiom, axiom).
    prove.

    % all.
    weak_l("#5").
    apply("#2", eq_r, eq_r, eq_r, id).
      prove.
    apply("#4", eq_r, eq_r, id).
      force("A1'", "h68").
      force("C'", "(x1\ cons (pair x1 h73) h65)").
      admit.
    apply("#2", id).
      force("T2", "s4").
      force("C2", "h65").
      admit.
    apply("#2", axiom, axiom, axiom).
    apply("#4", id).
      prove.
    apply("#4", id).
      force("C'0", "h65").
      admit.
    apply("#4", axiom, id).
      admit.
    apply("#4", id).
      admit.
    then(mu_r, right).
    instantiate.
      prove.
    