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

#define "narrowing c t :=
  pi s\t1\t2\ sub c s t =>
    nabla x\ context (cons (pair x t) c) =>
      sub (cons (pair x t) c) (t1 x) (t2 x) =>
        sub (cons (pair x s) c) (t1 x) (t2 x)".

#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
prove.

#lemma context_ww
  "pi c\s\t\ context c => nabla x\y\ context (cons (pair y (s x)) (cons (pair x (t y)) c))".
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
  "pi c\x\t\t'\ (nabla n\ bind x t (cons (pair n t') c)) => bind x t c".
prove.

#lemma bind_ss
  "pi c\x'\t'\ (nabla n\ bind (x' n) (t' n) c) =>
    sigma x\t\ x' = (a\ x), t' = (a\ t), bind x t c".
prove.
  
#lemma sub_w
  "pi c\a\b\ sub c a b => pi c'\ (pi x\t\ bind x t c => bind x t c') =>
    sub c' a b".
intros.
induction.
cases.
  prove.  % top.
  prove.  % bind reflexive.
  prove.  % bind transitive.
  
  % arrow.
  then(mu_r, left, right).
  prove.

  % all.
  pi_l("#2").
  force("C'", "(n1\ cons (pair n1 h10) c'3)").
  imp_l.
    weak_l("#1").
    intros.
    cases("#2").
      prove.

      cut_lemma("bind_ss").
      abstract.
      apply("#3", "_").
      simplify.
      apply("#1", "bind _ _ _").
      apply("bind_w").
      axiom.
  apply("#1", prove, prove).

#lemma lift_sub_w
  "nabla n\ pi c\a\b\ sub c a b =>
    pi c'\ (pi x\t\ bind x t c => bind x t c') =>
      sub c' a b".
admit.

#lemma sub_ww "pi c\s\t\ sub c s t => nabla x\ sub c s t".
intros.
induction.
cases.
  prove.

  then(mu_r, left, left, left, right).
  instantiate.
  force("U", "(n1\ u)").
  prove.

  then(mu_r, left, left, right).
  instantiate.
  force("U0", "(n1\ u0)").
  prove.
  prove.

  prove.

  then(mu_r, right).
  instantiate.
    prove.
    abstract.
    admit.  % TODO.

#lemma sub_lemma
  "pi c\a\b\ sub c a b =>
    nabla x\ pi t\ sub (cons (pair x t) c) a b".
intros.
apply("sub_ww").
intros.
apply("lift_sub_w").
  force("C''", "(x1\ cons (pair x1 (t' x1)) c)").
  prove.
  prove.

#lemma sub_subst
  "pi g\m\t\ (nabla x\ sub (g x) (m x) (t x)) =>
    (pi x\ sub (g x) (m x) (t x))".
simplify.
abstract.
induction.
async.
  prove.
  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"), prove).
  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"), prove).
  prove.
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
  "pi a\b\a'\b'\x\ (pi c\ context c => cut c a) =>
    (pi c\ context c => narrowing c a) =>
    (pi c\ context c => (nabla x\ cut (cons (pair x a') c) (b x))) =>
    pi c\ context c => sub c x (all a b) => sub c (all a b) (all a' b') =>
      sub c x (all a' b')".
intros.
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
    admit.

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
        apply("#3", axiom).
        mu_l("cut _ _").
        prove.

        nabla_r.
        apply("#4", axiom).
        mu_l("#4").
        apply("#4", axiom).
        nabla_l.
        apply("#4", then(apply("context_w"), axiom), axiom).
        apply("#5", axiom).
        nabla_l.
        weak_l.
        weak_l.
        weak_l.
        weak_l("#3").
        weak_l("#3").
        admit.

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
    repeat(pi_l("#3")).
    force("B", "b2").
    force("A0", "a03").
    imp_l("#3").
      repeat(weak_l("#4")).
      repeat(weak_l("mu _")).
      cases.
        prove.
        prove.
        then(left, right).
        instantiate.
          weak_l("#2").
          prove("0").
          weak_l.
          prove("0").
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
      imp_l("#3").
        axiom.
      imp_l.
        axiom.
      simplify.
      repeat(then(pi_l, imp_l, try(axiom("context h5")))).
      cut("sub h5 (arrow h6 h7) (arrow h26 h27)").
        repeat(weak_l("cut _ _")).
        repeat(weak_l("narrowing _ _")).
        then(mu_r, left, right).
        prove.
      cut_lemma("sub_arrow").
      apply("#11", "context h5", "cut _ h26", "cut _ h27", "_", "_").

    % all.
    weak_l("#2").
    weak_l("#3").
    cases.
      bind_absurd.
      apply("#3", axiom).
      apply("#4", then(apply("context_w"), axiom)).
      simplify.
      cases("#9").
        prove.
        bind_absurd.
        bind_absurd.


        then(mu_r, right).
        instantiate.
          apply("#3", "context h45").
          mu_l("cut _ _").
          apply("#3", axiom, axiom).
        
        weak_l("context h36").
        weak_l("#3").
        weak_l("#3").
        apply("#4", then(apply("context_w"), axiom)).
        mu_l("narrowing _ _").
        apply("#4", axiom).
        apply("#4", id).
          apply("context_ww").
          axiom.

        apply("#4", id).
        apply("sub_lemma").

        weak_l("#2").
        weak_l("#2").
        weak_l("#3").
        weak_l("#3").
      
      cut_lemma("sub_all").
      cut("sub h25 (all h9 h10) (all h26 h27)").
        then(mu_r, right).
        instantiate.
        axiom.
        prove.
      apply("#9", "context h25", "cut h25 h26", "narrowing h25 h26").
      prove.

  % Narrowing.
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

    % arrow (long).
    prove.

    % all.
    admit.

    
    
  
