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
  prove.  % arrow; long.

  % all.
  pi_l("#2").
  force("C'", "(n1\ cons (pair n1 h10) c'3)").
  imp_l.
    weak_l("#1").
    repeat(pi_r).
    imp_r.
    cases("#2").
      prove.

      cut_lemma("bind_ss").
      abstract.
      apply("#3", "_").
      simplify.
      apply("#1", "bind _ _ _").
      apply("bind_w").
      axiom.
  then(pi_l, imp_l).
    prove.
  weak_l("#3").
  prove.

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
    admit.

#lemma sub_lemma
  "pi c\a\b\ sub c a b =>
    nabla x\ pi t\ sub (cons (pair x t) c) a b".
intros.
apply("sub_ww").
pi_r.
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
  induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)").
    prove.
    prove.
  induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)").
    prove.
    prove.
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



#theorem sub_all
  "pi a\b\x\y\c\ context c => cut c a => narrowing c a =>
    (pi t\ nabla x\ cut (cons (pair x t) c) (b x)) =>
    sub c x (all a b) => sub c (all a b) y =>
      sub c x y".
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
    prove.

    % sub - all.
    weak_l("#2"). % unusable hypothesis.
    weak_l("#3"). % unusable hypothesis.
    cases("#7").
      % sub - top.
      prove.

      % sub - bind reflexive.
      bind_absurd.

      % sub - bind transitive.
      bind_absurd.

      % sub - all.
      then(mu_r, right).
      instantiate.
        mu_l("cut h21 h27").
        prove.

        mu_l("#5").
        apply("#5", "sub h21 h22 h27").
        nabla_l.
        imp_l.
          apply("context_w").
          axiom.
        imp_l.
          axiom.
        weak_l.
        weak_l.
        weak_l.
        weak_l.
        weak_l("#3").
        prove.


#set "firstorder.induction-unfold" "false".

#theorem sub_dual
  "pi g\t\ context c => type c t => 
    (cut c t, narrowing c t)".
intros.
induction("auto", "type _ _").
intros.
and_r.

  % Transitivity.
  then(mu_r, intros).
  #set "firstorder.induction-unfold" "true".
  induction("auto", "sub c a a1").
  and_r.
    prove.
  cases.
    
    % Top.
    prove.

    % Bound (Reflexivity).
    prove.

    % Bound (Transitivity).
    repeat(pi_l("#3")).
    force("o A0 B", "o c b2").
    imp_l("#3").
      eq_r.
    imp_l.
      prove.
    weak_l("#4").
    then(mu_r, left, left, right).
    prove.
    
    % arrow.  
    weak_l("#2").
    weak_l("#3").
    cases.
      bind_absurd.
      repeat(then(imp_l, try(prove("0")))).
      simplify.
      cut("sub c (arrow h2 h3) (arrow h11 h12)").
        prove.
      cut_lemma("sub_arrow").
      apply("#10", "context c", "cut _ h11", "cut _ h12", "_", "_").

    % all.
    weak_l("#2").
    weak_l("#3").
    cases.
      bind_absurd.
      repeat(then(imp_l, try(prove("0")))).

    cases("sub c (arrow _ _) _").
      iterate(try(bind_absurd)).  % Various bind cases.

      repeat(weak_l("pi _")).
      repeat(weak_l("_ => _")).
      prove.                      % sub (arrow ...) top.
      
      % inductive case.
      
    % All.
    
    cases("sub h8 (all _ _) _").
      iterate(try(bind_absurd)).  % Various bind cases.
      prove.                      % sub (all ...) top.

      % inductive case.
      admit.

  % Narrowing.
  intros.
  induction("auto", "sub _ t1 t2").
  cases.

    % Top.
    prove.

    % Bound (Reflexivity).
    prove.

    % Bound (Transitivity).
    

