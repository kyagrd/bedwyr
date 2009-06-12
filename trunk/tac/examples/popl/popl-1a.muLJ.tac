#include "popl-1a.mod".

#tactical bind_absurd then(
    find("bind _ _ _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _")),
    repeat(weak_l("cut _ _")),
    prove("1")).

#define "cut c x := pi a\b\ sub c a x => sub c x b => sub c a b".

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false)".

#lemma sub_refl "pi l\t\ closed l t => sub l t t".
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

#lemma narrowing
  "pi c\x\s\t1\t2\ context (cons (pair x t) c) =>
    sub c s t =>
    sub (cons (pair x t) c) t1 t2 =>
      sub (cons (pair x s) c)  t1 t2".
admit.

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
  
  simplify.
  cases.
    % type - top.
    bind_absurd.
    
    % type - bind.
    prove.

    % type - arrow.
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
  "pi a\b\x\y\c\ context c => cut c a => cut c b =>
    sub c x (all a b) => sub c (all a b) y =>
      sub c x y".
intros.
induction("auto", "sub c x (all a b)").
and_r.
  prove.

  simplify.
  cases.
    bind_absurd.
    prove.

    weak_l("#2").
    weak_l("#3").
    cases("#6").
      prove.
      bind_absurd.
      bind_absurd.
      repeat(mu_l("cut _ _")).
      then(mu_r, right).
      repeat(sigma).
      repeat(then(and_r, try(eq_r))).
        prove.
        abstract.

#set "firstorder.induction-unfold" "false".

#theorem sub_single
  "pi g\t\ context g => type g t => 
    pi c\ context c => cut c t".
intros.
induction("auto", "type g t").
cases.
  % type - top.
  prove.

  % type - bind.
  then(mu_r, intros).
  induction("auto", "sub c0 a h0").
  cases.
    % sub - top.
    bind_absurd.

    % sub - bind reflexive.
    axiom.

    % sub - bind transitive.
    prove.

    % sub - arrow.
    bind_absurd.

    % sub - all.
    bind_absurd.

  % type - arrow.
  imp_l.
    axiom.
  then(pi_l, imp_l).
  axiom("context c1").
  axiom.
  imp_l.
    axiom.
  then(pi_l, imp_l).
  force("C0", "c1").
  axiom.

  then(mu_r, simplify).
  cut_lemma("sub_arrow").
  prove("0").

  % type - all.

      
#theorem sub_dual
  "pi g\t\ context g => type g t => 
    ((pi c\s\u\ context c => sub c s t => sub c t u => sub c s u),
    (pi c\x\s\t1\t2\ context (cons (pair x t) c) =>
      sub c s t =>
      sub (cons (pair x t) c) t1 t2 =>
        sub (cons (pair x s) c)  t1 t2))".
intros.
induction("auto", "type _ _").
intros.
and_r.

  % Transitivity.
  intros.
  induction("auto", "sub c s a1").
  cases.
    
    % Top.
    prove.

    % Bound (Reflexivity).
    prove.

    % Bound (Transitivity).
    prove.
    
    % Arrow.
    cases("sub h5 (arrow _ _) _").
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
    

