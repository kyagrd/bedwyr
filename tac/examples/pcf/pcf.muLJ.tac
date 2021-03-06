#include "pcf.mod".

#tactical do then(right, repeat(orelse(sigma_r, orelse(and_r, eq_r)))).
#tactical of_axiom then(mu_r, do).
#tactical invert then(mu_l("of _ _ _"), async).
#tactical app then(repeat(pi_l), repeat(then(imp_l, try(axiom)))).
#tactical bind_absurd then(
    find("bind _ _ _"),
    find("context _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _")),
    repeat(weak_l("cut _ _")),
    mu_l("context _"),
    prove("0")).

#define "permute a b :=
  (pi m\t\ bind m t a => bind m t b), (pi m\t\ bind m t b => bind m t a)".

#define "context c :=
  (pi x\t1\t2\ bind x t1 c => bind x t2 c => t1 = t2),
  (pi x\t\ bind x t c =>
    (x = zero => false),
    (x = tt => false),
    (x = ff => false),
    (pi n\ (x = succ n) => false),
    (pi n\ (x = pred n) => false),
    (pi n\ (x = is_zero n) => false),
    (pi m\n1\n2\ (x = if m n1 n2) => false),
    (pi t\r\ (x = abs t r) => false),
    (pi l\r\ (x = app l r) => false),
    (pi r\t\ (x = rec t r) => false))".

#lemma permute_lift "pi l\ l'\ permute l l' => nabla x\ permute l l'".
intros.
then(mu_l,then(mu_r,then(and_r,simplify))).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma lift_permute_s
  "pi l\l'\ (nabla x\ permute (l x) (l' x)) =>
    nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma bind_s "pi l\x\t\ bind x t l => nabla a\ bind x t l".
prove.

#lemma of_weak "
  pi g\m\t\ of g m t => pi t'\ nabla x\ of (cons (pair x t') g) m t".
intros.
induction("g\m\t\ nabla x\ pi g'\ permute g' (cons (pair x t') g) =>
  of g' m t").

  % Invariant.
  prove.

  % Inductive.
  cases.
    % easy cases.
    iterate(try(prove("1"))).

    % abstraction.
    apply("lift_permute_s").
    weak_l("lift_permute _ _").
    intros("#1").
      force("G'''", "(x1\(x2\ cons (pair x1 t1) (g'6 x2)))").
      prove.
    prove.

    % rec.
    apply("lift_permute_s").
    weak_l("lift_permute _ _").
    intros("#1").
      force("G'''0", "(x1\(x2\ cons (pair x1 t3) (g'8 x2)))").
      prove.
    prove.

    % bind.
    apply("bind_s").
    prove.
% Qed.


#lemma of_cut "
 pi g\m\n\tm\tn\
  of (cons (pair n tn) g) m tm => of g n tn => of g m tm
".
intros.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           of g n tn => of g m tm").

  % invariant.
  pi_l.
  force("G", "g").
  prove.

  % inductive.
  cases.
    % easy pairs.
    iterate(try(prove("1"))).
    
    % abstraction.
    intros("#1").
      force("G0", "(n1\ cons (pair n1 t0) g7)").
      weak_l("of _ _ _").
      apply("permute_lift").
      weak_l("permute _ _").
      prove.

    cut_lemma("of_weak").
    prove.

    % rec.
    intros("#1").
      force("G1", "(n1\ cons (pair n1 t2) g9)").
      weak_l("of _ _ _").
      apply("permute_lift").
      weak_l("permute _ _").
      prove.

    cut_lemma("of_weak").
    prove.

    % bind.
    prove.
% Qed.

#lemma of_subst
  "pi g\m\t\ (nabla x\ of (g x) (m x) (t x)) =>
    (pi x\ of (g x) (m x) (t x))".
intros.
abstract.
induction.
cases.
  iterate(try(prove("1"))).
  of_axiom.
  prove.
% Qed.
  
#theorem subject_reduction
  "pi p\v\t\c\ eval p v => context c => of c p t => of c v t".
% Induction on eval.
intros.
induction.
cases.
  prove.  % zero.
  prove.  % tt.
  prove.  % ff.
  prove.  % succ.
  prove.  % pred zero.

  % pred n.
  intros("#1").
    axiom.
    imp_l.
      prove.
      prove.

  prove.  % is_zero tt.
  prove.  % is_zero ff.

  prove.  % if tt.
  prove.  % if ff.
  
  prove.  % abstraction.

  % application.
  cases("#4").
    apply("#1", axiom, axiom).
    apply("#2", axiom).
    force("T0", "t14").
    intros("#2").
      cases("#1").
        apply("of_subst").
        apply("of_cut").
        axiom.

        bind_absurd.
      prove.
    bind_absurd.
  
  % rec.
  contract_l("of _ _ _").
  cases("#3").
  apply("#1", axiom).
  force("T1", "t21").
  apply("of_subst").
  apply("of_cut").
  prove.
  bind_absurd.
% Qed.

#theorem eval_determinacy "pi e\v1\v2\ eval e v1 => eval e v2 => v1 = v2".
prove.


