#include "stlc-weak.mod".

#define "permute a b :=
  (pi m\t\ bind m t a => bind m t b), (pi m\t\ bind m t b => bind m t a)".

#define "context c :=
  (pi x\t1\t2\ bind x t1 c => bind x t2 c => t1 = t2),
  (pi x\t\ bind x t c =>
    (pi r\ (x = abs r) => false),
    (pi l\r\ (x = app l r) => false))".

#lemma permute_w "pi l\ l'\ permute l l' => nabla x\ permute l l'".
intros.
then(mu_l, mu_r, and_r, simplify).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma lift_permute_s
  "pi l\l'\ (nabla x\ permute (l x) (l' x)) =>
    nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l, mu_r, and_r, simplify).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma bind_w "pi l\x\t\ bind x t l => nabla a\ bind x t l".
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
  
    % abstraction.
    apply("lift_permute_s").
    weak_l("lift_permute _ _").
    intros("#1").
      force("G'''", "(x1\(x2\ cons (pair x1 t0) (g' x2)))").
      prove.
    prove.

    % Application.
    prove.

    % Bind.
    apply("bind_w").
    prove.
% Qed.


#lemma of_cut "
 pi g\m\n\tm\tn\
  of (cons (pair n tn) g) m tm => of g n tn => of g m tm
".
intros.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           of g n tn => of g m tm").

  % Invariant.
  pi_l.
  force("G", "g").
  prove.

  % Inductive.
  cases.
  
    % abstraction.
    intros("#1").
  
      % cons maintains permutation.
      force("G0", "(n1\ cons (pair n1 t) g0)").
      weak_l("of _ _ _").
      apply("permute_w").
      weak_l("permute _ _").
      prove.

      apply("of_weak").
      prove.

    % application.
    prove.

    % bind.
    prove.
% Qed.

#lemma of_subst
  "pi g\m\t\ (nabla x\ of (g x) (m x) (t x)) =>
    (pi x\ of (g x) (m x) (t x))".
simplify.
abstract.
induction.
cases.
  prove.
  prove.
  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
% Qed.


#theorem subject_reduction "pi e\v\t\c\ eval e v => context c => of c e t => of c v t".
intros.
induction.
cases.

  % abstraction (weak).
  axiom.

  % application.
  cases("#4").
    apply("#1", axiom, axiom).
    apply("#2", axiom).
    force("T", "t2").
    intros("#2").
      cases("#1").
        apply("of_subst").
        apply("of_cut").
        axiom.

        prove.    % bind absurd.
      prove.

    prove. %bind absurd.
% Qed.

#lemma eval_det "pi e\v1\v2\ eval e v1 => eval e v2 => v1 = v2".
prove.

