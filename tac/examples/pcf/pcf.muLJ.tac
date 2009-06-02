#include "pcf.mod".

#tactical do then(right, repeat(orelse(sigma_r, orelse(and_r, eq_r)))).
#tactical of_axiom then(mu_r, do).
#tactical of_rec then(mu_r, then(left, do)).
#tactical of_app then(mu_r, then(left, then(left, do))).
#tactical of_abs then(mu_r, then(left, then(left, then(left, do)))).
#tactical of_if then(mu_r, then(left, then(left, then(left, then(left, do))))).
#tactical of_is_zero then(mu_r, then(left, then(left, then(left, then(left, then(left, do)))))).
#tactical of_pred then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, do))))))).
#tactical of_succ then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, do)))))))).
#tactical of_ff then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, do))))))))).
#tactical of_tt then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, do)))))))))).
#tactical of_zero then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, repeat(orelse(sigma_r, orelse(and_r, eq_r)))))))))))))).
#tactical invert then(mu_l("of _ _ _"), async).
#tactical app then(repeat(pi_l), repeat(then(imp_l, try(axiom)))).

#define "permute a b :=
  (pi m\t\ bind m t a => bind m t b), (pi m\t\ bind m t b => bind m t a)
".

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
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.

#lemma lift_permute_s
  "pi l\l'\ (nabla x\ permute (l x) (l' x)) =>
    nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
weak_l("pi m\ pi t\ (bind m t (l' _) => _)").
prove.
weak_l.
prove.

#lemma bind_s "pi l\x\t\ bind x t l => nabla a\ bind x t l".
prove.

#lemma of_weak "
  pi g\m\t\ of g m t => pi t'\ nabla x\ of (cons (pair x t') g) m t".
simplify.
induction("g\m\t\ nabla x\ pi g'\ permute g' (cons (pair x t') g) =>
  of g' m t").

  % Invariant.
  prove.

  % Inductive.
  cases.
  
  iterate(try(prove("1"))).

  % Abstraction.
  apply("lift_permute_s").
  weak_l("lift_permute _ _").
  then(pi_l, imp_l).
  force("G'''", "(x1\(x2\ cons (pair x1 h7) (g'6 x2)))").
  prove.
  prove.

  % Rec.
  apply("lift_permute_s").
  weak_l("lift_permute _ _").
  then(pi_l, imp_l).
  force("G'''0", "(x1\(x2\ cons (pair x1 h13) (g'8 x2)))").
  prove.
  prove.

  % Bind.
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

  % Invariant.
  pi_l.
  force("G", "g").
  prove.

  % Inductive.
  cases.
  iterate(try(prove("1"))).
  
  % abstraction.
  then(pi_l, imp_l).
  force("G0", "(n1\ cons (pair n1 h7) g7)").
  weak_l("of _ _ _").
  apply("permute_lift").
  weak_l("permute _ _").
  prove.

  cut_lemma("of_weak").
  prove.

  % rec.
  then(pi_l, imp_l).
  force("G1", "(n1\ cons (pair n1 h13) g9)").
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
  then(pi_l, pi_l, imp_l).
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
  invert.
  app.
  invert.
  apply("of_subst").
  weak_l("of _ _ (arr _ _)").
  apply("of_cut").
  axiom.
  prove.
  prove.  % bind absurd.

  % rec.
  contract_l("of _ _ _").
  then(mu_l("of _ _ _"), repeat(or_l), simplify).
  app.
  apply("of_subst").
  apply("of_cut").
  axiom.
  prove.  % bind absurd.
% Qed.

#theorem eval_determinacy "pi e\v1\v2\ eval e v1 => eval e v2 => v1 = v2".
prove.


