#open "lemmas.muLJ.tac".

#lemma typeof_w
  "pi g\m\t\ typeof g m t => pi t'\ nabla x\ typeof (cons (pair x t') g) m t".
intros.
induction("g\m\t\ nabla x\ pi gg\
    permute gg (cons (pair x t') g) => typeof gg m t)").
  prove.
  cases.
    % BIND.
    apply("bind_s").
    prove.
    % APP.
    prove.
    % LAM.
    apply("lift_permute_s").
    weak_l("lift_permute _ _").
    intros("#1").
      force("Gg''","(x1\(x2\ (cons (pair x1 a) (gg1 x2))))").
      prove.
      prove.
% Qed.

#lemma typeof_cut "
 pi g\m\n\tm\tn\
  typeof g n tn => typeof (cons (pair n tn) g) m tm => typeof g m tm".
intros.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           typeof g n tn => typeof g m tm", "typeof (cons _ _) _ _").
  pi_l.
  force("G","g").
  prove.

  cases.
    % BIND.
    prove.
    % APP.
    apply("#1", axiom, axiom).
    apply("#2", axiom, axiom).
    prove.
    % LAMBDA.
    intros("#1").
      force("G0","(n1\ cons (pair n1 a) g3)").
      weak_l("typeof _ _ _").
      apply("permute_w").
      weak_l.
      prove.
    cut_lemma("typeof_w").
    prove.
% Qed.

#lemma typeof_subst "
  pi g'\m'\t'\
      (nabla x\ typeof (g' x) (m' x) (t' x))
   => (pi x\    typeof (g' x) (m' x) (t' x))".
intros.
abstract.
induction.
cases.
  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
  prove.
  prove.
% Qed.

#theorem subject_reduction "
  pi m\n\ one m n =>
   pi G\t\
    (pi a\b\c\ bind G (lambda a b) c => false) =>
    (pi a\b\c\ bind G (app a b) c => false) =>
    typeof G m t => typeof G n t".
intros.
induction.
cases.
  % Doing a beta-reduction.
  cases("typeof _ _ _").
    prove.
    cases("#3").
      prove.
      apply("typeof_subst").
      apply("typeof_cut").
      prove.
  prove.
  prove.

  % Going under an abstraction.
  abstract.
  cases("#4").
    prove.
    intros("#1").
      force("G'","(x\ cons (pair x t) g3)").
      prove.
    prove.
% Qed.

