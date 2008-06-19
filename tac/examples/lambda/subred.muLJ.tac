#open "lemmas.muLJ.tac".

#theorem typeof_subst "
  pi g'\m'\t'\
      (nabla x\ typeof (g' x) (m' x) (t' x))
   => (pi x\    typeof (g' x) (m' x) (t' x))
".
simplify.
abstract.
induction("g'\m'\t'\ pi x\ typeof (g' x) (m' x) (t' x)").
prove.
async.
then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
prove.
prove.
% Qed.

#theorem cut "
 pi g\m\n\tm\tn\
  typeof g n tn => typeof (cons (pair n tn) g) m tm => typeof g m tm
".
simplify.
rotate_l.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           typeof g n tn => typeof g m tm").
pi_l.
force("G","g").
prove.

then(repeat(or_l),simplify).
% BIND.
prove.
% APP.
then(focus,then(repeat(sync),try(unfocus))).
then(focus,then(repeat(sync),try(unfocus))).
prove.
% LAMBDA.
pi_l.
imp_l.
force("G0","(n1\ cons (pair n1 h1) g3)").
weak_l("typeof _ _ _").
apply("permute_s").
weak_l.
prove.
then(imp_l,try(prove("0"))).
weak_l.
induction("g\n\t\ nabla a\ pi gg\
    permute gg (cons (pair a h1) g) => typeof gg n t)").
prove.
then(repeat(or_l),simplify).
% BIND.
apply("bind_s").
prove.
% APP.
prove.
% LAM.
apply("lift_permute_s").
weak_l("lift_permute _ _").
pi_l.
imp_l.
force("Gg''","(x1\(x2\ (cons (pair x1 h6) (gg1 x2))))").
prove.
prove.
% Qed.

#theorem subject_reduction "
  pi m\n\ one m n =>
   pi G\t\
    (pi a\b\c\ bind G (lambda a b) c => false) =>
    (pi a\b\c\ bind G (app a b) c => false) =>
    typeof G m t => typeof G n t
".
abstract.
repeat(pi).
imp.
induction.
then(repeat(or_l),then(simplify,try(prove("0")))).
% Doing a beta-reduction.
then(mu_l,then(repeat(or_l),simplify)).
prove.
then(mu_l,then(repeat(or_l),simplify)).
prove.
apply("typeof_subst").
apply("cut").
% We have to admit it, because currently taci won't solve
% the unification h = h8 h5 which would allow to conclude
% by the axiom rule.
then(rotate_l,then(weak_l,then(weak_l,then(weak_l,then(weak_l,weak_l))))).
admit.

% Going under an abstraction.
then(pi_l,then(pi_l,imp_l)).
eq.
imp_l.
eq.
then(pi_l,then(pi_l,imp_l)).
force("G'","(x\ cons (pair x t) g0)").
rotate_l.
weak_l.
weak_l.
prove.
imp_l.
weak_l.
weak_l("typeof _ _ _").
prove.
prove.
% Qed.
