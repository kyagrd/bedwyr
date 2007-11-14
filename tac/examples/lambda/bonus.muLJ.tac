#open "definitions.muLJ.tac".

#theorem subst_1 "
  pi g'\m'\t'\
      (nabla x\ typeof (g' x) (m' x) (t' x))
   => (pi x\    typeof (g' x) (m' x) (t' x))
".
simplify.
abstract.
induction("g'\m'\t'\ pi x\ typeof (g' x) (m' x) (t' x)").
prove.
then(repeat(or_l),simplify).
then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
prove.
abstract.
prove.
% Qed.

#theorem cut "
 pi g\m\n\tm\tn\
  typeof g n tn => typeof (cons (pair n tn) g) m tm => typeof g m tm
".
simplify.
% TODO: a bug prevents me from using g instead of gg.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           typeof g n tn => typeof g m tm").
prove.
then(repeat(or_l),simplify).
% BIND.
cut("bind (cons (pair n tn) g1) M T0").
prove.
then(mu_l("bind (cons _ _) _ _"),then(or_l,simplify)).
axiom.
prove.
% APP.
prove.
% LAMBDA.
pi_l.
imp_l.
force("G0","(n1\ cons (pair n1 h) g)").
weak_l.
abstract.
cut("nabla x\ permute G (cons (pair n tn) g)").
rotate.
weak_l.
abstract.
then(mu_l,then(mu_r,simplify)).
% WATCH OUT, this one is not instantaneous.
then(and,prove).
abstract.
cut("nabla x\ typeof (cons (pair x h) g) n tn").
rotate.
weak_l.
weak_l.
abstract.
prove.
% Now we're left with two bureaucratic lemmas.
% ========== Lift a permutation.
abstract.
then(mu_l,then(mu_r,then(and_r,simplify))).
induction("l'\x'\t'\ pi l\ l'=(a\l) =>
   sigma x\t\ x'=(a\x), t'=(a\t), bind l x t").
then(pi_l,then(imp_l,simplify)).
cut("bind (cons (pair n0 tn0) g0) h0 h1").
prove.
weak_l.
induction("l\x\t\ nabla a\ bind l x t").
abstract.
prove.
prove.
prove.
induction("l'\x'\t'\ pi l\ l'=(a\l) =>
   sigma x\t\ x'=(a\x), t'=(a\t), bind l x t").
then(pi_l,then(imp_l,simplify)).
cut("bind G h0 h1").
prove.
induction("l\x\t\ nabla a\ bind l x t","bind G h0 h1").
abstract.
axiom.
prove.
prove.
% ========== Now for the second lemma.
weak_l("permute _ _").
weak_l("_ => _").
induction("g\n\tn\ pi g'\ nabla x\ permute (g' x) (cons (pair x h) g) =>
                            typeof (g' x) n tn").
prove.
then(repeat(or_l),simplify).
cut("nabla x\ bind (g'1 x) M T0").
then(induction("g\m\t\ nabla x\ bind g m t","bind _ _ _"),prove).
abstract.
prove.
prove.
abstract.
% Only remains the lambda case.
pi.
force("G''","(x1\(x2\ cons (pair x1 h0) (g' x2)))").
imp_l.
rotate.
prove.
% How boring: now we're lifting the lifted permutation judgement.
cut("nabla x1\x2\ permute (g' x2) (cons (pair x2 h) G)").
rotate.
abstract.
weak_l.
then(mu_l,then(mu_r,simplify)).
% Another LONG one.
then(and,prove).
cut("pi gamma\delta\
 (nabla x\   permute (gamma x) (delta x)) =>
 (nabla y\x\ permute (gamma x) (delta x))").
rotate.
then(abstract,prove).
abstract.
simplify.
rotate_l.
weak_l.
then(mu_l,then(mu_r,then(and_r,simplify))).
induction("l''\x''\t''\ pi l'\ l''=(x\l') =>
  sigma x'\t'\ x''=(a\x'), t''=(a\t'), nabla x\ bind (l' x) (x' x) (t' x)").
rotate.
prove.
rotate.
then(pi_l,then(imp_l,simplify)).
abstract.
cut("nabla x1\ bind (delta x1) (h x1) (h0 x1)").
then(abstract,prove).
abstract.
weak_l.
induction("l'\x'\t'\ nabla a\b\ bind (l' b) (x' b) (t' b)").
then(abstract,axiom).
prove.
induction("l''\x''\t''\ pi l'\ l''=(x\l') =>
  sigma x'\t'\ x''=(a\x'), t''=(a\t'), nabla x\ bind (l' x) (x' x) (t' x)").
rotate.
prove.
then(pi_l,then(imp_l,simplify)).
then(cut("nabla x\ bind (gamma x) (h x) (h0 x)"),abstract).
prove.
weak_l.
then(induction("l'\x'\t'\ nabla a\b\ bind (l' b) (x' b) (t' b)"),abstract).
prove.
prove.
% Qed.
