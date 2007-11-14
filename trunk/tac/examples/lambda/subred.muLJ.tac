#open "definitions.muLJ.tac".

#theorem subject_reduction "
  pi m\n\ one m n =>
   pi G\t\
    (pi a\b\c\ bind G (lambda a b) c => false) =>
    (pi a\b\c\ bind G (app a b) c => false) =>
    typeof G m t => typeof G n t
".
repeat(pi).
imp.
induction("m\n\
  pi G\ pi t0\
   (pi a\b\c\ bind G (lambda a b) c => false) =>
   (pi a\b\c\ bind G (app a b) c => false) =>
   (typeof G m t0 => typeof G n t0)").
prove.
then(repeat(or_l),simplify).
then(mu_l,then(repeat(or_l),simplify)).
prove.
then(mu_l,then(repeat(or_l),simplify)).
prove.
% This is done as a lemma in bonus.
rotate.
then(mu_l,then(repeat(or_l),simplify)).
prove.
prove.
then(mu_l,then(repeat(or_l),simplify)).
prove.
prove.
then(mu_l,then(repeat(or_l),simplify)).
prove.
cut("nabla n\ pi a\ pi b\ pi c\
 (bind (cons (pair n t) G0) (app a b) c => false)").
simplify.
abstract.
then(mu_l,then(or_l,simplify)).
induction("g'\x'\t'\
  pi g\ g'=(a\g) => sigma x\t\ x'=(a\x), t'=(a\t), bind g x t").
prove.
prove.
cut("nabla n\ pi a\ pi b\ pi c\
 (bind (cons (pair n t) G0) (lambda a b) c => false)").
simplify.
abstract.
then(mu_l,then(or_l,simplify)).
induction("g'\x'\t'\
  pi g\ g'=(a\g) => sigma x\t\ x'=(a\x), t'=(a\t), bind g x t").
prove.
prove.
prove.
% And this is the lemma we rotated out, proved in bonus_muLJ_tac.
% Qed.
