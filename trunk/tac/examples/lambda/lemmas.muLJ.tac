#open "definitions.def".

#theorem permute_example "
 pi a\b\ta\tb\l\la\
   permute (cons (pair a ta) l) la =>
   permute (cons (pair b tb) la) (cons (pair a ta) (cons (pair b tb) l))
".
prove.
% Qed.

% This is not interesting for the development,
% just a test that required some extra work in prove
% (logic vars on the left and progress)
#theorem stupid "pi l\ sigma l'\
   pi a\b\c\d\ bind (cons (pair c d) l') a b
            => bind (cons (pair c d) l ) a b".
prove.
% Qed.

#theorem bind_w  "pi l\x\t\ (nabla a\ bind l x t) => bind l x t".
prove.
% Qed.

#lemma bind_ww "pi l\x\t'\ (nabla a\ bind l x (t' a))
                  => sigma t\ t'=(a\t), bind l x t".
prove.
% Qed.

#theorem bind_www "pi l\x'\t'\ (nabla a\ bind l (x' a) (t' a))
              => sigma x\t\ x'=(a\x), t'=(a\t), bind l x t".
prove.
% Qed.

#lemma bind_s "pi l\x\t\ bind l x t => nabla a\ bind l x t".
prove.
% Qed.

#theorem permute_s "pi l\l'\ permute l l' => nabla a\ permute l l'".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

#theorem lift_permute_s "pi l\l'\ (nabla x\ permute (l x) (l' x))
                         => nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

#theorem typeof_s "pi g\m\t\ typeof g m t => nabla a\ typeof g m t".
simplify.
abstract.
induction.
async.
apply("bind_s").
prove.
prove.
prove.
% Qed.

#theorem typeof_ww "pi g\m\t'\ (nabla a\ typeof g m (t' a)) =>
                     sigma t\ t'=(a\t), typeof g m t".
simplify.
abstract.
induction.
async.
apply("bind_ww").
prove.
prove.
then(focus,repeat(sync)).
unfocus.
prove.
% Qed.
