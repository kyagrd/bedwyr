#open "definitions.def".

#lemma permute_example "
 pi a\b\ta\tb\l\la\
   permute (cons (pair a ta) l) la =>
   permute (cons (pair b tb) la) (cons (pair a ta) (cons (pair b tb) l))
".
prove.
% Qed.

% This is not interesting for the development,
% just a test that required some extra work in prove
% (logic vars on the left and progress)
#lemma stupid "pi l\ sigma l'\
   pi a\b\c\d\ bind (cons (pair c d) l') a b
            => bind (cons (pair c d) l ) a b".
prove.
% Qed.

#lemma bind_w  "pi l\x\t\ (nabla a\ bind l x t) => bind l x t".
prove.
% Qed.

#lemma bind_ww "pi l\x\t'\ (nabla a\ bind l x (t' a))
                  => sigma t\ t'=(a\t), bind l x t".
prove.
% Qed.

#lemma bind_www "pi l\x'\t'\ (nabla a\ bind l (x' a) (t' a))
              => sigma x\t\ x'=(a\x), t'=(a\t), bind l x t".
prove.
% Qed.

#lemma bind_s "pi l\x\t\ bind l x t => nabla a\ bind l x t".
prove.
% Qed.

#lemma permute_s "pi l\l'\ permute l l' => nabla a\ permute l l'".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

#lemma lift_permute_s "pi l\l'\ (nabla x\ permute (l x) (l' x))
                         => nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

#lemma typeof_s "pi g\m\t\ typeof g m t => nabla a\ typeof g m t".
cut_lemma("bind_s").
prove.
% Qed.

#lemma typeof_ww "pi g\m\t'\ (nabla a\ typeof g m (t' a)) =>
                     sigma t\ t'=(a\t), typeof g m t".
cut_lemma("bind_ww").
prove.
% Qed.
