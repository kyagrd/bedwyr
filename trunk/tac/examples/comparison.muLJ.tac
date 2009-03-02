#open "naturals.def".

#theorem eq_sym "pi x\ y\ eq x y => eq y x".
prove.

#theorem eq_refl "pi x\ nat x => eq x x".
prove.

#theorem leq_trans "pi x\ y\ z\ leq x y => leq y z => leq x z".
prove.

#theorem leq_refl "pi x\ leq x x".
prove.

#theorem leq_min "pi x\ nat x => sigma z\ nat z, leq z x".
prove.

#theorem leq_no_max "pi x\ nat x => sigma y\ leq x y".
prove.

#lemma leq_s "pi x\y\ leq x y => leq (s x) (s y)".
prove.

#set "firstorder.lemmas" "true".
#set "firstorder.lemmas.bound" "0".

#theorem decide_leq_leq "pi x\y\ nat x => nat y => leq x y ; leq y x".
prove.
% Qed.

#theorem decide_leq_gt "pi x\y\ nat x => nat y => leq x y ; gt x y".
% It uses lemma leq_s.
prove.
% Qed.

#theorem gt_leq "pi x\y\ gt x y => leq y x".
prove.
% Qed.
