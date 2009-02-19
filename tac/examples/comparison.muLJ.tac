#open "naturals.def".

#lemma leq_s "pi x\y\ leq x y => leq (s x) (s y)".
prove.
% Qed.

#proof_output "./".
#set "firstorder.lemmas" "true".
#set "firstorder.lemmas.bound" "0".
#theorem decide_leq_leq "pi x\y\ nat x => nat y => leq x y ; leq y x".
prove.

#theorem decide_leq_gt "pi x\y\ nat x => nat y => leq x y ; gt x y".
% cut_lemma("leq_s").
prove.
% Qed.

#theorem gt_leq "pi x\y\ gt x y => leq y x".
prove.
% Qed.
