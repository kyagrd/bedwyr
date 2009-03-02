#open "sorting.def".

#set "firstorder.lemmas" "true".
#set "firstorder.lemmas.bound" "1".
#set "firstorder.lemmas.freeze-lemmas" "true".

#lemma leq_s "pi x\y\ leq x y => leq (s x) (s y)".
prove.

% Requires lemma 'leq_s'.
#lemma decide_leq_gt "pi x\y\ nat x => nat y => leq x y ; gt x y".
prove.

% The following theorems may be useful when proving 
#lemma gt_leq "pi x\y\ gt x y => leq y x".
prove.
% Qed.


#lemma sorted "pi x\ pi l\ sorted (cons x l) => sorted l".
prove.

% Requires lemma 'decide_leq_gt' when proved by hand; doesn't work automatically.
#lemma insert_sorted
   "pi x\ y\ z\ nat x => sorted y => insert x y z => sorted z".
% TODO.
admit.

% Requires lemma 'insert_sorted'.
#theorem insertion_sort "pi x\ y\ nat_list x => sort x y => sorted y".
prove.

% Requires lemma 'decide_leq_gt'; doesn't work automatically.
#theorem insert_total
    "pi x\l\ nat x => nat_list l => sigma l'\ insert x l l', nat_list l'".
prove.
% Qed.

#theorem sort_length "pi x\y\n\ sort x y => length x n => length y n".
prove.
% Qed.

#theorem sort_mem "pi x\y\e\ sort x y => mem e x => mem e y".
prove.
% Qed.

% Requires lemma 'insert_total'.
#theorem sort_total "pi x\ nat_list x => sigma y\ sort x y, nat_list y".
prove.
% Qed.
