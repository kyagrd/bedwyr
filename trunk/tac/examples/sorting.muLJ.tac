#open "sorting.def".

#lemma leq_s "pi x\y\ leq x y => leq (s x) (s y)".
prove.
% Qed.

#lemma decide_leq_gt "pi x\y\ nat x => nat y => leq x y ; gt x y".
intros.
induction.
cases.
  prove.

  apply("#1", axiom).
  or_l.
    cases("leq _ _").
      prove.
      then(cut_lemma("leq_s"),prove).
    prove.
% Qed.

#lemma gt_leq "pi x\y\ gt x y => leq y x".
prove.
% Qed.

#theorem empty "pi x\ y\ nat x => insert x nil y => sorted y".
prove.
% Qed.

% Theorem: insert preserves sortedness.
#lemma insert_sorted
   "pi x\ y\ z\ nat x => sorted y => insert x y z => sorted z".
async.
#set "firstorder.induction-unfold" "true".
induction("auto", "insert _ _ _").
cases.
  % Nil Case.
  prove.
  % Leq Case.
  prove.
  % Gt Case.
  simplify.
  cases("sorted _").
    % sorted one.
    prove.
    cases("insert _ _ _").
    cut_lemma("gt_leq").
    prove.
    % sorted two.
    prove.
% Qed.
#set "firstorder.induction-unfold" "false".

#lemma insert_total
    "pi x\l\ nat x => nat_list l => sigma l'\ insert x l l', nat_list l'".
intros.
induction("auto", "nat_list _").
cases.
  prove.

  cut_lemma("decide_leq_gt").
  prove.
% Qed.

% Theorem: sort yields a sorted list.
#theorem insertion_sort "pi x\ y\ nat_list x => sort x y => sorted y".
% By induction on sort, the list hypothesis being useless.
intros.
induction.
% If you want to see more clearly: async, then prove for the base case.
cut_lemma("insert_sorted").
prove.
% Qed.

#theorem sort_length "pi x\y\n\ sort x y => length x n => length y n".
prove.
% Qed.

#theorem sort_mem "pi x\y\e\ sort x y => mem e x => mem e y".
prove.
% Qed.

#theorem sort_total "pi x\ nat_list x => sigma y\ sort x y, nat_list y".
intros.
induction.
cases.
  prove.

  cut_lemma("insert_total").
  prove.
% Qed.
