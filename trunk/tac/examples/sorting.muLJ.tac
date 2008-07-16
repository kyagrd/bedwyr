#open "sorting.def".

#theorem empty "pi x\ y\ nat x => insert x nil y => sorted y".
prove.

% Theorem: insert preserves sortedness; note that this isn't actually used
% by the real proof.
#theorem main_lemma "pi x\ y\ z\ nat x => sorted y => insert x y z => sorted z".
% prove along works, but let's look at the induction on insert.
async.
rotate_l.
rotate_l.
induction.
async.
  %Base Case:
  prove.
  %Inductive Case:
  prove.
% Qed.  

% Theorem: sort yields a sorted list.
#theorem insertion_sort "pi x\ y\ list x => sort x y => sorted y".
% By induction on sort, the list hypothesis being useless.
prove.
% Qed.

