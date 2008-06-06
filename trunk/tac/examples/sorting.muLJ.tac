#open "sorting.def".

#theorem empty "pi x\ y\ nat x => insert x nil y => sorted y".
prove.

% Theorem: insert preserves sortedness.
#theorem main_lemma "pi x\ y\ z\ nat x => sorted y => insert x y z => sorted z".
async.
rotate_l.
rotate_l.
induction.
  %Base Case:
  async.
  prove.
 
  %Inductive Case:
  

% Theorem: sort yields a sorted list.
#theorem insertion_sort "pi x\ y\ list x => sort x y => sorted y".
