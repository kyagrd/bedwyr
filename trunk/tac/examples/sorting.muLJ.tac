#open "sorting.def".

#theorem empty "pi x\ y\ nat x => insert x nil y => sorted y".
prove.

% Theorem: insert preserves sortedness; note that this isn't actually used
% by the real proof.
#theorem main_lemma "pi x\ y\ z\ nat x => sorted y => insert x y z => sorted z".
async.
rotate_l.
rotate_l.
#set "firstorder.induction-unfold" "true".
induction.
async.
  % Nil Case.
  prove.
  % Leq Case.
  prove.
  % Gt Case.
  and.
  prove.
  simplify.
  then(mu_l("sorted _"),async).
  prove.
  then(mu_l("insert _ _ _"),async).
  cut("pi x\y\ gt x y => leq y x").
  repeat(weak_l).
  prove.
  prove.
  prove.
% Qed.
#set "firstorder.induction-unfold" "false".

#theorem leq_gt_decide "pi x\y\ nat x => nat y => leq x y ; gt x y".
#set "firstorder.induction-unfold" "true".
simplify.
induction.
async.
prove.
induction.
async.
prove.
and.
prove.
simplify.
and.
prove.
imp_l.
simplify.
pi_l.
imp_l.
axiom.
weak_l("nat _").
weak_l("nat _").
async.
cut("pi x\ nat x => leq (s x) x => false").
repeat(weak_l).
simplify.
induction.
async.
prove.
and.
prove.
imp_r.
imp_l.

prove.
async.
prove.
prove.
orce("H","h1").
prove.
pi_l.
imp_l.

% Qed.

#theorem insert_total "pi x\l\ nat x => nat_list l => sigma l'\ insert x l l'".
simplify.
rotate_l.
induction.
async.
prove.
cut("pi x\y\ nat x => nat y => leq x y; gt y x").
prove.
pi_l.
imp_l.
then(force("X","x2"),axiom).
or_l.
prove.
prove.
% Qed.

% Theorem: sort yields a sorted list.
#theorem insertion_sort "pi x\ y\ list x => sort x y => sorted y".
% By induction on sort, the list hypothesis being useless.
prove.
% Qed.

#theorem sort_length "pi x\y\n\ sort x y => length x n => length y n".
prove.

#theorem sort_mem "pi x\y\e\ sort x y => mem e x => mem e y".
prove.

#theorem sort_total "pi x\ nat_list x => sigma y\ sort x y".
simplify.
induction.
async.
prove.


