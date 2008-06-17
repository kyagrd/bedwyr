% List definitions.
#open "lists.def".

% Equality Theorems.
#theorem equal_sym "pi x\ y\ list x => list y => equal x y => equal y x".
prove.
% It works better without the list hypothesis.
% Qed.

% Again, the list hypothesis are useless,
% but a good test.
#theorem equal_trans
  "pi x\ y\ z\
    list x => list y => list z =>
    equal x y => equal y z => equal x z".
prove.
% Qed.

% Append Theorems.
#theorem append_nil_1 "pi x\ list x => append x nil x, append nil x x".
prove.

#theorem append_nil_2
  "pi x\ y\ list x, list y, append x y nil => x = nil, y = nil".
prove.

#theorem append_equal_nil
  "pi x\ y\ list x, list y, append x nil y => equal x y".
prove.

#set "firstorder.lemmabound" "true".

#theorem sublist_refl "pi x\ list x => sublist x x".
prove.
% Qed.

#set "firstorder.lemmabound" "false".

#theorem append_assoc
  "pi x\ y\ z\ xy\ yz\ xy_z\ x_yz\ list x => list y => list z =>
    (append x y xy, append xy z xy_z, append y z yz, append x yz x_yz)
    => xy_z = x_yz".
prove.
% Qed.

% Avoid an infinite loop of "progressing" unfoldings.
#theorem neq_trap "pi x\y\ equal x (cons a y) => equal x y => false".
prove.
% Qed.

% Same, different order.
#theorem neq_trap "pi x\y\ equal x y => equal x (cons a y) => false".
prove.
% Qed.

#theorem simple_trap "pi x\ equal x (cons foo x) => false".
prove.

#theorem other_trap "pi x\ delayeq x (cons foo x) => false".
prove.

% Also check that prove doesn't loop on:
% #theorem check "sigma x\ equal x (cons foo x)".
% prove.

