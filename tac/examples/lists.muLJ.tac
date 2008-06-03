% List definitions.
#open "basic_definitions.def".

% Equality Theorems.
#theorem equal_sym "pi x\ y\ list x => list y => equal x y => equal y x".
prove.
% It works better without the list hypothesis.
% TODO Find out why it doesn't work in the first attempt,
% inducting on the extra list hypothesis -- seems to me that it should.
% Qed.

% This works but takes a while.
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

#theorem append_assoc
  "pi x\ y\ z\ xy\ yz\ xy_z\ x_yz\ list x => list y => list z =>
    (append x y xy, append xy z xy_z, append y z yz, append x yz x_yz)
    => xy_z = x_yz".
prove.
% Qed.

