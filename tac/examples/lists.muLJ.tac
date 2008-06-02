% List definitions.
#open "basic_definitions.def".

#proof_output "/tmp".

% Equality Theorems.
#theorem equal_sym "pi x\ y\ list x => list y => equal x y => equal y x".
prove.
% It works better without the list hypothesis.
% TODO Find out why it doesn't work in the first attempt,
% inducting on the extra list hypothesis -- seems to me that it should.
% Qed.

% This works but takes a while.
#theorem equal_trans
  "pi x\ y\ z\ list x => list y => list z =>
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

% Epic fail with the old statement:
%  pi x\ y\ z\ r\ list x => list y => list r =>
%    (sigma w\ list w => append x y w => append w z r) =>
%    (sigma w\ list w => append y z w => append x w r)
% which I'm not sure what it means.
% Works decently as follows.
#theorem append_assoc
  "pi x\ y\ z\ xy\ yz\ xy_z\ x_yz\ list x => list y => list z =>
    (append x y xy, append xy z xy_z, append y z yz, append x yz x_yz)
    => xy_z = x_yz".
simplify.
prove.

% Should fail.
#theorem reverse_image
  "pi x\ y\ (list x, list y, reverse x y) => reverse y x".
prove.

