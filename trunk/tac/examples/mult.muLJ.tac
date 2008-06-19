% Proof of the commutativity of mult.
#open "naturals.def".

% Theorem: x + y = z => y + x = z.
#theorem plus_com "pi x\ y\ z\ (nat x, nat y, plus x y z) =>
  (plus y x z)".
prove.
% Qed.

% Theorem: (x + y) + z = x + (y + z).
#theorem plus_trans
  "pi r\ x\ y\ z\
    (sigma w\ (plus x y w, plus w z r)) =>
    (sigma w\ (plus x w r, plus y z w))".
prove.

% Theorem: x * y = z => y * x = z.
% #theorem mult_com
%   "pi x\ y\ z\
%     (nat x, nat y, mult x y z) =>
%     (mult y x z)".
% TODO.
