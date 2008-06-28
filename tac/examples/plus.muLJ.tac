% Proof of the commutativity of plus.
#open "naturals.def".

% Thawing (now the default) is needed here.
#set "firstorder.frozens" "thaw".

% Theorem: x + y = z => y + x = z.
#theorem plus_com "pi x\ y\ z\ nat y => plus x y z => plus y x z".
prove.
% Qed.

% Theorem: (x + y) + z = x + (y + z).
#theorem plus_trans "pi r\ x\ y\ z\
  (sigma w\ (plus x y w, plus w z r)) =>
  (sigma w\ (plus x w r, plus y z w))".
prove.
% Qed.

% Theorem: x = y => y = z => x = z.
#theorem eq_assoc "pi x\ y\ z\ x = y => y = z => x = z".
prove.
% Qed.

% Theorem: 2 + 2 = 4.
#theorem bla "plus (s (s o)) (s (s o)) (s (s (s (s o))))".
prove.
% Qed.

#theorem plus_o "pi x\ nat x => plus x o x".
prove.
% Qed.

#theorem plus_s "pi x\y\z\ plus x y z => plus x (s y) (s z)".
prove.
% Qed.

#theorem plus_total "pi x\y\z\ nat x => sigma z\ plus x y z".
prove.
% Qed.
