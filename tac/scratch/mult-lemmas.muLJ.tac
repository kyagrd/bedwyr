% Proof of the commutativity of mult.
#open "../examples/naturals.def".

#set "firstorder.lemmas" "true".
#set "firstorder.lemmas.bound" "0".

% Theorem: x + y = z => y + x = z.
#theorem plus_com "pi x\ y\ z\ (nat x, nat y, plus x y z) =>
  (plus y x z)".
prove.
% Qed.

% Theorem: (x + y) + z = x + (y + z).
#lemma plus_assoc
  "pi r\ x\ y\ z\
    (sigma w\ (plus x y w, plus w z r)) =>
    (sigma w\ (plus x w r, plus y z w))".
prove.

% Theorem: x * 0 = 0.
#lemma mult_zero "pi x\ nat x => mult x o o".
prove.

#lemma mult_succ
  "pi x\y\z\r\
    mult x y z => plus x z r =>
    mult x (s y) r".
% TODO prove.
admit.

% Theorem: x * y = z => y * x = z.
#theorem mult_com
  "pi x\ y\ z\
    nat x => nat y => mult x y z =>
    mult y x z".
prove.
% Qed.
