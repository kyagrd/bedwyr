% Proof of the commutativity of plus.
#open "basic_definitions.def".
#proof_output ".\".

% Theorem: x + y = z => y + x = z.
#theorem plus_com "pi x\ y\ z\ (nat x, nat y, plus x y z) =>
	(plus y x z)".
prove.
% Qed.


% Theorem: (x + y) + z = x + (y + z).
#theorem plus_trans "pi r\ x\ y\ z\
  (sigma w\ (plus x y w, plus w z r)) =>
  (sigma w\ (plus x w r, plus y z w))".
prove.

% Theorem: x = y => y = z => x = z.
#theorem eq_assoc "pi x\ y\ z\ x = y => y = z => x = z".
prove.
% Qed.

% Theorem: 2 + 2 = 4.
#theorem bla "plus (s (s o)) (s (s o)) (s (s (s (s o))))".
prove.
% Qed.

% Lemma: x + 0 = x.
% cut("pi x\ nat x => plus x o x").
% simplify.
% then(induction("x\ plus x o x"),prove("0")).

% Lemma: x + y = z => x + (y + 1) = (z + 1).
% cut("pi x\ y\ z\ (nat x, plus x y z)=>(plus x (s y) (s z))").
% simplify.
% then(induction("x\ pi y\ z\ plus x y z => plus x (s y) (s z)",
	       "nat x"),prove("0")).

% Proving the theorem.
% simplify.
% then(induction("x\ pi y\ z\
%   nat y =>
%   plus x y z =>
%   (pi x0\ (nat x0 => plus x0 o x0)) =>
%   (pi x0\ y0\ z0\ ((nat x0, plus x0 y0 z0) => plus x0 (s y0) (s z0))) =>
%   plus y x z", "nat x"),prove("0")).
% Qed.


