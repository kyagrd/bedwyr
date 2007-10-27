% Proof of the commutativity of plus.
#open "basic_definitions.def".

% Theorem: x + y = z => y + x = z.
#theorem plus_com "pi x\ y\ z\ (nat x, nat y, plus x y z) =>
	(plus y x z)".

% Lemma: x + 0 = x.
cut("pi x\ nat x => plus x o x").
simplify.
then(induction("x\ plus x o x"),prove).

% Lemma: x + y = z => x + (y + 1) = (z + 1).
cut("pi x\ y\ z\ (nat x, plus x y z)=>(plus x (s y) (s z))").
simplify.
then(induction("x\ pi y\ z\ plus x y z => plus x (s y) (s z)",
	       "nat x"),prove).

% Proving the theorem.
simplify.
induction("x\ pi y\ z\
  nat y =>
  plus x y z =>
  (pi x0\ (nat x0 => plus x0 o x0)) =>
  (pi x0\ y0\ z0\ ((nat x0, plus x0 y0 z0) => plus x0 (s y0) (s z0))) =>
  plus y x z", "nat x").
prove.
% At this point, prove actually works but takes a very long time.

then(or_l, simplify).
prove.
mu_l("plus _ _ _").
then(or_l, simplify).
pi("pi y\ _").
pi("pi z\ _").
imp_l.
axiom.
imp_l.
axiom.
imp.
prove.
imp.
prove.
prove.
% Qed.

