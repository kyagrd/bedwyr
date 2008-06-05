#open "naturals.def".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
prove.
% Qed.

#theorem half_total "pi x\ nat x => sigma h\ half x h".
prove.
% Qed.

% Not quite the same.
#theorem half_total "pi x\ nat x => sigma h\ half x h".
simplify.
induction("x\ nat x, pi y\ leq y x => sigma h\ half y h").
prove.
async.
prove.
% Note that prove alone is slower.
then(and,prove).
% Qed.

% TODO #theorem half_double "pi x\y\ half x y => (x=s o => false) => double y x".

#theorem test_ack "sigma a\ ack (s (s o)) (s (s o)) a, a = a".
sigma.
and.
prove.
% If you're curious to see the result.
eq.
% Qed.

#theorem ack_nat "pi x\y\z\ nat y => ack x y z => nat z".
simplify.
rotate_l.
prove.
% TODO don't be sensitive to the order.
% Qed.

#theorem ack_total "pi x\ nat x => pi y\ nat y => sigma a\ nat a, ack x y a".
then(pi,imp).
induction.
async.
prove.
rotate_l.
contract_l.
% TODO contract_l(nat _) should work.
induction(
 "y\ nat y => (pi y1\ nat y1 => sigma a\ nat a, ack h y1 a) => sigma a\ ack (s h) y a, nat a").
rotate.
% Invariance.
% Case n=0.
async.
pi_l.
force("Y1","s o").
prove.
% Case n>0.
imp_l.
axiom.
imp_l.
prove.
simplify.
pi_l.
force("Y10","a").
imp_l.
axiom.
simplify.
sigma.
force("A","a0").
prove.
% Invariant => goal.
% prove doesn't work, at least not quickly.
imp_l.
prove.
imp_l.
prove.
pi_l.
imp.
eq.
rotate_l.
weak_l.
weak_l.
% prove should really work here.
sigma_l.
sigma_r.
then(and,then(simplify,then(repeat(freeze),prove))).
% Qed.
