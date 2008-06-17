#open "naturals.def".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
prove.
% Qed.

#theorem half_total "pi x\ nat x => sigma h\ half x h".
prove.
% Qed.

% Not quite the same proof, step by step.
#theorem half_total "pi x\ nat x => sigma h\ half x h".
simplify.
induction("x\ nat x, pi y\ leq y x => sigma h\ half y h").
prove.
async.
prove.
% Note that prove alone is slower.
then(and,prove).
% Qed.

#theorem half_double "pi x\y\ double x y => half y x".
prove.
% Qed.

#theorem even_half_double "pi x\y\ even x => half x y => double y x".
prove.
% Qed.

#theorem test_ack "sigma a\ ack (s (s o)) (s (s o)) a, a = a".
sigma.
and.
prove("10").
% If you're curious to see the result.
eq.
% Qed.

#theorem ack_nat "pi x\y\z\ nat y => ack x y z => nat z".
prove.
% Qed.

#theorem ack_total "pi x\ nat x => pi y\ nat y => sigma a\ ack x y a, nat a".
then(pi,imp).
induction.
async.
prove.
induction(
 "y\ nat y, pi h\ (pi y1\ nat y1 => sigma a\ ack h y1 a, nat a) => sigma a\ ack (s h) y a, nat a)").
prove.
% Invariance.
async.
prove.
and.
prove.
prove.
% Qed.
