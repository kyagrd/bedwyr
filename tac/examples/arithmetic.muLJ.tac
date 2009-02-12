#open "naturals.def".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
prove.
% Qed.

#theorem even_or_odd "pi x\ nat x => even x ; odd x".
prove.
% Qed.

#theorem even_plus_even "pi x\y\z\ even x => even y => plus x y z => even z".
prove.
% Qed.

#theorem even_double_even "pi x\y\ double x y => even y".
prove.
% Qed.

#theorem even_and_odd "pi x\y\ even x => odd y => even_and_odd x y".
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

% Yet another one, probably the simplest.
#theorem half_total "pi x\ nat x => sigma h\ half x h".
simplify.
then(
 induction("x\ (sigma h\ half x h); (sigma p\ x = s p, sigma h\ half p h)"),
 prove).
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
% We basically want to do the following:
% induction(
%  "y\ nat y, pi h\ (pi y1\ nat y1 => sigma a\ ack h y1 a, nat a) =>
%        sigma a\ ack (s h) y a, nat a)").
% We get the same with induction-unfold, modulo some garbage.
#set "firstorder.induction-unfold" "true".
induction.
async.
prove.
and.
prove.
async.
rotate_l.
rotate_l.
pi_l.
imp_l.
eq.
rotate_l.
pi_l.
% TODO it seems that "prove" is defeated by the need for the following guess.
force("H","h2").
prove.
% Qed.

