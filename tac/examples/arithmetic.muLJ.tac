#open "naturals.def".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
prove.
% Qed.

#theorem even_or_even_sss "pi x\ nat x => even x ; even (s (s (s x)))".
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
cases.
  prove.
  prove.
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

#theorem odd_half_s_double "pi x\y\z\ odd x => half x y => double y z => x = s z".
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
prove("4").
% Qed.
