% Just checking the abstraction order.
#theorem test "(nabla x1\x2\x3\ p x2 x3) => (nabla x1\x2\x3\ p x2 x3)".
imp.
repeat(nabla_l).
abstract.
axiom.
% Qed.

#define "term x := sigma y\ x = abs y, nabla a\ term (y a)".

#theorem lift_unfold "pi x\ (nabla a\ term (x a)) => (nabla a\ term (x a))".
pi.
imp.
repeat(nabla_l).
mu_l.
sigma_l.
and_l.
eq_l.
abstract.
mu_r.
sigma_r.
and_r.
eq.
% Lifting and unfolding do not commute, hence the axiom does not apply.
% This is not a bug of the logic,
% which would have done "abstract" first.
admit.
% Not qed.
