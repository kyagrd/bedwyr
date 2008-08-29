#define "inductive   dummy_mu x := foo".
#define "coinductive dummy_nu x := bar".

% Checking the polarities.
#theorem pat_pol "false, true, some_atom, dummy_nu 42
               => pi x\ sigma y\ x=y ; dummy_mu 42".
imp_r("-(_ => _)").
repeat(and_l("+(_, _)")).
pi_r("-(pi _)").
sigma_r("+(sigma _)").
nu_l("-(nu _)").
right("+(_;_)").
mu_r("+(mu _)").
async.
% Qed.

#theorem f "(pi w\ (nabla x\ (w=x))=>false)".
pi.
imp.
nabla.
eq.
% Qed.

% The eigen and logic vars have timestamps representing dependencies
% in a compact way. However some unifications on eigenvars can silently
% introduce inadequacies in that representation.

#theorem works "pi x\y\ sigma z\ z=y, (x=y => z=x)".
prove.
% Qed.

#theorem doesnt "pi x\y\ sigma z\ (x=y => z=x), z=y".
assert_fail(prove).
% Although z=x seems to have only one solution there are in fact two:
% either z is x or it is y. This is not llambda.

% An even more nasty bug related to level representation.
#theorem false "pi x\ sigma y\ pi z\ x = f z => y = g z".
assert_fail(prove).
% After the left equality, the level of z is lowered to that of x.
% Thus y = g z would be solvable. What happens in fact, if one looks beyond
% the level representation is that we have to solve Y (f z) = (g z),
% which is unsolvable and anyway outside of llambda.
