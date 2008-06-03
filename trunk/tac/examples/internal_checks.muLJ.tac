#define "inductive   dummy_mu x := foo".
#define "coinductive dummy_nu x := bar".

% Checking the 
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

