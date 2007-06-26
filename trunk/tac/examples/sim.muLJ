#open "basic_definitions.tac".

% Simulation is reflexive.
#theorem ref "pi p\ (sim p p)".
pi.
coinduction("sim", "p\ q\ (p=q)").
eq.
repeat(pi).
eq_l.
imp.
sigma.
and.
axiom.
eq.

% Simulation is transitive.
#theorem trans "pi p\ q\ r\ (sim p q)=>((sim q r)=>(sim p r))".
simplify.
coinduction("sim", "p\ r\ (sigma q\ (sim p q),(sim q r))").

 % Check that the coinvariant is satisfied.
 sigma.
 then(and, axiom).

 % Check the coinvariance of the coinvariant.
 simplify.
 nu_l("sim").
 then(repeat(pi_l),imp_l).
 axiom.
 simplify.
 rotate_l.
 rotate_l.
 nu_l("sim").
 then(repeat(pi_l),imp_l).
 axiom.
 simplify.
 sigma_r.
 and.
 axiom.
 sigma.
 and.
 axiom.
 axiom.






