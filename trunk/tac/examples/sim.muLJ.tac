#open "C:\zRXer\Projects\SlimmerSVN\trunk\tac\examples
	\basic_definitions.def".

% Simulation is reflexive.
#theorem ref "pi p\ (sim p p)".
pi.
coinduction("p\ q\ (p=q)").
eq.
eq.
repeat(pi).
imp.
sigma.
and.
axiom.
eq.

% Simulation is transitive.
#theorem trans "pi p\ q\ r\ (sim p q)=>((sim q r)=>(sim p r))".
simplify.
coinduction("p\ r\ (sigma q\ (sim p q),(sim q r))").

 % Check that the coinvariant is satisfied.
 sigma.
 then(and, axiom).

 % Check the coinvariance of the coinvariant.
 simplify.
 nu_l.
 then(repeat(pi_l),imp_l).
 axiom.
 simplify.
 nu_l("sim q q0").
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

