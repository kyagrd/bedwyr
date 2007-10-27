#open "basic_definitions.def".

% Simulation is reflexive.
#theorem ref "pi p\ (sim p p)".
pi.
then(coinduction("p\ q\ (p=q)"),prove).
% Qed.

% Simulation is transitive.
#theorem trans "pi p\q\r\ sim p q => sim q r => sim p r".
simplify.
then(coinduction("p\r\ sigma q\ sim p q, sim q r"),prove).
% Qed.
