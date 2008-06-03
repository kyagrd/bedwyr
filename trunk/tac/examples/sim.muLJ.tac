#open "basic_definitions.def".

% Simulation is reflexive.
#theorem ref "pi p\ sim p p".
pi.
coinduction("p\ q\ (p=q)").
eq_r.
simplify.
sigma.
and.
axiom.
eq_r.
% Qed.

#theorem ref_auto "pi p\ sim p p".
prove.
% Qed.

% Simulation is transitive.
#theorem trans "pi p\q\r\ sim p q => sim q r => sim p r".
simplify.
coinduction("p\r\ sigma q\ sim p q, sim q r").
prove.
simplify.
sigma.
and.
axiom.
% Something is broken, either in the display or the pushed abstractions.
% Qed.

#theorem trans_auto "pi p\q\r\ sim p q => sim q r => sim p r".
prove.
% Qed.
