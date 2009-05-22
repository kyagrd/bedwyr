#open "bisimulation.def".

% Simulation is reflexive, step by step.
#theorem sim_refl "pi p\ sim p p".
pi.
coinduction("p\q\ p=q").
eq_r.
async.
sigma.
and.
axiom.
eq_r.
% Qed.

#theorem sim_refl "pi p\ sim p p".
prove.
% Qed.


% Simulation is transitive, slow motion.
#theorem sim_trans "pi p\i\q\ sim p i => sim i q => sim p q".
simplify.
coinduction("p\q\ sigma j\ sim p j, sim  j q").
prove.
prove.
% Qed.

#theorem sim_trans "pi p\q\r\ sim p q => sim q r => sim p r".
prove.
% Qed.


% Bisimulation is reflexive.
#theorem bisim_refl "pi p\ bisim p p".
prove.

