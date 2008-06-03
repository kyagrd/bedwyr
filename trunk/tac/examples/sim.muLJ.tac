#open "basic_definitions.def".

% Simulation is reflexive, step by step.
#theorem ref "pi p\ sim p p".
pi.
coinduction("p\q\ p=q").
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

% Simulation is transitive, slow motion.
#theorem trans "pi p\i\q\ sim p i => sim i q => sim p q".
simplify.
coinduction("p\q\ sigma j\ sim p j, sim  j q").
prove.
simplify.
% Work on sim p0 j.
then(
 then(focus,then(repeat(sync),unfocus)),
 simplify).
rotate_l.
rotate_l.
% Work on sim j q0.
then(
 then(focus,then(repeat(sync),unfocus)),
 simplify).
% We have all we need.
then(repeat(orelse(sigma,and)),axiom).
% Qed.

#theorem trans_auto "pi p\q\r\ sim p q => sim q r => sim p r".
prove.
% Qed.

