#open "picdefs.tac".

#theorem one "bisim z (rx (x\ out x x z))".
prove.
% Qed.

#theorem two "bisim (out a a z) (rx (x\ out x x z))".
prove.
% Failure is normal.

#theorem three "(bisim (out a a z) (rx (x\ out x x z))) => false".
prove.
% Qed.

