#open "picdefs.tac".
#time on.

#theorem one "bisim z (rx (x\ out x x z))".
prove.
% Qed.

#theorem two "bisim (out a a z) (rx (x\ out x x z))".
prove.
% Failure is normal.

#theorem three "(bisim (out a a z) (rx (x\ out x x z))) => false".
prove.
% STUCK.

#tactical somesyn
   repeat(orelse(left, orelse(right, orelse(sigma_r, orelse(and_r,eq_r))))).

