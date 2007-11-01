#open "picdefs.tac".

#theorem one "bisim z (rx (x\ out x x z))".
prove.
#theorem two "bisim (out a a z) (rx (x\ out x x z))".
prove.
#theorem three "(bisim (out a a z) (rx (x\ out x x z))) => false".
prove.

#tactical somesyn repeat(orelse(left, orelse(right, orelse(sigma_r, orelse(and_r,eq_r))))).

