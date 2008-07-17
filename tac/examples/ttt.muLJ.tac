#open "ttt.def".

#theorem flip_involution
  "pi b1\ pi b2\ pi b3\ flip b1 b2, flip b2 b3 => b1 = b3".
prove.
% Qed.

#theorem flip_symmetric
  "pi b1\ pi b2\ flip b1 b2 => flip b2 b1".
prove.
% Qed.

#theorem flip_winner
  "pi b1\ pi b2\ pi w\ winner w b1, flip b1 b2 => winner w b2".
prove.
% Qed.

#theorem symmetry_winner
  "pi b1\ pi b2\ pi w\ winner w b1, symmetry b1 b2 => winner w b2".
prove.
% Qed

#theorem symmetry_symmetric
  "pi b1\ pi b2\ symmetry b1 b2 => symmetry b2 b1".
prove("6").
% Qed.

#theorem flip_xwin
 "pi b1\ pi b2\ pi w\ xwins b1, flip b1 b2 => xwins b2".
prove.
% Qed.

#theorem symmetry_xwins
  "pi b1\ pi b2\ pi w\ xwins b1, symmetry b1 b2 => xwins b2".
prove("6").
% DM's machine, 3 hours, didn't finish. 17.07.08



