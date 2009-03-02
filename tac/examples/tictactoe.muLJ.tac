#open "tictactoe.def".

#theorem flip_involution
  "pi b1\ pi b2\ pi b3\ flip b1 b2, flip b2 b3 => b1 = b3".
prove.
% Qed.

#theorem flip_symmetric
  "pi b1\ pi b2\ flip b1 b2 => flip b2 b1".
prove.
% Qed.

#theorem t2 "pi x\ l\ k\ l2\ k2\
  (flip l l2, move l x k, flip k k2) => move l2 x k2".
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

% From to this point it's too costly.

#theorem symmetry_symmetric
  "pi b1\ pi b2\ symmetry b1 b2 => symmetry b2 b1".
prove("6").
% Qed.

#theorem flip_xwin
 "pi b1\ pi b2\ pi w\ xwins b1, flip b1 b2 => xwins b2".
prove.
% Qed.

% Another theorem to consider, but it's too long in automated mode.
% #theorem symmetry_xwins
%   "pi b1\ pi b2\ pi w\ xwins b1, symmetry b1 b2 => xwins b2".
