#open "lists.def".

#theorem reverse_length
  "pi x\ y\ n\ reverse x y => length x n => length y n".
prove.

#theorem reverse_image
  "pi x\ pi y\ reverse x y => reverse y x".
prove.
% Qed.

% Proof of the above, by hand.  This proof is based off the
% proof generated automatically by prove, which is why it is
% hard to read!
#tactical focl then(repeat(pi_l),then(repeat(imp_l),try(eq_r))).
#tactical focr repeat(orelse(orelse(sigma_r,eq_r),and_r)).

#theorem reverse_image
  "pi x\ pi y\ reverse x y => reverse y x".
simplify.
induction.
async.
prove.
then(mu_l,async).
prove.
then(mu_l,async).
prove.
then(induction,async).
prove.
focl.
axiom.
axiom.
axiom.
prove.
% Qed.
