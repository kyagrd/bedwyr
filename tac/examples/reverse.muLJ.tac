#open "lists.def".

#theorem reverse_image
  "pi x\ pi y\ reverse x y => reverse y x".
prove.
% Qed.

#tactical focl then(repeat(pi_l),then(repeat(imp_l),try(eq_r))).
#tactical focr repeat(orelse(orelse(sigma_r,eq_r),and_r)).

#theorem reverse_image
  "pi x\ pi y\ reverse x y => reverse y x".
simplify.
induction.
async.
prove.
then(mu_l,async).
focl.
prove.
focl.
then(mu_l,async).
then(induction,async).
prove.
focl.
axiom.
axiom.
mu_l.
then(or_l,simplify).
then(mu_r,right).
focr.
then(mu_r,right).
focr.
axiom.
axiom.
then(mu_r,right).
focr.
axiom.
% Qed.
