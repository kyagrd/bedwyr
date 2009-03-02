#open "../examples/lists.def".

#theorem reverse_total "pi x\ list x => sigma y\ reverse x y".
% TODO prove.
admit.

#theorem reverse_length
  "pi x\ y\ n\ reverse x y => length x n => length y n".
prove.

#theorem reverse_inverse
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

#define "outer {x} y := rev x nil y".

#lemma rev_total "pi x\ list x => sigma y\ outer x y".
% TODO.
admit.

% Theorems about rev:
#lemma rev_n "rev nil nil nil".
prove.

#lemma rev_nil_x
  "pi x\ rev nil nil x => x = nil".
prove.

#lemma rev_nil_x_nil
  "pi x\ rev nil x nil => x = nil".
prove.

#theorem rev_x_nil
  "pi x\ (list x => rev x nil nil => x = nil)".
% TODO.
admit.

#theorem rev_length
  "pi x\ y\ n\ rev x nil y => length x n => length y n".
% TODO.

#theorem reverse_rev
  "pi x\ y\ n\ reverse x y => rev x nil y".
% TODO.

