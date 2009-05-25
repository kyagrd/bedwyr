#open "pcf.def".

#tactical do then(right, repeat(orelse(sigma_r, orelse(and_r, eq_r)))).
#tactical of_axiom then(mu_r, do).
#tactical of_rec then(mu_r, then(left, do)).
#tactical of_app then(mu_r, then(left, then(left, do))).
#tactical of_abs then(mu_r, then(left, then(left, then(left, do)))).
#tactical of_if then(mu_r, then(left, then(left, then(left, then(left, do))))).
#tactical of_is_zero then(mu_r, then(left, then(left, then(left, then(left, then(left, do)))))).
#tactical of_pred then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, do))))))).
#tactical of_succ then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, do)))))))).
#tactical of_zero then(mu_r, then(left, then(left, then(left, then(left, then(left, then(left, then(left, then(left, do))))))))).
#tactical invert then(mu_l, async).

#define "context c := pi x\t\t'\ of c x t => of c x t' => t = t'".


#theorem subject_reduction
  "pi p\v\t\c\ context c => eval p v => of c p t => of c v t".
% Induction on eval.
intros.
rotate_l.
async.

induction.

%Cases.
async.

  % Easy cases:
  iterate(try(prove("0"))).

  % Succ.
  invert.
  of_succ.
  prove.
  
  
  

  % REC.
  % This sucks: we need (of (rec h8 h7) t12) after unfolding it to
  % apply the inductive hypothesis.
  contract_l("of _ _").
  prove.

%Qed.

#theorem eval_determinacy "pi e\v1\v2\ eval e v1 => eval e v2 => v1 = v2".
prove.

#theorem of_determinacy "pi e\t1\t2\ of e t1 => of e t2 => t1 = t2".
intros.
induction.
async.

  % Easy cases:
  iterate(try(prove("1"))).


  mu_l.
  async.
  pi_l.
  imp_l.
  prove.


