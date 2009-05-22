#include "pcf.mod".

#theorem subject_reduction "pi p\v\t\ eval p v => of p t => of v t".
% Induction on eval.
intros.
induction.

%Cases.
async.

  % Easy cases:
  iterate(try(prove("2"))).

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


