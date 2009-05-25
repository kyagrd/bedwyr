#include "stlc.mod".
#open "diverge.def".

#lemma eval_det "pi e\v1\v2\ eval e v1 => eval e v2 => v1 = v2".
prove.

#theorem step_det "pi e1\e2\e3\ step e1 e2 => step e1 e3 => e2 = e3".
intros.
induction.
async.
mu_l.
async.
weak_l("true").
weak_l("true").
examine.


#theorem nstep_det "pi e\r1\r2\ nstep e (abs r1) => nstep e (abs r2) => r1 = r2".
admit.

#theorem nstep_det "pi e\r\ nstep e (abs r) => eval e (abs r)".
admit.

#theorem eval_sr "pi e\v\t\ eval e v => of e t => of v t".
prove.

#theorem step_sr "pi e1\e2\t\ step e1 e2 => of e1 t => of e2 t".
admit.

#theorem nstep_sr "pi e1\e2\t\ nstep e1 e2 => of e1 t => of e2 t".
admit.

#theorem self_diverge "diverge (app (abs (x\ (app x x))) (abs (x\ (app x x))))".
prove.

#theorem eval_or_diverge "pi x\y\ eval x y => diverge x => false".
intros.
induction.
async.

  prove.

  nu_l.
  async.
  prove.
  