% IWC Problem 17 (not done).
#open "../naturals.def".

#define
  "q {n} :=
    pi i\ leq i n =>
      (p i => ((p i => p (s i)), (p (s i) => p i))),
      (((p i => p (s i)), (p (s i) => p i)) => p i),
      (p n => ((p n => p o), (p o => p n))),
      (((p n => p o), (p o => p n)) => p n)".

#lemma l "pi n\ nat n => q (s n) => q n".
intros.
induction.
cases.
  mu_l.
  apply("#1", prove).
  mu_r.
  pi.
  imp_r.
  cases("#2").
  prove.

prove.

#set "firstorder.induction-unfold" "true".
#theorem dixon
  "pi n\ nat n => (q n => p o)".
intros.
induction.
cases.
  prove.
  mu_l("q.



