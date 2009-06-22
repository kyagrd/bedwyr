#include "popl-1a.mod".

#tactical bind_absurd then(
    find("bind _ _ _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _")),
    repeat(weak_l("cut _ _")),
    prove("1")).
#tactical instantiate then(repeat(sigma), repeat(then(and_r, try(eq_r)))).

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false)".

#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
prove.

#lemma absurd_tabs
  "pi c\t\e\l\r\ context c => of c (tabs t e) (arrow l r) =>
    false".
prove.
% Qed.

#lemma absurd_abs
  "pi c\t1\e\t2\t3\ context c => of c (abs t1 e) (all t2 t3) =>
    false".
prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#lemma app_progresses
  "pi c\e1\e2\t\ context c => of c (app e1 e2) t =>
    progresses e1 => progresses e2 =>
      progresses (app e1 e2)".
intros.
induction("auto", "of _ _ _").
and_r.
  cases.
    prove.
    prove.
    prove.
    then(mu_r, left, right).
    instantiate.
      force("T12", "t12").
      eq_r.
      prove.
      prove.
    prove.
  cases.
    weak_l("#2").
    weak_l("#3").
    cases("#4").
      cases("#5").
        cases("#4").
          prove.

          cut_lemma("absurd_tabs").
          prove.        
        prove.
      prove.
    prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#lemma tapp_progresses
  "pi c\e\t\ty\ context c => of c (tapp e ty) t =>
    progresses e =>
      progresses (tapp e ty)".
intros.
induction("auto", "of _ _ _").
and_r.
  cases.
    prove.
    prove.
    prove.
    then(mu_r, left, right).
    instantiate.
      force("T12", "t12").
      eq_r.
      prove.
      prove.
    prove.
  cases.
    weak_l("#2").
    cases("#4").
      cases("#4").
        cut_lemma("absurd_abs").
        prove.
        prove.
      prove.
    prove.
% Qed.

% Progress.
#set "firstorder.induction-unfold" "true".
#theorem progress "pi c\e\t\ context c => of c e t => progresses e".
intros.
induction("auto", "of _ _ _").
and_r.
  cases.
    prove.
    prove.
    prove.
    then(mu_r, left, right).
    instantiate.
      force("T12", "t12").
      eq_r.
      prove.
      prove.
    prove.
  cases.
    apply("#2", then(apply("context_w"), axiom)).
    prove.

    apply("#2", axiom).
    apply("#4", axiom).
    cut_lemma("app_progresses").
    prove.

    prove.

    apply("#3", axiom).
    cut_lemma("tapp_progresses").
    prove.

    prove.
% Qed.

