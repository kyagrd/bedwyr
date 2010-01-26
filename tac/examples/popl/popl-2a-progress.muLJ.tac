#open "popl.def".

#lemma absurd_tabs
  "pi oc\sc\t\e\l\r\
    context oc => context sc =>
    of oc sc (tabs t e) (arrow l r) =>
    false".
intros.
induction("auto", "of _ _ _ _").
cases.
  bind_absurd.
  prove.
% Qed.

#lemma absurd_abs
  "pi oc\sc\t1\e\t2\t3\
    context oc => context sc =>
    of oc sc (abs t1 e) (all t2 t3) =>
    false".
prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#lemma app_progresses
  "pi oc\sc\e1\e2\t\ context oc => context sc => of oc sc (app e1 e2) t =>
    progresses e1 => progresses e2 =>
      progresses (app e1 e2)".
intros.
then(induction("auto", "of _ _ _ _"),cases).
  bind_absurd.
  weak_l("#1").
  weak_l("#2").
  weak_l("#3").
  cases("#5").
    cases("#6").
      cases("#5").
        prove.
         cut_lemma("absurd_tabs").
        prove.        
      prove.
    prove.
  prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#lemma tapp_progresses
  "pi oc\sc\e\t\ty\
     context oc => context sc =>
     of oc sc (tapp e ty) t =>
     progresses e =>
     progresses (tapp e ty)".
intros.
then(induction("auto", "of _ _ _ _"),cases).
  bind_absurd.
  weak_l("#2").
  cases("#5").
    cases("#5").
      cut_lemma("absurd_abs").
      prove.
      prove.
    prove.
  prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#theorem progress
  "pi oc\sc\e\t\ context sc => of nil sc e t =>
    progresses e".
intros.
then(induction("auto", "of _ _ _ _"),cases).
  prove.

  prove.

  apply("#3", eq, axiom).
  apply("#5", eq, axiom).
  cut_lemma("app_progresses").
  intros("#7").
    force("Oc", "nil").
    prove.
  prove.

  prove.

  apply("#2", eq, axiom).
  cut_lemma("tapp_progresses").
  intros("#5").
    force("Oc0", "nil").
    prove.
  prove.

  prove.
% Qed.

