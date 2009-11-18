#include "popl-1a.mod".

#tactical bind_absurd then(
    find("bind _ _ _"),
    repeat(weak_l("pi _")),
    repeat(weak_l("_ => _")),
    repeat(weak_l("_ , _")),
    repeat(weak_l("sub _ _ _ _")),
    repeat(weak_l("cut _ _")),
    prove("1")).
#tactical instantiate then(repeat(sigma), repeat(then(and_r, try(eq_r)))).

#define "permute a b :=
  (pi m\t\ bind m t a => bind m t b), (pi m\t\ bind m t b => bind m t a)".

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false),
    (pi t\e\ x = (abs t e) => false),
    (pi t\e\ x = (tabs t e) => false),
    (pi e1\e2\ x = (app e1 e2) => false),
    (pi t\e\ x = (tapp t e) => false)".

#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
prove.

#lemma permute_w "pi l\ l'\ permute l l' => nabla x\ permute l l'".
intros.
then(mu_l, mu_r, and_r, simplify).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma lift_permute_s
  "pi l\l'\ (nabla x\ permute (l x) (l' x)) =>
    nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l, mu_r, and_r, simplify).
  weak_l("#2").
  prove.
  weak_l.
  prove.

#lemma permute_refl
  "pi m\n\ permute m n => permute n m".
prove.

#lemma bind_w "pi l\x\t\ bind x t l => nabla a\ bind x t l".
prove.

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

% Progress.
#set "firstorder.induction-unfold" "true".
#theorem progress
  "pi oc\sc\e\t\ context sc => of nil sc e t =>
    progresses e".
intros.
then(induction("auto", "of _ _ _ _"),cases).
  prove.

  prove.

  apply("#2", eq, axiom).
  apply("#4", eq, axiom).
  cut_lemma("app_progresses").
  intros("#6").
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

% === Preservation ===.

#lemma sub_w "pi c\s\t\ sub c s t => nabla x\ sub c s t".
intros.
abstract.
induction.
cases.
  prove.

  then(mu_r, left, left, left, right).
  instantiate.
  force("U'", "(x\ u)").
  apply("bind_w").
  axiom.

  then(mu_r, left, left, right).
  instantiate.
    force("U'0", "(x\ u0)").
    apply("bind_w").
    axiom.    
  prove.

  prove.
  prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#lemma invert_abs
  "pi s1\e\t1\t2\
    of nil nil (abs s1 e) (arrow t1 t2) =>
    (sigma s2\ nabla x\
      of (cons (pair x s1) nil) nil (e x) s2,
      (t1=s1 ; sub nil t1 s1),
      (s2=t2 ; sub nil s2 t2))".
simplify.
then(induction("auto", "of _ _ _ _"),cases).
% Bind: absurd.
bind_absurd.
% Abs: invert.
prove.
% Subtyping.
then(mu_l("sub _ _ _"),cases).
bind_absurd.
bind_absurd.
weak_l.
apply("#1",eq_r,eq_r,eq_r,eq_r).
simplify.
sigma.
abstract.
repeat(and_r).
axiom.
then(or_l,simplify).
apply("sub_w").
prove.
% Uses transitivity of subtyping, lifted.
admit.
weak_l("_;_").
weak_l("sub _ _ _").
then(or_l,simplify).
apply("sub_w").
prove.
admit.
% Qed.

#lemma invert_tabs
  "pi c\s1\e\t1\t2\ context c => of c (tabs s1 e) (all t1 t2) =>
    (sigma s2\ nabla x\
      of (cons (pair x s1) c) (e x) (s2 x),
      sub c t1 s1,
      sub (cons (pair x t1) c) (s2 x) (t2 x))".
admit.

#lemma transitivity
  "pi g\t\ context g => type g t => pi c\ context c => cut c t".
admit.

#set "firstorder.induction-unfold" "false".
#lemma of_sub_trans
  "pi c\e\s\t\ of c e s => sub c s t => of c e t".
prove.

#lemma lift_of_sub_trans
  "pi c\e\s\t\ nabla x\ of (c x) e s => sub (c x) s t =>
    of (c x) e t".
prove.
% Qed.

#lemma sub_w_context "pi c\s\t\ sub c s t => nabla x\ pi ty\ sub (cons (pair x ty) c) s t".
intros.
abstract.
induction.
cases.
  prove.
  
  then(mu_r, left, left, left, right).
  instantiate.
  force("U'", "(x\ u)").
  apply("bind_w").
  prove.

  then(mu_r, left, left, right).
  instantiate.
    force("U'0", "(x\ u0)").
    apply("bind_w").
    prove.
  prove.

  prove.

  then(mu_r, right).
  instantiate.
    prove.
    pi_l("#2").
    force("Ty'", "(x1\(x2\ ty4 x2))").
    admit.


#lemma sub_permute
  "pi c\c'\s\t\ sub c s t => permute c c' => sub c' s t".
intros.
induction("auto", "sub _ _ _").
cases.
  prove.
  prove.
  prove.
  prove.

  then(mu_r, right).
  instantiate.
    prove.
    abstract.
    intros("#2").
      force("C''", "(x\ cons (pair x t10) c'4)").
      cut_lemma("permute_cons").
      prove.
      admit.
    apply("#1", axiom, axiom).
    axiom.

#lemma sub_permute_2
  "pi c\c'\s\t\ sub c s t => permute c' c => sub c' s t".
cut_lemma("sub_permute").
cut_lemma("permute_refl").
prove.
% Qed.

#lemma of_permute
  "pi c\c'\s\t\ context c => of c s t => permute c c' => of c' s t".
intros.
induction("auto", "of _ _ _").
cases.
  apply("#1", then(apply("context_w"), axiom)).
  force("C'", "(x\ cons (pair x t1) c'0)").
  intros("#1").
    apply("permute_w").
    prove.
  then(mu_r, left, left, left, left).
  instantiate.
  prove.

  prove.
  
  then(mu_r, left, left, right).
  instantiate.
  intros.
  intros("#1").
    cut_lemma("sub_permute_2").
    apply("#4", axiom, axiom).
    prove.
  apply("#1", axiom, axiom).
  axiom.

  then(mu_r, left, right).
  instantiate.
    force("T12", "t120").
    eq_r.
  prove.

  cut_lemma("sub_permute").
  prove.

  apply("#1", axiom, axiom).
  cut_lemma("sub_permute").
  prove.

#lemma of_weak
  "pi g\m\t\ of g m t => pi t'\ nabla x\ of (cons (pair x t') g) m t".
intros.
induction("g\m\t\ nabla x\ pi g'\ permute g' (cons (pair x t') g) =>
  of g' m t").

  % Invariant.
  prove.

  % Inductive.
  cases.
    
    % abstraction.
    apply("lift_permute_s").
    weak_l("lift_permute _ _").
    intros("#1").
      force("G'''", "(x1\(x2\ cons (pair x1 t1) (g' x2)))").
      prove.
    prove.


    % application.
    prove.

    % type abstraction.
    admit.

    % type application.
    then(mu_r, left, right).
    instantiate.
      force("T12", "(x\ t120)").
      eq_r.
    force("T11", "(x\ t110)").
    intros("#1").
      force("G''", "g'2").
      prove.
    prove.
    admit. % need sub with context weakening.

    % transitivity.
    admit.

#lemma of_cut "pi g\m\n\tm\tn\
  of (cons (pair n tn) g) m tm => of g n tn => of g m tm".
intros.
induction("gg\m\tm\ pi g\ permute gg (cons (pair n tn) g) =>
           of g n tn => of g m tm").
  pi_l.
  force("G", "g").
  prove.

  cases.
    intros("#1").
      force("G0", "(n1\ cons (pair n1 t1) g0)").
      weak_l("of _ _ _").
      apply("permute_w").
      weak_l("permute _ _").
      prove.
    apply("of_weak").
    prove.

    then(mu_r, left, left, left, right).
    prove.

    admit.

    admit.
    
    apply("#1", axiom, axiom).
    admit.

#set "firstorder.induction-unfold" "false".
#lemma of_subst
  "pi g\m\t\ (nabla x\ of (g x) (m x) (t x)) =>
    (pi x\ of (g x) (m x) (t x))".
simplify.
abstract.
induction.
cases.
  prove.
  prove.
  then(mu_r, left, left, right).
  instantiate.
  intros.
  intros("#1").
    apply("sub_w").

  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
  prove.

#theorem preservation
  "pi c\e\v\t\ context c => of c e t => step e v =>
    of c v t".
intros.
induction("auto", "step _ _").
and_r.
  prove.
cases.
  admit.
  admit.
  admit.
  admit.
  admit.

