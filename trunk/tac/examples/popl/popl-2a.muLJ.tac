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

#define "permute a b :=
  (pi m\t\ bind m t a => bind m t b), (pi m\t\ bind m t b => bind m t a)".

#define "context c :=
  pi x\t\ bind x t c =>
    (x = top => false),
    (pi t1\t2\ x = (arrow t1 t2) => false),
    (pi t1\t2\ x = (all t1 t2) => false)".

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
      force("T12", "t120").
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
      force("T12", "t120").
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
      force("T12", "t120").
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

#lemma invert_abs
  "pi c\s1\e\t1\t2\ context c => of c (abs s1 e) (arrow t1 t2) =>
    (sigma s2\ nabla x\
      of (cons (pair x s1) c) (e x) s2,
      sub c t1 s1,
      sub c s2 t2)".
admit.

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

#lemma sub_weak "pi c\s\t\ sub c s t => nabla x\ sub c s t".
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

#lemma sub_weak_context "pi c\s\t\ sub c s t => nabla x\ pi ty\ sub (cons (pair x ty) c) s t".
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
    apply("sub_weak").

  then(induction("l'\x'\t'\ pi x\ bind (l' x) (x' x) (t' x)"),prove).
  prove.

#set "firstorder.induction-unfold" "true".
#theorem preservation
  "pi c\e\v\t\ context c => of c e t => step e v =>
    of c v t".
intros.
induction("auto", "of _ _ _").
and_r.
  cases.
    prove.
    prove.
    prove.
    then(mu_r, left, right).
    instantiate.
      force("T12", "t120").
      eq_r.
      prove.
    prove.
    prove.
cases.
  prove.  
  
  cases("#6").
    cut_lemma("invert_abs").
    apply("#6", axiom, axiom).
    simplify.
    cut("of context6 e21 t4").
      % transitivity?
      admit.
    cut_lemma("of_subst").
    cut_lemma("of_cut").
    
  apply("#6", axiom, axiom).
  simplify.
  apply("#6",

  prove.
  admit.
  prove.
















