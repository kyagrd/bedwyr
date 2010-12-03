#open "popl.def".

% "Import" part 1a.
#lemma sub_refl "pi l\t\ type l t => sub l t t".
prove.
% Qed.

#lemma lift_sub_refl "pi l\t\t'\
   type l t =>
   nabla x\ type (cons (pair x t) l) (t' x) =>
     sub (cons (pair x t) l) (t' x) (t' x)".
admit.
% Qed.

#lemma one_a
  "pi c\t\ context c => type c t => gcut t, gnarrowing t".
admit.
% Qed.

#lemma lift_one_a
  "nabla n\ pi c\t\ context c => type c t => gcut t, gnarrowing t".
admit.
% Qed.

#lemma sub_trans
  "pi a\b\c\ type nil b =>
     sub nil a b => sub nil b c => sub nil a c".
intros.
cut("context nil").
prove.
apply("one_a").
and_l.
nu_l("gcut _").
and_l.
weak_l("lift_gcut _").
prove.
% Qed.

#lemma lift_sub_trans
  "pi t\t'\ nabla n\ pi a\b\c\
     type (cons (pair n t') nil) b =>
     sub (cons (pair n t) nil) a b =>
     sub (cons (pair n t) nil) b c =>
     sub (cons (pair n t) nil) a c".
simplify.
cut("nabla x\ type (cons (pair x t) nil) (b x)").
repeat(weak_l("sub _ _ _")).
abstract.
induction("l'\b\ pi l\
                  (nabla x\ permute (l' x) (cons (pair x t') (l x))) =>
                  (nabla x\ type (cons (pair x t) (l x)) (b x))").
% Invariant => goal.
cut("nabla x\ permute (cons (pair x t') nil) (cons (pair x t') nil)").
then(repeat(weak_l),prove).
abstract.
apply("#1",axiom).
axiom.
% Invariance.
cases.
prove.
prove.
prove.
abstract.
pi_l.
apply("#1",axiom).
pi_l.
imp_l.
weak_l.
force("L'","(x1\(x2\ cons (pair x1 (t1'0 x2)) (l2 x2)))").
apply("lift_permute_s").
weak_l.
prove.
% TODO name shuffling.
admit.
% Now we have our type judgement on the right context.
weak_l.
abstract.
cut("nabla x\ context (cons (pair x t) nil)").
then(repeat(weak_l),prove).
abstract.
apply("lift_one_a").
and_l.
nu_l("lift_gcut _").
prove.
% Qed.

#lemma sub_narrow "
   pi a\b\ sub nil a b =>
   nabla x\ pi t\t'\
    sub (cons (pair x b) nil) t t' =>
    sub (cons (pair x a) nil) t t'".
admit.


% INVERSION LEMMAS.

#set "firstorder.induction-unfold" "true".

#lemma invert_abs
  "pi s1\e\t1\t2\
    type nil t1 => type nil t2 =>
    of nil nil (abs s1 e) (arrow t1 t2) =>
    (sigma s2\
      (nabla x\ of (cons (pair x s1) nil) nil (e x) s2),
      (t1=s1 ; sub nil t1 s1),
      (s2=t2 ; sub nil s2 t2))".
simplify.
then(induction("auto", "of _ _ _ _"),cases).
% Bind: absurd.
bind_absurd.
% Abs: invert.
prove.
% Subtyping.
then(mu_l("sub _ _ _"),cases,try(bind_absurd)).
then(mu_l("type _ (arrow _ _)"),cases,try(bind_absurd)).
weak_l("of _ _ _ _").
apply("#3",eq_r,eq_r,eq_r,eq_r,axiom,axiom).
simplify.
sigma.
abstract.
repeat(and_r).

 axiom.

 then(or_l,simplify).

  prove.

  % Uses transitivity of subtyping, lifted.
  apply("sub_trans").
  prove.

 weak_l("_;_").
 weak_l("sub _ _ _").
 then(or_l,simplify).
 prove.
 % TODO apply might be too naive here.
 cut_lemma("sub_trans").
 apply("#8","type nil t24",axiom,axiom).
 prove.
% Qed.

#lemma invert_tabs
  "pi s1\e\t1\t2\
    type nil (all t1 t2) =>
    of nil nil (tabs s1 e) (all t1 t2) =>
    (sigma s2\
      sub nil t1 s1,
      nabla x\
        of nil (cons (pair x s1) nil) (e x) (s2 x),
        sub (cons (pair x t1) nil) (s2 x) (t2 x))".
simplify.
then(induction("auto","of _ _ _ _"),cases).
% Bind: absurd.
bind_absurd.
% Forall.
weak_l("#2").
then(cases("type nil (all _ _)"),try(bind_absurd)).
instantiate.
then(apply("sub_refl"),prove).
nabla.
and.
axiom.
apply("lift_sub_refl").
axiom.
% Sub.
then(cases("sub _ _ _"),try(bind_absurd)).
apply("#3",eq_r,eq_r,eq_r,eq_r,axiom).
simplify.
then(cases("#1"),try(bind_absurd)).
instantiate.
then(apply("sub_trans"),prove).
nabla.
and.
abstract.
axiom.
cut_lemma("sub_narrow").
abstract.
apply("#10","sub nil t13 t14").
apply("#10",axiom).
cut_lemma("lift_sub_trans").
abstract.
apply("#11","lift_type _ (x1\ t25 x1)",axiom,axiom).
axiom.
% Qed.

#set "firstorder.induction-unfold" "true".

% MAIN THEOREM.

#theorem preservation
  "pi e\v\t\
     type nil t =>
     of nil nil e t => step e v => of nil nil v t".
intros.
then(induction("auto", "of _ _ _ _"),cases).
% Bind: absurd in the empty context.
bind_absurd.
% Arrow: no evaluation possible.
cases("step _ _").
% App.
cases("step _ _").
  % Case beta.
  repeat(weak_l("pi _")).
  cut_lemma("invert_abs").
  apply("#5",axiom,axiom,axiom).
  simplify.
  weak_l("of _ _ _ _").
  repeat(weak_l("type _ _")).
  admit.
  % Reduction on the left of an app.
  admit.
  % Reduction on the right.
  admit.
% Forall.
cases("step _ _").
% Tapp.
admit.
% Sub.
prove.
% Qed.


% #lemma of_sub_trans
%  "pi oc\sc\e\s\t\ of oc sc e s => sub sc s t => of oc sc e t".
%prove.

%#lemma lift_of_sub_trans
%  "pi c\e\s\t\ nabla x\ of (c x) e s => sub (c x) s t =>
%    of (c x) e t".
%prove.
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



