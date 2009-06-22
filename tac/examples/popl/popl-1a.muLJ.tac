#include "popl-1a.mod".

#lemma sub_refl "pi l\t\ closed l t => sub l t t".
prove.

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

#define "cut {c} {x} := pi a\b\ sub c a x => sub c x b => sub c a b".
#define "coinductive gcut {c} {x} :=
  cut c x, nabla y\ pi c'\ context c' => gcut c' x".

#define "narrowing {c} {t} :=
  pi s\t1\t2\ sub c s t =>
    nabla x\ context (cons (pair x t) c) =>
      sub (cons (pair x t) c) (t1 x) (t2 x) =>
        sub (cons (pair x s) c) (t1 x) (t2 x)".
#define "coinductive gnarrowing {c} {t} :=
  narrowing c t, nabla y\ pi c'\ context c' => gnarrowing c' t".
 
#lemma context_w
  "pi c\t\ context c => nabla x\ context (cons (pair x t) c)".
prove.

#lemma bind_w
  "pi x\t\c\ bind x t c => pi t'\ nabla n\ bind x t (cons (pair n t') c)".
intros.
induction.
cases.
  prove.
  pi_l.
  abstract.
  force("T'", "t'0").
  prove.

#lemma bind_s
  "pi c\x'\t'\ (nabla n\ bind (x' n) (t' n) c) =>
    sigma x\t\ x' = (a\ x), t' = (a\ t), bind x t c".
prove.

#set "firstorder.induction-unfold" "true".
#lemma sub_arrow
  "pi a\b\x\y\c\ context c => cut c a => cut c b =>
    sub c x (arrow a b) => sub c (arrow a b) y =>
      sub c x y".
intros.
induction("auto", "sub c x (arrow a b)").
and_r.
  % induction target.
  prove.
  
  % inductive case.
  then(simplify,cases).
    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
    then(mu_r,left,left,right). % TODO tactical bind_trans.
    prove.

    % sub - arrow.
    weak_l("#2").
    weak_l("#3").
    cases("#6").
      % sub - top.
      prove.

      % sub - bind reflexive.
      bind_absurd.

      %sub - bind transitive.
      bind_absurd.

      % sub - arrow.
      repeat(mu_l("cut _ _")).
      then(mu_r, left, right).  % unfold the arrow case.
      prove.

#lemma sub_all
  "pi c\a\b\a'\b'\x\ context c => cut c a => narrowing c a =>
    (nabla x\ cut (cons (pair x a') c) (b x)) =>
    sub c x (all a b) => sub c (all a b) (all a' b') =>
      sub c x (all a' b')".
intros.
induction("auto", "sub c x (all a b)").
and_r.
  % induction target.
  prove.

  % inductive case.
  then(simplify,cases).

    % sub - bind reflexive.
    bind_absurd.
    
    % sub - bind transitive.
    then(mu_r, left, left, right). % TODO tactical.
    instantiate.
    axiom.
    apply("#3", eq_r, axiom, axiom, axiom, prove, axiom).
    axiom.

    % sub - all.
    weak_l("#2"). % unusable hypothesis.
    weak_l("#3"). % unusable hypothesis.
    cases("#7").
      % sub - bind reflexive.
      bind_absurd.

      % sub - bind transitive.
      bind_absurd.

      % sub - all.
      then(mu_r, right).
      instantiate.
        mu_l("#4").
        apply("#4", axiom, axiom).
        axiom.

        nabla_r.
        mu_l("#5").
        apply("#5", axiom).
        nabla_l.
        apply("#5", then(apply("context_w"), axiom), axiom).
        mu_l("#6").
        apply("#6", axiom, axiom).
        axiom.

#set "firstorder.induction-unfold" "false".

#define "outer_inv g a1 :=
   (a1 = top);
   (sigma t\ bind a1 t g);
   (sigma t1\t2\
      a1 = (arrow t1 t2),
      (context g =>
       ((pi c\ context c => cut c t1),
        (pi c\ context c => narrowing c t1))),
      (context g =>
       ((pi c\ context c => cut c t2),
        (pi c\ context c => narrowing c t2))));
   (sigma t1\t2\
      a1 = (all t1 t2),
      (context g =>
       ((pi c\ context c => cut c t1),
        (pi c\ context c => narrowing c t1))),
      (nabla x\ context (cons (pair x t1) g) =>
          (pi c\ context c => cut c (t2 x)),
          (pi c\ context c => narrowing c (t2 x))))".

#set "firstorder.induction-unfold" "false".
#theorem sub_dual
  "pi g\t\ context g => type g t => 
    ((pi c\ context c => gcut c t),
    (pi c\ context c => gnarrowing c t))".
intros.
induction("auto", "type _ _").
intros.
cut("pi g\ context g => gcut g a10").

  % generalized cransitivity.
  intros.
  coinduction("auto", "gcut _ _").
  and_r.

    % cut.
    then(mu_r, intros).
    induction(
     "g\a\b\ (sub g a b)*,
        pi c\gt\ context gt => outer_inv gt b => context g =>
                 sub g b c => sub g a c",
     "sub c0 a5 x1").

      % invariant.
      simplify.
      intros("#5").
        force("Gt","a02").
        axiom.
      intros("#5").
        repeat(weak_l("mu _")).
        cases.
          then(mu_r,prove("0")).
          then(mu_r,prove("0")).
          then(mu_r,left,right).
          instantiate.
            then(weak_l("#2"),prove).
            then(weak_l,prove).
            then(mu_r,right).
            instantiate.
            then(weak_l("#2"),prove).
            then(weak_l, prove).
      apply("#5",axiom, axiom).
      axiom.

      % inductive.
      and_r.
        prove.
      cases.
        % top.
        weak_l("outer_inv _ _").
        prove.

        % bind (reflexive).
        weak_l("outer_inv _ _").
        prove.

        % bind (transitive).
        apply("#3","_","_","_").
        then(mu_r, left, left, right). % TODO tactical.
        prove.
        
        % arrow.
        weak_l("#2").
        weak_l("#3").
        cases("outer_inv _ _").
          bind_absurd.
          apply("#4", axiom).
          apply("#5", axiom).
          simplify.
          repeat(then(pi_l, imp_l, try(axiom("context context13")))).
          cut("sub context13 (arrow s11 s21) (arrow t16 t26)").
            then(mu_r, left, right).
            instantiate.
            prove.
            prove.
          cut_lemma("sub_arrow").
          apply("#11", "context context13", "cut _ t16", "cut _ t26", "_", "_").
          axiom.

        % all.
        weak_l("#2").
        weak_l("#3").
        cases("outer_inv _ _").
          bind_absurd.
     
          apply("#4", axiom).
          apply("#5", then(apply("context_w"), axiom)).
          simplify.
          weak_l("#3").
          cases("#8").
            prove.
            bind_absurd.
            bind_absurd.

            cut_lemma("sub_all").
            apply("#3", axiom).
            apply("#4", axiom).
            apply("#10", axiom, axiom, axiom).
            intros("#10").
              apply("#5", then(apply("context_w"), axiom)).
              prove.
            intros("#10").
              then(mu_r, right).
              instantiate.
                axiom.
                prove.
            intros("#10").
              then(mu_r, right).
              prove.
            axiom.

    % nabla cut.
    simplify.
    cases.
      prove.

      instantiate.
      then(left, left, right).
      instantiate.
      apply("bind_w").
      force("U0", "(x\ u8)").
      force("Context", "(x\ cons (pair x T') context20)").
      axiom.
      weak_l("#4").
      apply("context_w").
      axiom.
      axiom.
    
      instantiate.
      then(left, right).
      instantiate.
      intros.
        weak_l("#2").
        apply("#1", axiom).
        repeat(weak_l("mu _")).
        and_l.
        and_r.
          weak_l("#2").
          simplify.
          intros("#1").
          force("C1", "nil").
          prove.
          prove.

          weak_l.
          simplify.
          intros("#1").
          force("C2", "nil").
          prove.
          prove.
          nu_l.
          and_l.
          weak_l.
          abstract.
          apply("#1", axiom).
          axiom.
       intros.
       repeat(weak_l("mu _")).
       and_l.
       and_r.
        weak_l("#2").
        simplify.
        intros("#1").
        force("C3", "nil").
        prove.
        prove.
          
        weak_l.
        simplify.
        intros("#1").
        force("C4", "nil").
        prove.
        prove.

        force("Context0", "c'").
        axiom.
        axiom.
    
      instantiate.
      right.
      instantiate.
      apply("#1", axiom).
      intros("#2").
      apply("context_w").
      axiom.
      intros.
      repeat(weak_l("mu _")).
        weak_l("#2").
        admit.

        weak_l("#1").
        intros.
        admit.

        force("Context1", "c'").
        axiom.
        axiom.
      
    weak_l.
    weak_l.
    prove.

    weak_l.
    weak_l.
    prove.

  % Narrowing.
  intros.
  then(mu_r, intros).
  abstract.
  induction("auto", "lift_sub _ _ _").
  cases.

    % top.
    weak_l.
    prove.

    % bind reflexive.
    weak_l("#2").
    prove.

    % bind transitive.
    apply("#2", eq_r, eq_r, eq_r).
    force("A02", "a06").
    intros("#2").
      repeat(weak_l("mu _")).
      weak_l("#2").
      cases.
        prove.
        prove.
        then(left, right).
        instantiate.
          weak_l("#2").
          prove.
          weak_l.
          prove.
        right.
        instantiate.
          weak_l("#2").
          prove.
          weak_l.
          prove.
    weak_l("#3").
    apply("#2", axiom).
    intros("#2").
      repeat(weak_l("mu _")).
      prove.
    apply("#2", axiom, axiom, axiom).
    cases("#1").
      then(mu_r, left, left, right).
      instantiate.
      prove.
      % Here we use gcut.
      
    % arrow (long); this used to prove...
    weak_l("#5").
    apply("#2", eq_r, eq_r, eq_r, id).
      prove.
    apply("#4", eq_r, eq_r, eq_r, id).
      prove.
    weak_l("context a09").
    apply("#2", id).
      force("T0", "s3").
      force("C0", "h60").
      admit
    apply("#2", axiom, axiom).
    apply("#4", id).
      force("T1", "s3").
      force("C1", "h60").
      admit.
    apply("#4", axiom, axiom).
    prove.

    % all.
    weak_l("#5").
    apply("#2", eq_r, eq_r, eq_r, id).
      prove.
    apply("#4", eq_r, eq_r, id).
      force("A1'", "h68").
      force("C'", "(x1\ cons (pair x1 h73) h65)").
      admit.
    apply("#2", id).
      force("T2", "s4").
      force("C2", "h65").
      admit.
    apply("#2", axiom, axiom, axiom).
    apply("#4", id).
      prove.
    apply("#4", id).
      force("C'0", "h65").
      admit.
    apply("#4", axiom, id).
      admit.
    apply("#4", id).
      admit.
    then(mu_r, right).
    instantiate.
      prove.
    

