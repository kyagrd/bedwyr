#open "lemmas.muLJ.tac".

% This lemma is actually the most difficult bit of the proof.
#lemma typeof_w "
  pi ta\l\m\t'\
   (nabla a\ typeof (cons (pair a ta) l) m (t' a)) =>
   (sigma t\ t'=(a\t), typeof l m t)
".
intros.
abstract.
induction("l'\m'\t'\
  pi m\a\ta\l\
       (nabla a\ permute (cons (pair a ta) l) (l' a), (m' a)=m)
    => (sigma t\ t'=(a\t), typeof l m t)").
prove.
abstract.
cases.

  % ==== Bind ====.
  cut_lemma("bind_ww").
  prove.

  % ==== App ====.
  % This one works poorly without the progress annotation on typeof,
  % which strictly speaking is wrong: good example of user tweak.
  prove.

  % ==== Abs ====.
  intros("#1").
    apply("lift_permute_s").
    weak_l.
    force("M'","h3").
    force("Ta'","(a\ta2)").
    force("L'","(a\ cons (pair a h2) l2)").
    prove.
  prove.
% Qed.

% Note that this notion of well-formed context is stronger than usual.
#define "context G := pi x\t\ bind G x t => pi t'\ typeof G x t' => t=t'".

#lemma context_s "pi x\ context x => nabla a\ context x".
intros.
abstract.
induction.
cut_lemma("bind_www").
cut_lemma("typeof_ww").
prove.
% Qed.

#lemma context_ss "pi c\t\ context c =>
                       nabla a\ context (cons (pair a t) c)".
intros.
apply("context_s").
weak_l.
then(mu_l,then(mu_r,simplify)).
then(mu_l,then(or_l,simplify)).
  then(mu_l,async).
    prove.
    apply("bind_www").
    prove.
  apply("bind_www").
  cut_lemma("typeof_w").
  cut_lemma("typeof_s").
  prove.
% Qed.

#set "firstorder.induction-unfold" "true".
#theorem type_determinacy
  "pi g\x\t\ typeof g x t => context g => pi t'\ typeof g x t' => t=t'".
intros.
induction.
cases.
prove.
prove.
cut_lemma("context_ss").
prove.
% Qed.

