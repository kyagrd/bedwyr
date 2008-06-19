#open "definitions.def".

#theorem permute_example "
 pi a\b\ta\tb\l\la\
   permute (cons (pair a ta) l) la =>
   permute (cons (pair b tb) la) (cons (pair a ta) (cons (pair b tb) l))
".
prove.
% Qed.

% This is not interesting for the development,
% just a test that required some extra work in prove
% (logic vars on the left and progress)
#theorem stupid "pi l\ sigma l'\
   pi a\b\c\d\ bind (cons (pair c d) l') a b
            => bind (cons (pair c d) l ) a b".
prove.
% Qed.

#theorem bind_w  "pi l\x\t\ (nabla a\ bind l x t) => bind l x t".
prove.
% Qed.

#theorem bind_ww "pi l\x\t'\ (nabla a\ bind l x (t' a))
                  => sigma t\ t'=(a\t), bind l x t".
prove.
% Qed.

#theorem bind_www "pi l\x'\t'\ (nabla a\ bind l (x' a) (t' a))
              => sigma x\t\ x'=(a\x), t'=(a\t), bind l x t".
prove.
% Qed.

#theorem bind_s "pi l\x\t\ bind l x t => nabla a\ bind l x t".
prove.
% Qed.

#theorem permute_s "pi l\l'\ permute l l' => nabla a\ permute l l'".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

#theorem lift_permute_s "pi l\l'\ (nabla x\ permute (l x) (l' x))
                         => nabla a\x\ permute (l x) (l' x)".
simplify.
then(mu_l,then(mu_r,then(and_r,simplify))).
rotate_l.
weak_l.
prove.
weak_l.
prove.
% Qed.

% This lemma is actually the most difficult bit of the proof.
#theorem typeof_w "
  pi ta\l\m\t'\
   (nabla a\ typeof (cons (pair a ta) l) m (t' a)) =>
   (sigma t\ t'=(a\t), typeof l m t)
".
abstract.
simplify.
induction("l'\m'\t'\
  pi m\a\ta\l\
       (nabla a\ permute (cons (pair a ta) l) (l' a), (m' a)=m)
    => (sigma t\ t'=(a\t), typeof l m t)").
prove.
abstract.
then(repeat(or_l),simplify).

% ==== Bind ====.
rotate_l.
then(mu_l,simplify).
weak_l.
then(focus,then(repeat(sync),try(unfocus))).
rotate_l.
weak_l.
then(mu_l,then(or_l,simplify)).
apply("bind_ww").
weak_l.
simplify.
prove.

% ==== App ====.
prove.

% ==== Abs ====.
repeat(pi_l).
imp_l.
apply("lift_permute_s").
weak_l.
force("M'","h4").
force("Ta'","(a\ta2)").
force("L'","(a\ cons (pair a h2) l2)").
prove.
simplify.
weak_l("lift_permute _ _").
prove.
% Qed.

% Note that this notion of well-formed context is stronger than usual.
#define "context G := pi x\t\ bind G x t => pi t'\ typeof G x t' => t=t'".

#theorem typeof_ww "pi g\m\t'\ (nabla a\ typeof g m (t' a)) =>
                     sigma t\ t'=(a\t), typeof g m t".
simplify.
abstract.
induction.
async.
apply("bind_ww").
prove.
prove.
then(focus,repeat(sync)).
unfocus.
prove.
% Qed.

#theorem context_s "pi x\ context x => nabla a\ context x".
simplify.
then(mu_l,then(mu_r,simplify)).
apply("bind_www").
weak_l("lift_bind _ _ _").
simplify.
apply("typeof_ww").
weak_l("lift_typeof _ _ _").
prove.
% Qed.

#theorem typeof_s "pi g\m\t\ typeof g m t => nabla a\ typeof g m t".
simplify.
abstract.
induction.
async.
apply("bind_s").
prove.
prove.
prove.
% Qed.

#theorem context_ss "pi c\t\ context c =>
                       nabla a\ context (cons (pair a t) c)".
simplify.
apply("context_s").
weak_l.
then(mu_l,then(mu_r,simplify)).
then(mu_l,then(or_l,simplify)).
then(mu_l,async).
prove.
apply("bind_www").
weak_l("lift_bind _ _ _").
async.
apply("bind_www").
simplify.
pi_l.
pi_l.
imp_l.
axiom.
weak_l("lift_bind _ _ _").
weak_l("bind _ _ _").
apply("typeof_w").
simplify.
apply("typeof_s").
weak_l("lift_typeof _ _ _").
weak_l("typeof _ _ _").
prove.
% Qed.

#theorem type_determinacy
  "pi g\x\t\ typeof g x t => context g => pi t'\ typeof g x t' => t=t'".
then(repeat(pi),imp).
induction("g\x\t\
           typeof g x t, (context g => pi t'\ (typeof g x t' => (t = t')))").
prove.
and.
prove.
then(repeat(or_l),simplify).

% ******** Initial-rule case.
then(mu_l("context _"),prove).

% ******** App.
then(mu_l("typeof _ (app _ _) _"),then(repeat(or_l),simplify)).
% The typeof judgement is an instance of the initial rule.
cut("typeof g0 (app h10 h11) t'2").
prove.
then(mu_l("context _"),prove).
% The essential app-rule case is easier.
prove.

% ******** Lambda.
then(mu_l("typeof _ (lambda _ _) _"),then(repeat(or_l),simplify)).
cut("typeof g0 (lambda h8 h14) t'3").
prove.
then(mu_l("context _"),prove).
% The real lambda-rule case.
apply("context_ss").
weak_l("context _").
prove.
% Qed.
