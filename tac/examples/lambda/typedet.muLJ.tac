#debug off.
#proof_output "/tmp".

#theorem permute_example "
 pi a\b\ta\tb\l\la\
   permute (cons (pair a ta) l) la =>
   permute (cons (pair b tb) la) (cons (pair a ta) (cons (pair b tb) l))
".
simplify.
then(mu_l,then(mu_r,simplify)).
% An async conjunction helps a lot.
then(and,simplify).
iterate(prove("0")).
% Setting the bound to 1 makes it quite boring.
% With bound 0 it seems a bit faster with sync conj.
% Qed.

% This technical lemma is actually the most difficult bit of the proof.
#theorem core_lemma "
  pi ta\l\m\
   (nabla a\ sigma t\ typeof (cons (pair a ta) l) m t) =>
   (sigma t\ typeof l m t)
".
abstract.
simplify.
induction("l'\m'\t'\
  pi m\a\ta\l\
       (nabla a\ permute (cons (pair a ta) l) (l' a), (m' a)=m)
    => (sigma t\ t'=(a\t), typeof l m t)").
prove("0").
abstract.
then(repeat(or_l),simplify).

% ==== Bind ====.
then(cut("nabla a\ bind (cons (pair a ta) l1) h4 (T'0 a)"),abstract).
prove("0").
weak_l.
weak_l.
mu_l.
then(or_l,simplify).
then(induction("l'\x'\t'\
 pi ta\l\x\ (l'=(a\l), x'=(a\x)) =>
          (sigma t\ t'=(a\t), bind l x t)
"),prove("1")).

% ==== App ====.
prove("1").
% The previous one (with bound 2 or 1) takes FOREVER with async conjunctions!!!.
% Even in sync conj it's over-expensive with bound 0, but instantaneous with 1.
% In both too-long cases, we get lots of "logvar on the left".

% ==== Abs ====.
repeat(pi_l).
imp_l.
force("M'","h1").
force("Ta'","(a\ta)").
force("L'","(a\ cons (pair a h) l)").
then(and,try(eq)).
then(cut("nabla x2\x1\ permute (cons (pair x1 ta) l) (G' x1)"),abstract).
% Lifting lift_permute.
then(mu_l,then(mu_r,simplify)).
then(and_r,simplify).
% <=== .
induction("l''\m''\t''\ pi l'\ l''=(a\l') =>
  sigma m'\t'\ m''=(a\m'), t''=(a\t'), nabla a\ bind (l' a) (m' a) (t' a)").
% I need a tactic for doing this kind of simplification.
pi_l.
imp_l.
eq.
simplify.
abstract.
then(pi_l,then(pi_l,then(imp_l,try(axiom)))).
then(induction("x\y\z\ nabla b\ nabla a\ bind (x a) (y a) (z a)"),
  then(abstract,prove("0"))).
prove.
% ===> .
induction("l''\m''\t''\ pi l'\ l''=(a\l') =>
  sigma m'\t'\ m''=(a\m'), t''=(a\t'), nabla a\ bind (l' a) (m' a) (t' a)").
then(pi_l,then(imp_l,try(eq))).
then(simplify,abstract).
weak_l("pi _").
then(pi_l,then(pi_l,then(imp_l,try(axiom)))).
then(induction("x\y\z\ nabla b\ nabla a\ bind (x a) (y a) (z a)"),
  then(abstract,prove("0"))).
prove.
% This is permute_example lifted twice, (used to be) ouch.
weak_l.
then(mu_r,then(mu_l,then(and_r,simplify))).
prove("0").
prove("0").
simplify.
prove("0").
% Qed.

% Note that this notion of well-formed context is stronger than usual.
#define "context G := pi x\t\ bind G x t => pi t'\ typeof G x t' => t=t'".

#theorem type_determinacy
  "pi g\x\t\ typeof g x t => context g => pi t'\ typeof g x t' => t=t'".
then(repeat(pi),imp).
induction("g\x\t\
           typeof g x t, (context g => pi t'\ (typeof g x t' => (t = t')))").
prove.
and.
then(mu_r,prove("1")).
then(repeat(or_l),simplify).

% ******** Initial-rule case.
then(mu_l("context _"),prove).

% ******** App.
then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
% The judgement is an instance of the initial rule.
cut("typeof G (app h1 h2) T0").
then(mu_r,prove("1")).
then(mu_l("context _"),prove("1")).
% The real app-rule case is easy.
prove.

% ******** Lambda.
then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
% The judgement is an instance of the initial rule.
cut("typeof G (lambda h2 h3) (arrow h2 h4)").
then(mu_r,prove("1")).
% The previous one is too long, TODO tweak bounds.
then(mu_l("context _"),prove("1")).
% The real lambda-rule case.
cut("context G => nabla x\ context (cons (pair x h) G)").
rotate.
prove("1").
repeat(weak_l).

% The HUGE lemma: Well-formedness of the extended context.
then(simplify,then(mu_l,then(mu_r,simplify))).
abstract.
rotate_l.
% EITER x is the fresh name, OR it is in G and its abstraction is vacuous.
then(mu_l,then(or_l,simplify)).
 % EITHER.
 then(mu_l,then(repeat(or_l),simplify)).
 then(mu_l,then(or_l,simplify)).
 then(induction("l'\x'\t'\ pi l\ l'=(a\l) => x'=(x\x) => false"),prove).
 % OR.
 % Ground the binding judgement.
 induction("l'\x'\t'\ pi l\ l'=(x\l) =>
            sigma x\t\ x'=(a\x), t'=(a\t), bind l x t").
 rotate.
 prove.
 % Now work on the typeof judgement.
 then(pi_l,then(imp_l,orelse(eq,simplify))).
 then(pi_l,then(pi_l,then(imp_l,try(axiom)))).
 rotate_l.
 % See the lemma above.
 % Weaken the context of typeof.
 induction("l'\x'\t'\ pi tl\x\
  (nabla a\ permute (l' a) (cons (pair a h2) tl), (x' a)=x) =>
  sigma t\ t'=(a\t), typeof tl x t").
 prove.
 rotate.



