#debug off.

%Inductive definitions for lambda calculus.

#define "mem X G := sigma Y\L\ G = cons Y l, (X=Y ; mem X L)".

#define "term G X :=
	(sigma y\ mem X G);
	(sigma m\ n\ X = (app m n), (term G m), (term G n));
	(sigma m\ t\ X = (lambda t m), nabla x\ (term (cons x G) (m x)))".

#define "subterm X Y :=
 (X=Y);
 (sigma A\B\ X = (app A B), (subterm A Y ; subterm B Y));
 (sigma A\ X = (abs A), nabla a\ subterm (A a) Y)
".

#define "bind G V T :=
	(sigma G'\ G = (cons (pair V T) G'));
	(sigma G'\ V'\ T'\ G = (cons (pair V' T') G'), (bind G' V T))".

#define "typeof G M T :=
	(bind G M T);
	(sigma a\ m1\ m2\
		M = (app m1 m2),
		(typeof G m1 (arrow a T)),
		(typeof G m2 a));
	(sigma a\ b\ f\
		(M = (lambda a f)),
		(T = (arrow a b)),
		(nabla x\ (typeof (cons (pair x a) G) (f x) b)))".

#define "context G := pi x\t\ bind G x t => pi t'\ typeof G x t' => t=t'".

#theorem type_determinacy
  "pi g\x\t\ typeof g x t => context g => pi t'\ typeof g x t' => t=t'".
then(repeat(pi),imp).
induction("g\x\t\
           typeof g x t, (context g => pi t'\ (typeof g x t' => (t = t')))").
prove.
and.
then(mu_r,prove).
then(repeat(or_l),simplify).

% ******** Initial-rule case.
then(mu_l("context _"),prove).

% ******** App.
% The judgement is an instance of the initial rule.
then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
cut("typeof G (app h1 h2) T0").
then(mu_r,prove).
then(mu_l("context _"),prove).
% The real app-rule case is easy.
prove.

% ******** Lambda.
% The judgement is an instance of the initial rule.
then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
cut("typeof G (lambda h2 h3) (arrow h2 h4)").
then(mu_r,prove).
then(mu_l("context _"),prove).
% The real lambda-rule case.
then(cut("context G => nabla x\ context (cons (pair x h) G)"),try(prove)).
repeat(weak_l).

% The HUGE lemma: Well-formedness of the extended context.
then(simplify,then(mu_l,then(mu_r,simplify))).
abstract.
rotate_l.
% Either x is the fresh name, or it is in G and its abstraction is vacuous.
then(mu_l,then(or_l,simplify)).
 % EITHER.
 then(mu_l,then(repeat(or_l),simplify)).
 then(mu_l,then(or_l,simplify)).
 then(induction("l'\x'\t'\ pi l\ l'=(a\l) => x'=(x\x) => false"),prove).
 % OR.
 % Weakening of the generic context.
 induction("l'\x'\t'\ pi l\ l'=(x\l) =>
            sigma x\t\ x'=(a\x), t'=(a\t), bind l x t").
 rotate.
 then(or_l,simplify).
 then(repeat(sigma),then(repeat(and),orelse(eq,then(mu_r,prove)))).
 repeat(sigma).
 repeat(pi).
 imp.
 eq.
 simplify.
 then(repeat(and),orelse(eq_r,then(mu_r,prove))).
 % Now work on the typeof judgement.
 then(pi_l,then(imp_l,orelse(eq,simplify))).
 then(pi_l,then(pi_l,then(imp_l,try(axiom)))).
 rotate_l.
 % Weaken the context of typeof.
 induction("l'\x'\t'\ nabla a\ pi tl\x\t\
  l' = (a\ cons (pair a h2) tl) =>
  x' = (a\x) => t' = (a\t) =>
  typeof tl x t").
 rotate.
 then(repeat(or_l),simplify).
 abstract.
 then(mu_l,then(or_l,simplify)).
 then(mu_r,prove).
 then(repeat(pi_l),then(repeat(imp_l),try(eq))).
 abstract.
 eq.
 then(mu_r,prove).
 then(mu_r,right).
 then(repeat(sigma),then(repeat(and_r),try(eq))).
 abstract.
 then(repeat(pi_l),then(repeat(imp_l),try(eq))).

