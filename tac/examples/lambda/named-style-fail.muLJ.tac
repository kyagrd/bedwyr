% Inductive definitions for lambda calculus, defined in a named way.
% Here, variables are denoted by a specific "var" constructor,
% instead of having a context of "free variables" as in other files.
% As a consequence the notion of "valid context" is more usual,
% and doesn't require as much work in the proof.
% On the other hand, this style of specification does not support
% substitution as immediately as the other, and reasoning about it
% can involve unification problems outside of the higher-order patterns.
% In the end, this experiment is far from being satisfying.

% The definition of "term" is just for clarifying, it is actually unused.

#define "term X :=
	(sigma y\ X = (var y));
	(sigma m\ n\ X = (app m n), (term m), (term n));
	(sigma m\ t\ X = (lambda t m), nabla x\ term (m (var x)))".

#define "bind {G} V T :=
	(sigma G'\ G = (cons (pair V T) G'));
	(sigma G'\ V'\ T'\ G = (cons (pair V' T') G'), (bind G' V T))".

#define "context {X} :=
	(X = nil);
	(sigma v\ t\ tl\
		(X = cons (pair v t) tl),
		(pi T'\ bind tl v T' => false),
		context tl)".

#define "typeof G {M} T :=
	(sigma v\ M = var v, bind G v T);
	(sigma a\ m1\ m2\
		M = (app m1 m2),
		(typeof G m1 (arrow a T)),
		(typeof G m2 a));
	(sigma a\ b\ f\
		(M = (lambda a f)),
		(T = (arrow a b)),
		(nabla x\ (typeof (cons (pair x a) G) (f (var x)) b)))".

#define "one {m} n :=
   (sigma f\t\x\ m = (app (lambda t f) x), n = (f x));
   (sigma m1\m2\n1\ m = app m1 m2, one m1 n1, n = app n1 m2);
   (sigma m1\m2\n2\ m = app m1 m2, one m2 n2, n = app m1 n2);
   (sigma m'\n'\ m = lambda t m', n = lambda t n',
                 nabla x\ one (m' (var x)) (n' (var x)))
".

#define "permute {a} {b} :=
   (pi m\t\ bind a m t => bind b m t), (pi m\t\ bind b m t => bind a m t)
".

#theorem context_s "pi g\t\ context g => nabla a\ context (cons (pair a t) g)".
simplify.
abstract.
mu_r.
right.
then(repeat(sigma),then(repeat(and),try(eq))).
prove.
prove.
% Qed.

#theorem bind_ww "pi g\m'\t\ (nabla a\ bind g (m' a) t) =>
                    sigma m\ m'=(a\m), bind g m t".
prove.
% Qed.

#theorem determinacy "pi G\ M\ T\
	(typeof G M T) =>
	(context G) =>
	(pi T'\ (typeof G M T') => (T = T'))".
simplify.
induction("G\M\T\ (context G => pi T'\ (typeof G M T' => (T = T')))").

% Invariant => Goal.
  prove.

% Invariant is invariant.
  then(repeat(or_l),simplify).

  % VAR.
   then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
   then(induction("G\ pi h\t\t'\ bind G h t => bind G h t' => t=t'",
                  "context _"),prove).

  % APP.
   prove.

  % LAM.
   then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
   imp_l.
   apply("context_s").
   prove.
   prove.
% Qed.

% Subject reduction shows a weakness of this approach: it requires several
% unification outside of the higher-order patterns fragment.
% As a result we have to do a lot more by hand, and eventually get stuck.
% (And we get all these warnings about abortions due to unhandled unifications.)
% Note, however, that a more powerful unification algorithm could be used to
% carry out the proof: this in not a problem of the logic, but a problem
% of its implementation -- although a serious one in our opinion.

#theorem subject_reduction "
  pi m\n\ one m n => pi g\t\ typeof g m t => typeof g n t
".
repeat(pi).
imp.
induction("m\n\ pi g\t\ typeof g m t => typeof g n t").
prove.
then(repeat(or_l),simplify).
rotate.
prove.
prove.
prove.
% The only interesting case: the beta redex.
async.
induction("g'\m'\t'\ pi g\m\t\
 (nabla x\ permute (g' x) (cons (pair x h12) g),
           (m' x)=(m (var x)), (t' x)=t) =>
 (typeof g h11 h12) => typeof g (m h11) t").
% Invariant => goal.
 repeat(pi_l).
 imp.
 nabla.
 repeat(and).
 force("G","g").
 prove.
 % Non-llambda unification, needs help.
 force("M","h10").
 eq_r.
 eq_r.
 imp.
 axiom.
 % Almost there, modulo non-llambda.
 admit.

% Invariance.
 then(repeat(or_l),simplify).
 % BIND.
 cut("nabla x\ bind (cons (pair x h12) g3) (h14 x) h15").
 prove.
 nabla.
 then(mu_l("bind _ _ _"),then(or_l,simplify)).
 % Again, we are only one unification away from the axiom.
 then(weak_l,weak_l).
 admit.
 % One non-llambda shy of completing.
 apply("bind_ww").
 simplify.
 repeat(weak_l("lift_bind _ _ _")).
 weak_l.
 weak_l("typeof _ _ _").
 % Another non-llambda...
 admit.

 % APP.
 % This case should really be trivial but there are several problems.
 % Again, some non-llambda unifs, like the one saying that m2 is an app.
 % But you can also see in the two induction hypothesis that there is
 % a serious mismatch between HOAS and named-style, in the equality
 % (x1\ h24 x1) = (x\ m4 (var x1)): we tried to keep substitution for free
 % by not having the var construct on bound variables, but it backfires now.
 % To treat it we would have to induct over an extra (term h24) hypo.
 admit.
 % LAM: same mess.
 admit.
% Not quite Qed.


