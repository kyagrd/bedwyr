% Inductive definitions for lambda calculus.

#define "term X :=
	(sigma y\ X = (var y));
	(sigma m\ n\ X = (app m n), (term m), (term n));
	(sigma m\ t\ X = (lambda t m), nabla x\ (term m x))".

#define "bind G V T :=
	(sigma G'\ G = (cons (pair V T) G'));
	(sigma G'\ V'\ T'\ G = (cons (pair V' T') G'), (bind G' V T))".

#define "context X :=
	(X = nil);
	(sigma v\ t\ tl\
		(X = cons (pair v t) tl),
		(pi T'\ bind tl v T' => false),
		context tl)".

#define "typeof G M T :=
	(sigma v\ M = var v, bind G v T);
	(sigma a\ m1\ m2\
		M = (app m1 m2),
		(typeof G m1 (arrow a T)),
		(typeof G m2 a));
	(sigma a\ b\ f\
		(M = (lambda a f)),
		(T = (arrow a b)),
		(nabla x\ (typeof (cons (pair x a) G) (f (var x)) b)))".


#theorem sr "pi G\ M\ T\
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
   mu_l("typeof _ _ _").
   then(repeat(or_l),simplify).
   then(imp_l,try(prove("1"))).
   % The context extended with a fresh variable is still a context.
   mu_r.
   right.
   repeat(sigma_r).
   repeat(and).
   eq.
   rotate.
   % NOTE This axiom only works in non-strict.
   axiom.
   simplify.
   % The fresh variable can't be bound in G.
   induction("G\ nabla n\ bind G n (T' n) => false","context G").
   prove.
   prove.
% Yay.
