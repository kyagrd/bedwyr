% Inductive definitions for lambda calculus, defined in a named way.

#define "term X :=
	(sigma y\ X = (var y));
	(sigma m\ n\ X = (app m n), (term m), (term n));
	(sigma m\ t\ X = (lambda t m), nabla x\ term (m (var x))".

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
   % The context extended with a fresh variable is still a context.
   mu_r.
   right.
   repeat(sigma_r).
   repeat(and).
   eq.
   simplify.
   % The fresh variable can't be bound in G.
   then(induction("G\ nabla n\ bind G n (T' n) => false","context G"),
     then(abstract,prove)).
   induction("G\ nabla x\ context G","context _").
   prove.
   then(repeat(or_l),simplify).
   prove.
   abstract.
   then(mu_r,right).
   then(repeat(sigma),then(repeat(and),simplify)).
   then(induction("l'\x'\t'\
     pi l\ l'=(x\l) => sigma x\t\ x'=(a\x), t'=(a\t), bind l x t"),prove).
   prove.
   prove.
% Qed.


