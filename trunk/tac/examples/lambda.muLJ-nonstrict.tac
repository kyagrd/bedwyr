%Inductive definitions for lambda calculus.
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
then(repeat(pi),imp).
induction("G\M\T\ (context G => pi T'\ (typeof G M T' => (T = T')))").

% Invariant => Goal.
  prove.

% Invariant is invariant.
  then(repeat(or_l),simplify).

  % VAR.
   then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
   induction("G\ pi h\t\t'\ bind G h t => bind G h t' => t=t'",
             "context _").
   % Goal IS the invariant.
   repeat(pi_l).
   imp_l.
   axiom.
   imp_l.
   axiom("bind G h1 T").
   then(eq_l,eq_r).
   % VAR/mu(context): Invariance.
   then(or_l,simplify).
   mu_l.
   then(or_l,simplify).
   % Cons case of induction over ctxt.
   mu_l("bind _ _ _").
   then(or_l,simplify).
   mu_l.
   then(or_l,simplify).
   prove.
   mu_l("bind (cons _ _) _ _").
   then(or_l,simplify).
   prove.
   weak_l("pi _").
   % TODO prove.
   then(repeat(pi_l),repeat(imp_l)).
   axiom.
   axiom("bind _ _ t").
   then(eq_l,eq_r).

  % APP.
   mu_l("typeof _ _ _").
   prove.

  % LAM.
   mu_l("typeof _ _ _").
   then(repeat(or_l),simplify).
   eq_l.
   eq_l.
   imp_l.

   % Let's do the conclusion first.
   rotate.
   then(pi_l,then(imp_l,try(axiom))).
   then(eq_l,eq_r).
  
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
   induction("G\ nabla n\ bind G n T' => false","context G").
   then(nabla_l,imp_l).
   axiom.
   false.
   then(or_l,simplify).
   mu_l.
   then(or_l,simplify).
   eq_l.
   eq_l.
   mu_l("bind (cons _ _) _ _").
   then(or_l,simplify).
   eq_l.
   imp_l.
   axiom.
   false.

%Yay.

