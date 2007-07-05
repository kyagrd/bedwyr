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
repeat(pi).
imp.
induction("G\M\T\ (context G => pi T'\ (typeof G M T' => (T = T')))").

% Invariant => Goal.
  simplify.
  imp_l.
  axiom.
  then(pi_l,imp_l).
  % TODO Two goals.
  axiom.
  then(eq_l,eq_r).

% Invariant is invariant.
  repeat(or_l).

  % VAR.
   simplify.
   then(mu_l("typeof _ _ _"),then(repeat(or_l),simplify)).
   % TODO simplify should have done the job of the next tactic.
   iterate(try(eq_l)).
   induction("G\ bind G h T' => bind G h T0 => T0=T'",
             "context _").
   % Goal IS the invariant.
   imp_l.
   axiom.
   imp_l.
   axiom.
   then(eq_l,eq_r).
   % VAR/mu(context): Invariance.
   then(or_l,simplify).
   mu_l.
   then(or_l,then(repeat(orelse(sigma_l,and_l)),eq_l("nil = cons _ _"))).
   % TODO repeat(eq_l) is bugged.
   % Cons case of induction over ctxt.
   mu_l("bind _ _ _").
   then(or_l,simplify).
   mu_l.
   then(or_l,simplify).
   eq_r.
   then(pi_l,imp_l).
   axiom.
   false.
   mu_l("bind (cons _ _) _ _").
   then(or_l,simplify).
   then(pi_l,imp_l).
   axiom.
   false.
   imp_l.
   axiom.
   imp_l.
   axiom.
   then(eq_l,eq_r).

  % APP.
   simplify.
   mu_l("typeof _ _ _").
   then(repeat(or_l),simplify).
   eq_l.
   imp_l.
   axiom.
   pi_l.
   imp_l.
   axiom.
   eq_l.
   eq_r.
   eq_l.

  % LAM.
   simplify.
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

