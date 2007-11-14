% Inductive definitions for lambda calculus, defined in a named way.
% Here, variables are denoted by a specific "var" constructor,
% instead of having a context of "free variables" as in other files.
% As a consequence the notion of "valid context" is more usual,
% and doesn't require as much work in the proof.

#define "nat X := X=0 ; sigma Y\ X = s Y, nat Y".

% The definition of "term" is just for clarifying, it is actually unused.

#define "term X :=
	(sigma y\ X = (var y));
	(sigma m\ n\ X = (app m n), (term m), (term n));
	(sigma m\ t\ X = (lambda t m), nabla x\ term (m (var x)))".

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

#define "one m n :=
   (sigma f\t\x\ m = (app (lambda t f) x), n = (f x));
   (sigma m1\m2\n1\ m = app m1 m2, one m1 n1, n = app n1 m2);
   (sigma m1\m2\n2\ m = app m1 m2, one m2 n2, n = app m1 n2);
   (sigma m'\n'\ m = lambda t m', n = lambda t n',
                 nabla x\ one (m' (var x)) (n' (var x)))
".

#define "permute a b :=
   (pi m\t\ bind a m t => bind b m t), (pi m\t\ bind b m t => bind a m t)
".

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
   % Lifting the "context" judgment.
   induction("G\ nabla x\ context G","context _").
   prove.
   then(repeat(or_l),simplify).
   prove.
   abstract.
   then(mu_r,right).
   then(repeat(sigma),then(repeat(and),simplify)).
   % Un-lifting the "bind" judgment.
   then(induction("l'\x'\t'\
     pi l\ l'=(x\l) => sigma x\t\ x'=(a\x), t'=(a\t), bind l x t"),prove).
   prove.
   prove.
% Qed.

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
% The only interesting case.
then(mu_l,then(repeat(or_l),simplify)).
then(mu_l,then(repeat(or_l),simplify)).
abstract.
induction("g'\m'\t'\ pi g\m\t\
 (nabla x\ permute (g' x) (cons (pair x h) g), (m' x)=(m (var x)), (t' x)=t) =>
 (typeof g h2 h) => typeof g (m h2) t").
repeat(pi_l).
imp.
nabla.
repeat(and).
force("G","g").
prove.
force("M","h2").
eq_r.
eq_r.
imp.
axiom.
% Almost there, modulo non-llambda.
rotate.
then(repeat(or_l),simplify).
cut("nabla x\ bind (cons (pair x h6) g2) (h7 x) h8").
abstract.
prove.
nabla.
then(mu_l("bind _ _ _"),then(or_l,simplify)).
% One non-llambda shy of completing.
rotate.
% Non-llambda everwhere:(.
