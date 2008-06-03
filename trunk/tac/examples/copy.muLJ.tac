
#define "assoc x y l := sigma a\b\tl\ l = cons (pair a b) tl,
                           ((x=a,y=b);assoc x y tl)".

#define "eq gamma m n := assoc m n gamma
                       ; (sigma m1\n1\m2\n2\ m = app m1 m2, n = app n1 n2,
                                             eq gamma m1 n1, eq gamma m2 n2)
                       ; (sigma m1\n1\ m = abs m1, n = abs n1,
                          nabla a\ eq (cons (pair a a) gamma) (m1 a) (n1 a))".

% First, let's focus on the main lemma.
#theorem main "pi gamma\m\n\
    (nabla a\b\ eq (cons (pair a b) gamma) (m a) (n b))
 => (nabla   a\ eq (cons (pair a a) gamma) (m a) (n a))".
simplify.
abstract.
then(induction("g\m\n\ nabla a\ eq (g a a) (m a a) (n a a)"),abstract).
axiom.
then(repeat(or_l),simplify).
then(induction("a\b\l\ nabla c\ assoc (a c c) (b c c) (l c c)"),abstract).
% These are all trivial.
iterate(prove("1")).
% Qed.

#define "cp gamma m n := assoc m n gamma
                       ; (sigma m1\n1\m2\n2\ m = app m1 m2, n = app n1 n2,
                                             eq gamma m1 n1, eq gamma m2 n2)
                       ; (sigma m1\n1\ m = abs m1, n = abs n1,
                          nabla a\b\ eq (cons (pair a b) gamma) (m1 a) (n1 b))".

#theorem copy "pi m\n\ cp nil m n => m=n".
simplify.
% The outer induction shows that cp implies eq.
induction("g\m\n\ eq g m n").
 % The inner induction shows that eq implies equality.
 induction("g\m\n\ (pi a\b\ assoc a b g => a=b) => m=n").
  prove("0").
  % Inner invariance proof.
  then(repeat(or_l),then(simplify,try(prove("0")))).
  abstract.
  then(imp_l("_ => (x1\ _ x1) = (x1\ _ x1)"),simplify).
  then(mu_l,then(simplify,then(or_l,simplify))).
  % The invariant has to say that the abstraction is vacuous.
  induction("m'\n'\g'\ pi g\ (x\g' x) = (x\g)
             => sigma m\n\ (x\m' x)=(x\m), (x\n' x)=(x\n), assoc m n g").
  prove("0").
  prove("0").
% Outer invariance.
then(repeat(or_l),then(simplify,try(then(mu_r,prove("0"))))).
then(mu_r,right).
then(repeat(sigma_r),then(repeat(and_r),try(eq_r))).
% This is the "main lemma" that we proved first.
abstract.
then(induction("g\m\n\ nabla a\ eq (g a a) (m a a) (n a a)"),abstract).
axiom.
then(repeat(or_l),simplify).
then(induction("a\b\l\ nabla c\ assoc (a c c) (b c c) (l c c)"),abstract).
% These are all trivial.
iterate(prove("1")).
% Qed.