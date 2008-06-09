
#define "assoc x y l := sigma a\b\tl\ l = cons (pair a b) tl,
                           ((x=a,y=b);assoc x y tl)".

#define "eq gamma m n := assoc m n gamma
                       ; (sigma m1\n1\m2\n2\ m = app m1 m2, n = app n1 n2,
                                             eq gamma m1 n1, eq gamma m2 n2)
                       ; (sigma m1\n1\ m = abs m1, n = abs n1,
                          nabla a\ eq (cons (pair a a) gamma) (m1 a) (n1 a))".

% A simple check.
#theorem warmup "pi x\y\z\ (nabla a\ assoc x y z) => assoc x y z".
prove.
% It involved an induction with an invariant saying that the generic
% variable is unused.
% Qed.

% First, let's focus on the main lemma.
#theorem main "pi gamma\m\n\
    (nabla a\b\ eq (cons (pair a b) gamma) (m a) (n b))
 => (nabla   a\ eq (cons (pair a a) gamma) (m a) (n a))".
simplify.
abstract.
then(induction("g\m\n\ nabla a\ eq (g a a) (m a a) (n a a)"),abstract).
axiom.
then(async,try(prove)).
% Only the var case is left.
then(induction("a\b\l\ nabla c\ assoc (a c c) (b c c) (l c c)"),prove).
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
  prove.
  % Inner invariance proof.
  then(async,try(prove)).
  abstract.
  then(imp_l,simplify).
  % Automated induction inside,
  % deriving assoc from lift_assoc in case of vacuous abstractions.
  then(mu_l,prove).
% Outer invariance.
then(async,try(prove)).
% This is the "main lemma" that we proved first.
abstract.
then(induction("g\m\n\ nabla a\ eq (g a a) (m a a) (n a a)"),abstract).
prove.
then(async,try(prove)).
then(induction("a\b\l\ nabla c\ assoc (a c c) (b c c) (l c c)"),prove).
% Qed.
