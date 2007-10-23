#open "examples/basic_definitions.def".

#proof_output "/tmp".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
simplify.
then(induction("x\ (even x);(even (s x))"),prove).

#theorem half "pi x\ nat x => sigma h\ half x h".

simplify.
then(induction("x\ (nat x),(pi y\ (leq y x)=>(sigma h\ (half y h)))"),
then(repeat(or_l),simplify)).

 % Proving that the invariant fits.
 prove.

 % Invariance Proof.

  % Zero Case.
  prove.

  % Heredity Step.
  and_r.

  % Nat is stable under successor.
  prove.

  % Interesting Heredity Case: if it's true for all nats <= x,
  % then it must be true for all nats <= s x.
  simplify.

pi_l.
imp_l.
then(mu_r,left).
eq.
simplify.
mu_l("half _ _").
then(repeat(or_l),simplify).
prove.
% It doesn't show very much switching rules, I don't know where it is.
prove.

  % Case analysis on y <= s x.
  mu_l.
  then(or_l,simplify).
   % Equality Case: we divide (s x) by two.
   % We need to reduce division to the pre-pre-decessor.
   mu_l.
   then(or_l,simplify).
   % We know that half 1 0.
   prove.
   % Now we can access the pre-predecessor,
   % and use the induction hypothesis on it.
   prove.

   % This is the strict case of leq,
   % where we can immediately use the induction hypothesis.
   prove.






