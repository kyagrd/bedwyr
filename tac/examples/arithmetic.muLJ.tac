#open "examples/basic_definitions.def".

#theorem even_or_even_s "pi x\ (nat x)=>(even x); (even (s x))".

simplify.
induction("x\ (even x);(even (s x))").
or_l.
then(left,axiom).
then(right,axiom).

% Now for the proper proof of invariance.
or_l.

  % Zero case.
  then(eq_l,then(left,mu_r)).
  then(left,eq).

  % Heredity.
  simplify.
  or_l.
  right.
  mu_r.
  right.
  sigma.
  and.
  eq.
  axiom.
  left.
  axiom.

#theorem half "pi x\ (nat x)=>(sigma h\ (half x h))".

simplify.
induction("x\ (nat x),(pi y\ (leq y x)=>(sigma h\ (half y h)))").

 % Proving that the invariant fits.
 simplify.
 pi_l.
 imp_l.
 mu_r.
 left.
 eq_r.
 sigma_l.
 sigma_r.
 axiom.

 % Invariance Proof.
 or_l.

  % Zero Case.
  eq_l.
  and.
  mu_r.
  then(left,eq_r).
  simplify.
  % Case analysis on "something"<=zero.
  mu_l.
  or_l.

   % Equality case: "something"=0, we know how to divide it by two.
   eq_l.
   sigma.
   mu_r.
   left.
   and.
   then(left,eq).
   eq.

   % Absurd case: "something"<0.
   simplify.
   % TODO simplify should be enough here.
   eq_l.

  % Heredity Step.
  simplify.
  and_r.

  % Nat is stable under successor.
  mu_r.
  right.
  sigma.
  and_r.
  eq.
  axiom.

  % Interesting Heredity Case: if it's true for all nats <= x,
  % then it must be true for all nats <= s x.
  simplify.
  % Case analysis on "something" <= s x.
  mu_l.
  or_l.

   % Equality Case: we divide (s x) by two.
   eq_l.
   % We need to reduce division to the pre-predecessor.
   mu_l.
   then(or_l,simplify).
   % We know that half 1 0.
   sigma_r.
   mu_r.
   then(left,and).
   then(right,eq_r).
   eq_r.
   % Now we can access the pre-predecessor,
   % and use the induction hypothesis on it.
   pi_l.
   imp_l.
   mu_r.
   then(right, then(sigma_r,and)).
   eq_r.
   then(mu_r,then(left,eq)).
   sigma_l.
   sigma_r.
   mu_r.
   right.
   repeat(sigma_r).
   repeat(and).
   eq_r.
   eq_r.
   axiom.

   % This is the strict case of leq,
   % where we can immediately use the induction hypothesis.
   then(sigma_l,then(and_l,eq_l)).
   then(pi_l,imp_l).
   axiom.
   simplify.
   then(sigma_r,axiom).