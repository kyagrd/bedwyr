#open "examples/basic_definitions.def".

#proof_output "/tmp".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".

simplify.
induction("x\ (even x);(even (s x))").
prove.

% Now for the proper proof of invariance.
then(or_l,simplify).

  % Zero case.
  left.
  then(mu_r,prove).

  % Heredity.
  or_l.
  right.
  then(mu_r,prove).
  prove.

#theorem half "pi x\ nat x => sigma h\ half x h".

simplify.
then(induction("x\ (nat x),(pi y\ (leq y x)=>(sigma h\ (half y h)))"),
then(repeat(or_l),simplify)).

 % Proving that the invariant fits.
 pi_l.
 imp_l.
 then(mu_r,prove).
 prove.

 % Invariance Proof.

  % Zero Case.
  and.
  then(mu_r,prove).
  simplify.
  % Case analysis on y<=0 yields y=0.
  then(mu_l,then(or_l,simplify)).
  sigma.
  then(mu_r,prove).

  % Heredity Step.
  and_r.

  % Nat is stable under successor.
  then(mu_r,prove).

  % Interesting Heredity Case: if it's true for all nats <= x,
  % then it must be true for all nats <= s x.
  simplify.
  % Case analysis on y <= s x.
  mu_l.
  then(or_l,simplify).

   % Equality Case: we divide (s x) by two.
   % We need to reduce division to the pre-pre-decessor.
   mu_l.
   then(or_l,simplify).
   % We know that half 1 0.
   sigma_r.
   then(mu_r,prove).
   % Now we can access the pre-predecessor,
   % and use the induction hypothesis on it.
   pi_l.
   force("Y","h0").
   imp_l.
   mu_r.
   right.
   sigma.
   and.
   eq.
   then(mu_r,prove).
   sigma_l.
   sigma_r.
   mu_r.
   prove.

   % This is the strict case of leq,
   % where we can immediately use the induction hypothesis.
   prove.

