#open "basic_definitions.def".

#proof_output "/tmp".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
simplify.
then(induction("x\ (even x);(even (s x))"),prove("0")).
% Qed.

#theorem half "pi x\ nat x => sigma h\ half x h".
simplify.
induction("x\ nat x, pi y\ leq y x => sigma h\ half y h").
prove("1").
then(repeat(or_l),simplify).
prove("0").
% prove("2").
% With a synchronous "and", the following works MUCH better:.
then(and,prove("2")).
% Qed.


