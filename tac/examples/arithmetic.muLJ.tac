#open "examples/basic_definitions.def".

#proof_output "/tmp".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
simplify.
then(induction("x\ (even x);(even (s x))"),prove).

#theorem half "pi x\ nat x => sigma h\ half x h".
simplify.
then(induction("x\ (nat x),(pi y\ (leq y x)=>(sigma h\ (half y h)))"),
     prove("4")).
% Qed.

