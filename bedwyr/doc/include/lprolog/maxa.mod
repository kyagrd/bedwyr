% The predicate a holds for 3, 5, and 2.
a (s (s (s z))).
a (s (s (s (s (s z))))).
a (s (s z)).

% The less-than-or-equal relation
leq z N.
leq (s N) (s M) :- leq N M.

% Compute the maximum of a
maxa N :- a N, pi x\ a x => leq x N.
