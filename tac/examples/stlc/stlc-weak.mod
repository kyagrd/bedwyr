%progress bind A B {C}.
bind X T ((pair X T)::C).
bind X T (H::C) :- bind X T C.

%progress of C {X} T.
of Context (abs R) (arrow T U) :- nabla n\ of ((pair n T)::Context) (R n) U.
of Context (app M N) T :- of Context M (arrow U T), of Context N U.
of Context X T :- bind X T Context.

%progress eval {E} V.
eval (abs R) (abs R).
eval (app M N) V :- eval M (abs R), eval (R N) V.
