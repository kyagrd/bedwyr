%progress bind A B {C}.
bind X T ((pair X T)::C).
bind X T (H::C) :- bind X T C.

%progress eval {E} V.
eval zero zero.
eval tt tt.
eval ff ff.
eval (succ M) (succ V) :- eval M V.
eval (pred M) zero :- eval M zero.
eval (pred M) V :- eval M (succ V).
eval (is_zero M) tt :- eval M zero.
eval (is_zero M) ff :- eval M (succ V).
eval (if M N1 N2) V :- eval M tt, eval N1 V.
eval (if M N1 N2) V :- eval M ff, eval N2 V.
eval (abs T R) (abs T R).
eval (app M N) V :- eval M (abs T R), eval (R N) V.
eval (rec T R) V :- eval (R (rec T R)) V.

%Note: this is not strictly correct.
%progress of Context {V} T.
of Context zero num.
of Context tt bool.
of Context ff bool.
of Context (succ M) num :- of Context M num.
of Context (pred M) num :- of Context M num.
of Context (is_zero M) bool :- of Context M num.
of Context (if M N1 N2) T :- of Context M bool, of Context N1 T, of Context N2 T.
of Context (abs T R) (arr T U) :-
  nabla n\ of ((pair n T) :: Context) (R n) U.
of Context (app M N) T :- of Context M (arr U T), of Context N U.
of Context (rec T R) T :-
  nabla n\ of ((pair n T) :: Context) (R n) T.
of Context N T :- bind N T Context.
