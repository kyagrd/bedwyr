%progress subformula X {A}.
subformula X (arrow X U).
subformula X (arrow U X).

%progress bind A B {C}.
bind X T ((pair X T)::C).
bind X T (H::C) :- bind X T C.

% Subtyping.
sub Context S top.
sub Context X X :- bind X U Context.
sub Context X T :- bind X U Context, sub Context U T.
sub Context (arrow S1 S2) (arrow T1 T2) :- sub Context T1 S1, sub Context S2 T2.
sub Context (all S1 S2) (all T1 T2) :-
  sub Context T1 S1,
  nabla x\ sub ((pair x T1)::Context) (S2 x) (T2 x).

% Typing
of Context (abs T1 E) (arrow T1 T2) :-
  nabla x\ of (cons (pair x T1) Context) (E x) T2.
of Context (app E1 E2) T12 :-
  of Context E1 (arrow T11 T12), of Context E2 T11.
of Context (tabs T1 E) (all T1 T2) :-
  pi x\ sub Context x T1 => of Context (E x) (T2 x).
of Context (tapp E T2) (T12 T2) :-
  of Context E (all T11 T12), sub Context T2 T11.
of Context E T :- of Context E S, sub Context S T.


% Small step evaluation
%progress value {V}.
value (abs T E).
value (tabs T E).

progresses E :- value E.
progresses E :- step E E'.

%progress step {E} V.
step (app (abs T E1) E2) (E1 E2).
step (tapp (tabs T1 E) T2) (E T2).
step (app E1 E2) (app E1' E2) :- step E1 E1'.
step (app V1 E2) (app V1 E2') :- value V1, step E2 E2'.
step (tapp E T) (tapp E' T) :- step E E'.

% Closed types.
closed Context top.
closed Context X :- bind X U Context.
closed Context (arrow T1 T2) :- closed Context T1, closed Context T2.
closed Context (all T1 T2) :-
  closed Context T1,
  nabla x\ closed ((pair x T1)::Context) (T2 x).

% Open types.
type Context top.
type Context X :- bind X U Context.
type Context (arrow T1 T2) :- type Context T1, type Context T2.
type Context (all T1 T2) :-
  type Context T1,
  nabla x\ type ((pair x T1)::Context) (T2 x).
