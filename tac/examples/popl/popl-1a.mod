%progress subformula X {A}.
subformula X (arrow X U).
subformula X (arrow U X).

%progress bind A B {C}.
bind X T ((pair X T)::C).
bind X T (H::C) :- bind X T C.

sub Context S top.
sub Context X X :- bind X U Context.
sub Context X T :- bind X U Context, sub Context U T.
sub Context (arrow S1 S2) (arrow T1 T2) :- sub Context T1 S1, sub Context S2 T2.
sub Context (all S1 S2) (all T1 T2) :-
  sub Context T1 S1,
  nabla x\ sub ((pair x T1)::Context) (S2 x) (T2 x).

closed Context top.
closed Context X :- bind X U Context.
closed Context (arrow T1 T2) :- closed Context T1, closed Context T2.
closed Context (all T1 T2) :-
  closed Context T1,
  nabla x\ closed ((pair x T1)::Context) (T2 x).

type Context top.
type Context X :- bind X U Context.
type Context (arrow T1 T2) :- type Context T1, type Context T2.
type Context (all T1 T2) :-
  type Context T1,
  nabla x\ type ((pair x T1)::Context) (T2 x).
