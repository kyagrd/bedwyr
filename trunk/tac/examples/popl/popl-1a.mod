%progress bind A B {C}.
bind X T ((pair X T)::C).
bind X T (H::C) :- bind X T C.

% In the following,
% OfContext denotes a context binding term variables to types (X:T),
% SubContext one that binds type variables to types (X<:T).

% Well formed types under a given typing context,
% where type variable must be bound.
type SubContext top.
type SubContext X :- bind X U SubContext.
type SubContext (arrow T1 T2) :- type SubContext T1, type SubContext T2.
type SubContext (all T1 T2) :-
  type SubContext T1,
  nabla x\ type ((pair x T1)::SubContext) (T2 x).

% Terms.
term OfContext SubContext X :- bind X T OfContext.
term OfContext SubContext (abs T M) :-
  type SubContext T,
  nabla x\ term ((pair x T)::OfContext) SubContext (M x).
term OfContext Subtyping (tabs T M) :-
  type Subtyping T,
  nabla t\ term OfContext ((pair t T)::SubContext) (M t).
term OfContext SubContext (app M N) :-
  term OfContext SubContext M,
  term OfContext SubContext N.
term OfContext SubContext (tapp M T) :-
  term OfContext SubContext M,
  type SubContext T.

% Subtyping.
sub Context S top.
sub Context X X :- bind X U Context.
sub Context X T :- bind X U Context, sub Context U T.
sub Context (arrow S1 S2) (arrow T1 T2) :- sub Context T1 S1, sub Context S2 T2.
sub Context (all S1 S2) (all T1 T2) :-
  sub Context T1 S1,
  nabla x\ sub ((pair x T1)::Context) (S2 x) (T2 x).

% Typing
of OfContext SubContext X T :- bind X T OfContext.
of OfContext SubContext (abs T1 E) (arrow T1 T2) :-
  nabla x\ of ((pair x T1)::OfContext) SubContext (E x) T2.
of OfContext SubContext (app E1 E2) T12 :-
  type SubContext T11,
  of OfContext SubContext E1 (arrow T11 T12), of OfContext SubContext E2 T11.
of OfContext SubContext (tabs T1 E) (all T1 T2) :-
  nabla x\ of OfContext ((pair x T1)::SubContext) (E x) (T2 x).
of OfContext SubContext (tapp E T2) (T12 T2) :-
  of OfContext SubContext E (all T11 T12), sub SubContext T2 T11.
of OfContext SubContext E T :-
  % Here we require that the middle type is well-formed,
  % which wouldn't be ensured otherwise even when T is well-formed.
  type SubContext S,
  of OfContext SubContext E S, sub SubContext S T.


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

% This useless definition is there so that tac knows about
% the global constant "nil".
is_nil nil.
