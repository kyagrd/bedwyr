% This Teyjus module file describes paths through untyped lambda-terms
% with and without marked beta-redexes.

% These clause are encoded into "prog" clauses in paths.def.

module paths.

path (abs R)   (bnd S)   :- pi x\ pi p\ path x p => path (R x) (S p).
path (app M _) (left P)  :- path M P.
path (app _ M) (right P) :- path M P.

bpath (abs R)    (bnd S)   :- pi x\ pi p\ bpath x p => bpath (R x) (S p).
bpath (app M _)  (left P)  :- bpath M P.
bpath (app _ M)  (right P) :- bpath M P.
bpath (beta R N) P         :- pi x\ jump x N => bpath (R x) P.
bpath X          P         :- jump X N, bpath N P.

% The best specification for defining a path through a beta-redex
% involves a third-order clause, namely,
%%  bpath (beta R N) P :-
%%     pi x\ (pi Q\ bpath x Q :- bpath N Q) => bpath (R x) P.
% Instead, we use (jump x N) to name the clause
%    (pi Q\ bpath x Q :- bpath N Q).
