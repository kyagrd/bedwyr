% Magic square problem (in lambda Prolog)

% This module implements a generate-and-test approach to solving the
% following problem: select a placement of the number 1, 2, ..., 9 in
% a 3x3 square so that the sum of the rows, columns, and diagonals 
% all total 15.

% There are two implementations of this query below.  The square query
% picks some placement of these numbers and then checks the sums.  The
% square' query interleaves the placement of numbers with some checks 
% as to their sums.  

% The first query is much slower in lambda Prolog than the second.  One
% timing run had the "list_all" predicate taking 14.74 sections while the 
% "list_all'" predicate took 0.04 seconds.

% Contrast this file to the square.def example for Bedwyr.

module square.

select A (A :: Rest) Rest.
select A (B :: Tail) (B :: Rest) :- select A Tail Rest.

plus z N N.
plus (s N) M (s P) :- plus N M P.

leq z N.
leq (s N) (s M) :- leq N M.

lt z (s N).
lt (s N) (s M) :- lt N M.

% Notice that this predicate is functional (in the third argument).
fifteen I J K :- plus I J Sum, fiveNten Fifteen,
  (leq Fifteen Sum, K = none; 
   lt  Sum Fifteen, plus Sum M Fifteen, K = (some M)).

square [X1,X2,X3,X4,X5,X6,X7,X8,X9] :- one2nine L0,
  select X1 L0 L1,  select X2 L1 L2,  select X3 L2 L3,
  select X4 L3 L4,  select X5 L4 L5,  select X6 L5 L6,
  select X7 L6 L7,  select X8 L7 L8,  select X9 L8 nil,
% sum the rows
  fifteen X1 X2 (some X3), fifteen X4 X5 (some X6), fifteen X7 X8 (some X9),
% sum the diagonals
  fifteen X1 X5 (some X9), fifteen X3 X5 (some X7),
% sum the columns
  fifteen X1 X4 (some X7), fifteen X2 X5 (some X8), fifteen X3 X6 (some X9).

%% The following reschedules the goals above to become much more effective
%% using lambda Prolog's search strategies (involving unification, etc).

square' [X1,X2,X3,X4,X5,X6,X7,X8,X9] :- one2nine L0,
                           select X1 L0 L1,  % Guess X1
                           select X2 L1 L2,  % Guess X2
  fifteen X1 X2 (some X3), select X3 L2 L3,  % Compute X3
                           select X4 L3 L4,  % Guess X4
  fifteen X1 X4 (some X7), select X7 L4 L5,  % Compute X7
  fifteen X3 X5 (some X7), select X5 L5 L6,  % Compute X5
  fifteen X4 X5 (some X6), select X6 L6 L7,  % Compute X6
  fifteen X2 X5 (some X8), select X8 L7 L8,  % Compute X8
  fifteen X7 X8 (some X9), select X9 L8 nil, % Compute X9
  % Additional checks
  fifteen X1 X5 (some X9),
  fifteen X3 X5 (some X7),
  fifteen X3 X6 (some X9).

print_list T :- term_to_string T Str, print Str, print "\n".
list_all     :- square  L, nat_list_int_list L K, print_list K, fail.
list_all'    :- square' L, nat_list_int_list L K, print_list K, fail.

fiveNten (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z))))))))))))))).

one2nine [
  (s z), 
  (s (s z)), 
  (s (s (s z))), 
  (s (s (s (s z)))), 
  (s (s (s (s (s z))))), 
  (s (s (s (s (s (s z)))))), 
  (s (s (s (s (s (s (s z))))))), 
  (s (s (s (s (s (s (s (s z)))))))), 
  (s (s (s (s (s (s (s (s (s z)))))))))].

nat_int z 0.
nat_int (s N) I :- nat_int N J, I is (J + 1).

nat_list_int_list nil nil.
nat_list_int_list (N::L) (I::K) :- nat_int N I, nat_list_int_list L K.

%% The solutions are eight symmetries of 
%% (2 :: 7 :: 6 :: 9 :: 5 :: 1 :: 4 :: 3 :: 8 :: nil)

