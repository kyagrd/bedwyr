% List definitions.
#open "lists.def".

% Equality Theorems.
#theorem equal_sym "pi x\ y\ list x => list y => equal x y => equal y x".
prove.
% It works better without the list hypotheses.
% Qed.

#theorem equal_length "pi x\ y\ n\ list x => list y => equal x y => length x n => length y n".
prove.
% It works better without the list hypotheses.
% Qed.

% Again, the list hypotheses are useless,
% but a good test.
#theorem equal_trans
  "pi x\ y\ z\
    list x => list y => list z =>
    equal x y => equal y z => equal x z".
prove.
% Qed.

% Append Theorems.
#lemma append_nil_1 "pi x\ list x => append x nil x, append nil x x".
prove.
% Qed.

#theorem append_nil_2
  "pi x\ y\ list x, list y, append x y nil => x = nil, y = nil".
prove.
% Qed.

#theorem append_equal_nil
  "pi x\ y\ list x, list y, append x nil y => equal x y".
prove.
% Qed.

#theorem append_assoc
  "pi x\ y\ z\ xy\ yz\ xy_z\ x_yz\ list x => list y => list z =>
    (append x y xy, append xy z xy_z, append y z yz, append x yz x_yz)
    => xy_z = x_yz".
prove.
% Qed.

#theorem append_length_plus
  "pi x\ y\ z\ m\ n\ p\ append x y z =>
    length x m => length y n => length z p =>
    plus m n p".
prove.
% Qed.

#theorem append_plus_length
  "pi a\b\l\na\nb\n\ append a b l =>
     length a na => length b nb => plus na nb n =>
     length l n".
prove.
% Qed.

% Sublist Theorems.
% If x is a sublist of y, then x is shorter than (or the same length as) y.
#theorem sublist_size
  "pi x\ y\ m\ n\ sublist x y => length x m => length y n => leq m n".
prove.
% Qed.

% Sublist is associative.
% #theorem sublist_assoc
%   "pi x\ y\ z\ sublist x y => sublist y z => sublist x z".
% prove.

% Sublist is reflexive.
% We need lemmas on this one.
#set "firstorder.lemmas" "true".
#set "firstorder.lemmas.bound" "0".
#lemma sublist_refl "pi x\ list x => sublist x x".
% cut_lemma("append_nil_1").
prove.
% Qed.
#set "firstorder.lemmas" "false".

% Theorem: 
%#theorem sublist_antisym "pi x\ y\ sublist x y, sublist y x => equal x y".
%cut_lemma("append_nil_1").
%prove.


% Some 'traps' related to infinite progressings in the synchronous and
% asynchronous phases.
% Avoid an infinite loop of "progressing" unfoldings.
#theorem neq_trap "pi x\y\ equal x (cons a y) => equal x y => false".
prove.
% Qed.

% Same, different order.
#theorem neq_trap "pi x\y\ equal x y => equal x (cons a y) => false".
prove.
% Qed.

#theorem simple_trap "pi x\ equal x (cons foo x) => false".
prove.

#theorem other_trap "pi x\ delayeq x (cons foo x) => false".
prove.

% Also check that prove doesn't loop on:
% #theorem check "sigma x\ equal x (cons foo x)".
% prove.
