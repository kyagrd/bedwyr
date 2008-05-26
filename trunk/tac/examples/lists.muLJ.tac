% List definitions.
#define "list X := (X = nil); (sigma H\ TL\ X = (cons H TL), (list TL))".
#define
  "equal X Y :=
    (X = nil, Y = nil);
    (sigma H1\ H2\ T1\ T2\
      X = cons H1 T1, Y = cons H2 T2, H1 = H2, equal T1 T2)".

#define
  "append L1 L2 L3 :=
    (L1 = nil, L2 = L3);
    (sigma H\ T1\ T3\
      L1 = cons H T1, 
      L3 = cons H T3,
      append T1 L2 T3)".

#define
  "reverse L1 L2 :=
    (L1 = nil, L2 = nil); 
    (sigma H\ T\ RT\
      L1 = cons H T, reverse T RT, append RT (cons H nil) L2)".

% Equality Theorems.
#theorem equal_sym "pi x\ y\ list x => list y => equal x y => equal y x".
prove.

% This works but takes a while.
#theorem equal_trans
  "pi x\ y\ z\ list x => list y => list z =>
  equal x y => equal y z => equal x z".
% prove.
admit.

% Append Theorems
#theorem append_nil_1 "pi x\ list x => append x nil x, append nil x x".
prove.

#theorem append_nil_2
  "pi x\ y\ list x, list y, append x y nil => x = nil, y = nil".
prove.

#theorem append_equal_nil
  "pi x\ y\ list x, list y, append x nil y => equal x y".
prove.

% Epic fail.
#theorem append_assoc
  "pi x\ y\ z\ r\ list x => list y => list r =>
    (sigma w\ list w => append x y w => append w z r) =>
    (sigma w\ list w => append y z w => append x w r)".
prove.

#theorem reverse_image
  "pi x\ y\ (list x, list y, reverse x y) => reverse y x".
prove.

