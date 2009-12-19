% Whisky problem
% Summary:
% Requires generalization.

#define "nat {x} := x=o ; sigma y\ x = s y, nat y".

#define
  "p {x} y :=
    (x = o, y = o);
    (sigma x'\ x = (h x'), y = o, p x' o);
    (sigma y'\ y = (s y'), p (h x) y')".

#define
  "all_h x :=
    (x = o);
    (sigma x'\ x = (h x'), all_h x')".

#lemma whisky_ext "pi x\ y\ nat y => all_h x => p x y".
prove.

#theorem whisky "pi y\ nat y => p o y".
cut_lemma("whisky_ext").
prove.
