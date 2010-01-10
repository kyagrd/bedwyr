% Taken from twelf/examples/prop-calc:
% deduction theorem for Hilbert-style intuitionistic propositional calculus.

#define "mem x {l} := sigma hd\tl\ l = cons hd tl, (x=hd; mem x tl)".

#define "prove gamma th :=
  (mem th gamma);
  (sigma a\b\ th = arrow a (arrow b a));
  (sigma a\b\c\
     th = arrow (arrow a (arrow b c)) (arrow (arrow a b) (arrow a c)));
  (th = true);
  (sigma a\b\ th = arrow a (arrow b (and a b)));
  (sigma a\b\ th = arrow (and a b) a);
  (sigma a\b\ th = arrow (and a b) b);
  (sigma a\b\ th = b, prove gamma (arrow a b), prove gamma a)".

#theorem abst "pi a\b\ prove (cons a nil) b => prove nil (arrow a b)".
prove("4").

