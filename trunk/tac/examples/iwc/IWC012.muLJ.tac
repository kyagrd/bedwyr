% Verifying Abstractions in Model Checking
% ----------------------------------------
% Safety Lemma for the prefix Operation.

% Summary:
% Generalisation(?)
% Lemmas
% Challenges for Rippling.

%% ==== TYPES ====.

#define "nat {x} := x=z; sigma y\ x = s y, nat y".
#define "list {l} := l=nil; sigma hd\tl\ l=cons hd tl, nat hd, list tl".

#define "bool  {x} := x=true; x=false".

% Abstraction of natural numbers: 1, 2, the rest.

#define "aelem {x} := x=e1; x=e2; x=ne".

% A first abstraction of lists of natural numbers
% epsl : empty list
% e1l : only one 1, no 2, anything else
% e2l : one one 2, no 1, anything else
% e1e2l : exactly one 1 and one 2 in that order, anything else
% e2e1l : opposite
% error : the rest.

#define "order {x} := x=epsl; x=e1l; x=e2l; x=e1e2l; x=e2e1l; x=error".

% A quadruple of two booleans, an aelem and an order
% forming the abstraction of a list of naturals:
% The first boolean indicates whether the list is non-empty,
% the second whether it has exactly one element.

#define "alist {x} := sigma b1\b2\a\o\
                        bool b1, bool b2, order o,
                        x = alist b1 b2 o".

%% ==== FUNCTIONS ====.

#define "alphaelem {x} {a} := (x=s z, a=e1);
                              (x=s (s z), a=e2);
                              (((x=s z;x=s (s z))=>false), a=ne)".

#lemma nat_alphaelem_aelem "pi x\ nat x => sigma y\ alphaelem x y, aelem y".
prove.

#lemma nat_alphaelem "pi x\ nat x => sigma y\ alphaelem x y".
prove.

#theorem test "pi x\y\ nat x => alphaelem x y => aelem y".
prove.

#define "combine {a} {i} o := (a=ne, i=o);
                          (a=e1,
                             ((i=epsl, o=e1l);
                              (i=e2l, o=e1e2l);
                              (((i=epsl;i=e2l)=>false), o=error)));
                          (a=e2,
                             ((i=epsl, o=e2l);
                              (i=e1l, o=e2e1l);
                              (((i=epsl;i=e1l)=>false), o=error)))".

#lemma combine_total "pi a\o\ aelem a => order o => sigma y\ combine a o y".
prove.

#theorem test "pi a\o\ aelem a => order o => sigma x\ combine a o x, order x".
prove.

% Compute the rough abstraction.

#define "alphaorder {l} o := (l=nil, o=epsl);
                             (sigma hd\ahd\tl\atl\ l = cons hd tl,
                                alphaelem hd ahd,
                                alphaorder tl atl,
                                combine ahd atl o)".

#lemma step "pi x\l\o\ nat x => order o => alphaorder l o => sigma y\z\
   alphaelem x y, combine y o z".
cut_lemma("nat_alphaelem_aelem").
cut_lemma("combine_total").
prove.

#lemma list_alphaorder_order "pi x\ list x => sigma y\ alphaorder x y, order y".
cut_lemma("step").
prove.

% Compute the final abstraction.

#define "alpha {l} a :=
  (l=nil, a = alist false false epsl);
  (sigma x\ao\
     l = cons x nil,
     alphaorder l ao,
     a = alist true true ao);
  (sigma h1\h2\t\ao\
     l = cons h1 (cons h2 t),
     alphaorder l ao,
     a = alist true false ao)".
 
#define "prefix {p} l :=
             p=nil;
             (sigma h\t1\t2\ p=cons h t1, l=cons h t2, prefix t1 t2)".

#theorem test "pi x\y\ list x => prefix y x => list y".
prove.

% prefix [] *, prefix * error
% prefix [ne] [_], prefix epsl len>1
% prefix [e1] e1l, prefix e1l (e1l,len<>1), prefix e1l e1e2l
% prefix [e2] e2l, prefix e2l (e2l,len<>1), prefix e2l e2e1l
% prefix e1e2l e1e2l, prefix e2e1l e2e1l.
#define "aprefix p l := sigma a\b\c\e\f\g\
   (p = alist false a b, l = alist e f g);
   (p = alist a b c, l = alist e f error);

   (p = alist a true epsl, l = alist true true e);
   (p = alist a b epsl, l = alist true false e);

   (p = alist a true e1l, l = alist e f e1l);
   (p = alist a b e1l, l = alist e false e1l);
   (p = alist a b e1l, l = alist e f e1e2l);

   (p = alist a true e2l, l = alist e f e2l);
   (p = alist a b e2l, l = alist e false e2l);
   (p = alist a b e2l, l = alist e f e2e1l);

   (p = alist a b e1e2l, l = alist e f e1e2l);
   (p = alist a b e2e1l, l = alist e f e2e1l)".

% Test aprefix for prefixes of length 0 to 3.

#lemma test_0 "pi l\a\anil\
   list l => alpha l a => alpha nil anil => aprefix anil a".
prove.

#lemma test_1 "pi x\l\ax\al\
   list l => alpha l a =>
   nat x => alpha (cons x nil) ax =>
   prefix (cons x nil) l => aprefix ax al".
prove.

#lemma test_2 "pi x\y\l\axy\al\
   list l => alpha l a =>
   nat x => nat y => alpha (cons x (cons y nil)) axy =>
   prefix (cons x (cons y nil)) l => aprefix axy al".
prove.

#lemma test_3 "pi x\y\z\l\axyz\al\
   list l => alpha l a =>
   nat x => nat y => nat z => alpha (cons x (cons y (cons z nil))) axyz =>
   prefix (cons x (cons y (con z nil))) l => aprefix axyz al".
prove.

#lemma test "pi x\ alist x => aprefix x x".
prove("5").

#lemma cons_step "pi x\y\z\xy\xz\
  aprefix (alist true false y) (alist true false z) =>
  combine x y xy => combine x z xz =>
  aprefix (alist true false xy) (alist true false xz)".
prove.

% The fact that we can prove this lemma somehow shows
% that the specification is a bit artificial / loose.
#lemma step "pi x\y\ox\oy\
  prefix x y => alphaorder x ox => alphaorder y oy =>
  aprefix (alist true false ox) (alist true false oy)".
simplify.
% Here "prove" needs a little help:
% we indicate by which induction to start.
then(induction("auto","prefix _ _"),prove).

#lemma alphaelem_unique "pi x\y\z\ alphaelem x y => alphaelem x z => y=z".
prove.

#theorem final "pi l1\l2\al1\al2\
   prefix l1 l2 =>
   alpha l1 al1 => alpha l2 al2 =>
   aprefix al1 al2".
simplify.
cases("prefix _ _").
prove.
cases("prefix _ _").
prove.
% Async performs progressing unfoldings.
async.
% At this point we can cut all those lemmas and conclude using prove,
% but this wouldn't make for a clearer or more concise proof,
% especially since lemmas used twice have to be cut-in twice.
cut("ahd=ahd1").
  then(cut_lemma("alphaelem_unique"),prove).
cut("ahd0=ahd2").
  then(cut_lemma("alphaelem_unique"),prove).
simplify.
apply("step").
apply("cons_step").
weak_l("aprefix _ _").
apply("cons_step").
axiom.
% Qed.
