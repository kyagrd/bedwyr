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
                        bool b1, bool b2, aelem a, order o,
                        x = alist b1 b2 a o".

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
simplify.
apply("nat_alphaelem_aelem").
simplify.
apply("combine_total").
prove.

#lemma list_alphaorder_order "pi x\ list x => sigma y\ alphaorder x y, order y".
simplify.
then(induction,cases).
prove.
then(apply("step"),prove).

% Compute the final abstraction.

#define "alpha {l} a :=
  (l=nil, a = alist false false ne epsl);
  (sigma x\ax\ao\
     l = cons x nil,
     alphaelem x ax,
     alphaorder l ao,
     a = alist true true ax ao);
  (sigma h1\ah1\h2\t\ao\
     l = cons h1 (cons h2 t),
     alphaelem h1 ah1,
     alphaorder l ao,
     a = alist true false ah1 ao)".
 
#define "prefix {p} l :=
             p=nil;
             (sigma h\t1\t2\ p=cons h t1, l=cons h t2, prefix t1 t2)".

#theorem test "pi x\y\ list x => prefix y x => list y".
prove.

#define "order_prefix o1 o2 :=
  (o2 = error);
  (o1 = o2);
  (o1 = e1l, o2 = e1e2l);
  (o1 = e2l, o2 = e2e1l)".

#define "is_epsl {l} :=
   l = nil;
   sigma hd\tl\ l = cons hd tl, alphaelem hd ne, is_epsl tl".
#define "is_e1l {l} :=
   (sigma tl\ l = cons (s z) tl, is_epsl tl);
   (sigma hd\tl\ l = cons hd tl, alphaelem hd ne, is_e1l tl)".
#define "is_e2l {l} :=
   (sigma tl\ l = cons (s (s z)) tl, is_epsl tl);
   (sigma hd\tl\ l = cons hd tl, alphaelem hd ne, is_e2l tl)".
#define "is_e1e2l {l} :=
   (sigma tl\ l = cons (s z) tl, is_e2l tl);
   (sigma hd\tl\ l = cons hd tl, alphaelem hd ne, is_e1e2l tl)".
#define "is_e2e1l {l} :=
   (sigma tl\ l = cons (s (s z)) tl, is_e1l tl);
   (sigma hd\tl\ l = cons hd tl, alphaelem hd ne, is_e2e1l tl)".

% Works much better to prove all at once.
#lemma alphaorder_to_is "pi x\o\ alphaorder x o =>
  ((o=epsl => is_epsl x),
   (o=e1l => is_e1l x),
   (o=e2l => is_e2l x),
   (o=e1e2l => is_e1e2l x),
   (o=e2e1l => is_e2e1l x))".
prove.
#lemma is_to_alphaorder "pi x\ list x =>
   ((is_epsl x => alphaorder x epsl),
    (is_e1l x => alphaorder x e1l),
    (is_e2l x => alphaorder x e2l),
    (is_e1e2l x => alphaorder x e1e2l),
    (is_e2e1l x => alphaorder x e2e1l))".
prove.

#theorem test "pi x\y\ prefix x y => is_epsl y => is_epsl x".
prove.

#theorem test "pi x\y\
   prefix x y => is_epsl y => pi o\ alphaorder x o => o=epsl".
prove.

#theorem test "pi x\y\
   prefix x y =>
     ((is_epsl y => is_epsl x),
      (is_e1l y => is_epsl x ; is_e1l x),
      (is_e2l y => is_epsl x ; is_e2l x),
      (is_e1e2l y => is_epsl x ; is_e1l x ; is_e1e2l x),
      (is_e2e1l y => is_epsl x ; is_e2l x ; is_e2e1l x))".
prove.

% prefix [] *, prefix * error
% prefix [ne] [_], prefix epsl len>1
% prefix [e1] e1l, prefix e1l (e1l,len<>1), prefix e1l e1e2l
% prefix [e2] e2l, prefix e2l (e2l,len<>1), prefix e2l e2e1l
% prefix e1e2l e1e2l, prefix e2e1l e2e1l.
#define "aprefix p l := sigma a\b\c\d\e\f\g\h\
   (p = alist false a b c, l = alist e f g h);
   (p = alist a b c d, l = alist e f g error);

   (p = alist a true d epsl, l = alist true true g h);
   (p = alist a b d epsl, l = alist true false g h);

   (p = alist a true d e1l, l = alist e f g e1l);
   (p = alist a b d e1l, l = alist e false g e1l);
   (p = alist a b d e1l, l = alist e f g e1e2l);

   (p = alist a true d e2l, l = alist e f g e2l);
   (p = alist a b d e2l, l = alist e false g e2l);
   (p = alist a b d e2l, l = alist e f g e2e1l);

   (p = alist a b d e1e2l, l = alist e f g e1e2l);
   (p = alist a b d e2e1l, l = alist e f g e2e1l)".

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

#lemma cons_step "pi u\v\w\x\y\z\xy\xz\
  aprefix (alist true false u y) (alist true false v z) =>
  combine x y xy => combine x z xz =>
  aprefix (alist true false w xy) (alist true false x xz)".
prove.

#theorem final "pi l1\l2\al1\al2\
   list l1 => list l2 =>
   prefix l1 l2 =>
   alpha l1 al1 => alpha l2 al2 =>
   aprefix al1 al2".
simplify.
cases("prefix _ _").
prove.
cases("prefix _ _").
prove.
async.
cut("alphaorder tl0 atl0 => aorder atl0").
repeat(weak_l).
prove.

prove.

------
Comments:

Provided by Dieter Hutter for 2000 Challenges.  The presentation above has
been altered from Dieter's for no good reason except to provide some
kind of consistency of presentation.  Believe the problems
involve the need for generalisations and some challenges for Rippling.

Lemmas required by INKA include:
aprefix(quad(true, false, U, Y), quad(true, false, V, Z)) ->
aprefix(quad(true, false, W, combine(X, Y)),
	quad(trye, false, W, combine(X, Z)))

aprefix(quad(true, false, U, combine(U, epsl)),
	quad(true, false, U, combine(U, V)))

prefix(Y, Z) ->
	aprefix(quad(true, false, Z, alphaorder(Y)),
		quad(ture, false, X, alphaorder(Z)))


------
Dieter's Presentation:

Problem:  Verifying Abstractions in Model Checking
Contact:  Dieter Hutter <hutter@dfki.de>
Date:     4/28/2000  (revised 6/7/2000)
=================================================================



Many thanks to Dennis Dams (Eindhoven University) who provided
this challenge.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


structure nil, cons(car:nat, cdr:list):list;

structure tt,ff:bool;

% Our own version of the booleans, used in a limited way.
enum structure tt, ff : bool;
function mynot(b:bool):bool =
if b = tt then ff %
if b = ff then tt; %


%
% The abstract side.
% For a natural number, the only information we are interested in is whether 
% it's p2, p5, or something else.
%

% Abbreviations for some positive numbers.
function p2:nat = s(s(0));
function p5:nat = s(s(s(p2))); %

% Abstraction for the naturals. The idea is that e1 represents p2,
% e2 represents p5, and ne represents any other number (ne is also
% used to represent "nothing" in case of abstracting the head of an
% empty list. We'll refer to
% a natural that abstracts into e1 as an "e1-element", and a natural
% that abstracts into e2 as an "e2-element".
enum structure e1, e2, ne : aelem;

% The abstraction of naturals is captured by the function alphaelem.
function alphaelem(a:nat):aelem =
 if a = p2 then e1
 otherwise { if a = p5 then e2
             otherwise ne};

% Abstraction of lists over naturals, based on the above abstraction of
% individual naturals. Basically, the abstraction of a list says whether
% there are occurences of e1-elements and e2-elements, if so, in which
% order they occur, and whether there are multiple e1 or e2 elements. In
% addition, the information whether the list is empty, whether it has
% exactly one element, and what is the abstraction of its head is
% maintained.  More precisely, an abstract list is a quadruple
% quad(nonempty:bool, oneelem:bool, hd:aelem, ord:order), where nonempty
% tells us whether the list is nonempty, oneelem whether it has exactly
% one element, and hd is the abstraction of the head. The last field,
% ord, basically gives information about the occurrence and order of
% e1-elements and e2-elements in the list. In the case that there are
% multiple occurrences of e1 or e2 in the list, then this is represented
% by the ord field having value error.
enum structure epsl, e1l, e2l, e1e2l, e2e1l, error : order;

structure quad(nonempty:bool, oneelem:bool, hd:aelem, ord:order) : alist;

% The following auxiliary functions will be used for computing the
% abstraction of a list by function alpha below.

function check_nonempty(l:list):bool =
 if l = nil then ff
 otherwise tt;


function hasoneelem(l:list):bool =
if l = nil then ff
otherwise{ if cdr(l) = nil then tt
           otherwise ff};


function combine(x:aelem, y:order):order =
 if x = ne then y
 if x = e1 and y = epsl then e1l
 if x = e1 and y = e2l then e1e2l
 if x = e2 and y = epsl then e2l
 if x = e2 and y = e1l then e2e1l
 otherwise error;

function alphaorder(l:list):order =
 if l = nil then epsl
 otherwise  combine(alphaelem(car(l)), alphaorder(cdr(l)));


% Now we can define the function alpha that abstracts a concrete list.
% Uses a hack: when taking the car of an empty list, INKA seems to
% always return the "first" value of the element type. So the car of
% an empty list over nat is 0. This fact is used in calculating the
% 3rd field. Note that this is wrong when 0 is a distinguished element 
% (e1-element).
function alpha(l:list):alist =
 quad(check_nonempty(l), hasoneelem(l), alphaelem(car(l)), alphaorder(l));


;%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% prefix(l1,l2) checks whether l1 is a prefix of l2.
function prefix(l1,l2:list):bool = 
if l1 = nil then tt
if l1 of cons then 
  { if car(l1) = car(l2) then prefix(cdr(l1), cdr(l2))
    otherwise ff
  };

% The abstract prefix relation and the corresponding safety lemma.

function aprefix(l1:alist, l2:alist):bool = 
if nonempty(l1) = ff then tt
otherwise 
{if tl(l2) = error then tt
 otherwise
 {if tl(l1) = epsl AND nonempty(l2) = tt AND oneelem(l1) = tt then tt
  otherwise
  {if tl(l1) = epsl AND nonempty(l2) = tt AND oneelem(l2) = ff then tt 
   otherwise
   {if tl(l1) = e1l AND tl(l2) = e1l AND oneelem(l1) = tt then tt 
    otherwise
    {if tl(l1) = e1l AND tl(l2) = e1l AND oneelem(l2) = ff then tt
     otherwise
     {if tl(l1) = e1l AND tl(l2) = e1e2l then tt
      otherwise
      {if tl(l1) = e2l AND tl(l2) = e2l AND oneelem(l1) = tt then tt
       otherwise
       {if tl(l1) = e2l AND tl(l2) = e2l AND oneelem(l2) = ff then tt
        otherwise
        {if tl(l1) = e2l AND tl(l2) = e2e1l then tt
         otherwise
         {if tl(l1) = e1e2l AND tl(l2) = e1e2l then tt
          otherwise 
          {if tl(l1) = e2e1l AND tl(l2) = e2e1l then tt
           otherwise ff
}}}}}}}}}}};

% In order to successfully guide INKA through the proof of the safety
% lemma for prefix/aprefix, the following three auxiliary lemmata are
% needed.

% This first auxiliary lemma is proven automatically by INKA:
all x,w,u,v:aelem all y,z:atail
     aprefix(quad(tt, ff, u, y), quad(tt, ff, v, z)) = tt ->
     aprefix(quad(tt, ff, w, combine(x, y)),
             quad(tt, ff, w, combine(x, z))) = tt;

% Also the second auxiliary lemma is proven automatically by INKA:
all u:aelem all v:atail
  aprefix(quad(tt, tt, u, combine(u, epsl)),
          quad(tt, ff, u, combine(u,v))) = tt;

%  To prove this third auxiliary lemma, interaction is necessary:
all y,z:list all x:aelem
  prefix(y, z) = tt ->
    aprefix(quad(tt, ff, x, alphatail(y)),
            quad(tt, ff, x, alphatail(z))) = tt;

% The safety lemma for prefix/aprefix.
% (***NOT Automatically proven by INKA as of 20.4.00***)
all l1,l2:list all n:nat 
  prefix(l1,l2) = tt -> aprefix(alpha(l1),alpha(l2)) = tt;








