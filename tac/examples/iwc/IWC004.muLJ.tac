% Rotate length
% Summary:
% Requires a generalisation

#define "list {l} := (l=nil); (sigma hd\tl\ l = cons hd tl, list tl)".
#define "nat {n} := n=z; sigma p\ n=s p, nat p".

#define "len {l} {n} := (l=nil, n=z);
                      (sigma hd\tl\p\ n=(s p), l=(cons hd tl), len tl p)".

#define "app {l} m {n} := (l=nil, m=n) ;
                          (sigma hd\tl\n'\
                            l = (cons hd tl),
                            app tl m n',
                            n = cons hd n')".

#define "rotate {n} l o := (n=z, l=o);
                           (sigma p\hd\tl\ n = s p, l = cons hd tl,
                              sigma a\ app tl (cons hd nil) a, rotate p a o)".

% Sanity.

#theorem test_1 "sigma y\ list y, pi n\ nat n => rotate n y y".
prove.

#theorem test_2 "pi n\ nat n => rotate n (cons foo nil) (cons foo nil)".
prove.

% Test.

% app X (app Y (H::nil)) = app (app X Y) (H::nil).
#lemma app_cons_1 "pi x\y\z\h\
  app x y z => list y =>
  sigma yh\zh\ app y (cons h nil) yh, app z (cons h nil) zh, app x yh zh".
prove.

% app (app X (H::nil)) Y = app X (H::Y).
#lemma app_cons_2 "pi x\y\z\h\xh\
  app x (cons h y) z => app x (cons h nil) xh => app xh y z".
prove.

#lemma app_list "pi x\y\z\ app x y z => list x".
prove.

#lemma app_cons_3 "pi x\y\z\h\a\b\
   app x y z => app y a b =>
   sigma yh\zh\ app y (cons h nil) yh, app z (cons h nil) zh, app x yh zh".
cut_lemma("app_list").
prove.

#lemma generalization "pi x\y\n\
   len x n => pi xy\yx\ app x y xy => app y x yx => rotate n xy yx".
simplify.
then(induction,async).
% Base case: nil.
prove.
% Case: cons.
then(mu_r,right,
     repeat(sigma),repeat(and),iterate(try(eq))).
then(apply("app_cons_3"),simplify).
apply("app_cons_2").
prove.
% Qed.

#lemma app "pi x\ list x => app x nil x".
prove.

#theorem th "pi x\n\ list x => len x n => rotate n x x".
cut_lemma("generalization").
cut_lemma("app").
prove.



