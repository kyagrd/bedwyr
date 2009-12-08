% Even Length Append

% Summary:
% Needs induction scheme on two variable
% Needs 1 lemmata

#define "len {l} {n} := (l=nil, n=z);
                      (sigma hd\tll\p\ n=(s p), l=(cons hd tl), len tl p)".

#define "even {n} := n=z ; (n=(s z), false) ; (sigma p\ n=(s(s p)), even p)".

#define "list {l} := (l=nil); (sigma hd\tl\ l = cons hd tl, list tl)".

#define "app {l} m {n} := (l=nil, m=n) ;
                          (sigma hd\tl\n'\
                            l = (cons hd tl),
                            app tl m n',
                            n = cons hd n')".

% A couple sanity checks

#theorem test_1 "even z".
prove.
#theorem test_2 "pi x\ even x => even (s (s x))".
prove.
#theorem test_3 "pi l\ list l => app l nil l, app nil l l".
prove.

% The real test

#theorem th_1 "pi x\y\z1\n1\z2\n2\ list x => list y =>
  app x y z1, app y x z2, len z1 n1, len z2 n2, even n1 => even n2".
prove.

% More faithful version (but less natural in our tool)

#define "ev {n} o := (n=z, o=tt); (n=(s z), o=ff);
                     (sigma p\ n=(s (s p)), ev p o)".

#theorem th_2 "pi x\y\z1\n1\z2\n2\e1\e2\ list x => list y =>
  app x y z1, app y x z2, len z1 n1, len z2 n2, ev n2 e2, ev n1 e1 => e1=e2".
prove.

% The comment from TWC002.txt seems irrelevant with Tac:
% Its the (non-mutually recursive) definition of even that requires a
% non-straigtforward induction scheme.

#theorem th_3 "pi x\y1\y2\y\z1\z2\n1\n2\
  app x (cons y1 (cons y2 y)) z1, len z1 n1,
  app y x z2, len z2 n2
  => n1 = (s (s n2))".
prove.
