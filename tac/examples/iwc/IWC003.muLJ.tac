% Case Analysis
% Summary:
% Requires Case Analysis
% Not and equality theorem

#define "list {l} := (l=nil); (sigma hd\tl\ l = cons hd tl, list tl)".

#define "app {l} m {n} := (l=nil, m=n) ;
                          (sigma hd\tl\n'\
                            l = (cons hd tl),
                            app tl m n',
                            n = cons hd n')".
#define "member x {l} := (sigma hd\tl\ l = cons hd tl,
                            (x=hd; ((x=hd=>false), member x tl)))".

#define "mem x {l} o := (l=nil, o=ff);
                        (sigma hd\tl\ l = cons hd tl,
                            ((x=hd, o=tt); ((x=hd=>false), mem x tl o)))".

% Sanity check

#theorem test "pi x\l\ member x l => mem x l tt".
prove.

#theorem test "pi x\l\ mem x l tt => member x l".
prove.

% Test

#theorem th "pi x\y\z\a\ member x y, app y z a => member x a".
prove.

#theorem th_fun "pi x\y\z\a\o\o'\ mem x y o, app y z a =>
                                  (o=ff; (mem x a o' => o=o'))".
prove.
