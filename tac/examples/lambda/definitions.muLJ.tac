
% Some unused definitions to clarify.
% This is unused because inductions are not on the term structure.

#define "mem X L :=
	(sigma TL\   L = (cons X TL));
	(sigma Y\TL\ L = (cons Y TL), (mem X TL))".

#define "term G T :=
        (mem T G);
        (sigma M\N\ T = app M N, term G M, term G N);
        (sigma T'\  T = abs T', nabla x\ term (cons x G) (T' x))".

% Now the useful things.

#define "bind G V T :=
	(sigma G'\ G = (cons (pair V T) G'));
	(sigma G'\ V'\ T'\ G = (cons (pair V' T') G'), (bind G' V T))".

#define "typeof G M T :=
	(bind G M T);
	(sigma a\ m1\ m2\
		M = (app m1 m2),
		(typeof G m1 (arrow a T)),
		(typeof G m2 a));
	(sigma a\ b\ f\
		(M = (lambda a f)),
		(T = (arrow a b)),
		(nabla x\ (typeof (cons (pair x a) G) (f x) b)))".

#define "permute a b :=
   (pi m\t\ bind a m t => bind b m t), (pi m\t\ bind b m t => bind a m t)
".
