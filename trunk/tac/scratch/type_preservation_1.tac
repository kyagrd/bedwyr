% A type preservation example featuring variable binding.
% Started an interactive proof, didn't finish it..

#open "../examples/naturals.def".

#define "bind {G} X T := sigma Y\Ty\G'\ G = bind Y Ty G',
                        ((X=Y,T=Ty);bind G' X T)".
#define "of G {E} T :=
   (E = z, T = nat) ;
   (sigma E'\ E = s E', T = nat, of G E' nat) ;
   (sigma E'\E''\ E = add E' E'', of G E' nat, of G E'' nat) ;
   (sigma E'\T'\E''\ E = let E' E'', of G E' T',
                  nabla x\ of (bind x T' G) (E'' x) T) ;
   (bind G E T)".

#define "eval {E} V :=
   (E = z, V = z) ;
   (sigma E'\V'\ E = s E', eval E' V', V = s V') ;
   (sigma E'\E''\V'\V''\ E = add E' E'',
                         eval E' V', eval E'' V'',
                         plus V' V'' V)".

#theorem preservation "pi g\e\t\ of g e t => pi e'\ eval e e' => of g e' t".
simplify.
induction.
async.
% Case.
prove.
% Case.
prove.
% Case.
cut("pi x\y\z\ plus x y z => nat y => nat z").
then(repeat(weak_l),prove).
% We need to show that values are nat.
cut("nat v'").
rotate_l.
weak_l.
rotate_l.
weak_l.
weak_l.
weak_l.

