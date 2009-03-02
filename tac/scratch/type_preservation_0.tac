% The simplest possible example of type preservation theorem.
% Doesn't work fully automatically, didn't explore it semi-manually yet.

#open "../examples/naturals.def".

#define "of {E} T :=
   (E = z, T = nat) ;
   (sigma E'\ E = s E', T = nat, of E' nat) ;
   (sigma E'\E''\ E = add E' E'', of E' nat, of E'' nat)".

#define "eval E V :=
   (E = z, V = z) ;
   (sigma E'\V'\ E = s E', eval E' V', V = s V') ;
   (sigma E'\E''\V'\V''\ E = add E' E'',
                         eval E' V', eval E'' V'',
                         plus V' V'' V)".

#theorem preservation "pi e\t\ of e t => pi e'\ eval e e' => of e' t".
prove.
% Qed.
