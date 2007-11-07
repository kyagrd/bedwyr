#open "picdefs.tac".

#theorem first  "sigma R\ one (out a b z) R".
prove.
#theorem second "sigma R\ one (rx (x\ out a x (out b b z))) R".
prove.
#theorem third "pi R\ one (rx (x\ out x x z)) R => false".
prove.

%% Currently the following two theorems are not proved by the "prove"
%% tactical.  I haven't worked enough on this to know where the error
%% lies. 
#theorem hope "one (rx (x\ (in a (y\ z)))) (resp (dn a) (y\ rx (x\ z)))".
prove.
#theorem four "sigma R\ one (rx (x\ (in a (y\ (par (in x (w\ z)) (out y a z)))))) R".
prove.
