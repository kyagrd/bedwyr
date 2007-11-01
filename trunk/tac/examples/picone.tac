#open "picdefs.tac".

%% Currently the following fails to be proved.

#theorem hope "one (rx x\ (in a y\ z)) (resp (dn a) (y\ rx (x\ z)))".

#theorem four "sigma R\ one (rx (x\ (in a (y\ (par (in x (w\ z)) (out y a z)))))) R".
prove.

#theorem first  "sigma R\ one (out a b z) R".
prove.
#theorem second "sigma R\ one (rx (x\ out a x (out b b z))) R".
prove.
#theorem third "pi R\ one (rx (x\ out x x z)) R => false".
prove.

