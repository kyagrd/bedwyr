#open "picalculus.defs".

#theorem foo "one (in a (y\z)) (resp (dn a) (y\z))".
prove("0").

#theorem hope "one (rx (x\ (in a (y\ z)))) (resp (dn a) (y\ rx (x\ z)))".
prove("0").

#theorem first  "sigma R\ one (out a b z) R".
prove("0").

#theorem second "sigma R\ one (rx (x\ out a x (out b b z))) R".
prove("0").

#theorem third "pi R\ one (rx (x\ out x x z)) R => false".
prove("0").

#theorem four "
  sigma R\ one (rx (x\ (in a (y\ (par (in x (w\ z)) (out y a z)))))) R
".
prove("0").


