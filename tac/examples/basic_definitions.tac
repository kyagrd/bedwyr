#define "isTrue x := x = true".

#define "nat x := (x=o);(sigma y\ (x=(s y),(nat y)))".
#define "even x := (x=o);(sigma y\ (x=(s (s y)),(even y)))".
#define "odd x := (x=(s o));(sigma y\ (x=(s (s y)),(odd y)))".
#define "leq x y := (x=y);(sigma z\ (y=(s z),(leq x z)))".
#define "half x h := (((x=o);(x=(s o))),(h=o)); (sigma xx\ hh\ (x=(s (s xx)),h=(s hh), (half xx hh)))".

#define "coinductive sim p q := pi a\ p'\ ((step p a p') => (sigma q'\ (step q a q'),(sim p' q')))".

#define "empty x := (x = nil)".
#define "list x := (x=nil);(sigma y\ z\ (x=(cons y z),list z))".
