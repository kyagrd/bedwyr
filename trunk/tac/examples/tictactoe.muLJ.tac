#define "winner x {l} := sigma a\ b\ d\ e\ f\ g\
l = c x (c x (c x (c a (c b (c g (c d (c e (c f nil)))))))) ;
l = c a (c b (c g (c x (c x (c x (c d (c e (c f nil)))))))) ;
l = c d (c e (c f (c a (c b (c g (c x (c x (c x nil)))))))) ;
l = c x (c a (c d (c x (c b (c g (c x (c e (c f nil)))))))) ;
l = c b (c x (c e (c a (c x (c g (c d (c x (c f nil)))))))) ;
l = c g (c f (c x (c a (c b (c x (c d (c e (c x nil)))))))) ;
l = c x (c b (c f (c a (c x (c g (c d (c e (c x nil)))))))) ;
l = c b (c d (c x (c a (c x (c g (c x (c e (c f nil))))))))".

#define "nowinner {l} := pi x\ winner x l => x=n".

#define "move x {l} {k} := (sigma l0\ l = c n l0, k = c x l0) ;
 (sigma l0\ k0\ a\ l = c a l0, k = c a k0, move x l0 k0)".

#define "wins p o l := winner p l ; pi l0\ move o l l0 =>
 sigma l1\ move p l0 l1, wins p o l1".

#define "flip l1 l2 := sigma a\ b\ d\ e\ f\ g\ h\ i\ j\
 l1 = c a (c b (c d (c e (c f (c g (c h (c i (c j nil)))))))),
 l2 = c d (c b (c a (c g (c f (c e (c j (c i (c h nil))))))))".

#theorem t1 "pi x\ l\ k\ flip l k => winner x l => winner x k".
prove.

#theorem t2 "pi x\ l\ k\ l2\ k2\ (flip l l2, move x l k, flip k k2) => move x l2 k2".
prove.

