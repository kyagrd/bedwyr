% IWC Problem 15 (just the statement).
#open "../lists.def".

#theorem paulson
  "pi f\x\y\z\e\l\r1\r2\
    (f x e) = x, (f (f x y) z) = (f x (f y z)),
    foldleft f e l r1, foldleft f y l r2 =>
      (o y r1) = r2".
