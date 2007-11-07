#define "one V W := 
    (sigma X\ sigma M\
       V = (in X M), W = (resp (dn X) M))
  ; (sigma X\ sigma Y\ sigma P\
       V = (out X Y P), W = (res (up X Y) P))
  ; (sigma P\
       V = (taup P), W = (res tau P))
  ; (sigma X\ sigma P\ sigma A\ sigma Q\
       V = (match X X P), W = (res A Q), one P (res A Q))
  ; (sigma X\ sigma P\ sigma A\ sigma M\
       V = (match X X P), W = (resp A M), one P (resp A M))
  ; (sigma P\ sigma Q\ sigma A\ sigma R\
       V = (plus P Q), W = (res A R), one P (res A R))
  ; (sigma P\ sigma Q\ sigma A\ sigma R\
       V = (plus P Q), W = (res A R), one Q (res A R))
  ; (sigma P\ sigma Q\ sigma A\ sigma R\ sigma M\
       V = (plus P Q), W = (resp A M), one P (resp A M))
  ; (sigma P\ sigma Q\ sigma A\ sigma R\ sigma M\
       V = (plus P Q), W = (resp A M), one Q (resp A M))
  ; (sigma P\ sigma Q\ sigma A\ sigma P1\
       V = (par P Q), W = (res A (par P1 Q)), one P (res A P1))
  ; (sigma P\ sigma Q\ sigma A\ sigma Q1\
       V = (par P Q), W = (res A (par P Q1)), one Q (res A Q1))
  ; (sigma P\ sigma Q\ sigma A\ sigma M\
       V = (par P Q), W = (resp A (x\ par (M x) Q)), one P (resp A M))
  ; (sigma P\ sigma Q\ sigma A\ sigma N\
       V = (par P Q), W = (resp A (x\ par P (N x))), one Q (resp A N))
  ; (sigma P\ sigma Q\ sigma A\
       V = (rx P), W = (resp A (y\ rx (x\ Q x y))),
       nabla x\ one (P x) (resp A (Q x)))
  ; (sigma P\ sigma Q\ sigma A\
       V = (rx P), W = (res A (rx Q)),
       nabla x\ one (P x) (res A (Q x)))
  ; (sigma M\ sigma X\ sigma N\
       V = (rx M), W = (resp (up X) N), nabla y\ one (M y) (res (up X y) (N y)))
  ; (sigma P\ sigma Q\ sigma M\ sigma N\ sigma R\ sigma T\ sigma X\ sigma Y\ sigma M\
       V = (par P Q), W = (res tau (par R T)),
       one P (resp (dn X) M), one Q (res (up X Y) T), R = (M Y))
  ; (sigma P\ sigma Q\ sigma M\ sigma N\ sigma R\ sigma T\ sigma X\ sigma Y\ sigma M\
       V = (par P Q), W = (res tau (par R T)),
       one Q (resp (dn X) M), one P (res (up X Y) R), T = (M Y))
  ; (sigma P\ sigma Q\ sigma A\
       V = (rx P), W = (resp A (rx Q)), nabla x\ one (P x) (resp A (Q x)))
  ; (sigma P\ sigma Q\ sigma M\ sigma N\ sigma X\
       V = (par P Q), W = (res tau (rx (y\ par (M y) (N y)))),
       one P (resp (dn X) M), one Q (resp (up X) N))
  ; (sigma P\ sigma Q\ sigma M\ sigma N\ sigma X\
       V = (par P Q), W = (res tau (rx (y\ par (M y) (N y)))),
       one P (resp (up X) M), one Q (resp (dn X) N))
  ".

#define "coinductive bisim P Q := 
  (pi A\ pi P1\ one P (res A P1) => sigma Q1\ one Q (res A Q1), bisim P1 Q1),
  (pi X\ pi M\  one P (resp (dn X) M) => sigma N\ one Q (resp (dn X) N), pi w\ bisim (M w) (N w)),
  (pi X\ pi M\  one P (resp (up X) M) => sigma N\ one Q (resp (up X) N), nabla w\ bisim (M w) (N w)),
  (pi A\ pi Q1\ one Q (res A Q1) => sigma P1\ one P (res A P1), bisim Q1 P1), 
  (pi X\ pi N\  one Q (resp (dn X) N) => sigma M\ one P (resp (dn X) M), pi w\ bisim (N w) (M w)),
  (pi X\ pi N\  one Q (resp (up X) N) => sigma M\ one P (resp (up X) M), nabla w\ bisim (N w) (M w))".

#define "congr P Q := bisim P Q ; (P = z, Q = z) ;
  (sigma U\ sigma V\ P = (taup U), Q = (taup V), congr U V) ;
  (sigma U\ sigma V\ sigma X\ sigma Y\ P = (par  U V), Q = (par  X Y), congr U X, congr V Y) ;
  (sigma U\ sigma V\ sigma X\ sigma Y\ P = (plus U V), Q = (plus X Y), congr U X, congr V Y) ;
  (sigma U\ sigma V\ sigma X\ sigma Y\ sigma N\ sigma M\ P = (match N U V), Q = (match M X Y), N = M, U = X, congr V Y) ;
  (sigma U\ sigma V\ sigma X\ sigma Y\ sigma N\ sigma M\ P = (out   N U V), Q = (out   M X Y), N = M, U = X, congr V Y) ;
  (sigma U\ sigma V\ sigma X\ sigma Y\ P = (in U V), Q = (in X Y),  U = X, pi x\ congr (V x) (Y x)) ;
  (sigma U\ sigma V\ P = (rx U), Q = (rx V), nabla x\ congr (U x) (V x))".

