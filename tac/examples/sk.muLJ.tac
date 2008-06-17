#define "sk x :=
  (sigma m\n\ x = app m n, sk m, sk n);
  (x = k) ; (x = s) ; (sigma v\ x = var v)
".

#define "step x y :=
  (sigma m\n\mm\ x = app m n, step m mm, y = app mm n);
  (sigma m\n\nn\ x = app m n, step n nn, y = app m nn);
  (sigma a\b\ x = app (app k a) b, y = a);
  (sigma a\b\c\ x = app (app (app s a) b) c, y = app (app a c) (app b c))
".

#define "eval x y := x=y ; (sigma i\ step x i, eval i y)".
#define "convert a b := sigma c\ eval a c, eval b c".

#theorem test "pi x\ eval (app (app (app s k) k) x) x".
prove.
% Qed.

#define "sk_subst t x v st :=
  (sigma m\n\sm\sn\ t = app m n,
     sk_subst m x v sm, sk_subst n x v sn, st = app sm sn);
  (t = k, st = k) ; (t = s, st = s) ;
  (t = var x, st = v) ;
  (sigma y\ t = var y, (y=x => false), st = var y)
".

#define "sk_abs t x st :=
  ((t = k ; t = s), st = app k t);
  (sigma m\n\sm\sn\ t = app m n, sk_abs m x sm, sk_abs n x sn,
                    st = app (app s sm) sn);
  (sigma y\ t = var y, ( (x = y, st = app (app s k) k) ;
                         (st = app k t, (x = y => false) )))
".

#theorem abs_is_abs
  "pi t\x\at\
     sk_abs t x at =>
     pi y\st\ sk_subst t x y st =>
       eval (app at y) st".
repeat(pi).
imp.
% Induction sur la relation d'abstraction.
induction("t\x\at\ pi y\st\ sk_subst t x y st => eval (app at y) st").
prove.
then(repeat(or_l),simplify).
% Cas 1: on a t = st2.
prove.
% Cas 2: on passe sous un app.
then(mu_l,then(repeat(or_l),simplify)).
then(pi_l,then(pi_l,imp_l)).
axiom.
weak_l("sk_subst _ _ _ _").
then(pi_l,then(pi_l,imp_l)).
axiom.
weak_l("sk_subst _ _ _ _").
% On n'a pas de eval big-step, faut bosser.
induction("a\b\ pi c\d\ eval c d => eval (app a c) (app b d)").
prove.
then(or_l,simplify).
then(induction("a\b\ pi c\ eval (app c a) (app c b)"),prove).
prove.
% Dernier cas, les variables.
then(or_l,simplify).
then(mu_l,then(repeat(or_l),prove)).
then(mu_l,then(repeat(or_l),prove)).
% Qed.

