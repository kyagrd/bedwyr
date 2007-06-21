#open "basic_definitions.tac".
#theorem half "pi x\ (nat x)=>(sigma h\ (half x h))".
then(pi, imp).
induction("nat", "x\ (nat x),(pi y\
	(leq y x)=>(sigma h\ (half y h)))").
and.
pi.
imp.
mu_r("leq").
then(or, eq).
sigma_l.
sigma_r.
axiom.
or.
eq.
and.
mu_r("nat").
then(or, eq).
then(pi, imp).
induction("leq", "x\ y\ (x=y);(sigma z\ (y=(s z),(leq x z)))").
or.
eq.
sigma.
mu_r("half").
or.
and.
or.
eq.
eq.
sigma.
and.
eq.
or.
or.
eq.
eq.
or.
sigma_l.
sigma_r.
and.
and.
eq.
eq.
eq.
mu_r("leq").
or.
or.
eq.
eq.
sigma.
and.
eq.




or.
eq.
sigma.
and.
eq.
and.
and.
mu_r("nat").
then(or, sigma).



and.
eq.
axiom.
pi_r.
imp_r.
imp.
induction("leq", "x\ y\ (x=y);(sigma z\ (y=(s z),(leq x z)))").
or.
eq.
sigma.
mu_r("half").
or.







#theorem n "pi x\ (nat x)=>(even x); (even (s x))".
pi.
imp.
or.
induction("nat", "x\ (even x);(even (s x))").
or.
rotate.
axiom.
rotate.
axiom.
or.
eq.
or.
mu_r("even").
or.
eq.
or.
sigma.
and.
eq.
or.
rotate.
rotate.
rotate_r.
mu_r("even").
or.
sigma.
and.
eq.
axiom.
axiom.


#theorem ref "pi p\ (sim p p)".
pi.
coinduction("sim", "p\ q\ (p=q)").
eq.
repeat(pi).
eq.
imp.
sigma.
and.
axiom.
eq.


#theorem f "(pi w\ (nabla x\ (w=x))=>foo)".
pi.
imp.
nabla.
eq.

#theorem trans "pi p\ q\ r\ (sim p q)=>((sim q r)=>(sim p r))".
repeat(pi).
repeat(imp).
coinduction("sim", "p\ r\ (sigma q\ (sim p q),(sim q r))").
sigma.
then(and, axiom).
then(sigma_l,repeat(pi_r)).
imp.
and.
nu_l("sim").
repeat(pi).
imp.
axiom.
sigma_l.
and.
rotate_l.
rotate_l.
nu_l("sim").
repeat(pi).
imp.
axiom.
sigma_l.
and.
sigma.
and.
axiom.
sigma.
and.
axiom.
axiom.
