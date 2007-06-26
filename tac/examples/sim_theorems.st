#open "C:\zRXer\Projects\SlimmerSVN\trunk\tac\examples
	\basic_definitions.tac".

#theorem half "pi x\ (nat x)=>(sigma h\ (half x h))".
async.
induction("nat", "x\ (nat x),(pi y\
	(leq y x)=>(sigma h\ (half y h)))").
%Proving that the invariant fits.
async.
pi_l.
imp_l.
mu_r("leq").
async.
sigma_l.
sigma_r.
async.

%Invariance Proof.
or_l.

%Zero Case.
eq_l.
and.
mu_r("nat").
async.
async.
induction("leq", "x\ y\ (x=y);(sigma z\ (y=(s z),(leq x z)))").
or.

%Equality.
eq_l.
sigma.
mu_r("half").
async.
and_r.
async.
eq.

%Absurd Case: Smaller than 0.
async.

%Justifying the unfolding of leq.
async.
async.
async.
or_l.
eq_l.
eq_r.
sigma_r.
and_r.
sigma_l.
async.
mu_r("leq").
async.

%Heredity Step
async.
and_r.



%Stable under successor.
mu_r("nat").
then(or, sigma).
and.
eq.
axiom.

%Interesting Heredity Case.
pi_r.
imp_r.
induction("leq", "x\ y\ (x=y);(sigma z\ (y=(s z),(leq x z)))").
or.

%Equality Case.
eq_l.
induction("nat", "x\ (x=o);(sigma y\ (x=(s y)),(nat y))").
then(or,async).
pi_l.
imp_l.
mu_r("leq").
then(or, sigma_r).
and.
eq.
mu_r("leq").
or.
eq.
sigma_l.
sigma_r.


mu_r("half").
or.
sigma.
sigma.
and.
and.
eq.
eq.
axiom.

pi_l.
imp.
mu_r("leq").
or.
eq.
sigma_l.
sigma_r.
mu_r("half").
or.
and_r.
or.
eq.
eq.
or_l.
async.
or_r.
async.
or.
eq_l.
sigma.
and.
eq.
mu_r("nat").
async.
async.
sigma.
and.
eq.
mu_r("nat").
or.
sigma_r.
and.
eq.
axiom.
async.
pi.
imp.
axiom.
sigma.
sigma.
async.

%One More thing.
async.
or.
eq.
eq.
async.
or.
eq.
sigma.
and.
eq.
mu_r("leq").
or.
eq.
async.
sigma.
and.
eq.
mu_r("leq").
or.
sigma.
and.
eq.
axiom.



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
