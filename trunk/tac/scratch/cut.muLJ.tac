% Preliminary experiments on cut-elimination.
% Study the difficulties of context-as-lists.

#open "../examples/lists.def".

#define "form P :=
  P = tt ; (sigma A\B\ P = and A B) ; (sigma A\B\ P = imp A B)".

#define "prove Gamma P :=
  (mem P Gamma) ;
  (P = tt) ;
  (sigma A\B\ mem (and A B) Gamma, prove (cons A (cons B Gamma)) P) ;
  (sigma A\B\ P = and A B, prove Gamma A, prove Gamma B) ;
  (sigma A\B\ mem (imp A B) Gamma, prove Gamma A, prove (cons B Gamma) P) ;
  (sigma A\B\ P = imp A B, prove (cons A Gamma) B)".

#define "permute {l} {l'} :=
   (pi x\ mem x l => mem x l'), (pi x\ mem x l' => mem x l)".

#theorem and_comm "pi a\b\ prove nil (imp (and a b) (and b a))".
prove("4").

#theorem prove_permute
  "pi l\l'\ permute l l' => pi p\ prove l p => prove l' p".
simplify.
rotate_l.
induction.
async.
% Hyp.
prove.
% Top.
prove.
% And-l.
pi_l.
imp_l.
force("L'","(cons a (cons b l'2))").
prove.
prove.
% And-r.
prove.
cut("prove l'4 a0").
prove.
% Imp-l.
weak_l("pi _").
pi_l.
imp_l.
force("L'0","cons b0 l'4").
prove.
prove.
% Imp-r.
pi_l.
imp_l.
force("L'1","cons h1 l'5").
prove.
prove.
% Qed.

#lemma top "pi l\l'\ permute l (cons tt l') => pi p\ prove l p => prove l' p".
simplify.
async.
induction.
async.
prove.
prove.
iterate(admit).


#theorem cut
   "pi h\c\g\ form h => prove (cons h g) c => prove g h => prove g c".
simplify.
induction.
async.
% TOP.
weak_l("prove _ tt").
cut("permute (cons tt g0) (cons tt g0)").
prove.
apply("top").
prove.
% And.

induction.
async.
prove.
prove.
prove.

