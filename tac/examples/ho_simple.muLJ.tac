#proof_output "/tmp".

% =========== MEMBERSHIP =================.

#define "mem x l := sigma hd\tl\ l = cons hd tl, (x=hd ; mem x tl)".

% ********** .
% A way to weaken nabla: use a dummy fresh variable.
% It's not so nice: where does that variable come from ?
% In fact, we are proving
%  (nabla n\ A) => (pi n\ A)
% rather than
%  (nabla n\ A) => A.
#theorem mem_w "pi x\l\ (nabla n\ mem x l) => (mem x l)".
simplify.
abstract.
% We need a dummy "fresh" variable.
then(induction("x'\l'\ mem (x' dummy) (l' dummy)"),prove).
% QED.

% ********** .
% A cleaner way to prove the same thing.
#theorem mem_w "pi x\l\ (nabla n\ mem x l) => (mem x l)".
simplify.
abstract.
then(induction("x'\l'\ pi x\l\ (x'=(a\x), l'=(a\l)) => mem x l"),prove).
% QED.

% ********** .
% It is also possible to weaken nabla around the negation of mem.
% That's much easier.
#theorem notmem_w "pi x\l\ (nabla n\ mem x l => false) => (mem x l => false)".
simplify.
abstract.
then(imp_l,simplify).
then(induction("x\l\ nabla n\ mem x l"),then(abstract,prove)).
% QED.

% ============ CONTEXT ============.

% A well-formed context is a list without the same element twice.
#define "ctxt l :=
           (l = nil) ;
           (sigma hd\tl\ l = cons hd tl, ctxt tl, (mem hd tl => false))".

% ********** .
% The following theorem can't be proved with the naive weakening thechnique
% used at the beginning, but we need to use the second technique.
% Otherwise we'd have to prove (mem (x n) (l n) => lift_mem x l)
% which is true only if n is fresh.
% By including that statement in the invariant, everything goes fine.
#theorem ctxt_w "pi l\ (nabla n\ ctxt l) => ctxt l".
simplify.
abstract.
induction("l'\ pi l\ l' = (x\l) => ctxt l").
prove.
then(or_l,simplify).
prove.
then(mu_r,then(right,then(repeat(sigma),and))).
prove.
then(imp_r,then(imp_l,simplify)).
then(induction("x\l\ nabla a\ mem x l"),then(abstract,simplify)).
prove.
prove.
% QED.

% ============ LAMBDA-TERMS ============== .

#define "term c t :=
  mem t c ;
  (sigma t1\t2\ t = app t1 t2, term c t1, term c t2) ;
  (sigma t1\ t = abs t1, nabla x\ term (cons x c) (t1 x))".

% Weakening isn't more difficult here than with mem.
#theorem term_w "pi c\t\ (nabla n\ term c t) => term c t".
simplify.
abstract.
induction("c'\t'\ pi c\t\ (c'=(x\c), t'=(x\t)) => term c t").
prove.
then(repeat(or_l),simplify).
then(induction("x'\l'\ pi x\l\ (x'=(a\x), l'=(a\l)) => mem x l"),prove).
prove.
then(abstract,prove).
% QED.
