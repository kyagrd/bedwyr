
O=.cmx
A=.cmxa
I=-I Nologic -I Propositional -I Firstorder -I ndcore
OCAMLC=ocamlopt
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

SOURCE= ndcore/term.ml ndcore/norm.ml ndcore/unify.ml ndcore/pprint.ml \
	listutils.ml properties.ml\
	absyn.ml output.ml option.ml \
	logic.ml \
	Nologic/nologic.ml \
	Propositional/propositionalabsyn.ml \
	Propositional/propositionalparser.mly \
	Propositional/propositionallexer.mll \
	Propositional/propositional.ml \
	Firstorder/firstorderabsyn.ml \
	Firstorder/firstorderparser.mly \
	Firstorder/firstorderlexer.mll \
	Firstorder/firstordertypes.ml \
	Firstorder/firstordertacticals.ml \
	Firstorder/firstorder.ml \
  Firstorder/LP/firstorderlp.ml \
  Firstorder/LP/lpabsyn.ml \
  Firstorder/LP/lpparser.mly Firstorder/LP/lplexer.mll \
	toplevellexer.mll toplevelparser.mly \
	toplevel.ml interpreter.ml interface.ml logics_gen.ml logics.ml main.ml

PREMLS=$(SOURCE:.mly=.ml)
MLS=$(PREMLS:.mll=.ml)
OBJ=$(MLS:.ml=$(O))
MLIS=$(wildcard $(MLS:.ml=.mli))

taci: $(OBJ)
	$(OCAMLC) $(I) unix$(A) str$(A) $(OBJ) -o $@

logics_gen.ml: ../logics_gen/bin/Logics.in
	make -C ../logics_gen
	../logics_gen/logics_gen --input $(<) --output logics_gen

clean:
	rm -f .depend
	make -C ../logics_gen clean
	for dir in . Nologic Propositional Firstorder Firstorder/LP ndcore ; do \
	  rm -f $$dir/*.cm* $$dir/*.o ; \
	done
	rm -f toplevellexer.ml toplevelparser.ml toplevelparser.mli
	rm -f logics_gen.*

.depend: $(MLS) $(MLIS)
	ocamldep $(I) $(MLS) $(MLIS) > .depend
-include .depend

%.cmx: %.ml
	$(OCAMLC) $(I) -c $<
%.cmo: %.ml
	$(OCAMLC) $(I) -c $<
%.cmi: %.mli
	$(OCAMLC) $(I) -c $<
%.ml: %.mly Makefile
	$(OCAMLYACC) $<
%.mli: %.mly Makefile
	$(OCAMLYACC) $<
%.ml: %.mll
	$(OCAMLLEX) $<

dist:
	for f in $(SOURCE) $(MLIS) Makefile README ; do \
	  cp --parents $$f $(DISTDIR) ; \
	done
