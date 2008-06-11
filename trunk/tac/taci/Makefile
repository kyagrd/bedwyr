
O=.cmx
A=.cmxa
I=-I Nologic -I Propositional -I Firstorder -I ndcore
OCAMLC=ocamlopt
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

SOURCE= ndcore/term.ml ndcore/norm.ml ndcore/unify.ml ndcore/pprint.ml \
	listutils.ml properties.ml\
	absyn.ml output.ml option.ml \
	logic.ml propositionalabsyn.ml \
	Nologic/nologic.ml \
	Propositional/propositionalparser.ml \
	Propositional/propositionallexer.ml \
	Propositional/propositional.ml \
	Firstorder/firstorderabsyn.ml \
	Firstorder/firstorderparser.ml \
	Firstorder/firstorderlexer.ml \
        Firstorder/firstordertypes.ml \
        Firstorder/firstordertacticals.ml \
	Firstorder/firstorder.ml \
	toplevellexer.ml toplevelparser.ml \
	toplevel.ml interpreter.ml interface.ml logics_gen.ml logics.ml main.ml
OBJ= $(SOURCE:.ml=$(O))

taci: $(OBJ)
	$(OCAMLC) $(I) unix$(A) str$(A) $(OBJ) -o $@

logics_gen.ml: ../logics_gen/bin/Logics.in
	make -C ../logics_gen
	../logics_gen/logics_gen --input $(<) --output logics_gen

clean:
	rm -f .depend
	make -C ../logics_gen clean
	for dir in . Nologic Propositional Firstorder ndcore ; do \
	  rm -f $$dir/*.cm* $$dir/*.o ; \
	done
	rm -f toplevellexer.ml toplevelparser.ml toplevelparser.mli
	rm -f logics_gen.*

HEADERS=$(wildcard $(SOURCE:.ml=.mli)) \
  $($(wildcard SOURCE:.ml=.mly):.mly=.mli)
.depend: $(SOURCE)
	ocamldep $(I) $(SOURCE) $(HEADERS) > .depend
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
