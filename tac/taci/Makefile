
O=.cmo
A=.cma
I=-I Nologic -I Propositional -I FirstOrder
OCAMLC=ocamlc
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

SOURCE= absyn.ml output.ml option.ml logic.ml propositionalabsyn.ml \
	Nologic/nologic.ml \
	Propositional/propositionalparser.ml \
	Propositional/propositionallexer.ml \
	Propositional/propositional.ml \
	Firstorder/firstorderabsyn.ml \
	Firstorder/firstorderparser.ml \
	Firstorder/firstorderlexer.ml \
	Firstorder/firstorder.ml \
	toplevellexer.ml toplevelparser.ml \
	toplevel.ml interpreter.ml interface.ml logics_gen.ml main.ml
OBJ= $(SOURCE:.ml=$(O))

taci: $(OBJ)
	$(OCAMLC) str$(A) $(OBJ) -o $@

clean:
	rm -f *.cm* Nologic/*.cm* Propositional/*.cm*

.depend: $(SOURCE)
	ocamldep $(SOURCE) > .depend
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
