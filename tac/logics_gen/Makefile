
O=.cmo
A=.cma
I=
OCAMLC=ocamlc
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

SOURCE= absyn.ml parser.ml lexer.ml main.ml
OBJ= $(SOURCE:.ml=$(O))

logics_gen: $(OBJ)
	$(OCAMLC) str$(A) $(OBJ) -o $@

clean:
	rm -f *.cm*

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
