all:
	ocamlc -I +xml-light xml-light.cma str.cma tactex.ml -o tactex

dist:
	for f in tactex.ml README Makefile view ; do \
	  cp --parents $$f $(DISTDIR) ; \
	done
