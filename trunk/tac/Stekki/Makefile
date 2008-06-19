stekki: stekki.ml
	ocamlopt -I +labltk str.cmxa unix.cmxa labltk.cmxa stekki.ml -o stekki
.PHONY: clean
clean:
	rm -f stekki
dist:
	for f in stekki.ml README Makefile ; do \
	  cp --parents $$f $(DISTDIR) ; \
	done
