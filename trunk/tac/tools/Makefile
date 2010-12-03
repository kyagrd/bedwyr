FILES = mod2def.ml tactex.ml view README Makefile \
		clean.bat compile.bat tools.vcproj

all: tactex mod2def

tactex: tactex.ml
	ocamlc -I +xml-light xml-light.cma str.cma tactex.ml -o tactex

MOD_DEPS = str.cmxa ../taci/option.cmx ../taci/listutils.cmx \
		   ../taci/Firstorder/LP/lpabsyn.cmx \
		   ../taci/Firstorder/LP/lplexer.cmx \
		   ../taci/Firstorder/LP/lpparser.cmx \
		   ../taci/Firstorder/LP/firstorderlp.cmx

mod2def: mod2def.ml
	make -C ../taci
	ocamlopt -I ../taci/Firstorder/LP $(MOD_DEPS) mod2def.ml -o mod2def

dist:
	for f in $(FILES) ; do \
	  cp --parents $$f $(DISTDIR) ; \
	done
