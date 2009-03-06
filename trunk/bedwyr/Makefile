
all: src/Makefile
	make -C src bedwyr

src/Makefile: src/Makefile.in configure
	./configure
configure: configure.ac
	autoconf

XPL = examples/scoping.def examples/internal/checks.def \
      examples/miniml.def examples/internal/typecheck.def \
      examples/3bits.def examples/lambda.def examples/progs.def \
      examples/graph-alt.def examples/minmax.def examples/multisim.def \
      examples/tictactoe.def examples/pi/pi_nat.def examples/pi/pi_church.def
test: src/Makefile
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing bedwyr on examples
	make -C src bedwyr
	@time for i in $(XPL) ; do \
	  echo "==== Running tests in $$i ====" ; \
	  if src/bedwyr -t -I $$i ; then echo "All done." ; else break ; fi ; \
	done

.PHONY: doc
doc:
	make -C doc

clean:
	make -C src clean
	make -C doc clean

VERSION=1.1
D=bedwyr-$(VERSION)
dist: configure doc
	find . -name '*~' -exec rm \{\} \;
	rm -rf $(D)
	mkdir $(D)
	mkdir $(D)/doc
	mkdir $(D)/examples
	mkdir $(D)/examples/pi
	mkdir $(D)/examples/internal
	mkdir $(D)/examples/ccs_vp
	mkdir $(D)/examples/ccs_vp/timing
	mkdir $(D)/contrib
	mkdir $(D)/src
	mkdir $(D)/src/ndcore
	cp COPYING README TODO configure configure.ac install-sh Makefile $(D)
	cp contrib/bedwyr.el contrib/bedwyr.vim $(D)/contrib
	cp doc/*.tex doc/userguide.bib doc/Makefile $(D)/doc
	cp doc/userguide.pdf doc/userguide.ps.gz doc/userguide.html $(D)/doc
	for file in `find examples -type f '!' -path '*.svn*'` ; do \
	  cp $$file $(D)/$$file ; \
	done
	cp src/*.ml* src/Makefile.in $(D)/src
	rm -f $(D)/src/parser.ml $(D)/src/parser.mli $(D)/src/lexer.ml
	cp src/ndcore/*.ml* $(D)/src/ndcore
	tar cjf $(D).tar.bz2 $(D)
	tar czf $(D).tar.gz $(D)
	rm -rf $(D)
