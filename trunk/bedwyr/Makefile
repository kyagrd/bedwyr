
all: src/Makefile
	make -C src bedwyr

src/Makefile: src/Makefile.in configure
	./configure
configure: configure.ac
	autoconf

XPL = list.def internal/scoping.def internal/checks.def \
      miniml.def internal/typecheck.def \
      3bits.def lambda.def progs.def \
      graph-alt.def minmax.def multisim.def \
      tictactoe.def \
	  pi/pi_trace.def pi/corr-assert.def pi/pi_modal.def \
	  pi/pi_mini.def pi/pi_nat.def pi/pi_church.def

.PHONY: tests
test: src/Makefile
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing bedwyr on examples
	make -C src bedwyr
	@time $(MAKE) examples_tests

.PHONY: examples_tests
examples_tests:
	for i in $(XPL) ; do \
	  echo "==== Running tests in $$i ====" ; \
	  if src/bedwyr -t -I examples/$$i ; then echo "All done." ; else break ; fi ; \
	done

.PHONY: doc
doc:
	make -C doc

clean:
	make -C src clean
	make -C doc clean

VERSION=1.2
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
	mkdir $(D)/src/ndcore/tests
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
	cp src/ndcore/tests/*.ml* $(D)/src/ndcore/tests
	tar cjf $(D).tar.bz2 $(D)
	tar czf $(D).tar.gz $(D)
	rm -rf $(D)
