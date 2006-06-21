
default:
	make -C src bedwyr

XPL = examples/3bits.def \
      examples/lambda.def examples/pi_nat.def examples/pi_church.def \
      examples/graph-alt.def examples/tictactoe.def \
      examples/minmax.def examples/seq.def
test:
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing bedwyr on examples
	make -C src bedwyr
	@time for i in $(XPL) ; do \
	  echo "==== Running $$i ====" ; \
	  src/bedwyr $$i -e "test, exit." ; \
	done

.PHONY: doc
doc:
	make -C doc

clean:
	make -C src clean
	make -C doc clean

VERSION=0.1beta2
D=bedwyr-$(VERSION)
dist:
	find . -name '*~' -exec rm \{\} \;
	rm -rf $(D)
	mkdir $(D)
	mkdir $(D)/doc
	mkdir $(D)/examples
	mkdir $(D)/contrib
	mkdir $(D)/src
	mkdir $(D)/src/ndcore
	cp README TODO configure configure.ac install-sh Makefile $(D)
	cp contrib/bedwyr.el $(D)/contrib
	cp doc/*.tex doc/Makefile $(D)/doc
	cp examples/*.def $(D)/examples
	rm -f $(D)/examples/andor.def
	cp src/*.ml* src/Makefile.in $(D)/src
	rm -f $(D)/src/parser.ml $(D)/src/parser.mli $(D)/src/lexer.ml
	cp src/ndcore/*.ml* $(D)/src/ndcore
	tar cjf $(D).tar.bz2 $(D)
	tar czf $(D).tar.gz $(D)
	rm -rf $(D)
