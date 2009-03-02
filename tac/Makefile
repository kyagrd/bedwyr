TEST=lists.muLJ.tac sim.muLJ.tac internal_checks.muLJ.tac tictactoe.muLJ.tac \
	 lift-oddity.muLJ.tac ho_simple.muLJ.tac lambda/lemmas.muLJ.tac \
	 copy.muLJ.tac buchi.muLJ.tac binarytree.muLJ.tac plus.muLJ.tac \
	 arithmetic.muLJ.tac comparison.muLJ.tac \
	 reverse.muLJ.tac sorting.muLJ.tac \
	 sk.muLJ.tac picbisim.muLJ.tac picone.muLJ.tac
DEFS=naturals.def lists.def tictactoe.def sorting.def lambda/definitions.def \
     binarytrees.def bisimulation.def picalculus.def
EXAMPLES=lambda/subred.muLJ.tac lambda/typedet.muLJ.tac \
		 lambda/named-style-fail.muLJ.tac

.PHONY: test notest taci/taci Stekki/stekki tools taci stekki
all: taci/taci
taci: taci/taci
stekki: Stekki/stekki
taci/taci:
	make -C taci
Stekki/stekki:
	make -C Stekki
tools:
	make -C tools
tools/tactex: tools


test: taci/taci
	@echo Testing: ; \
	base=`pwd` ; \
	taci=$$base/taci/taci ; \
	for t in $(TEST) ; do \
	  printf "  $$t...\t" ; \
	  cd $$base/examples/`dirname $$t` ; \
	  $$taci --logic muLJ --batch `basename $$t` || exit 1 ; \
	done

# List examples that are not in TEST. They should be in EXAMPLES if they need
# to be released.
notest:
	cd examples ; find . -name '*.tac' \
	  | grep -v -F "`echo $(TEST) | tr ' ' '\n'`"

VERSION=0.5.0
FILES=Makefile INSTALL README README.lifting

tarball:
	rm -rf taci-$(VERSION)
	mkdir taci-$(VERSION)
	for d in taci tools Stekki logics_gen ; do \
	  mkdir taci-$(VERSION)/$$d ; \
	  make -C $$d DISTDIR=../taci-$(VERSION)/$$d dist ; \
	done
	@for f in $(EXAMPLES) $(DEFS) $(TEST) ; do \
	  cp --parents examples/$$f taci-$(VERSION) ; \
	done
	@for f in $(FILES) ; do \
	  cp --parents $$f taci-$(VERSION) ; \
	done
	tar cjvf taci-$(VERSION).tar.bz2 taci-$(VERSION)
