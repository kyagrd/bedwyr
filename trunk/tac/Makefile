TEST=lists.muLJ.tac sim.muLJ.tac internal_checks.muLJ.tac tictactoe.muLJ.tac \
	 copy.muLJ.tac buchi.muLJ.tac binarytree.muLJ.tac plus.muLJ.tac \
	 arithmetic.muLJ.tac reverse.muLJ.tac sorting.muLJ.tac \
	 lift-oddity.muLJ.tac ho_simple.muLJ.tac sk.muLJ.tac \
	 picbisim.muLJ.tac picone.muLJ.tac

.PHONY: test notest taci/taci Stekki/stekki tools
all: taci/taci Stekki/stekki
taci/taci:
	make -C taci
Stekki/stekki:
	make -C Stekki
tools:
	make -C tools
tools/tactex: tools


test: taci/taci
	@echo Testing: ; \
	cd examples && for t in $(TEST) ; do \
	  printf "  $$t...\t" ; \
	  ../taci/taci --logic muLJ --batch $$t || exit 1 ; \
	done

notest:
	cd examples ; find . -name '*.tac' \
	  | grep -v -F "`echo $(TEST) | tr ' ' '\n'`"
