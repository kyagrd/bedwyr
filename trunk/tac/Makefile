TEST=lists.muLJ.tac sim.muLJ.tac internal_checks.muLJ.tac tictactoe.muLJ.tac \
	 copy.muLJ.tac buchi.muLJ.tac binarytree.muLJ.tac plus.muLJ.tac \
	 arithmetic.muLJ.tac reverse.muLJ.tac \
	 lift-oddity.muLJ.tac ho_simple.muLJ.tac sk.muLJ.tac

.PHONY: taci/taci Stekki/stekki tools
all: taci/taci Stekki/stekki
taci/taci:
	make -C taci
Stekki/stekki:
	make -C Stekki
tools:
	make -C tools
tools/tactex: tools


test: taci/taci
	@cd examples && for t in $(TEST) ; do \
	  echo Testing $$t... ; \
	  echo -n "  " ; \
	  ../taci/taci --logic muLJ --batch $$t || exit 1 ; \
	done
