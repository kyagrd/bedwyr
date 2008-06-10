TEST=lists.muLJ.tac sim.muLJ.tac internal_checks.muLJ.tac tictactoe.muLJ.tac \
	 copy.muLJ.tac buchi.muLJ.tac
# Some examples that work but not in batch mode:
#  ho_simple.muLJ.tac
#  lift-oddity.muLJ.tac

test:
	@cd examples && for t in $(TEST) ; do \
	  echo Testing $$t... ; \
	  echo -n "  " ; \
	  ../taci/taci --logic muLJ --batch $$t || exit 1 ; \
	done
