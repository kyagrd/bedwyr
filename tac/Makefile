TEST=lists.muLJ.tac sim.muLJ.tac internal_checks.muLJ.tac
test:
	@cd examples && for t in $(TEST) ; do \
	  echo Testing $$t... ; \
	  echo -n "  " ; \
	  ../taci/taci --logic muLJ --batch $$t || exit 1 ; \
	done
