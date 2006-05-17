
default:
	make -C src bedwyr

XPL = examples/3bits.def examples/4bits.def \
      examples/andor.def examples/tictactoe.def
test:
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing bedwyr on examples
	-@for i in $(XPL) ; do \
	  time src/bedwyr $$i -e "test, exit." ; \
	done

clean:
	make -C src clean
