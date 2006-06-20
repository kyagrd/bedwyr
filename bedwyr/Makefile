
default:
	make -C src bedwyr

XPL = examples/3bits.def \
      examples/lambda.def examples/pi.def \
      examples/graph-alt.def examples/tictactoe.def \
      examples/minmax.def examples/seq.def
test:
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing bedwyr on examples
	-@for i in $(XPL) ; do \
	  echo Running $$i... ; \
	  time src/bedwyr $$i -e "test, exit." ; \
	done

.PHONY: doc
doc:
	make -C doc

clean:
	make -C src clean
	make -C doc clean
