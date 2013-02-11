.PHONY: test clean

test: gensq
	@./sq bc > time.bc 2> /dev/null
	@./sq lbc > time.lbc 2> /dev/null

clean:
	@rm -rf gensq sq*.def time.bc time.lbc
