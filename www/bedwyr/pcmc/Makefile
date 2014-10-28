TARGETS=index.html pcpm-examples.tbz pcpm-examples.zip
EXAMPLES=generic-harness.thm logic.thm cert-sig.thm generic-fpc.thm kernel.thm \
	 reachable-harness.thm reachable-fpc.thm reachable-examples.thm adj.thm \
	 unreachable-harness.thm unreachable-fpc.thm unreachable-examples.thm \
	 sim-harness.thm sim-fpc.thm sim-examples.thm lts.thm \
	 nonsim-harness.thm nonsim-fpc.thm nonsim-examples.thm lts.thm

all: $(TARGETS)

index.html: index.php.html $(EXAMPLES:=.html)
	@php $< > $@

pcpm-examples.tbz: $(EXAMPLES)
	@tar -czf $@ $^

pcpm-examples.zip: $(EXAMPLES)
	@zip -q $@ $^

clean:
	@rm -vf $(TARGETS) $(EXAMPLES:=.html)

%.thm.html: %.thm
	@vim -n \
	  +'set nonumber' \
	  +'let html_use_css=1' \
	  +'TOhtml' \
	  +'/<pre\>/,/<\/pre>/d a' \
	  +'%d' \
	  +'1pu a' \
	  +'1,2d' \
	  +'$$d' \
	  +"wq! $@" \
	  +'q!' $<
