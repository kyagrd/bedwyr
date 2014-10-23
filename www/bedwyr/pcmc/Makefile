TARGETS=index.html pcpm-examples.tbz pcpm-examples.zip
EXAMPLES=cert-sig.thm clerks-experts.thm harness-generic.thm \
	 harness-reachable.thm harness-unreachable.thm kernel.thm \
	 logic.thm reachable-fpc.thm unreachable-fpc.thm

all: $(TARGETS)

index.html: index.php.html
	@php $< > $@

pcpm-examples.tbz: $(EXAMPLES)
	@tar -czf $@ $^

pcpm-examples.zip: $(EXAMPLES)
	@zip -q $@ $^

clean:
	@rm -vf $(TARGETS)
