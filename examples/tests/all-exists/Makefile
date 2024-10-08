WHY3=why3
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib
FILES=havoc_test.rl

all: examples.rl havoc_test.mlw

examples.mlw: examples.rl
	$(WHYREL) -debug -margin 168 -o $@ $^

havoc_test.mlw: $(FILES)
	$(WHYREL) -debug -margin 168 -o $@ $^

ide: examples.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

.PHONY: clean
clean:
	rm -f havoc_test.mlw
