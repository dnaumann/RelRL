WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed

all: test.mlw

test.mlw: test.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: test.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $^

.PHONY: clean
clean:
	rm -f test.mlw
