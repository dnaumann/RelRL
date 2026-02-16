WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed

all: swap.mlw

swap.mlw: swap.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: swap.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $^

.PHONY: clean
clean:
	rm -f swap.mlw
