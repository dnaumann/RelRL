WHY3=why3
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib

all: prog.mlw


prog.mlw: prog.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: prog.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f prog.mlw
