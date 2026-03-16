WHY3=why3
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib

all: cell.mlw

cell.mlw: cell.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: cell.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

type: cell.rl
	$(WHYREL) -type-check -debug $^

check: cell.mlw
	$(WHY3) prove -L $(WHYREL_STDLIB) --type-only $<

replay: cell.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) cell

smoke: cell.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) cell --smoke-detector deep

smoketop: cell.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) cell --smoke-detector top

.PHONY: clean
clean:
	rm -f cell.mlw

