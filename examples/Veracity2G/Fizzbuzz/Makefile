WHY3=why3
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib

all: prog.mlw

prog.mlw: prog.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: prog.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

replay:  $(PROG)/why3session.xml
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) prog

.PHONY: clean
clean:
	rm -f prog.mlw
