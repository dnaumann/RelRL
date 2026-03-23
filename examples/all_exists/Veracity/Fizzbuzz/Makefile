WHY3=why3
WHYREL=../../../../bin/whyrel
WHYREL_STDLIB=../../../../stdlib
PROG=prog

all: prog.mlw

$(PROG).mlw: $(PROG).rl
	$(WHYREL) -debug -all-exists -margin 80 -o $@ $^

ide: prog.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

replay: prog.mlw $(PROG)/why3session.xml
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) prog

.PHONY: clean
clean:
	rm -f prog.mlw
