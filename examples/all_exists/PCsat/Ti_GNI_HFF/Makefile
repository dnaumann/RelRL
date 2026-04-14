WHY3=why3
WHYREL=../../../../bin/whyrel
WHYREL_STDLIB=../../../../stdlib
PROG = prog

all: $(PROG).mlw

$(PROG).mlw: $(PROG).rl
	$(WHYREL) -debug -all-exists -margin 80 -o $@ $^

ide: $(PROG).mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

replay: $(PROG).mlw $(PROG)/why3session.xml
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) $(PROG)

.PHONY: clean
clean:
	rm -f $(PROG).mlw
