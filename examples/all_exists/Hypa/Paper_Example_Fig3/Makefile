WHY3=why3
WHYREL=whyrel
WHYREL_STDLIB=${HOME}/RelRL/stdlib
PROG = prog

all: $(PROG).mlw

$(PROG).mlw: $(PROG).rl
	$(WHYREL) -debug -all-exists -margin 80 -o $@ $^

ide: $(PROG).mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

.PHONY: clean
clean:
	rm -f $(PROG).mlw
