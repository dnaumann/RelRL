WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib

all: fact.mlw

fact.mlw: fact.rl
	$(WHYREL) -margin 136 -o $@ $^


ide: fact.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

replay: fact.mlw fact/why3session.xml
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) fact
	

.PHONY: clean
clean:
	rm -f fact.mlw
