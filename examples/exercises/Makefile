WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=ex.rl

all: ex.mlw

ex.mlw: $(FILES)
	$(WHYREL) -margin 136 -o $@ $^

ide: ex.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

type: $(FILES)
	$(WHYREL) -debug -type-check $^

.PHONY: clean
clean:
	rm -f ex.mlw

