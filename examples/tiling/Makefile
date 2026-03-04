WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
FILES=tiling.rl 
EXTERN_FILES_DIR=.

all: prog.mlw

prog.mlw: $(FILES)
	$(WHYREL) -margin 136 -o $@ $^

ide: prog.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) -L $(EXTERN_FILES_DIR) $<

# 	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^
replay: prog.mlw $(PROG)/why3session.xml
	$(WHY3) replay -L $(WHYREL_STDLIB) prog

.PHONY: clean
clean:
	rm -f prog.mlw

