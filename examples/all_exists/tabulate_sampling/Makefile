WHY3 ?= why3
WHYREL ?= ../../../bin/whyrel
WHYREL_STDLIB ?= ../../../stdlib

.PHONY: all prove replay

all: prog.mlw

prog.mlw: prog.rl
	$(WHYREL) -all-exists -o $@ $<

prove:
	$(WHYREL) prove -all-exists -o prog.mlw prog.rl

replay: prog.mlw
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) prog
