WHY3=why3 -C why3.conf
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib
PROVER=CVC5,,
TIMEOUT=30
FILES=prog.rl

all: prog.mlw

prog.mlw: $(FILES) reverse_theory.mlw
	$(WHYREL) -margin 136 -o $@ $(FILES)

type: $(FILES)
	$(WHYREL) -type-check $(FILES)

stats: $(FILES)
	$(WHYREL) -stats-csv $(FILES)

ide: prog.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $<

prove: prog.mlw
	$(WHY3) prove -L . -P "$(PROVER)" -a split_vc -t $(TIMEOUT) reverse_theory.mlw
	$(WHY3) prove -L . -L $(WHYREL_STDLIB) -P "$(PROVER)" -a split_vc -t $(TIMEOUT) prog.mlw

replay: prog.mlw prog/why3session.xml
	$(WHY3) replay -L . -L $(WHYREL_STDLIB) prog

.PHONY: all type stats ide prove replay clean
clean:
	rm -f prog.mlw
