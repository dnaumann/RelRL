WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
THEORY_DIR=.
POST_PROCESS=../../util/post-process.sed

all: sumpub.mlw

sumpub.mlw: sumpub.rl
	$(WHYREL) -margin 80 -o $@ $^

# sumpub.mlw: presumpub.mlw
# 	python3 post-process.py $< > $@

ide: sumpub.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) -L $(THEORY_DIR) $<

type: sumpub.rl
	$(WHYREL) -type-check -debug $^

theory: sumpub_theory.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) -L $(THEORY_DIR) $<

check: sumpub.mlw
	$(WHY3) prove -L $(WHYREL_STDLIB) -L $(THEORY_DIR) --type-only $<

replay: sumpub.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) -L $(THEORY_DIR) sumpub

smoke: sumpub.mlw
	$(WHY3) replay -L $(WHYREL_STDLIB) -L $(THEORY_DIR) sumpub --smoke-detector top

.PHONY: clean
clean:
	# rm -f presumpub.mlw
	rm -f sumpub.mlw
