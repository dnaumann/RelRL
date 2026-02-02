WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=pqueue.rl pqueuer.rl pqueuebi.rl client.rl

all: pqueue.mlw

# prepqueue.mlw: $(FILES)
# 	$(WHYREL) -margin 136 -o $@ $^

pqueue.mlw: $(FILES)
	# python3 post-process.py $< > $@
	$(WHYREL) -margin 136 -o $@ $^
	sed -f $(POST_PROCESS) -i $@

ide: pqueue.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

type: $(FILES)
	$(WHYREL) -type-check -debug $^

check: pqueue.mlw
	$(WHY3) prove -L . -L $(WHYREL_STDLIB) --type-only $^

.PHONY: clean
clean:
	# rm -f prepqueue.mlw
	rm -f pqueue.mlw

