WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=pqueue.rl pqueuer.rl pqueuebi.rl client.rl

all: prog.mlw

prog.mlw: $(FILES)
	$(WHYREL) -margin 136 -o $@ $^

ide: prog.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^


.PHONY: clean
clean:
	rm -f prog.mlw

