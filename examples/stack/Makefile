WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=stack.rl arraystack.rl liststack.rl relstack.rl client.rl

all: prog.mlw

prog.mlw: $(FILES)
	$(WHYREL) -margin 136 -o $@ $^
	python3 add_lemmas.py $@


ide: prog.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

type: $(FILES)
	$(WHYREL) -debug -type-check $^

.PHONY: clean
clean:
	rm -f prog.mlw

