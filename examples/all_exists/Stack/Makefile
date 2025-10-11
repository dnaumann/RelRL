WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=stack.rl arraystack.rl liststack.rl relstack.rl client.rl

all: stack.mlw

prestack.mlw: $(FILES)
	$(WHYREL) -margin 136 -o $@ $^
	sed -f $(POST_PROCESS) -i $@

stack.mlw: prestack.mlw # $(FILES)
	# $(WHYREL) -margin 136 -o $@ $^
	# sed -f $(POST_PROCESS) -i $@
	python3 replacements.py $< > $@

ide: stack.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

type: $(FILES)
	$(WHYREL) -debug -type-check $^

.PHONY: clean
clean:
	rm -f prestack.mlw
	rm -f stack.mlw

