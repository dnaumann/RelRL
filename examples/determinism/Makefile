WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed

all: example.mlw

example.mlw: preexample.mlw
	python3 post-process.py $^ > $@

preexample.mlw: example.rl
	$(WHYREL) -margin 136 -o $@ $^

ide: example.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f example.mlw
	rm -f preexample.mlw

