WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib

all: majorization.mlw

majorization.mlw: premajorization.mlw
	python3 post-process.py $< > $@

premajorization.mlw: major.rl
	$(WHYREL) -margin 158 -o $@ $^

ide: majorization.mlw
	$(WHY3) ide -L $(WHYREL_STDLIB) $<

.PHONY: clean
clean:
	rm -f premajorization.mlw
	rm -f majorization.mlw

