WHY3=why3
WHYREL=../../bin/whyrel
WHYREL_STDLIB=../../stdlib
POST_PROCESS=../../util/post-process.sed
FILES=uf.rl quickfind.rl quickunion.rl kruskal.rl ufrel.rl

all: uf.mlw

# preuf.mlw: $(FILES)
# 	$(WHYREL) -margin 136 -o $@ $^

uf.mlw: $(FILES) # preuf.mlw
	$(WHYREL) -margin 136 -o $@ $^
	sed -f $(POST_PROCESS) -i $@
	# python3 post-process.py $< > $@

ide: uf.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

type: $(FILES)
	$(WHYREL) -debug -type-check $^

.PHONY: clean
clean:
	# rm -f preuf.mlw
	rm -f uf.mlw

