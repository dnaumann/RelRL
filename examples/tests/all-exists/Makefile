WHY3=why3
WHYREL=../../../bin/whyrel
WHYREL_STDLIB=../../../stdlib
FILES=havoc_test.rl examples.rl

all: all_exists_tests.mlw

all_exists_tests.mlw: $(FILES)
	$(WHYREL) -debug -all-exists -margin 80 -o $@ $^

ide: all_exists_tests.mlw
	$(WHY3) ide -L . -L $(WHYREL_STDLIB) $^

.PHONY: clean
clean:
	rm -f all_exists_tests.mlw
