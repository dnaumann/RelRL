OCB = ocamlbuild
OCB_FLAGS = -use-ocamlfind -use-menhir -yaccflags --explain
EXECUTABLE = src/tools/main.native
BYTE_CODE_EXECUTABLE = src/tools/main.byte
PAGER ?= cat
PARSER = src/parser.mly

all: main.byte

.PHONY: main.native
main.native:
	$(OCB) $(OCB_FLAGS) $(EXECUTABLE)
	mkdir -p bin
	cp -L main.native bin/whyrel

.PHONY: main.byte
main.byte:
	$(OCB) $(OCB_FLAGS) $(BYTE_CODE_EXECUTABLE)
	mkdir -p bin
	cp -L main.byte bin/whyrel

explain:
	$(PAGER) _build/src/parser/parser.conflicts

menhir-repl:
	menhir --interpret --interpret-show-cst --interpret-error $(PARSER)

.PHONY: clean
clean:
	$(OCB) -clean
