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

.PHONY: dep-graph
dep-graph: main.byte
	ocamlfind ocamldoc -package why3 -dot -o codebase.dot -I _build/src/parser -I _build/src/pretrans -I _build/src/tools -I _build/src/translate -I _build/src/typing -I _build/src/util _build/src/parser/ast.ml _build/src/parser/astutil.ml _build/src/pretrans/boundary_info.ml _build/src/pretrans/derive_biinterface.ml _build/src/pretrans/encap_check.ml _build/src/pretrans/locEq.ml _build/src/pretrans/pretrans.ml _build/src/pretrans/resolve_datagroups.ml _build/src/tools/main.ml _build/src/translate/translate.ml _build/src/translate/why3constants.ml _build/src/typing/annot.ml _build/src/typing/ctbl.ml _build/src/typing/pretty.ml _build/src/typing/typing.ml _build/src/util/lib.ml _build/src/util/why3util.ml

.PHONY: dep-graph-functions
dep-graph-functions:
	@echo "Extracting function-level dependencies with module information..."
	python3 tools/extract_function_deps.py src codebase_functions.dot
	@echo "Converting to visual formats..."
	@if command -v dot &> /dev/null; then \
		dot -Tpng codebase_functions.dot -o codebase_functions.png && echo "✓ Generated: codebase_functions.png"; \
		dot -Tsvg codebase_functions.dot -o codebase_functions.svg && echo "✓ Generated: codebase_functions.svg"; \
	else \
		echo "Graphviz 'dot' not found. Install it to visualize the graph."; \
	fi