# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

WhyRel is a compiler/verification tool for reasoning about **relational properties** of object-based programs. It translates source programs (`.rl` files) into WhyML (`.mlw` files) that act on an explicit heap model, then uses the Why3 platform with SMT solvers to discharge verification conditions. Use cases include ADT equivalence, noninterference, and program transformation verification.

This is a reimplementation of an earlier WhyRel version, focused on encoding experiments and new features. The source language has ML/WhyML-like syntax with Java-like features (mutable locals, implicit dereferencing, null references).

## Build Commands

```bash
make                    # Build bytecode executable (default) -> bin/whyrel
make main.native        # Build native executable -> bin/whyrel
make clean              # Clean build artifacts
make explain            # Show Menhir parser conflicts
```

Dependencies: OCaml 5.1.1+, Why3 1.7.2, OCamlbuild 0.14.3, Menhir. Install via:
```bash
opam switch create whyrel 5.1.1
opam install why3.1.7.2 ocamlbuild
```

## Running WhyRel

```bash
bin/whyrel prog.rl -o prog.mlw              # Translate single file
bin/whyrel f1.rl f2.rl f3.rl -o out.mlw     # Multiple files (order doesn't matter)
bin/whyrel prog.rl -parse                    # Stop after parsing (syntax check)
bin/whyrel prog.rl -type-check               # Stop after type checking
bin/whyrel prog.rl -debug -o prog.mlw        # Enable debug output
bin/whyrel prog.rl -margin 136 -o prog.mlw   # Set output line width
why3 ide -L ./stdlib prog.mlw                # Verify in Why3 IDE (must include -L stdlib)
```

Key flags: `-no-encap` (skip encapsulation check), `-no-frame` (omit frame lemmas), `-all-exists` (forall-exists semantics), `-locEq METHOD` (derive local equivalence spec, experimental).

## Working with Examples

Each example in `examples/` has a Makefile with standard targets:
```bash
cd examples/factorial
make          # Generate prog.mlw from prog.rl
make ide      # Open in Why3 IDE for interactive verification
make clean    # Remove generated files
```

Some examples (e.g., stack) compile multiple `.rl` files and may run post-processing scripts.

Regression testing replays Why3 proof sessions:
```bash
cd examples && ./regression_test.sh
```

## Compilation Pipeline

The compiler follows a 4-stage pipeline orchestrated by `src/tools/main.ml`:

1. **Parsing** (`src/parser/`): `lexer.mll` + `parser.mly` → `Ast.program` (AST defined in `ast.ml`)
2. **Type Checking** (`src/typing/typing.ml`): Validates well-formedness, builds class table (`ctbl.ml`) and program environment (`penv`). Annotated types in `annot.ml`.
3. **Pre-translation** (`src/pretrans/pretrans.ml`): Expands specs with invariants, checks encapsulation (`encap_check.ml`), resolves datagroups (`resolve_datagroups.ml`), derives biinterfaces, generates frame lemmas.
4. **Translation** (`src/translate/translate.ml`): Converts to Why3 parse trees (`Why3.Ptree`). Builds the state module (heap model with reftype algebraic type), translates classes/methods/formulas/bicommands to Why3 constructs. Helper utilities in `why3util.ml` and `why3constants.ml`.

## Key Source Layout

```
src/parser/       Lexer, parser, AST types (ast.ml), AST utilities (astutil.ml)
src/typing/       Type checker (typing.ml), annotated types (annot.ml),
                  class table (ctbl.ml), pretty printer (pretty.ml)
src/pretrans/     Pre-translation passes: spec expansion, encapsulation,
                  datagroup resolution, biinterface derivation, local equivalence
src/translate/    Why3 code generation (translate.ml ~4100 lines), Why3 helpers
src/util/         General utilities (lib.ml: Result monad, list ops)
src/tools/        Entry point (main.ml)
stdlib/           WhyRel standard library (prelude.mlw, whyrel_array.mlw)
```

## Key Abstractions

- **penv** (`definition M.t`): Program environment mapping identifiers to definitions (interfaces, modules, bimodules, datagroups, externs). Threaded through the entire pipeline.
- **ctbl** (`Ctbl.t`): Class table — central registry of class/method/field definitions with visibility and invariant info.
- **tenv**: Type environment in the type checker containing variable bindings, class table, datagroups, and extern types.
- **Result monad** (`lib.ml`): Error handling pattern used throughout (`Ok`/`Error` with `>>=` bind).
- **Definitions**: `Unary_interface | Module | Biinterface | Bimodule | Datagroup | Extern` — the top-level constructs the tool processes.

## Adding a New Language Construct

Follow the pipeline — each stage needs a corresponding case:
1. `lexer.mll` — add token
2. `parser.mly` — add grammar rule
3. `ast.ml` — add AST variant
4. `typing.ml` — add type checking case
5. `translate.ml` — add translation case
6. `pretty.ml` — add pretty printing

## Known Issues and Gotchas

- Formulas of the form `(p -> q) /\ (r -> s)` can translate incorrectly to Why3 due to the Why3 pretty printer producing wrong precedence: `((p -> q) /\ r) -> s`. Use conjunction/disjunction forms instead.
- In WhyRel alignment guards, avoid using `->` as it causes precedence issues with `<->`.
- The `regression_test.sh` script is adapted from Why3's own regression test infrastructure; it looks for `why3session.xml` files one level deep by default.
- Global gensym for fresh identifiers can invalidate manual Why3 IDE proofs when local variable names change.
