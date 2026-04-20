# WhyRel Codebase Summary

## Technology Stack

- **Language**: OCaml 5.1.1+
- **Build System**: OCamlbuild 0.14.3
- **Parser**: Menhir (Yacc for OCaml)
- **Lexer**: ocamllex
- **External Dependencies**: Why3 1.7.2


## Command Line Reference

### Basic Usage
```bash
whyrel file.rl -o output.mlw          # Translate to Why3 in all all mode
whyrel f1.rl f2.rl -o all.mlw         # Multiple input files
whyrel -version                       # Show version
whyrel -help                          # Show help

whyrel file.rl --parse-only           # Stop after parsing
whyrel file.rl --typecheck-only       # Stop after type checking
whyrel file.rl --debug                # Enable debug output
whyrel file.rl --margin 120 -o out.mlw  # Set output margin

whyrel file.rl --locEq MethodName     # Derive local equivalence
whyrel file.rl --no-encap-check       # Skip encapsulation check
whyrel file.rl --no-frame-lemma       # Omit frame lemmas
whyrel file.rl -all-exists            # Use forall-exists mode
```
