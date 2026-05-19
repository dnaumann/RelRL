# Tools Module (`src/tools/`)

**Purpose**: Command-line interface and entry point that orchestrates the full pipeline.

## Key File

- **`main.ml`** (218 lines)
  - Entry point: `run : unit -> unit`
  - Command-line argument parsing
  - Coordinates parsing → type checking → pre-translation → translation
  - Output formatting and file management

## Command-Line Options

```
whyrel [files...] [options]

Options:
  -o FILE              Output file name
  -version             Print version
  --parse-only         Stop after parsing
  --typecheck-only     Stop after type checking
  --debug              Enable debug output
  --no-encap-check     Skip encapsulation validation
  --no-frame-lemma     Omit frame lemmas
  --locEq METHOD       Derive local equivalence for method
  --margin N           Output margin width
  -all-exists          Use forall-exists semantics
```

## Full Execution Flow

```
main () [tools/main.ml]
  │
  ├─ parse_program !program_files
  │  └─ parse_file (for each file)
  │      ├─ Lexing.from_string (lexer.mll)
  │      └─ Parser.top Lexer.token lexbuf
  │          → Ast.program list
  │
  └─ typecheck_program parsed_program
      └─ Typing.tc_program
          ├─ Build initial environments
          ├─ Process each program element
          └─ Return: (penv, ctbl)

  └─ (if not --typecheck-only)
      ├─ Pretrans.process ctbl penv
      │  ├─ Expand_method_spec.expand
      │  ├─ Encap_check.check
      │  ├─ Derive_biinterface.derive
      │  ├─ Resolve_datagroups.resolve
      │  └─ Generate frame lemmas
      │      → penv (modified)
      │
      ├─ Translate.compile_penv context penv
      │  ├─ Build_State.mk (create heap module)
      │  ├─ trans_exp / trans_formula / trans_command
      │  └─ Return: Why3.Ptree.mlw_file list
      │
      └─ Format and output
          ├─ get_formatter() (stdout or file)
          ├─ Why3.Mlw_printer.pp_mlw_file
          └─ Write to .mlw file
```
