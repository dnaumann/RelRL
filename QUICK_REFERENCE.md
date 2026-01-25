# WhyRel Quick Reference Guide

## File Organization Cheat Sheet

```
PARSING & LEXING
└── src/parser/
    ├── ast.ml ........................ Core types (types, expressions, formulas, commands)
    ├── astutil.ml .................... Helper functions on AST
    ├── lexer.mll ..................... Tokenizer (Ocamllex)
    └── parser.mly .................... Grammar rules (Menhir)

TYPE CHECKING & ANNOTATION
└── src/typing/
    ├── typing.ml ..................... Type checker (entry: tc_program)
    ├── annot.ml ...................... Annotated AST definitions
    ├── ctbl.mli/ml ................... Class table (class info storage)
    └── pretty.ml ..................... Pretty printer for WhyRel

PRE-TRANSLATION ANALYSIS
└── src/pretrans/
    ├── pretrans.ml ................... Main orchestrator (entry: process)
    ├── encap_check.mli/ml ............ Encapsulation validation
    ├── derive_biinterface.ml ......... Bimodule interface construction
    ├── locEq.mli/ml .................. Local equivalence derivation
    ├── resolve_datagroups.mli/ml ..... Expand datagroup "any"
    ├── boundary_info.mli/ml .......... Module boundary info cache
    └── rename_locals.ml .............. Rename local variables

TRANSLATION TO WHY3
└── src/translate/
    ├── translate.ml .................. Main translator (entry: compile_penv)
    ├── why3constants.ml .............. Why3 identifier names
    └── why3util.ml ................... Why3 tree builders

UTILITIES & ENTRY POINT
├── src/util/
│   ├── lib.ml ....................... General utilities (Result monad, lists)
│   └── why3util.ml .................. Why3 construction helpers
└── src/tools/
    └── main.ml ....................... Main entry point + CLI parsing

BUILD & CONFIGURATION
├── Makefile .......................... Build targets, dependency graphs
├── stdlib/
│   ├── prelude.mlw .................. Core Why3 definitions
│   └── whyrel_array.mlw ............. Array support in Why3
└── examples/ ......................... ~12 case studies with Makefiles

GENERATED OUTPUTS
├── bin/whyrel ........................ Compiled executable
└── _build/ ........................... OCamlbuild artifacts
```

---

## Processing Pipeline Quick Map

```
✓ STAGE 1: PARSING (parser.mly → ast.ml)
  Input:   foo.rl (text)
  Process: Lexer → Parser
  Output:  Ast.program list
  Entry:   Parser.top
  
✓ STAGE 2: TYPE CHECKING (typing.ml)
  Input:   Ast.program list
  Process: Validate types, build environments
  Output:  (penv: definition M.t, ctbl: Ctbl.t)
  Entry:   Typing.tc_program
  
✓ STAGE 3: PRE-TRANSLATION (pretrans.ml)
  Input:   (penv, ctbl)
  Process: Expand specs, check encapsulation, add lemmas
  Output:  penv (modified)
  Entry:   Pretrans.process
  
✓ STAGE 4: TRANSLATION (translate.ml)
  Input:   (penv, ctbl)
  Process: Convert to Why3 parse trees
  Output:  Why3.Ptree.mlw_file list
  Entry:   Translate.compile_penv
  
✓ STAGE 5: OUTPUT (main.ml)
  Input:   Why3 parse trees
  Process: Format and write
  Output:  foo.mlw (file)
```

---

## Key Data Types Reference

### Expressions
```ocaml
Econst(Eint 42)              (* Integer literal *)
Evar(Id "x")                 (* Variable *)
Ebinop(Plus, E1, E2)         (* Arithmetic *)
Ecall(Id "foo", [E1; E2])    (* Method call *)
Esingleton(Evar x)           (* Singleton set {x} *)
Eimage(Evar obj, Id "field") (* Object.field *)
```

### Formulas (Specifications)
```ocaml
Ftrue / Ffalse               (* Boolean constants *)
Fexp(E)                      (* Expression as formula *)
Fpointsto(x, f, v)           (* x.f ↦ v *)
Fsubseteq(A, B)              (* A ⊆ B *)
Fquant(Forall, [qb], F)      (* ∀ qb . F *)
Fconn(Conj, F1, F2)          (* F1 ∧ F2 *)
```

### Commands
```ocaml
Skip                         (* skip *)
Assign(x, E)                 (* x := E *)
New_class(x, "Cell")         (* x := new Cell *)
Field_assign(x, f, E)        (* x.f := E *)
Havoc(x)                     (* havoc x (nondeterministic) *)
```

### Type System
```ocaml
(* Annotated types *)
Tint, Tbool, Trgn, Tprop
Tclass(name)                 (* Class types *)
Tmath(name, Some ty)         (* Math types (for heap) *)

(* Type bindings *)
M.empty                      (* Empty context *)
M.add (Id "x") Tint env.ctxt (* Add binding *)
```

---

## Common Function Signatures

### Parsing
```ocaml
val parse_file : pathname -> Ast.program list
val parse_with_error : Lexing.lexbuf -> Ast.program
```

### Type Checking
```ocaml
val tc_program : Ast.program list -> (penv * Ctbl.t) Result.t
val tc_exp : tenv -> Ast.exp -> Annot.ity Result.t
val tc_formula : tenv -> Ast.formula -> unit Result.t
```

### Pre-translation
```ocaml
val process : Ctbl.t -> penv -> penv
```

### Translation
```ocaml
val compile_penv : ctxt -> penv -> Why3.Ptree.mlw_file list
val trans_exp : ctxt -> Annot.exp -> Why3.Ptree.expr
val trans_formula : ctxt -> Annot.formula -> Why3.Ptree.term
```

### Utilities
```ocaml
(* From Lib module *)
val concat_map : ('a -> 'b list) -> 'a list -> 'b list
val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
val last : 'a list -> 'a

(* Result monad *)
let ( let* ) x f = Result.bind x f
let ( let+ ) x f = Result.map x f
```

---

## Command Line Reference

### Basic Usage
```bash
whyrel file.rl -o output.mlw          # Translate to Why3
whyrel f1.rl f2.rl -o all.mlw         # Multiple input files
whyrel -version                       # Show version
whyrel -help                          # Show help
```

### Diagnostic Flags
```bash
whyrel file.rl --parse-only           # Stop after parsing
whyrel file.rl --typecheck-only       # Stop after type checking
whyrel file.rl --debug                # Enable debug output
whyrel file.rl --margin 120 -o out.mlw  # Set output margin
```

### Feature Flags
```bash
whyrel file.rl --locEq MethodName     # Derive local equivalence
whyrel file.rl --no-encap-check       # Skip encapsulation check
whyrel file.rl --no-frame-lemma       # Omit frame lemmas
whyrel file.rl -all-exists            # Use forall-exists mode
```

---

## Build Commands

### Main Targets
```bash
make                    # Build bytecode (main.byte)
make main.native        # Build native executable
make clean              # Clean build artifacts
```

### Development
```bash
make dep-graph          # Generate module dependency graph
make dep-graph-functions  # Generate function dependency graph
make explain            # Show parser conflicts
make menhir-repl        # Interactive parser testing
```

---

## Debugging Workflow

### 1. Check Syntax
```bash
whyrel file.rl --parse-only
# Errors: Check lexer.mll and parser.mly
```

### 2. Check Types
```bash
whyrel file.rl --typecheck-only
# Errors: Check typing.ml and annot.ml
```

### 3. Check Generated Code
```bash
whyrel file.rl -o output.mlw
cat output.mlw | head -100
# Review generated Why3 syntax
```

### 4. Verify in Why3
```bash
why3 ide output.mlw
# Interactive proof checking
```

### 5. Enable Debug Output
```bash
whyrel file.rl --debug 2>&1 | less
# Look for:
#   - Type checking steps
#   - Environment state
#   - Translation decisions
```

---

## Module Map by Task

| Task | Primary Module | Secondary Modules |
|------|---|---|
| Add language feature | parser | typing, translate |
| Fix type error | typing | annot |
| Add analysis pass | pretrans | typing |
| Debug code generation | translate | why3util |
| Improve encapsulation | pretrans::encap_check | ctbl |
| Handle new class feature | ctbl | typing |
| Change output format | translate::why3util | why3constants |
| Profile performance | lib | (all modules) |

---

## Important Patterns

### Result Monad Usage
```ocaml
let ( let* ) = Result.bind

let my_function () : 'a Result.t =
  let* x = parse_file "file.rl" in
  let* (penv, ctbl) = tc_program x in
  let* () = validate_encapsulation ctbl penv in
  Ok penv
```

### Class Table Lookups
```ocaml
(* From ctbl.ml *)
let find_class ctbl name : class_def = ...
let find_method ctbl cname mname : method_def = ...
let find_interface ctbl name : interface_def = ...
```

### Type Checking Pattern
```ocaml
let rec tc_exp tenv exp : ity Result.t =
  match exp.elt with
  | Evar x -> 
    begin match M.find x tenv.ctxt with
    | Some ty -> Ok ty
    | None -> Error ("Unknown variable: " ^ string_of_ident x)
    end
  | Ebinop(op, e1, e2) ->
    let* ty1 = tc_exp tenv e1 in
    let* ty2 = tc_exp tenv e2 in
    let (t1, t2, tr) = binop_ty op in
    if ty1 = t1 && ty2 = t2 then Ok tr
    else Error "Type mismatch in binary operation"
  (* ... *)
```

### Translation Pattern
```ocaml
let rec trans_exp ctxt exp : Why3.Ptree.expr =
  match exp.elt with
  | Econst (Eint n) -> 
    mk_const (Why3.Number.int_literal n)
  | Evar x -> 
    let (_, qualid) = M.find x ctxt.ident_map in
    mk_ident qualid
  | Ebinop(Plus, e1, e2) ->
    let e1_why3 = trans_exp ctxt e1 in
    let e2_why3 = trans_exp ctxt e2 in
    mk_binop Plus e1_why3 e2_why3
  (* ... *)
```

---

## Testing Your Changes

### Minimal Test
```bash
# Create simple.rl
interface I = 
  class C { f: int }
end

# Test
whyrel simple.rl --typecheck-only
echo "Status: $?"
```

### Run Example Suite
```bash
cd examples/Cell && make
why3 ide _why3_sessions.xml
```

### Check Regression
```bash
make clean && make
cd examples/factorial
make clean && make
# Should complete without errors
```

---

## File Size Reference

| File | Lines | Purpose | Complexity |
|------|-------|---------|-----------|
| typing.ml | 2467 | Type checking | ★★★★★ |
| translate.ml | 4136 | Code generation | ★★★★★ |
| pretrans.ml | 1455 | Pre-analysis | ★★★★ |
| parser.mly | ~500 | Grammar | ★★★ |
| ast.ml | 386 | AST types | ★★ |
| main.ml | 218 | CLI | ★★ |
| ctbl.ml | ~500 | Class table | ★★★ |
| annot.ml | ~200 | Annotations | ★★ |

---

## Critical Constants & Conventions

### Naming Conventions
```ocaml
(* Type constructors: Capitalized *)
Tclass, Tint, Tmath, Trgn

(* Values: lowercase *)
int_ty, bool_ty, rgn_ty, unit_ty

(* Classes in Why3: Capitalized *)
Cell → "Cell", M::MyClass → "M_MyClass"

(* Fields in Why3: lowercase_class_field *)
Cell.value → "cell_value"

(* Methods: preserved from source *)
foo() → "foo"
```

### Type Abbreviations
```ocaml
type ity = Annot.ity      (* Intermediate type *)
type ident = Ast.ident    (* Qualified/unqualified name *)
type loc = Ast.loc        (* Source location *)
type penv = definition M.t  (* Program environment *)
type ctbl = Ctbl.t        (* Class table *)
```

### Standard Maps
```ocaml
(* String → Type mapping *)
let env = M.empty
M.add (Id "x") Tint env

(* Class → Info mapping *)
Ctbl.classes ctbl  (* class_name → class_info *)
```

---

## Common Errors & Solutions

### Parse Errors
```
"syntax error"
→ Check lexer.mll for tokenization issues
→ Check parser.mly for grammar rule conflicts
→ Run: make explain
```

### Type Errors
```
"Unknown class: Foo"
→ Class not declared in interface/module
→ Check ctbl.ml class lookup
→ Run: whyrel file.rl --debug

"Type mismatch: expected Tint, got Tbool"
→ Type checking failed in typing.ml
→ Check type environment setup
```

### Encapsulation Errors
```
"Private field accessed"
→ External code accessing hidden field
→ Check visibility in module definition
→ Review encap_check.ml rules
```

### Why3 Proof Failures
```
"Proof obligation not discharged"
→ Generated Why3 lacks necessary lemmas
→ Check frame lemma generation in pretrans.ml
→ Review invariant expansion
→ May need stronger user-provided specs
```

---

## Performance Tips

### For Large Programs
1. Use `--parse-only` to check syntax quickly
2. Use `--typecheck-only` before full compilation
3. Disable `--no-frame-lemma` if not needed
4. Consider using `-all-exists` mode for specific cases

### Build Speed
```bash
make main.byte    # Faster than native
make -j 4         # Parallel build (if supported)
```

### Why3 Proving
1. Use fast solvers first (Alt-Ergo)
2. Save sessions in Why3 IDE
3. Use `why3 replay` to check cached results

---

## Resources by File Type

### To Learn About...
- **Language syntax** → `parser/parser.mly`
- **Type system** → `typing/annot.ml`, look at `ity` type
- **Proof rules** → Examples in `examples/` directory
- **Translation strategy** → Read `translate/translate.ml` preamble
- **Why3 integration** → `translate/why3util.ml`, `translate/why3constants.ml`

### For Examples
- **Equivalence** → `examples/Cell/`, `examples/factorial/`
- **Information flow** → `examples/sumpub/`
- **Compiler optimization** → `examples/tiling/`
- **Complex data structures** → `examples/Kruskal/`, `examples/SSSP/`

