# WhyRel Architecture Guide


### What is WhyRel?

**WhyRel** is a tool for verifying **relational properties** of object-oriented programs written in a Java-like language. It enables developers to prove:

- **Program equivalence**: Two implementations produce the same results
- **Information flow security**: Programs don't leak sensitive information
- **Program transformations**: Compiler optimizations preserve behavior
- **Encapsulation**: Hidden invariants are maintained

### Key Features

- **Built on Why3**: Leverages the Why3 platform for deductive verification
- **Relational Region Logic**: Implements relational specifications for heap-based reasoning
- **Unary Region Logic**: Supports single-program verification
- **SMT Solver Integration**: Uses Alt-Ergo, Z3, CVC3, CVC4 to discharge verification conditions
- **Modular Reasoning**: Supports encapsulation, module interfaces, and modular linking rules

## System Architecture Overview


WhyRel follows a classic compiler pipeline architecture:

```
Source Code (*.rl)
    ↓
Lexer/Parser           → see parser/
    ↓
Type Checker           → see typing/
    ↓
Pre-translator         → see pretrans/
    ↓
Translator             → see translate/
    ↓
Why3 Output (*.mlw)
```


### High-Level Component Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        WhyRel Tool Chain                                │
└─────────────────────────────────────────────────────────────────────────┘

                              INPUT
                                ↓
                    ┌───────────────────────┐
                    │   WhyRel Source File  │
                    │      (file.rl)        │
                    └───────────┬───────────┘
                                ↓
        ┌───────────────────────────────────────────────────┐
        │            PARSING PHASE (parser/)                │
        ├───────────────────────────────────────────────────┤
        │ • Lexer (lexer.mll) - Tokenization              │
        │ • Parser (parser.mly) - Syntax Analysis         │
        │ • AST (ast.ml) - Syntax Tree Representation     │
        └───────────────┬────────────────────────────────┬─┘
                        ↓                                ↓
            If --parse-only → EXIT            Parse Output
                                                    ↓
        ┌───────────────────────────────────────────────────┐
        │       TYPE CHECKING PHASE (typing/)              │
        ├───────────────────────────────────────────────────┤
        │ • Build type environments (Annot, Ctbl)         │
        │ • Validate well-formedness                       │
        │ • Check expressions and formulas                 │
        │ • Generate annotated AST with types             │
        │ • Entry: typing.ml::tc_program                  │
        └───────────────┬────────────────────────────────┬─┘
                        ↓                                ↓
        If --typecheck-only → EXIT        Type-checked Program
                                           (penv, ctbl)
                                                    ↓
        ┌───────────────────────────────────────────────────┐
        │     PRE-TRANSLATION PHASE (pretrans/)            │
        ├───────────────────────────────────────────────────┤
        │ • Expand specs with invariants                    │
        │ • Check encapsulation constraints                │
        │ • Derive biinterfaces                            │
        │ • Resolve datagroups                             │
        │ • Generate frame lemmas                          │
        │ • Add proof obligations                          │
        │ • Entry: pretrans.ml::process                    │
        └───────────────┬────────────────────────────────┬─┘
                        ↓                                ↓
                                        Transformed Program
                                           (penv, ctbl)
                                                    ↓
        ┌───────────────────────────────────────────────────┐
        │      TRANSLATION PHASE (translate/)              │
        ├───────────────────────────────────────────────────┤
        │ • Build state module (heap model)                │
        │ • Translate classes → algebraic types           │
        │ • Translate methods → Why3 functions            │
        │ • Translate formulas → Why3 terms               │
        │ • Translate bimodules → relational predicates   │
        │ • Entry: translate.ml::compile_penv            │
        └───────────────┬────────────────────────────────┬─┘
                        ↓                                ↓
                                       Why3 Parse Trees
                                    (mlw_file list)
                                                    ↓
        ┌───────────────────────────────────────────────────┐
        │      OUTPUT GENERATION (main.ml)                 │
        ├───────────────────────────────────────────────────┤
        │ • Format Why3 parse trees                        │
        │ • Write to output file                           │
        └───────────────┬────────────────────────────────┬─┘
                        ↓                                ↓
                                            OUTPUT FILE
                                         (file.mlw)
                                                    ↓
                        ┌───────────────────────────────┐
                        │    Why3 + SMT Solvers         │
                        │ (Verification Outside Scope)  │
                        └───────────────────────────────┘
```

---

## Module Dependency Graph

```
                              main.ml
                                 │
                    ┌────────────┴────────────┐
                    ↓                         ↓
            Parser (ast, astutil)      Typing (typing.ml)
                    │                         │
                    ├──→ astutil ←────────────┘
                    │
                    └──→ Lexer/Parser
                         (lexer, parser)

                            Typing
                    ┌────────────┬────────────┐
                    ↓            ↓            ↓
              annot.ml      ctbl.ml      pretty.ml
                    │            │
                    └────────────┴───→ lib.ml (utilities)

              Typing (type-checked)
                    │
                    └──→ Pretrans.ml
                         │
                    ┌────┼────┬──────────┬──────────┐
                    ↓    ↓    ↓          ↓          ↓
                 Rename Encap LocEq Datagroup Boundary
                 Locals Check      Resolution  Info
                    │    │    │          │          │
                    └────┴────┴──────────┴──────────┘
                         │
                    Pretrans (output: penv)
                         │
                    ┌────┴────────┐
                    ↓             ↓
              Translate.ml  Why3util.ml
                    │             │
                    └─────┬───────┘
                          ↓
                  Why3constants.ml
                          │
                          └──→ Why3 Output

                    Utility Modules
                          │
                    ┌─────┴─────┐
                    ↓           ↓
                 lib.ml    why3util.ml
```

---

## Data Flow Through Processing Stages


### Stage 1: Parsing

```
file.rl (Text Input)
    ↓
    ├─ Lexer → Stream of Tokens
    │           (Keywords, Identifiers, Operators, Literals)
    ↓
    ├─ Parser (Menhir) → Parse Tree
    │                    (Following parser.mly grammar)
    ↓
AST (Abstract Syntax Tree)
    ├─ Ast.program list
    ├─ Each program is:
    │  ├─ Unary_interface {name, elements}
    │  ├─ Module {name, interface, elements}
    │  ├─ Bimodule {name, left, right, elements}
    │  └─ Datagroup {name, fields}
    └─ Each element has:
       ├─ Classes (with fields)
       ├─ Methods (with signatures)
       ├─ Specifications
       └─ Command implementations
```

**Key Data**: `Ast.program list`

### Stage 2: Type Checking

```
Ast.program list
    ↓
Type Checker (typing.ml::tc_program)
    │
    ├─ Build class table (ctbl)
    │  └─ Maps: className → class_info
    │           methodName → method_info
    │           fieldName → field_info
    │
    ├─ Build program environment (penv)
    │  └─ Maps: name → interface | module | bimodule | datagroup
    │
    ├─ Validate well-formedness
    │  ├─ Classes are well-defined
    │  ├─ Methods have consistent signatures
    │  ├─ Specifications type-check
    │  └─ All referenced identifiers exist
    │
    ├─ Type check expressions
    │  └─ Infer types, ensure operations are valid
    │
    ├─ Type check formulas
    │  └─ Ensure logical operations are sound
    │
    └─ Generate Annot.program list
       └─ AST + type annotations

Output: (penv, ctbl)
```

**Key Data**: 
- `penv`: Program Environment (name → definition M.t)
- `ctbl`: Class Table (comprehensive class info)
- `Annot.program list`: Type-annotated AST

### Stage 3: Pre-translation

```
(penv, ctbl)
    ↓
Pretrans.process(ctbl, penv)
    │
    ├─ Expand_method_spec
    │  ├─ Add public invariants to interface methods
    │  ├─ Add private invariants to module methods
    │  └─ Add coupling predicates to bimodule methods
    │
    ├─ Encap_check
    │  └─ Verify private fields not accessed from outside
    │
    ├─ Derive_biinterface
    │  └─ Create biinterface from module pairs
    │
    ├─ LocEq (optional)
    │  └─ Derive local equivalence specifications
    │
    ├─ Resolve_datagroups
    │  └─ Expand "any" to concrete field sets
    │
    ├─ Generate_frame_lemmas
    │  └─ Create modular linking rule lemmas
    │
    └─ Generate_proof_obligations
       └─ Add verification conditions

Output: penv (transformed)
```

**Key Data**: Modified `penv` with expanded specifications and proof obligations

### Stage 4: Translation

```
(penv, ctbl)
    ↓
Translate.compile_penv(context, penv)
    │
    ├─ Build_State.mk
    │  └─ Create Why3 state module (heap model)
    │     ├─ type reftype = Class1 {...} | Class2 {...}
    │     ├─ type heap = heap_record
    │     └─ accessor/updater functions
    │
    ├─ For each Interface in penv:
    │  ├─ Translate type declarations
    │  ├─ Translate method signatures
    │  └─ Translate method axioms/lemmas
    │
    ├─ For each Module in penv:
    │  ├─ Translate class definitions
    │  ├─ Translate field declarations
    │  ├─ For each method:
    │  │  ├─ Translate pre/post-conditions
    │  │  ├─ Translate body (commands → Why3)
    │  │  └─ Add frame lemmas
    │  └─ Translate invariants
    │
    ├─ For each Bimodule in penv:
    │  ├─ Translate bimethod specifications
    │  ├─ Translate relational predicates
    │  └─ Translate bicommand implementations
    │
    └─ Generate Why3 modules

Output: Why3.Ptree.mlw_file list
```

**Key Transformations**:
1. Classes → Why3 type constructors
2. Fields → Why3 functions (accessor/updater)
3. Methods → Why3 let-functions with pre/post
4. Formulas → Why3 terms
5. Bimodules → Relational Why3 predicates



### Stage 5: Output

```
Why3.Ptree.mlw_file list
    ↓
Format.pp_mlw_file
    │
    └─ Convert parse tree → readable Why3 syntax

Write to file (main.ml::get_formatter)
    │
    └─ Output .mlw file
```


---

## Key Data Structures

### 1. Type System

```
┌─ Annotated Types (ity)
│  ├─ Tint         (Integer)
│  ├─ Tbool        (Boolean)
│  ├─ Trgn         (Region - heap subset)
│  ├─ Tprop        (Proposition - logical formula)
│  ├─ Tclass(name) (User-defined class)
│  └─ Tmath(...)   (Math type for heap encoding)
│
└─ Raw Types (ty)
   └─ Tctor(name, type_list)
      (Constructor-based type system)
```

### 2. Environment Types

```
tenv (Type Environment):
├─ ctxt: ident → ity (variable type mappings)
├─ ctbl: Ctbl.t (class information)
├─ grps: (ident * ident list) list (datagroups)
└─ exts: ident list (extern types)

bi_tenv (Bimodular Type Environment):
├─ left_tenv: tenv
├─ right_tenv: tenv
└─ bipreds: bipred_params M.t (relational predicates)
```

### 3. Program Environment (penv)

```
penv: ident → definition

definition:
├─ Unary_interface of interface_def
│  └─ Contains: classes, methods, public fields, invariants
├─ Module of module_def
│  └─ Contains: interface, classes, fields, method impls
├─ Biinterface of biinterface_def
│  └─ Relational interface (two unary interfaces)
├─ Bimodule of bimodule_def
│  └─ Relational module (two modules + bicommands)
├─ Datagroup of datagroup_def
│  └─ Field groupings for abstraction
└─ Extern of extern_def
   └─ External definitions
```

### 4. Class Table (Ctbl.t)

```
Ctbl.t contains:
├─ classes: ident → class_info
│  └─ class_info: {name, fields, super, ...}
├─ interfaces: ident → interface_info
│  └─ interface_info: {name, methods, ...}
├─ modules: ident → module_info
│  └─ module_info: {name, interface, ...}
└─ bimodules: ident → bimodule_info
   └─ bimodule_info: {name, left, right, ...}
```

## Module Interaction Patterns

### Pattern 1: Type Environment Threading

```
Initial environment setup (typing.ml):
tenv = { ctxt: M.add (Id "alloc") Trgn M.empty; ctbl; ... }

Pass through type checking:
tc_exp tenv expr → Result(ity)
tc_formula tenv formula → Result(())

Update environment:
let tenv' = {tenv with ctxt = M.add (Id "x") Tint tenv.ctxt}

Use updated environment:
tc_statement tenv' statement
```

### Pattern 2: Class Table Lookup

```
Get class info:
let cls = Ctbl.find_class ctbl (Id "MyClass")

Access class fields:
List.iter (fun field → 
  printf "%s: %s" field.name field.type
) cls.fields

Validate field access:
if List.mem_assoc field_name cls.fields
then Ok (get_field_type cls field_name)
else Error "Field not found"
```

### Pattern 3: Program Environment Traversal

```
Iterate all interfaces:
M.iter (fun name def → match def with
  | Unary_interface iface → process_interface iface
  | _ → ()
) penv

Find specific element:
match M.find (Id "ClassName") penv with
| Unary_interface {...} → ...
| Module {...} → ...
| _ → Error "Not found"
```
---

---

## Function Call Chain Analysis

### Complete WhyRel Execution

```
main () [tools/main.ml]
  │
  ├─ parse_program !program_files
  │  │
  │  └─ parse_file (for each file)
  │      │
  │      ├─ Lexing.from_string (lexer.mll)
  │      └─ Parser.top Lexer.token lexbuf
  │          → Ast.program list
  │
  └─ typecheck_program parsed_program
      │
      └─ Typing.tc_program
          │
          ├─ Build initial environments
          ├─ Process each program element
          │  ├─ tc_interface/tc_module/tc_bimodule
          │  ├─ tc_exp for expressions in methods
          │  └─ tc_formula for formulas in specs
          ├─ Validate encapsulation
          └─ Return: (penv, ctbl)
       
  └─ (if not --typecheck-only)
      │
      ├─ Pretrans.process ctbl penv
      │  │
      │  ├─ Expand_method_spec.expand
      │  ├─ Encap_check.check
      │  ├─ Derive_biinterface.derive
      │  ├─ Resolve_datagroups.resolve
      │  └─ Generate frame lemmas
      │      → penv (modified)
      │
      ├─ Translate.compile_penv context penv
      │  │
      │  ├─ Build_State.mk (create heap module)
      │  ├─ For each interface/module/bimodule:
      │  │  ├─ trans_exp (translate expressions)
      │  │  ├─ trans_formula (translate formulas)
      │  │  └─ trans_command (translate commands)
      │  └─ Return: Why3.Ptree.mlw_file list
      │
      └─ Format and output
          │
          ├─ get_formatter() (stdout or file)
          ├─ Why3.Mlw_printer.pp_mlw_file
          └─ Write to .mlw file
```

---

## Critical Code Paths

### Path 1: Adding a New Expression Type

```
1. ast.ml
   Add: | Enewexpr of exp node
   
2. lexer.mll
   Add token for syntax
   
3. parser.mly
   Add: | NEWKW expr { no_loc (Enewexpr $2) }
   
4. typing.ml
   Add case in tc_exp:
   | Enewexpr e -> ...
   
5. annot.ml
   If type needs special representation
   
6. translate.ml
   Add case in trans_exp:
   | Enewexpr e -> ...
   
7. pretty.ml
   Add printing support
```

### Path 2: Type Checking Flow

```
tc_program input
  │
  ├─ Parse input → Ast.program list
  │
  ├─ For each interface:
  │  ├─ Register in class table
  │  └─ Check method signatures
  │
  ├─ For each module:
  │  ├─ Validate against interface
  │  ├─ Check field declarations
  │  └─ Type check methods:
  │     ├─ tc_method_body
  │     │  ├─ tc_command (for each statement)
  │     │  │  ├─ tc_exp (for each expression)
  │     │  │  └─ Update type environment
  │     │  └─ Check command sequence
  │     └─ Check specs:
  │        ├─ tc_formula (preconditions)
  │        └─ tc_formula (postconditions)
  │
  ├─ For each bimodule:
  │  ├─ Check interfaces match
  │  ├─ Type check bicommands (2-program execution)
  │  └─ Type check specifications
  │
  └─ Return: (penv, ctbl)
```

### Path 3: Translation Flow

```
compile_penv context penv
  │
  ├─ Build state module
  │  ├─ Create reftype algebraic type
  │  │  └─ For each class: | ClassName of field list
  │  └─ Create accessor/updater functions
  │
  ├─ Process interfaces
  │  └─ For each method:
  │     ├─ Create Why3 signature
  │     └─ Translate specifications
  │
  ├─ Process modules
  │  └─ For each method:
  │     ├─ trans_formula → why3_term (pre/post)
  │     ├─ trans_command → why3_stmt
  │     │  ├─ Translate assignments
  │     │  ├─ Translate field access
  │     │  └─ Translate new/delete
  │     └─ Add frame lemmas
  │
  └─ Process bimodules
     └─ For each bimethod:
        ├─ Create bimethod predicate
        ├─ trans_formula → why3_relational_term
        └─ trans_bicommand → why3_stmt pair
```

---


## Memory/Heap Model

### WhyRel to Why3 Heap Translation

```
WhyRel (Object-oriented):
  obj.field := value
  x := obj.field

Why3 (Functional):
  heap' = update_field heap obj field_name value
  value = read_field heap obj field_name

Explicit heap representation:
  type heap = {
    cell_value: heap → reftype → int;
    cell_rep: heap → reftype → rgn;
    ...
  }

Accessor functions:
  let cell_value (h: heap) (r: reftype): int = h.cell_value r
  let cell_rep (h: heap) (r: reftype): rgn = h.cell_rep r

Updater functions:
  let update_cell_value (h: heap) (r: reftype) (v: int): heap = {
    h with cell_value = fun obj → if obj = r then v else h.cell_value obj
  }
```

---

## Why3 Integration Points

```
┌─ AST (WhyRel)
│  └─ Program structure
│     (interfaces, modules, methods, fields)
│
├─ Annotated AST
│  └─ Types and specifications
│
├─ Why3 Parse Tree
│  ├─ mlw_file (modules)
│  ├─ type_def (types)
│  ├─ decl (declarations)
│  ├─ expr (terms)
│  ├─ term (logical formulas)
│  └─ spec (pre/post-conditions)
│
└─ Why3 Verification
   ├─ Generates verification conditions
   ├─ Calls SMT solvers
   └─ Produces proof discharge results
```

---

## Error Handling Flow

```
Parsing phase:
  Lexer_error/Parser.Error
    │
    └─ Print position info
    └─ Exit with error

Type checking phase:
  Result monad (Ok/Error)
    │
    ├─ Type mismatch
    ├─ Undefined variable
    ├─ Encapsulation violation
    └─ Well-formedness failure
    │
    └─ Format error message
    └─ Exit with error

Pre-translation phase:
  Exception or Result
    │
    └─ Encapsulation check failure
    └─ Invalid specification
    └─ Exit with error

Translation phase:
  Exception (unlikely if prior phases succeeded)
    │
    └─ Handle gracefully
    └─ Report position in source

Output phase:
  File I/O errors
    │
    └─ Handle file write failures
```



X