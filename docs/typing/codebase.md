# Typing Module (`src/typing/`)

**Purpose**: Type checking, well-formedness validation, and AST annotation.

## Key Files

- **`typing.ml`** (2467 lines)
  - Main type checker and well-formedness validator
  - Implements region logic type system
  - Validates classes, methods, bimodules, formulas
  - Core function: `tc_program : Ast.program -> (penv * Ctbl.t) result`

- **`annot.ml`**
  - Defines annotated AST with type information
  - Types include: class types, logical properties types
  - Maps raw AST to typed AST

- **`ctbl.mli` / `ctbl.ml`**
  - **Class Table**: Data structure holding class definitions
  - Methods, fields, interfaces, invariants
  - Encapsulation information and visibility scopes

- **`pretty.ml`**
  - Pretty printer for WhyRel syntax trees
  - Formats expressions, formulas, and commands

## Key Concepts

### Typing Environments

```ocaml
type tenv = {
  ctxt: ity M.t;              (* Type context for identifiers *)
  ctbl: Ctbl.t;               (* Class table *)
  grps: (ident * ident list) list;  (* Datagroups *)
  exts: ident list;            (* Extern types *)
}
```

### Intermediate Type System (`ity`)

- Core types: `Tint`, `Tbool`, `Trgn` (regions), `Tprop` (propositions)
- Class types: `Tclass of class_name`
- Math types: `Tmath of name * ty option` (for heap model)

### Program Environment (`penv`)

- Collections of: interfaces, modules, bimodules, datagroups
- Stored as: `(ident, definition) M.t` (map data structure)

## Data Flow

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
```

**Output**: `(penv, ctbl)`

## Type Checking Flow

```
tc_program input
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

## Interaction Patterns

### Type Environment Threading

```ocaml
(* Initial environment setup *)
tenv = { ctxt: M.add (Id "alloc") Trgn M.empty; ctbl; ... }

(* Pass through type checking *)
tc_exp tenv expr → Result(ity)
tc_formula tenv formula → Result(())

(* Update environment *)
let tenv' = {tenv with ctxt = M.add (Id "x") Tint tenv.ctxt}
```

### Class Table Lookup

```ocaml
let cls = Ctbl.find_class ctbl (Id "MyClass")

(* Validate field access *)
if List.mem_assoc field_name cls.fields
then Ok (get_field_type cls field_name)
else Error "Field not found"
```
