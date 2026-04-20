# Translation Module (`src/translate/`)

**Purpose**: Converts annotated AST to Why3 code.

## Key Files

- **`translate.ml`** (4136 lines)
  - Main translator from WhyRel to Why3
  - Entry function: `compile_penv : context -> penv -> Why3.Ptree.mlw_file list`
  - Handles classes, methods, bimodules, predicates

- **`why3constants.ml`**
  - Standard Why3 identifier names
  - Pre-defined functions and modules

## Translation Strategy

### Heap Model

- Explicit heap representation in Why3
- Classes → constructors of `reftype` algebraic datatype
- Fields → accessor functions
- Pointer/field updates → heap updates

### Example Class Translation

```
WhyRel Source:
  class Cell { value: int; rep: rgn; }

Why3 Output:
  type reftype = Cell payload ...
  let cell_value (h : heap) (r : reftype) : int
  let cell_rep (h : heap) (r : reftype) : rgn
```

### Specification Translation

- Pre/post-conditions → Why3 pre/post-conditions
- Invariants → lemmas and assertions
- Relational predicates → two-program Why3 predicates

## Data Flow

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
```

**Output**: `Why3.Ptree.mlw_file list`

## Key Transformations

1. Classes → Why3 type constructors
2. Fields → Why3 functions (accessor/updater)
3. Methods → Why3 let-functions with pre/post
4. Formulas → Why3 terms
5. Bimodules → Relational Why3 predicates

## Why3 Heap Model

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

Updater functions:
  let update_cell_value (h: heap) (r: reftype) (v: int): heap = {
    h with cell_value = fun obj → if obj = r then v else h.cell_value obj
  }
```
