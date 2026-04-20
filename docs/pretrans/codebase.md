# Pre-translation Module (`src/pretrans/`)

**Purpose**: Program analysis and transformation before code generation.

## Key Files

- **`pretrans.ml`** (1455 lines)
  - Main orchestrator for pre-translation
  - Expands specs with invariants
  - Adds frame lemmas and proof obligations
  - Entry function: `process : Ctbl.t -> penv -> penv`

- **`encap_check.mli` / `encap_check.ml`**
  - Validates encapsulation constraints
  - Ensures hidden fields aren't leaked

- **`boundary_info.mli` / `boundary_info.ml`**
  - Tracks module boundaries
  - Caches information about public/private interfaces

- **`derive_biinterface.ml`**
  - Constructs bimodule interfaces from unary modules
  - Essential for relational reasoning

- **`locEq.mli` / `locEq.ml`**
  - Derives local equivalence specifications
  - Experimental feature (`-locEq` flag)

- **`resolve_datagroups.mli` / `resolve_datagroups.ml`**
  - Expands datagroup wildcards (e.g., `any`)
  - Maps to actual field sets

## Transformations Applied

1. **Spec Expansion**: Adds invariants to pre/post-conditions
2. **Frame Lemmas**: Generates lemmas encoding modular linking rules
3. **Encapsulation**: Validates privacy constraints
4. **Datagroup Resolution**: Expands `any` references

## Data Flow

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
```

**Output**: Modified `penv` with expanded specifications and proof obligations
