# Utility Module (`src/util/`)

**Purpose**: Common utility functions shared across all pipeline stages.

## Key Files

- **`lib.ml`**
  - List utilities (map, filter, fold variants)
  - Option/Result handling
  - String manipulation
  - The `M` map module (keyed by `Ast.ident`)

- **`why3util.ml`**
  - Helpers for constructing Why3 parse trees
  - Identifier creation, type building, expression wrapping
