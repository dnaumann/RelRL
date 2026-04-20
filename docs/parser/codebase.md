# Parser Module (`src/parser/`)

**Purpose**: Converts source text into abstract syntax trees.

## Key Files

- **`ast.ml`** (386 lines)
  - Defines the Abstract Syntax Tree types
  - Core types: expressions, formulas, commands, declarations
  - Type definitions, modifiers, operators, effects
  - Location tracking for error reporting

- **`astutil.ml`**
  - Utility functions for AST manipulation
  - Printing, comparison, and traversal functions
  - Constructors for common AST nodes

- **`lexer.mll`** (ocamllex)
  - Tokenizes source code
  - Handles keywords, identifiers, operators, literals
  - Comments, whitespace, and location tracking

- **`parser.mly`** (Menhir)
  - Context-free grammar for WhyRel language
  - Builds AST from tokens
  - Error recovery and conflict resolution

## AST Structure Highlights

```ocaml
(* Identifiers *)
type ident = Id of string | Qualid of string * string list

(* Types *)
type ty = Tctor of ident * ty node list
let int_ty = Tctor(Id "int", [])
let rgn_ty = Tctor(Id "rgn", [])  (* regions for heap location sets *)

(* Expressions *)
type exp =
  | Econst of const_exp node
  | Evar of ident
  | Ebinop of binop * exp node * exp node
  | Ecall of ident * exp node list
  (* ... and more *)

(* Formulas (logical specifications) *)
type formula =
  | Ftrue | Ffalse
  | Fexp of exp node
  | Fpointsto of ident * ident * exp node  (* x.f ↦ e *)
  | Fsubseteq of exp node * exp node       (* set containment *)
  | Fquant of quantifier * quantifier_bindings * formula node
  (* ... and more *)

(* Commands (statements) *)
type atomic_command =
  | Skip
  | Assign of ident * exp node
  | New_class of ident * ident
  | Field_assign of ident * ident * exp node
  (* ... and more *)
```

## Data Flow

```
file.rl (Text Input)
    ↓
    ├─ Lexer → Stream of Tokens
    │           (Keywords, Identifiers, Operators, Literals)
    ↓
    ├─ Parser (Menhir) → Parse Tree
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

**Output**: `Ast.program list`
