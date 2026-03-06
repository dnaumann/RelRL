# WhyRel Codebase Documentation

## Table of Contents

1. [Project Overview](#project-overview)
2. [Architecture](#architecture)
3. [Directory Structure](#directory-structure)
4. [Core Components](#core-components)
5. [Processing Pipeline](#processing-pipeline)
6. [Key Data Structures](#key-data-structures)
7. [Module Reference](#module-reference)
8. [Development Guide](#development-guide)
9. [Examples](#examples)

---

## Project Overview

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

### Technology Stack

- **Language**: OCaml 5.1.1+
- **Build System**: OCamlbuild 0.14.3
- **Parser**: Menhir (Yacc for OCaml)
- **Lexer**: ocamllex
- **External Dependencies**: Why3 1.7.2

---

## Architecture

### High-Level Design

WhyRel follows a **classic compiler pipeline** architecture:

```
Source Code (*.rl)
    ↓
Lexer (lexer.mll)
    ↓
Parser (parser.mly)
    ↓
Abstract Syntax Tree (AST)
    ↓
Type Checker & Annotator
    ↓
Annotated AST with Types
    ↓
Pre-translator (Analysis & Transformations)
    ↓
Translator
    ↓
Why3 Output (*.mlw)
    ↓
Why3 Prover (with SMT solvers)
```


## Core Components

### 1. Parser Module (`src/parser/`)

**Purpose**: Converts source text into abstract syntax trees.

#### Key Files:

- **`ast.ml`** (386 lines)
  - Defines the Abstract Syntax Tree types
  - Core types: expressions, formulas, commands, declarations
  - Type definitions, modifiers, operators, effects
  - Location tracking for error reporting

- **`astutil.ml`**
  - Utility functions for AST manipulation
  - Printing, comparison, and traversal functions
  - Constructors for common AST nodes

- **`lexer.mll`** (Ocamllex)
  - Tokenizes source code
  - Handles keywords, identifiers, operators, literals
  - Comments, whitespace, and location tracking

- **`parser.mly`** (Menhir)
  - Context-free grammar for WhyRel language
  - Builds AST from tokens
  - Error recovery and conflict resolution

#### AST Structure Highlights:

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

### 2. Typing Module (`src/typing/`)

**Purpose**: Type checking, well-formedness validation, and AST annotation.

#### Key Files:

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

#### Key Concepts:

**Typing Environments**:
```ocaml
type tenv = {
  ctxt: ity M.t;              (* Type context for identifiers *)
  ctbl: Ctbl.t;               (* Class table *)
  grps: (ident * ident list) list;  (* Datagroups *)
  exts: ident list;            (* Extern types *)
}
```

**Intermediate Type System** (`ity`):
- Core types: `Tint`, `Tbool`, `Trgn` (regions), `Tprop` (propositions)
- Class types: `Tclass of class_name`
- Math types: `Tmath of name * ty option` (for heap model)

**Program Environment** (`penv`):
- Collections of: interfaces, modules, bimodules, datagroups
- Stored as: `(ident, definition) M.t` (map data structure)

### 3. Pre-translation Module (`src/pretrans/`)

**Purpose**: Program analysis and transformation before code generation.

#### Key Files:

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

#### Transformations Applied:

1. **Spec Expansion**: Adds invariants to pre/post-conditions
2. **Frame Lemmas**: Generates lemmas encoding modular linking rules
3. **Encapsulation**: Validates privacy constraints
4. **Datagroup Resolution**: Expands `any` references

### 4. Translation Module (`src/translate/`)

**Purpose**: Converts annotated AST to Why3 code.

#### Key Files:

- **`translate.ml`** (4136 lines)
  - Main translator from WhyRel to Why3
  - Entry function: `compile_penv : context -> penv -> Why3.Ptree.mlw_file list`
  - Handles classes, methods, bimodules, predicates

- **`why3constants.ml`**
  - Standard Why3 identifier names
  - Pre-defined functions and modules

#### Translation Strategy:

**Heap Model**:
- Explicit heap representation in Why3
- Classes → constructors of `reftype` algebraic datatype
- Fields → accessor functions
- Pointer/field updates → heap updates

**Example Class Translation**:
```
WhyRel Source:
  class Cell { value: int; rep: rgn; }

Why3 Output:
  type reftype = Cell payload ...
  let cell_value (h : heap) (r : reftype) : int
  let cell_rep (h : heap) (r : reftype) : rgn
```

**Specification Translation**:
- Pre/post-conditions → Why3 pre/post-conditions
- Invariants → lemmas and assertions
- Relational predicates → two-program Why3 predicates

### 5. Utility Module (`src/util/`)

**Purpose**: Common utility functions.

#### Files:

- **`lib.ml`**
  - List utilities (map, filter, fold variants)
  - Option/Result handling
  - String manipulation

- **`why3util.ml`**
  - Helpers for constructing Why3 parse trees
  - Identifier creation, type building, expression wrapping

### 6. Tools Module (`src/tools/`)

**Purpose**: Command-line interface and entry point.

#### Key File:

- **`main.ml`** (218 lines)
  - Entry point: `run : unit -> unit`
  - Command-line argument parsing
  - Coordinates parsing → type checking → pre-translation → translation
  - Output formatting and file management

#### Command-Line Options:

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

---



### Understanding the Codebase

**Entry Points for Learning**:

1. Start with `src/tools/main.ml` - Understand the main pipeline
2. Review `src/parser/ast.ml` - Core data structures
3. Examine `src/typing/typing.ml` - Type checking logic
4. Study `src/translate/translate.ml` - Code generation strategy

**Key Files by Functionality**:

| Goal | File(s) |
|------|---------|
| Add new language feature | `parser/{ast,lexer,parser}` |
| Modify type system | `typing/typing.ml`, `typing/annot.ml` |
| Change to code generation | `translate/translate.ml` |
| Add new analysis pass | `pretrans/pretrans.ml` |
| Fix bug in class handling | `typing/ctbl.ml` |

### Common Development Tasks

#### Adding a New Expression Type

1. **Define in AST** (`src/parser/ast.ml`):
   ```ocaml
   type exp = 
     | (* ... existing cases ... *)
     | Enew_op of exp node  (* Your new case *)
   ```

2. **Add parser rule** (`src/parser/parser.mly`):
   ```menhir
   exp:
     | (* ... existing rules ... *)
     | NEW exp { no_loc (Enew_op $2) }
   ```

3. **Add to pretty printer** (`src/typing/pretty.ml`):
   ```ocaml
   let rec string_of_exp = function
     | (* ... existing cases ... *)
     | Enew_op e -> Printf.sprintf "new %s" (string_of_exp (e.elt))
   ```

4. **Add type checker** (`src/typing/typing.ml`):
   ```ocaml
   let rec tc_exp tenv exp : ity result =
     match exp with
     | (* ... existing cases ... *)
     | Enew_op e -> 
       let* e_ty = tc_exp tenv e in
       (* validate type, return result type *)
   ```

5. **Add translator** (`src/translate/translate.ml`):
   ```ocaml
   let rec trans_exp ctxt exp : Ptree.expr =
     match exp with
     | (* ... existing cases ... *)
     | Enew_op e -> 
       let e_why3 = trans_exp ctxt e in
       (* convert to Why3 expression *)
   ```


## Code Style Guidelines

- **Naming**: Use snake_case for functions, lowercase modules
- **Type annotations**: Annotate non-trivial functions
- **Comments**: Document complex logic, especially in typing.ml and translate.ml
- **Error handling**: Use `Result` monad (defined in `lib.ml`)
- **Modules**: Split large modules into logical components with `.mli` interfaces
