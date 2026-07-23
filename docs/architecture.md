# WhyRel Architecture Guide


### What is WhyRel?

**WhyRel** is a tool for verifying **relational properties** of object-oriented programs written in a Java-like language. 

- **Built on Why3**: Leverages the Why3 platform for deductive verification
- **Relational Region Logic**: Implements relational specifications for heap-based reasoning
- **Unary Region Logic**: Supports single-program verification
- **Modular Reasoning**: Supports encapsulation, module interfaces, and modular linking rules

It enables developers to prove:

- **Program equivalence**: Two implementations produce the same results
- **Information flow security**: Programs don't leak sensitive information
- **Program transformations**: Compiler optimizations preserve behavior
- **Encapsulation**: Hidden invariants are maintained

## System Architecture Overview

### High-Level Component Diagram

```
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
## Workflows

### Type Checking Flow

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
  │  ├─ Type check specifications
  │  └─ ★ Projection check (wf_bimeth_def @ typing.ml:2099)
  │     ├─ projl_simplify cc ≡ left unary method body
  │     ├─ projr_simplify cc ≡ right unary method body
  │     └─ Error "Malformed bicommand (<side>): <method>" on mismatch
  │     (Biif4 also asserts left/right projections agree across the
  │      four branches @ typing.ml:1887)
  │
  └─ Return: (penv, ctbl)
```

### Translation Flow

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

## Alignment Subsystem (`align/`)

Besides the default translate-to-Why3 pipeline above, `main.ml` exposes a
second mode, **`-align`**, that takes a pair of unary methods and produces an
*aligned biprogram* (a `bicommand`) relating their two executions — the input
the bimodule translation later consumes. It has two flavors: a one-shot
**batch** export and a stateful **interactive** HTTP server (`-i`).

A typical interactive invocation:

```
whyrel -align -i -l M0 fact -r M1 fact -port 8083 prog.rl -o align_output.rl
```

### Entry and dispatch

```
main () [tools/main.ml]   (-align mode)
  │
  ├─ Arg.parse sets flags; parse_program → typecheck_program → (penv, ctbl)
  │    -l <mod> <meth>   left method        -i           interactive server
  │    -r <mod> <meth>   right method       -port <n>    server port
  │    -rpre / -rpost    relational spec    -o <file>    output .rl
  │
  └─ Align.run penv ctbl program_files lmod lmeth rmod rmeth
               output_file rpre rpost port ~interactive   [align/align.ml]
       │
       ├─ interactive = false  (batch):
       │    Auto.compose_sequentially  →  Rewrites.auto_align
       │      → Pretty.bicommand_to_string → stdout + output_file
       │
       └─ interactive = true:
            Interactive.run …   (HTTP rewriting server; blocks on Lwt loop)
```

`Align.run` is the single root for both modes; `main.ml` does no alignment
work beyond flag parsing. (The batch/interactive branching and the CLI
parameters formerly threaded directly into `Interactive.run` from `main.ml`
were consolidated into `Align.run`.)

### Modules in `align/`

```
            ┌──────────────────────────────────────────────┐
            │ Align        align.ml — root: dispatch        │
            │              batch vs. interactive            │
            └───────┬───────────────────────────┬──────────┘
                    ↓                           ↓
        ┌───────────────────────┐   ┌──────────────────────────┐
        │ Auto                  │   │ Interactive               │
        │ compose_sequentially  │   │ stateful HTTP API: holds  │
        │ (default bialignment) │   │ current bicommand,/suggest│
        │ enrich_decl,          │   │ /rewrite /undo /export    │
        │ merge_method_specs    │   │ /verify, serves UI        │
        └───────────┬───────────┘   └──────┬─────────────┬──────┘
                    │                       ↓             ↓
                    │              ┌────────────────┐ ┌─────────┐
                    │              │ Http_server    │ │ Ui      │
                    │              │ (Lwt server)   │ │ (/ui    │
                    │              └────────────────┘ │ client) │
                    ↓                                  └─────────┘
        ┌───────────────────────────────────────────┐
        │ Rewrites                                   │
        │ rewrite registry: weave_seq/sync/if/if4/   │
        │ while, add_invariant, change_ag,           │
        │ add_assert_*, un-weave; auto_align;        │
        │ path navigation (apply_at, subterm_at)     │
        └───────────────────────────────────────────┘

  Bicommand pretty-printing: Pretty.bicommand_to_string (typing/pretty.ml),
  shared by Align and Interactive — align/ has no internal pretty-printer and
  nothing in align/ depends back on Align.
```

- **`auto.ml`** — `compose_sequentially` builds the default alignment: leading
  `Vardecl`s are lifted to shared `Bivardecl` scope and the remaining bodies
  become a single `Bisplit (lc, rc)`. `enrich_decl`/`merge_method_specs`/
  `has_effect_spec` resolve a method's decl, folding interface specs (notably
  the effects clause) into the implementation decl.
- **`rewrites.ml`** — the rewrite algebra over `bicommand` trees:
  `type rewrite = bicommand -> bicommand option`, the named registry
  (`weave_*`, `add_invariant`, `remove_invariant`, `change_ag`,
  `add_assert_before/after`, `unweave_seq`, `unsync`, `skip_split`),
  `auto_align` (greedy weave to lockstep), and path-based navigation
  (`apply_at`, `subterm_at`, `child_count`, `scope_at`, `suggest_at`).
- **`interactive.ml`** — the stateful rewriting session behind an HTTP API
  (`Interactive.run`).
- **`http_server.ml`** — a minimal Lwt-based HTTP server (request parsing,
  query decoding, dispatch) used only by `Interactive`.
- **`ui.ml`** — the single-page browser client served at `/ui`.

### Interactive session setup (`Interactive.run`)

When `Align.run` enters interactive mode it hands the same CLI parameters to
`Interactive.run`, which:

1. `Auto.compose_sequentially penv lmod lmeth rmod rmeth` builds the default
   `Bisplit(lc, rc)` (leading `Vardecl`s lifted); stored as `base` and the
   mutable `current`.
2. `find_method_decl` + `Annot.find_interface_decl` + `Auto.enrich_decl`
   → `ldecl`, `rdecl` (signatures with interface specs merged in).
3. `check_rformula` (if `-rpre`/`-rpost` supplied) → `spec_pre`, `spec_post`,
   via `Astutil.parse_rformula_string` then `Typing.tc_rformula` against a
   `restricted_tenv` (method args + `result` only).
4. Closes over `current`, `history`, `future` and defines `handler`.
5. `Http_server.start_dispatch_server handler port`.

### `http_server.ml` — transport loop

`run_accept_loop` binds the socket; per connection it reads raw bytes →
`parse_request` → `(meth, path, query)` → `query_params` (percent-decodes) →
calls the single `handler` → `http_response` → writes bytes. There is no
routing framework: the handler is one large `match` on `(path, get "rule")`.

### `Interactive` per-request dispatch (`handler`)

| Request | Path through handler |
|---|---|
| `GET /` , `GET /help` | the `help` string (endpoint listing) |
| `GET /ui` | `Ui.build_interactive_html` → HTML string |
| `GET /bicom` | `serialize ()` = `Pretty.bicommand_to_string !current` (canonical text) |
| `GET /bicom-tree` | `json_of_alines !current` → JSON `[{lineno, path, text}]` (the form the UI renders) |
| `GET /spec` | `show_spec ()` → relational pre/postcondition (read-only) |
| `GET /history` | `history_json ()` → undo/redo availability + stack depths |
| `GET /rules` | names in `Rewrites.all_rewrites` (rewrite registry only) |
| `GET /suggest[?path=P]` | `suggestions_at` / `suggestions_all` → `Rewrites.suggest_at` + per-loop `add_invariant` / `remove_invariant` / `change_ag` suggestions → `json_of_suggestions` |
| `GET /invariants?path=P` | `Rewrites.subterm_at` + `coupling_candidates` → JSON (carried invariants + `v =:= v` candidates) |
| `POST /rewrite?rule=R&path=P` | `resolve` looks up `R` in `Rewrites.all_rewrites` → `apply_rewrite` → `Rewrites.apply_at p r !current`; on success: `snapshot` (push to `history`, clear `future`), `current := cc'` |
| `POST /rewrite?rule=weave_while&guard_left=L&guard_right=R` | `parse_custom_guard` (parses + type-checks L, R in loop-local `bi_tenv` from `loop_tenv`/`scope_at`) → `Rewrites.weave_while_guard ag`; no guards ⇒ registry `weave_while` (default `<false \| false>`) |
| `POST /rewrite?rule=change_ag&guard_left=L&guard_right=R&path=P` | `parse_custom_guard` → `Rewrites.change_ag ag` (replace a woven loop's guard pair) |
| `POST /rewrite?rule=add_invariant&formula=F` | `add_mcp_invariant`: `parse_rformula_string` + `tc_rformula` in loop scope → `Rewrites.apply_at p (Rewrites.add_invariant trf)` |
| `POST /rewrite?rule=remove_invariant&formula=F` | parse + type-check `F`, then `Rewrites.remove_invariant trf` |
| `POST /undo` / `POST /redo` | `do_undo` / `do_redo`: swap between `history`, `current`, `future` stacks. **Not** routed through `/rewrite`. |
| `POST /auto` | `Rewrites.auto_align !current`; clears both stacks |
| `POST /reset` | `current := base`; clears both stacks |
| `POST /export` | `bimodule_skeleton` assembles `.rl` text from `serialize()`, `ldecl`/`rdecl`, `spec_pre`/`spec_post`; writes to `output_file` |
| `POST /verify[?t=N&theory=T]` | translate program + exported skeleton, then discharge the bimodule's VCs with the prover portfolio (`tools/whyrel_prove.py`) asynchronously (`setsid` process group); returns `202` |
| `GET /verify/status` | poll the running pipeline → `running` / `idle` / cached driver JSON or error text |
| `POST /verify/abort` | kill the verification process group |

### `rewrites.ml` — core rewriting (called from the handler paths above)

- `suggest_at`: filters `all_rewrites` by `apply_at` applicability.
- `apply_at`: navigates the tree by path using `get_child`/`with_child`,
  applies the rewrite at the focus.
- `weave_while` / `weave_while_guard`: match `Bisplit(While, While)` →
  `Biwhile` via `biwhile_spec_of` (lifts unary invariants and frames).
- `auto_align`: recursively applies forward weaving rules depth-first until
  fixpoint (also the batch path's lockstep weave).

### How the browser UI talks to the handler

The UI is a **single-page app**: the HTML is served *once* (`GET /ui` →
`Ui.build_interactive_html`, a self-contained page with markup, CSS, and inlined
JS). After that the browser never reloads; all interaction exchanges *data*
(JSON/text) via `fetch()`.

```
        Browser (stateless view)              Server (OCaml, holds the truth)
   +------------------------------+      +---------------------------------+
   |  DOM built from JSON          |      |  current : bicommand ref        |
   |  fetch() GET  ----- reads --->| ---> |  history / future : stacks      |
   |  fetch() POST ---- mutates -->| ---> |  handler closure over them      |
   |  re-GET to redraw  <----------|      |                                 |
   +------------------------------+      +---------------------------------+
```

- **Bootstrap**: on load an IIFE fires `refreshBicom()` (`GET /bicom-tree`) and
  `suggestAtPath()` (`GET /suggest`); the browser builds the DOM (`renderCode` /
  `renderSuggestions`). The server does no HTML rendering past the initial load.
- **Mutation**: clicking "Apply Rewrite" issues
  `fetch('/rewrite?rule=R&path=P&...', {method:'POST'})` — **parameters ride in
  the query string, not a body** — and on success re-issues a fresh
  `GET /bicom-tree` to redraw. A POST never returns HTML.
- **Where state lives**: `current` and the undo/redo stacks are plain OCaml
  `ref`s captured in the handler closure set up by `Interactive.run`. The
  browser holds no authoritative state, so two tabs on the same port share and
  edit one session.

### Design decisions (endpoint surface)

The endpoint surface was deliberately trimmed; rationale for anyone tempted to
re-add things:

- **Undo/redo are kept distinct from rewrites.** `/rewrite` only applies entries
  from `Rewrites.all_rewrites` (pure tree transformations); undo/redo are
  *session-history* operations over `history`/`future` at their own `POST /undo`
  / `POST /redo`. The old `/rewrite?rule=undo|redo` aliases were removed, so
  `rule=undo` returns `unknown rule` and `/rules` lists only real rewrites.
- **`change_ag` operates on the guard *pair*** (`guard_left`/`guard_right` via
  the same `parse_custom_guard` as `weave_while`), not a single `formula`,
  because a loop's alignment guard is a left/right pair. The UI prefills both.
- **`add_invariant` takes a `formula`, not a candidate index.** `formula=<rformula>`
  can express any invariant, including a typed-out coupling candidate `v =:= v`;
  `/invariants` still *lists* candidates for discovery.
- **Removed `/bicom.html` + `Ui.build_html`** (a static HTML view, superseded by
  the client-rendered `/ui`); its `html_escape` helper went with it.
- **`/bicom` (text) is kept despite overlapping `/bicom-tree`.** `/bicom` is the
  *canonical* `Pretty.pp_bicommand` output, whereas `/bicom-tree`'s `alines`
  rebuilds `While`/`Var`/`if` headers itself for the per-line path mapping — so
  the two are content-equivalent but not byte-identical. `/bicom` is retained as
  the exact pretty-printer text for scripts.
- **`Rewrites.guard_candidates` was deleted** as dead code; the live candidate
  generator is `coupling_candidates` (used by `/invariants`).

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
    │  ├─ All referenced identifiers exist
    │  └─ Bicommand projection check (wf_bimeth_def)
    │     ├─ For each bimodule method with a bicommand body:
    │     │  ├─ Compute left projection:  projl_simplify cc  (annot.ml)
    │     │  │  └─ Extracts the left unary command from cc, then simplifies
    │     │  │     (Bisync → both sides, Bisplit → left branch,
    │     │  │      Bihavoc_right → Skip, alignment constructs → Skip)
    │     │  ├─ Compute right projection: projr_simplify cc  (annot.ml)
    │     │  │  └─ Mirror of projl: extracts the right unary command
    │     │  ├─ Check left projection ≡ left module's unary method body
    │     │  └─ Check right projection ≡ right module's unary method body
    │     └─ Error: "Malformed bicommand (<side>): <method>" if mismatch
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