# Align mode: `-i` CLI invocation walkthrough

This document traces the call chain for a typical interactive alignment invocation:

```
whyrel -align -i -l M0 fact -r M1 fact -port 8083 prog.rl -o align_output.rl
```

---

## `main.ml` — startup

1. `Arg.parse` sets flags; `parse_program` parses `prog.rl`
2. `typecheck_program` → `(penv, ctbl)`
3. Both `align_mode` and `align_interactive_mode` are set → calls `Interactive.run`

---

## `interactive.ml` — session setup (`Interactive.run`)

4. `Auto.compose_sequentially penv "M0" "fact" "M1" "fact"` → builds the default `Bisplit(lc, rc)` and lifts leading `Vardecl`s; stored as `base` and `current`
5. `find_method_decl` + `find_interface_decl` + `enrich_decl` → `ldecl`, `rdecl` (method signatures with merged interface specs)
6. `check_rformula` (if `-rpre`/`-rpost` supplied) → `spec_pre`, `spec_post` via `Astutil.parse_rformula_string` then `Typing.tc_rformula` against a `restricted_tenv`
7. Closes over `current`, `history`, `future` and defines the `handler` function
8. `Http_server.start_dispatch_server handler port`

---

## `http_server.ml` — transport loop

9. Binds socket, calls `run_accept_loop` with `handle_dispatch handler`
10. Per connection: reads raw bytes → `parse_request` → `(meth, path, query)` → `query_params` (percent-decodes) → calls `handler` → `http_response` → writes bytes

---

## `interactive.ml` — per-request dispatch (`handler`)

| Request | Path through handler |
|---|---|
| `GET /ui` | `Ui.build_interactive_html` → HTML string |
| `GET /bicom` | `Align.bicommand_to_string !current` |
| `GET /bicom.html` | `Ui.build_html` wrapping `serialize ()` |
| `GET /suggest[?path=P]` | `suggestions_at` / `suggestions_all` → `Rewrites.suggest_at` + `coupling_candidates` → `json_of_suggestions` |
| `GET /invariants?path=P` | `Rewrites.subterm_at` + `coupling_candidates` → JSON |
| `POST /rewrite?rule=R&path=P` | `resolve` looks up rule in `Rewrites.all_rewrites` → `apply_rewrite` → `Rewrites.apply_at p r !current`; on success: `snapshot` (push to `history`), `current := cc'` |
| `POST /rewrite?rule=weave_while&guard_left=L&guard_right=R` | `parse_custom_guard` (parses + type-checks L, R in loop-local `bi_tenv` from `loop_tenv`/`scope_at`) → `Rewrites.weave_while_guard ag` → `apply_rewrite` |
| `POST /rewrite?rule=add_invariant&formula=F` | `add_mcp_invariant`: `parse_rformula_string` + `tc_rformula` in loop scope → `Rewrites.apply_at p (Rewrites.add_invariant trf)` |
| `POST /undo` / `POST /redo` | `do_undo` / `do_redo`: swap between `history`, `current`, `future` stacks |
| `POST /auto` | `Rewrites.auto_align !current`; clears both stacks |
| `POST /reset` | `current := base`; clears both stacks |
| `POST /export` | `bimodule_skeleton` assembles `.rl` text from `serialize()`, `ldecl`/`rdecl`, `spec_pre`/`spec_post`; writes to `output_file` |

---

## `rewrites.ml` — core rewriting (called from handler paths above)

- `suggest_at`: filters `all_rewrites` by `apply_at` applicability
- `apply_at`: navigates the tree by path using `get_child`/`with_child`, applies the rewrite at the focus
- `weave_while` / `weave_while_guard`: match `Bisplit(While, While)` → `Biwhile` via `biwhile_spec_of` (lifts unary invariants and frames)
- `auto_align`: recursively applies forward weaving rules depth-first until fixpoint

---

## Module dependency summary

```
main.ml
  └─ Interactive.run
       ├─ Auto.compose_sequentially      (builds initial Bisplit)
       ├─ Rewrites.*                     (suggest, apply, auto_align)
       ├─ Align.bicommand_to_string      (serialise for /bicom)
       ├─ Ui.build_interactive_html      (serves /ui)
       └─ Http_server.start_dispatch_server
            └─ handle_dispatch           (per-connection transport)
```
