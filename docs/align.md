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
| `GET /` , `GET /help` | the `help` string (endpoint listing) |
| `GET /ui` | `Ui.build_interactive_html` → HTML string |
| `GET /bicom` | `serialize ()` = `Align.bicommand_to_string !current` (canonical text) |
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

---

## How the browser UI talks to the handler

The UI is a **single-page app**: the HTML is served *once*, and after that the
browser never reloads. All subsequent interaction exchanges *data* (JSON/text)
with the server via `fetch()` — the server never sends HTML again.

### 1. Initial load (one time)

```
Browser:  GET /ui
Handler:  Ui.build_interactive_html  ->  one HTML string (markup + CSS + <script> JS)
Browser:  parses HTML, runs the embedded JS
```

`build_interactive_html` returns a self-contained page: markup, styling, and all
the client logic (`renderCode`, `renderSuggestions`, `applyRewrite`, ...) inlined
in a single string.

### 2. Bootstrap fetches (JS runs on load)

An IIFE at the bottom of the embedded JS fires immediately:

```js
await refreshBicom();   // GET /bicom-tree  -> JSON [{lineno, path, text}]
await suggestAtPath();  // GET /suggest     -> JSON [suggestions]
```

The server sends *data*; the **browser** builds the DOM (`renderCode` /
`renderSuggestions`). The server does no HTML rendering past step 1.

### 3. User input -> POST -> re-fetch

Clicking "Apply Rewrite":

```
Browser JS (applyRewrite):  builds  /rewrite?rule=R&path=P&guard_left=...&guard_right=...
            fetch(url, {method:'POST'})        <- params ride in the query string, no body
Handler:    parses query -> looks up rule -> mutates server state -> returns serialized result
Browser JS: on success, calls refreshBicom() -> GET /bicom-tree -> re-renders
```

Two transport details:
- **Parameters are in the URL query string, not a request body.** `http_server.ml`
  percent-decodes them into `query_params`; the handler reads them via
  `get "rule"`, `get "path"`, etc.
- **A POST does not return new HTML** — it returns a small text/JSON result, and
  the JS then issues a *fresh GET* (`/bicom-tree`) to redraw.

### Where state lives

```
        Browser (stateless view)              Server (OCaml, holds the truth)
   +------------------------------+      +---------------------------------+
   |  DOM built from JSON          |      |  current : bicommand ref        |
   |  fetch() GET  ----- reads --->| ---> |  history / future : stacks      |
   |  fetch() POST ---- mutates -->| ---> |  handler closure over them      |
   |  re-GET to redraw  <----------|      |                                 |
   +------------------------------+      +---------------------------------+
```

The bicommand under edit (`current`) and the undo/redo stacks are plain OCaml
`ref`s captured in the handler closure set up by `Interactive.run`. The browser
holds *no* authoritative state — every redraw is a fresh read from the server, so
two tabs on the same port share and edit one session.

### Transport mechanics

`http_server.ml` runs an accept loop; per connection it reads the raw request ->
`parse_request` yields `(method, path, query)` -> calls the single `handler` ->
writes back an `http_response`. There is no routing framework: the handler is one
large `match` on `(method, path, get "rule")`.

---

## Design decisions (endpoint surface)

The endpoint surface was deliberately trimmed; the rationale, for anyone tempted
to re-add things:

- **Undo/redo are kept distinct from rewrites.** `/rewrite` only applies entries
  from the `Rewrites.all_rewrites` registry (pure tree transformations). Undo/redo
  are *session-history* operations over the `history`/`future` stacks and live at
  their own `POST /undo` and `POST /redo` endpoints. The earlier
  `/rewrite?rule=undo|redo` aliases (and the `mcp_undo_rule`/`mcp_redo_rule`
  plumbing) were removed, so `rule=undo` now returns `unknown rule`, and `/rules`
  lists only real rewrites.

- **`change_ag` operates on the guard *pair*.** It reads `guard_left`/`guard_right`
  (via the same `parse_custom_guard` as `weave_while`), not a single `formula`,
  because a loop's alignment guard is a left/right pair. The UI prefills both
  fields from the loop's current guards.

- **`add_invariant` takes a `formula`, not a candidate index.** The old
  `add_invariant&inv=K` path (apply the K-th coupling candidate from
  `/invariants`) was removed as redundant: `formula=<rformula>` can express any
  invariant, including a coupling candidate `v =:= v` typed out. `/invariants`
  still *lists* candidates for discovery; you add one by copying its text into a
  `formula=` request.

- **Removed `/bicom.html` + `Ui.build_html`.** It was a static HTML view of the
  alignment, fully superseded by the interactive `/ui` (which renders the same
  data client-side from `/bicom-tree`). Its only helper, `html_escape`, went with
  it.

- **`/bicom` (text) is kept despite overlapping `/bicom-tree`.** Joining the
  `text` fields of `/bicom-tree` reconstructs the alignment content, so the two
  are content-equivalent. But `/bicom` is the *canonical* `Pretty.pp_bicommand`
  output, whereas `/bicom-tree`'s `alines` rebuilds `While`/`Var`/`if` headers
  itself for the per-line path mapping — so they are not byte-identical. `/bicom`
  is retained as the source of the exact pretty-printer text for scripts/MCP.

- **`Rewrites.guard_candidates` was deleted** as dead code (never referenced); the
  live candidate generator is `coupling_candidates` (used by `/invariants`).

### Suggestions: `needs_input` and defaults

`/suggest` entries carry a `needs_input` flag so a client knows whether a click
can apply immediately or must collect input first:

- `needs_input = false` (e.g. `weave_seq`, `unsync`, `skip_split`,
  `remove_invariant` — which prefills the exact carried formula): apply on click.
- `needs_input = true` (`weave_while`, `add_invariant`, `change_ag`): fill the
  fields and wait. `weave_while` additionally has a **default** — applying it with
  empty guard fields uses `<false | false>` (the registry rule), so input is
  optional there; `add_invariant`/`change_ag` have no default.

`change_ag` suggestions prefill `guard_left`/`guard_right`; `add_invariant`
prefills nothing; `remove_invariant` prefills `formula`.

