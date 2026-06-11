# The Why3 hybrid (C′): batch discharge, and the failed-VC diagnosis loop

Status: exploration companion to `docs/boogie_backend_plan.md` (§"Option C′").
The hybrid = keep Why3 as VC engine, re-encode the translation to be
SMT-first (totalized maps + field-splitting, explicit wf predicates instead
of type invariants, triggers, smaller cloned theories), and discharge in
batch (`why3 prove` / strategies) instead of the IDE.

The question this document answers: **when not all VCs discharge, how do you
know what to fix, and is it always fixable in source code?**

## 1. What a failed batch run gives you

After `split_vc`, each leaf goal carries:

- a **status** per prover: `Valid`, `Timeout`, `Unknown` (with or without a
  model), rarely `Invalid`;
- an **explanation chain**: Why3's built-in `[@expl:]` kinds (postcondition,
  precondition, loop invariant init / preservation, assertion, variant
  decrease, type invariant) *plus* WhyRel's own `explain_term/expr`
  annotations ("guard agreement", "locals type invariant", pretty-printed
  atomic commands, frame-condition tags);
- a **source location** — currently `Loc.dummy_position` almost everywhere in
  translate.ml, so this channel is dead today. Threading real `.rl` positions
  through translation is moderate effort and the single highest-value
  diagnosability fix, for *either* backend.

So the raw signal is: *which obligation kind, of which method, under which
explanation path, failed in which way (timeout vs unknown vs countermodel)*.

## 2. Triage: three root causes, three observable signatures

Every failed VC has exactly one of these root causes, and they are
distinguishable (imperfectly but usefully) by observable behavior:

**(A) The program or spec is actually wrong** — loop invariant too weak or
too strong, missing precondition, wrong coupling relation, genuine bug.
*Signature*: a prover returns a model, often quickly; the countermodel
survives `--check-ce` validation (Why3 re-executes the program on the model
— "giant-step" checking — and reports whether the CE is genuine or an
artifact of incompleteness). *Fix*: in source, necessarily — no amount of
proof engineering proves a false thing. Loop-invariant weakness is the
overwhelmingly common case: the invariant-preservation goal fails with a
model that satisfies the invariant but not the postcondition path.

**(B) True, provable from the VC's hypotheses, but the solver can't find
the proof** — instantiation search space too large; the dihedral/case-split
failure mode. *Signature*: `Timeout` across the portfolio (z3, cvc5,
alt-ergo), and the goal *does* go through in the IDE after a couple of
splits or a hand instantiation. *Fix*: in source — asserts and lemma calls
(§3) — or in the encoding (triggers, smaller context).

**(C) True, but not provable from the VC's hypotheses** — a needed fact is
missing from the context: an unstated list lemma, a fact requiring
induction, a consequence of a hidden invariant that the encoding doesn't
expose at this point. *Signature*: fast `Unknown`/`Timeout` with no model,
and adding the missing fact as an `assume` makes the goal go through
instantly (the standard probe: bisect by assumption). *Fix*: state the fact
as a source-level `lemma` (the language has them) or a prelude lemma; prove
it once — by SMT if it's first-order, by ITP/induction if not.

The probe toolkit for separating B from C is mechanizable: (i) try the goal
with a 10× time budget (separates "slow" from "never"); (ii) re-run with the
candidate missing fact assumed; (iii) `--check-ce` on any model. A batch
driver can run all three automatically on failures — this is exactly the
kind of loop the existing why3 MCP server (`why3_get_first_unproved`,
`why3_apply_tactic`) already half-implements.

## 3. Is it always fixable in code? The completeness picture

There is a clean theoretical answer with two practical residues.

**The positive result (annotation completeness).** Floyd-style: any Hoare
(and by extension RRL) proof can be reflected into the program as
annotations. If you assert the full intermediate condition at every program
point (and supply the loop invariants the proof uses), each VC collapses to
a single implication between adjacent annotations across one atomic step —
no search, minimal instantiation depth. Source `Assert`/`Biassert` is the
cut rule made syntax; the tiling experience (tactic script transcribed as
source asserts, after which plain SMT discharges everything) is this theorem
operating in practice. So: *if WhyRel's logic proves the judgment, there is
an annotation of the source that makes every VC a local implication.*

**Residue 1: facts vs. cuts.** An assert only *splits* the proof; it adds no
facts. When the local implication itself needs a fact the context lacks —
list induction, a nontrivial region-algebra consequence, a property of an
abstraction function — you need a *lemma*, not an assert. In source: declare
the `lemma` (translates to a Why3 goal + available hypothesis) and, where
needed, "call" it by asserting its instantiation. The lemma itself must then
be proven, which leads to:

**The hybrid's unique escape hatch.** If a lemma needs induction or
interactive work, you prove it *once* in the IDE (or via the `induction`
transformation in a strategy), and the proof persists in the **session**.
`why3 replay` re-checks sessions in CI deterministically. Crucially, Why3's
session pairing (goal shapes) re-matches goals across source edits, so
stable goals keep their proofs and only changed goals are re-attempted —
batch verification is *incremental*. This is the structural advantage over
Boogie: in Boogie, category-C facts that SMT can't prove become trusted
axioms (soundness debt); in the hybrid they become proven-once session
artifacts. **You never need everything to be fixable in code, because the
ITP fallback is per-goal and quarantined** — the methodology is: code fixes
preferred (robust, self-documenting, survive re-translation), ITP confined
to lemma-land where proofs are stable by construction.

**Residue 2: failures caused by the encoding itself — these are NOT fixable
in source.** If a single field load expands to an fmap `find`-over-`add`
chain whose axioms the solver must unfold per access, an assert doesn't
remove that cost — it duplicates it on both sides of the cut. If the VC
context carries every lemma of a monolithic prelude, irrelevant quantifiers
poison every goal regardless of annotation. If countermodels are opaque
because the heap is an abstract fmap term, triage signal (A) degrades and
you misclassify failures. These are exactly what the C′ re-encoding targets:

- totalized maps + field-splitting → loads/stores become array select/store,
  decided structurally; assert-decomposed goals actually become cheap;
- explicit triggers on prelude quantifiers → category-B failures become rare
  and deterministic instead of seed-dependent;
- smaller cloned theories + per-module `use` granularity → context control
  (weaker than Boogie's `/prune`, but real);
- concrete map models → readable countermodels → reliable A-vs-BC triage.

So the honest answer to "is it all possible to fix in code?": **fixable in
code: A (always), B (in principle always, by annotation completeness —
*provided* the encoding makes the decomposed pieces cheap), C (by source
lemmas, with ITP-once for inductive ones). Not fixable in code: encoding
pathologies — and on the current encoding, category B often masquerades as
unfixable precisely because of them.** The re-encoding is not optional
polish; it is what makes the "fix it in source" loop converge.

## 4. The operational loop (ops manual sketch)

```
whyrel-prove file.rl
  → translate → why3 prove -a split_vc, portfolio {z3, cvc5, alt-ergo}, t=5s
  → for each unproved leaf:
      report (method, expl-path, status per prover)
      auto-probe: 10× budget | --check-ce | strategy: split + compute + retry
  → classify A / B / C with the probe results
```

Fix menu, in order (each step strictly more invasive):

1. **A**: fix code/spec; usually strengthen the loop invariant the CE points
   at.
2. **B**: add an assert chain at the failing point — transcribe what the
   tactic proof would do (the tiling pattern); for relational goals, the
   skeletons already catalogued (frame/agreement, boundary identity
   collapse) are assert templates.
3. **C**: state a source `lemma`; if SMT proves it, done.
4. **C-inductive**: prove the lemma once interactively / with the induction
   transformation; session-persist; `why3 replay` in CI.
5. **Encoding**: only if the same shape recurs across examples — add a
   triggered prelude lemma or adjust the encoding; this is a translator
   change, ledger-documented.

Monotonicity matters: steps 1–4 don't invalidate previously proved goals
(sessions re-pair by shape), so the loop converges goal-by-goal rather than
globally re-rolling the dice.

## 5. What the spike should measure

Two weeks, on existing examples (stack family, sumpub, tiling, one RHLE):

1. **Baseline**: batch-run the *current* encoding (`why3 prove -a split_vc`,
   portfolio): % goals auto, wall time, failure signatures. (Sessions in the
   repo tell us the interactive effort that batch must replace.)
2. **Re-encode the prelude only** (fmap → map + domain set; triggers on
   every quantifier) and rerun — cheap proxy for the full C′ before touching
   translate.ml.
3. **Apply the fix menu** to residual failures; log per failure: category
   (A/B/C/encoding), time-to-diagnosis, fix size in source lines.
4. **Exit criteria**: if ≥~90% of goals discharge with fixes confined to
   steps 1–4 and diagnosis time is dominated by genuine spec work (A), the
   hybrid is viable and cheaper than the Boogie backend; if failures
   concentrate in "encoding" with prelude-only changes insufficient, that is
   evidence the field-splitting rewrite is mandatory — at which point the
   marginal cost of emitting Boogie instead of re-emitting WhyML shrinks,
   and the Boogie plan's M0/M1 reuse this spike's encoding work directly.

Shared-work observation: the re-encoding design (totalization,
field-splitting, trigger discipline, lemma granularity) is identical in C′
and the Boogie backend; the spike de-risks both. The genuinely
backend-specific assets are: sessions/induction/replay (Why3 only) vs.
`/prune`, `hide/reveal`, per-assert splitting, `/printModel` (Boogie only).

## 6. Gaps to close in either case

- **Thread real source locations** through translate (replace
  `Loc.dummy_position` with `.rl` positions) — turns "which obligation"
  into "which line"; prerequisite for a usable batch loop.
- **Richer `[@expl:]` coverage**: every generated obligation (frame
  conditions, agreement conjuncts, okState conjuncts) should carry a
  distinct explanation; mostly done, audit the gaps.
- **Counterexample plumbing**: `[@model_trace:]` attributes on state
  components so CE output names `.rl`-level variables/fields rather than
  encoding internals; only worthwhile after totalization.
- **Driver**: promote the why3 MCP server's goal-iteration logic into a
  `whyrel prove` batch command with the §4 probe/classify loop.
