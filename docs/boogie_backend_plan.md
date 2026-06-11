# A Boogie backend for WhyRel: design and implementation plan

Status: draft for discussion. Companion to `docs/architecture.md`.

## 1. Goal and verification-theoretic framing

WhyRel implements *relational region logic* (RRL): unary region logic with
dynamic frames and dynamic boundaries [Banerjee–Naumann–Rosenberg, ECOOP'08;
Banerjee–Naumann, JACM'13 Part II], extended to relational judgments over
*biprograms* with refperm-based agreement and second-order framing
[Banerjee–Nagasamudram–Naumann–Nikouei, TOPLAS'22; the PLS'22 lecture notes;
WhyRel tool paper, TACAS'23]. Today the tool realizes the logic by translating
annotated programs into WhyML: state is a record of finite maps
(`fmap.MapApp`), programs are WhyML let-functions, and Why3's WP calculus
produces VCs that are discharged *interactively* (IDE / why3 MCP), with
transformations and `[@rewrite]` hints doing real work.

The goal is a second backend at the same pipeline position as
`src/translate/`, targeting the Boogie intermediate verification language:
parse → typecheck → pretrans stay untouched; a new stage emits `.bpl`; the
Boogie verifier performs VC generation and discharges via Z3 (CVC5
experimental). This is exactly the separation of concerns Boogie was designed
for ["This is Boogie 2", Leino 2008]: Boogie imposes *no memory model*, so
WhyRel's region-logic state (heaps, regions, refperms) can be axiomatized
directly, while Boogie supplies the parts that are hard to build and easy to
get wrong:

- **Passification / dynamic single assignment** [Flanagan–Saxe, POPL'01] and
  the linear-size weakest-precondition construction for unstructured programs
  [Barnett–Leino, PASTE'05]. A naïve WP is exponential in sequential branching;
  reimplementing this correctly is the main hidden cost of a direct SMT-LIB
  backend.
- Loop handling by invariant cutting (havoc assigned variables, assert/assume
  invariant), procedure-modular reasoning via contracts and `modifies` frames.
- Per-assertion error attribution, counterexample models (`/printModel`),
  VC splitting (`{:split_here}`, `/vcsSplitOnEveryAssert`), time limits,
  random-seed stability testing.
- Quantifier instantiation control: explicit `{:trigger}` annotations, and in
  current Boogie (the readthedocs reference is self-admittedly stale; the
  GitHub repo is the source of truth) `datatype` declarations,
  monomorphization, function `uses { … }` axiom blocks with `/prune` (axioms
  enter the VC only when their function symbol is reachable), and
  `hide`/`reveal` for opaque function definitions.

### 1.1 Soundness story (the adequacy chain)

The argument that "Boogie says verified" implies the RRL judgment holds is a
chain of four links, each with a clear owner:

1. **Biprogram adequacy** (already owned by WhyRel's type checker): the
   projection check (`wf_bimeth_def`, typing.ml) ensures each bicommand's
   left/right projections equal the unary method bodies, so a verdict about
   the biprogram is a verdict about the pair of programs. This is the
   alignment-completeness obligation of product-program constructions
   [Barthe–Crespo–Kunz, FM'11]; WhyRel discharges it syntactically.
2. **Translation correctness** (this project's obligation): the generated
   Boogie code is a small-step-preserving interpretation of WhyRel's
   operational semantics in the Boogie heap model (§2). Each construct's
   translation mirrors the corresponding RRL proof rule; the table in §3 makes
   this per-construct correspondence explicit and reviewable.
3. **Boogie's VC generation is sound** (owned by Boogie; widely deployed via
   Dafny, Viper, Corral).
4. **Prelude validity** (this project's obligation): the background axioms
   (`prelude.bpl`) must hold in the intended model (finite-support maps over a
   countable set of references; finite sets; partial bijections). Mitigation:
   every axiom is the statement of a lemma *already proven* in
   `stdlib/prelude.mlw` under Why3, modulo encoding. The Why3 development
   becomes the certificate for the Boogie prelude. A `TRUSTED` ledger in
   `prelude.bpl` records each axiom's provenance (§4.4).

## 2. The Boogie encoding of WhyRel state

### 2.1 References, classes, allocation

```boogie
type Ref;
const null: Ref;

type ClassName;
const unique ClassName.Cell: ClassName;   // one unique const per class
const unique ClassName.Node: ClassName;   // distinctness for free

var allocd: [Ref]bool;      // domain of the alloc table
var alloct: [Ref]ClassName; // totalized: meaningful only where allocd
```

Why3's `fmap.MapApp` (partial map with `mem`/`find`/`add` axioms) is replaced
by the *totalization* pattern: a total SMT array plus an explicit domain set.
This removes a layer of axiomatized indirection — `find (add k v m) k = v`
becomes the SMT array theory's built-in select-of-store, decided without
quantifier instantiation. This is one of the two main SMT-friendliness wins
over the current encoding.

**Field-splitting (Burstall–Bornat).** Each declared field `f` of class `C`
becomes its own global map:

```boogie
var Node.nxt: [Ref]Ref;
var Node.val: [Ref]int;
```

The "update of `f` does not affect `g`" frame property — currently a fact
about record-of-fmaps updates that the solver must derive — becomes
*definitional*: distinct global variables. This is the standard Spec#/Dafny
move [Bornat, MPC'00] and the second main win.

**Allocation.** `new C` translates to:

```boogie
havoc tmp;
assume tmp != null && !allocd[tmp];
allocd[tmp] := true;  alloct[tmp] := ClassName.C;
Node.nxt[tmp] := null;  Node.val[tmp] := 0;   // field defaults
```

The freshness `assume` is consistent only if `Ref` is infinite and `allocd`
has finite support; this is the same trusted assumption the current backend
makes (the abstract Why3 `val` allocator with
`ensures { st_previously_unalloc'd … }`), now stated explicitly. Recorded in
the trusted ledger.

**The ok-state invariant.** `Build_State.mk_ok_state` (null not allocated,
reference-typed fields point to allocated-or-null objects of the right class,
region-typed globals contain only allocated refs) becomes a defined predicate
`okState(allocd, alloct, Node.nxt, …)`, supplied as (checked) `requires`/
`ensures` on every procedure and as an auto-injected loop invariant — exactly
where translate.ml injects `locals/globals type invariant` and
`alloc_does_not_shrink` today. Boogie has no type invariants, so what Why3
enforces by typing is threaded explicitly; this is pervasive but mechanical,
and `free requires` can be used where the obligation is established by the
caller side to avoid re-proving.

### 2.2 State as globals; two-vocabulary doubling for relational

The current backend passes state records explicitly. In Boogie the idiomatic
choice is *globals + `modifies` + `old()`*: pre-state references in
postconditions come for free, and frame conditions quantify over the
distinguished pre-state. For relational judgments, the two-vocabulary
signature of RRL is realized by **doubling**: every field map and global `g`
yields `l_g` and `r_g`. A bimethod becomes a single procedure over the doubled
vocabulary — the product construction of self-composition
[Barthe–D'Argenio–Rezk, CSFW'04] in its aligned form [Barthe–Crespo–Kunz,
FM'11; Eilers–Müller–Hitz, ESOP'18], except that WhyRel's bicommands *are*
the aligned product already, so no alignment inference is needed at this
level.

### 2.3 Regions

```boogie
type Rgn = [Ref]bool;
function Rgn#union(Rgn, Rgn): Rgn;
axiom (forall a, b: Rgn, r: Ref :: {Rgn#union(a,b)[r]} Rgn#union(a,b)[r] <==> a[r] || b[r]);
// likewise inter, diff, subset, singleton, emptyRgn
```

Sets-as-Boolean-maps; SMT arrays are extensional, so region equality is map
equality (after monomorphization, the default in current Boogie). Membership
axioms carry explicit triggers. Boogie `lambda` expressions are an
alternative lowering for the same operators; we prefer named functions +
axioms because triggers are then under our control. **No cardinality**: the
source language doesn't use it (verified — `Rgn.cardinal` appears only in the
prelude's `singleton` ensures), and `M.size` in `partialBijection` is
redundant given the mutual-inverse conditions, so the worst SMT feature
(set cardinality) is avoided entirely.

**Image expressions** ``G`f`` get per-(class, field) functions mirroring
`mk_image_axiom`:

```boogie
function img_Node_nxt(g: Rgn, nxt: [Ref]Ref, alloct: [Ref]ClassName, allocd: [Ref]bool): Rgn;
axiom (forall g: Rgn, nxt: [Ref]Ref, alloct: [Ref]ClassName, allocd: [Ref]bool, p: Ref ::
  {img_Node_nxt(g, nxt, alloct, allocd)[nxt[p]], g[p]}    // membership intro
  g[p] && allocd[p] && alloct[p] == ClassName.Node ==> img_Node_nxt(g, nxt, alloct, allocd)[nxt[p]]);
axiom (forall …, q: Ref :: {img_Node_nxt(…)[q]}            // membership elim
  img_Node_nxt(…)[q] ==> (exists p: Ref :: g[p] && allocd[p] && alloct[p] == ClassName.Node && nxt[p] == q));
```

The elimination direction carries an existential under a guarded trigger —
the same shape Dafny uses for set comprehension axioms; the intro direction
is the one used in framing proofs and is existential-free. `rgnSubK`
(filtering a region by `alloct` value, used for `r``ty` expressions) gets the
same treatment, with the `rgnSubK_*` lemmas from prelude.mlw becoming either
triggered axioms or lemma procedures (§4.2).

### 2.4 Refperms and agreement

```boogie
var pi.lor: [Ref]Ref;   var pi.ldom: [Ref]bool;
var pi.rol: [Ref]Ref;   var pi.rdom: [Ref]bool;

function wf_pi(lor: [Ref]Ref, ldom: [Ref]bool, rol: [Ref]Ref, rdom: [Ref]bool): bool
{ // partialBijection minus the (redundant) size clause, plus null ∉ dom/rng
  (forall x: Ref :: {ldom[x]} ldom[x] ==> rdom[lor[x]] && rol[lor[x]] == x) &&
  (forall y: Ref :: {rdom[y]} rdom[y] ==> ldom[rol[y]] && lor[rol[y]] == y) &&
  !ldom[null] && !rdom[null]
}
```

`idRef`, `idRgn`, `extends`, `identity` translate directly as defined
functions (bodies, not axioms — so `/prune` and `hide`/`reveal` apply).
Why3's *type invariant* on `PreRefperm.t` becomes `wf_pi` threaded as
requires/ensures of every biprocedure; it is *checked* only where the refperm
is mutated, i.e., in the one place that mutates it:

```boogie
procedure UpdateRefperm(x: Ref, y: Ref);   // Biupdate(x|y)
  requires x != null && y != null && !pi.ldom[x] && !pi.rdom[y];
  modifies pi.lor, pi.ldom, pi.rol, pi.rdom;
  ensures pi.lor == old(pi.lor)[x := y] && pi.ldom == old(pi.ldom)[x := true];
  ensures pi.rol == old(pi.rol)[y := x] && pi.rdom == old(pi.rdom)[y := true];
```

with a one-line *implementation* that Boogie verifies against the contract —
the contract is then certified, not trusted. The prelude lemmas
(`extends_idRgn`, `idRgn_union_singleton`, …) follow the lemma-procedure
pattern (§4.2): stated as contracts, proven once by their bodies, invoked by
`call` exactly where an ITP proof would apply them.

**Agreement formulas.** Per-field agreement predicates mirror
`Build_State.mk_agreement_predicate`:

```boogie
function agree_Node_val(lor: [Ref]Ref, ldom: [Ref]bool,
                        l_alloct: [Ref]ClassName, l_allocd: [Ref]bool, l_val: [Ref]int,
                        r_val: [Ref]int, g: Rgn): bool
{ (forall p: Ref :: {g[p]}
    g[p] && l_allocd[p] && l_alloct[p] == ClassName.Node && ldom[p]
    ==> l_val[p] == r_val[lor[p]]) }
```

(for reference-valued fields, the conclusion is `idRef`), plus
`agree_allfields` as their conjunction. Full agreement `Agree(G`f)` is the
left-to-right predicate plus its mirror through the inverse — exactly the
`Ragree` decomposition at translate.ml:3046. These quantifiers, instantiated
per region member through the refperm, are the heaviest part of relational
VCs; they are also precisely where field-splitting + totalization pays off,
since each instantiation is now a single array select rather than an fmap
`find` chain.

**Existential refperms.** RRL postconditions are implicitly
"∃π' ⊇ π. …"; both the current backend and this one realize the existential
*constructively*: π is ghost state, `Biupdate` extends it monotonically, and
`extends` lemmas transport agreements. No `exists` over maps ever reaches the
VC — source-level Skolemization. The same applies to ∀∃ specs (§3,
`Bihavoc_right`).

### 2.5 Effects and framing

Write effects `wr G`f` become generated postconditions, mirroring
`mk_wr_frame_condition`:

```boogie
ensures (forall p: Ref :: {Node.val[p]}
  old(allocd)[p] && !old(g)[p] ==> Node.val[p] == old(Node.val[p]));
```

`modifies` lists every touched field map (coarse, per Boogie's requirement);
the quantified ensures refine it to the region. Allocation monotonicity
(`old(allocd)[p] ==> allocd[p]`, `alloct` preserved on old allocations) is a
`free ensures` on every procedure — free because it holds by construction of
the translation (only `new` writes `allocd`, monotonically), a fact checked
once at the meta level, not per VC. Read effects participate in the
boundary/encap obligations computed by pretrans, unchanged.

Frame lemmas generated by pretrans (`gen_frame_lemma`,
`frm_agreements` at translate.ml:2769 — agreement on a boundary implies
invariant transfer, the `boundary_frames_invariant` pattern) become lemma
procedures whose bodies must verify; during bring-up they may be temporarily
`free ensures` (ledger-tracked) to unblock downstream milestones.

### 2.6 Mathematical types

`datatype List { Nil(), Cons(head: int, tail: List) }` via Boogie datatypes
(SMT datatypes underneath: constructors/selectors/testers decided natively).
The cost of leaving Why3: ListRich's *inductive* lemmas (used by the stack
family and Kruskal) cannot be proven in Boogie — no induction. Policy:
each needed lemma is stated as an axiom with a `TRUSTED(listrich:<name>)`
ledger entry pointing at its Why3-proven counterpart, or as a lemma procedure
when a non-inductive proof exists. This is the honest soundness debt of the
backend and is kept auditable in one file. Extern types/consts (`Extern_type`
elements) map to uninterpreted types + axiomatized functions as today.

## 3. Translating commands and bicommands

Unary commands are routine; the notable difference is that safety VCs
currently induced by Why3 *preconditions on prelude operations* (e.g.
`M.find` requires `mem`) become explicit translator-inserted `assert`s
(null-dereference, allocatedness) carrying `{:msg}`/source-location
attributes — same proof obligations, better provenance. User loop invariants
translate directly; the auto-injected invariants (locals/globals type
invariants, `okState`, alloc monotonicity, boundary agreement where required)
mirror translate.ml:2077–2099. User-supplied variants (`wvariant`) become a
ghost `assert 0 <= measure && measure < old_measure` at loop end; absent a
variant, partial correctness matches Boogie's default (no termination check).

The relational core, case-by-case against `compile_bicommand`
(translate.ml:3265), each justified by the RRL proof rule it encodes:

| Bicommand | Boogie translation | Logical justification |
|---|---|---|
| `Bisync ac` (atomic) | left translation (over `l_*`) `;` right translation (over `r_*`) | sequential product is sound because the two vocabularies are disjoint by construction; commutation is syntactic |
| `Bisplit (c \| c')` | same: left block `;` right block | one-sided rules (rEmb/rDisj of the embedding) |
| `Bisync (Call m)`, m a bimethod | `call l_res, r_res := BiM(...)` against the biprocedure contract | relational procedure rule; coupling in pre/post via pretrans spec expansion |
| `Biassert R` / `Biassume R` | `assert`/`assume` of the two-vocabulary formula | rConseq embedding |
| `Biupdate (x\|y)` | `call UpdateRefperm(l_x, r_y)` | constructive refperm extension (§2.4) |
| `Bihavoc_right x R` | `havoc r_x; assume ⟦R⟧` | ∀∃ witness introduction: havoc-assume *is* the angelic choice, made demonic-safe because R must be established, not assumed sound — matches the existing desugaring to `Bisplit(skip, havoc); Biassume` at translate.ml:3268 |
| `Biif (lg\|rg) cc1 cc2` | `assert ⟦lg⟧_l == ⟦rg⟧_r;` (guard agreement) `if (⟦lg⟧_l) {…} else {…}` | rIf: alignment legitimacy is a checked obligation, then a single product branch |
| `Biif4` | 3-level nested `if` on (lg,rg) ∈ {tt, tf, ft, ff} | the four-way conditional rule; no agreement obligation |
| `Biwhile` lockstep (`lf=rf=false`) | `assert lg==rg` before loop and at body end; `while (l_g) inv ⟦R_inv⟧ ∧ auto-invs { body }` | rWhile with lockstep alignment |
| `Biwhile` one-sided | `while (⟦g⟧_side) inv … { side-only body }` | one-sided iteration rule |
| `Biwhile` general (alignment guards `lf`, `rf`) | `while (l_g \|\| r_g) inv … { if (⟦lf⟧) left-only else if (⟦rf⟧) right-only else { assert l_g == r_g; lockstep } }` | the full adequate-alignment rule; the alignment-guard trichotomy is exactly the KAT-style condition the typing already enforces |

∀∃ mode (`all_exists_mode`) changes no encoding — only which constructs are
admitted (`Bihavoc_right`) and the direction of agreement obligations, as in
the current backend. The curated `boogie_examples/all_exists/` files (PCSat,
HyPA, Forex) serve as *oracles*: hand-written encodings whose trigger and
witness patterns the generated code should reproduce; several can become
differential tests (same program, hand vs. generated `.bpl`).

## 4. VC quality engineering

This is the actual hard problem — notes.md already documents the failure
modes (dihedral: quantifier-context blowup where even a trivial loop body
times out once enough quantified postconditions are in scope; case-analysis
VCs stalling on memberships). Design principles, in priority order:

1. **Every prelude quantifier has an explicit trigger.** No exceptions; a CI
   check greps for trigger-less `forall` in generated and prelude code.
2. **Lemma procedures over ambient axioms.** Facts an ITP proof would `apply`
   become procedures invoked by `call` at the point of use (the Boogie
   community's standard pattern). The quantified fact enters exactly one VC's
   context instead of all of them. The tiling lesson (source-level Asserts
   mirroring the tactic script) generalizes: *the replacement for tactics is
   asserts + lemma calls*, and WhyRel's source `Assert`/`Biassert` already
   provides the user-facing syntax.
3. **Context pruning.** Function definitions via bodies (not axioms) where
   possible; `uses { … }` blocks + `/prune` so per-field image and agreement
   axioms enter a VC only when that field occurs; one `.bpl` per module +
   shared prelude to bound the ambient context.
4. **Opacity.** Coupling relations and module invariants are large defined
   predicates; emit them `{:hide}` and generate `reveal` at use sites
   (folding/unfolding, as an ITP proof would), keeping them opaque inside
   client VCs — the SOF discipline made operational.
5. **Splitting.** `{:split_here}` at bicommand alignment points (translator
   knows them); `/vcsSplitOnEveryAssert` as a per-method fallback.
6. **Debugging loop.** `/printModel:1` plus source-location attributes maps
   countermodels back to `.rl` positions — a strictly better failure-analysis
   loop than the IDE's unproved-goal list.

### 4.4 Trusted ledger

`prelude.bpl` carries a header table: every `axiom` is tagged
`TRUSTED(<provenance>)` where provenance is `prelude.mlw:<lemma>` (Why3-proven),
`listrich:<lemma>` (Why3 stdlib-proven), or `meta:<argument>` (e.g. allocator
freshness, alloc monotonicity). The ledger is the audit surface for link 4 of
the soundness chain; CI fails if an axiom lacks a tag.

## 5. Architecture and implementation

```
src/boogie/
  bpl_ast.ml      -- small ADT for Boogie decls/stmts/exprs (incl. attributes, triggers)
  bpl_pp.ml       -- Format-based printer; round-trips through `boogie /noVerify` in tests
src/translate_boogie/
  trans_b.ml      -- mirrors translate.ml's structure: ctxt / bi_ctxt,
                     Build_State analogue (per-program decls), compile_{exp,formula,command,
                     rformula,bicommand,meth,bimeth}, effect→ensures generation
  bpl_constants.ml-- names mirroring why3constants.ml
stdlib/prelude.bpl -- handwritten; certified against prelude.mlw (§1.1, §4.4)
```

Notable simplification vs. the Why3 backend: Boogie has *one* expression
language, so the expr/term duality (`interp_exp` with `as_expr`/`as_term`
interpretations, duplicated `st_load`/`st_load_term`, …) collapses — roughly
a third of translate.ml's mechanism disappears. The ident/qualification
machinery (`ctxt`, `bi_ctxt`, left/right renaming) ports as-is.

Driver: `main.ml` gains `--target boogie|why3` (default why3) and `-o
out.bpl`; a separate runner script (later: `--run-boogie`) shells out to
`boogie /timeLimit:30 /prune …` and parses the per-assertion results back to
source locations. Testing: golden `.bpl` snapshots for translation stability;
actual Boogie runs in CI for the green set; a results matrix
(verified / time / timeout) per example with the Why3 backend as baseline.

## 6. Milestones

- **M0 — Prelude.** `prelude.bpl` + a validation harness: every prelude.mlw
  lemma restated as a Boogie lemma procedure and *proven* (not assumed). This
  calibrates triggers before any program translation exists, on the axioms
  that all later VCs will instantiate. Exit: harness green under
  `/randomSeed` variation (robustness, not luck).
- **M1 — Unary core.** `bpl_ast`/`bpl_pp` + translation of: classes, field
  load/store, `new`, locals, `if`, `while` + invariants, `assert`, direct
  calls; effect→frame-condition generation; okState threading. Exit: a cell
  example end-to-end, VCs verified by Boogie.
- **M2 — Unary region logic complete.** Boundaries, module invariants, frame
  lemma generation, datagroups (pretrans output, unchanged), math lists +
  ledger. Exit: `examples/all_all/stack` unary side (stack, liststack,
  arraystack) verified.
- **M3 — Relational ∀∀ lockstep.** Doubled vocabulary, refperm globals,
  agreement predicates, `Bisync`/`Bisplit`/`Biassert`/`Biassume`/`Biif`,
  lockstep `Biwhile`, biprocedure contracts with coupling, locEq-derived
  specs. Exit: `relstack` verified.
- **M4 — Alignment generality.** `Biif4`, general `Biwhile` with alignment
  guards, `Biupdate`. Exit: sumpub + the tiling example (the latter is the
  regression test for the asserts-replace-tactics thesis: its source already
  carries the needed asserts).
- **M5 — ∀∃.** `Bihavoc_right`, all_exists mode obligations. Exit: RHLE
  examples; differential comparison against `boogie_examples/all_exists/`
  hand encodings.
- **M6 — Encapsulation / SOF.** Encap-check obligations, boundary agreement
  frame conditions, `boundary_frames_invariant`-style lemma procedures
  (replacing the interactive skeletons in the memory notes). Exit: a
  hiding-based example (e.g., the client against two stack implementations).
- **M7 — Evaluation.** Full `examples/` matrix vs. the Why3 backend; ledger
  audit; writeup of where source asserts were needed and why (this is the
  research payload: a catalogue of SMT-amenable relational VC patterns).

## 7. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Inductive list lemmas as axioms (soundness debt) | ledger + Why3-proven provenance; lemma procedures where induction-free proofs exist |
| Quantifier blowup on agreement VCs (dihedral redux) | §4 discipline; M0 trigger calibration before program VCs exist; `/prune`; per-module emission |
| Allocator-freshness assume consistency | same assumption as current backend; `meta` ledger entry; `Ref` uninterpreted (infinite models exist) |
| Z3-centric (CVC5 second-class in Boogie) | acceptable for v1; the direct SMT-LIB backend (CVC5 native sets) remains the documented escape hatch if axiomatized regions hit a wall |
| Two backends drifting | shared parse/typing/pretrans; golden tests on both; projection checks unchanged |
| Boogie surface changes (docs stale) | pin Boogie version in CI; rely on repo + `boogie /help`, not readthedocs |

## 8. References

- Banerjee, Naumann, Rosenberg. *Regional logic for local reasoning about global invariants.* ECOOP 2008.
- Banerjee, Naumann. *Local reasoning for global invariants, Part II: dynamic boundaries.* JACM 2013.
- Banerjee, Nagasamudram, Naumann, Nikouei. *A relational program logic with data abstraction and dynamic framing.* TOPLAS 2022. (Lecture-notes form: banerjee_PLS_2022.pdf.)
- Nagasamudram, Banerjee, Naumann. *The WhyRel prototype for modular relational verification of pointer programs.* TACAS 2023.
- Leino. *This is Boogie 2.* 2008. Current reference: boogie-docs.readthedocs.io (stale) + github.com/boogie-org/boogie.
- Barnett, Leino. *Weakest-precondition of unstructured programs.* PASTE 2005.
- Flanagan, Saxe. *Avoiding exponential explosion: generating compact verification conditions.* POPL 2001.
- Bornat. *Proving pointer programs in Hoare logic.* MPC 2000 (field-splitting; after Burstall 1972).
- Barthe, D'Argenio, Rezk. *Secure information flow by self-composition.* CSFW 2004.
- Barthe, Crespo, Kunz. *Relational verification using product programs.* FM 2011.
- Eilers, Müller, Hitz. *Modular product programs.* ESOP 2018.
