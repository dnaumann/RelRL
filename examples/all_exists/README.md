# All Exists Examples


### CCR

Conditional Contextual Refinement verification from POPL 2023. Demonstrates refinement of array-based map implementation against function-based maps.

### Conditional_Loop

Conditional loop alignment example.

### Havoc_Test

Introductory example using havoc and HavocR constructs. 

### HiccupSum

Demonstrates loops with nondeterministic behavior guarded by existential variables.

### Hypra

- **lowError**: Existential property verification.

### Veracity

Veracity challenge problems that were not verifiable using the Veracity framework. See https://github.com/veracity-lang/veracity/

- **Fizzbuzz**: Veracity challenge problem.
- **Simple_IO**: Veracity challenge problem.
- **Simple_Vector**: Veracity challenge problem.

### Itzhaky

Relational verification from [Itzhaky et al. ESOP 2024](https://easychair.org/publications/preprint_download/jKLf). Demonstrates reasoning about programs with multiple execution paths and nondeterministic values.

### Hypa

Examples from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa).

- **asynch_gni**: Asynchronous generalized noninterference.
- **compiler_opt**: Compiler optimization verification.
- **compiler_opt2**: Compiler optimization verification (variant 2).
- **counter_diff**: Counter difference property.
- **non_det_add**: Nondeterministic addition.
- **p1_gni**: Generalized noninterference property 1.
- **p2_gni**: Generalized noninterference property 2.
- **p3_gni**: Generalized noninterference property 3.
- **p4_gni**: Generalized noninterference property 4.
- **paper_example**: Example from published paper.
- **refine**: Refinement verification.
- **refine2**: Refinement verification (variant 2).
- **smaller**: Simplified refinement example.

#### K-Safety

K-safety properties from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/K_safety).

- **Coll_Item_Sym**: Collection item symmetry K-safety property.
- **Counter_Det**: Counter determinism K-safety property.
- **Double_Square_NI**: Double-square noninterference K-safety property.
- **Fig2**: K-safety example from published paper figure.

### PCSat

Examples from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/tree/main/benchmarks/pcsat).

- **paper_gni_example**: Generalized noninterference example from paper.
- **ti_gni_hff**: GNI with specific configuration.
- **ti_gni_hft**: GNI with specific configuration.
- **ti_gni_htt**: GNI with specific configuration.
- **ts_gni_hff**: GNI with specific configuration (equivalent to ti_gni_hff).
- **ts_gni_hft**: GNI with specific configuration.
- **ti_gni_htt**: GNI with specific configuration.

### Sumpub

Information flow case study verifying that a program summing public elements in
a list with public and non-public elements does not leak information about
non-public values. Existential property over two runs.

### Tabulate

Example showing how specs in region logic can be formulated for relational reasoning without encapsulation.

### RHLE

Examples from [ORHLE experiments](https://github.com/rcdickerson/orhle/tree/main/experiments). Function calls modeled using havoc-assume; existential specs used for right program.

#### API Refinement

- **add3_shuffled**: API refinement with shuffled operations.
- **add3_sorted**: API refinement with sorted operations.
- **conditional_nonrefinement**: Nonrefinement with conditionals.
- **conditional_refinement**: Refinement with conditionals.
- **loop_nonrefinement**: Nonrefinement with loops.
- **loop_refinement**: Refinement with loops.
- **loop_refinement2**: Refinement with loops (variant 2).
- **perm_inv_refinement**: Refinement with permutation invariants.
- **simple_nonrefinement**: Simple nonrefinement example.
- **simple_refinement**: Simple refinement example.

#### Blackjack

Unary existential property specifications: `{2 <= handValue && handValue <= 20} biprog {handValue == 21}`.

- **do_nothing**: No body; invalid.
- **draw_once**: Single card draw; existential procedure call; invalid.
- **draw_until_21**: Draw until reaching 21; existential procedure call with choice variable instantiation; loop invariant `{handValue <= 21}`; valid.

#### Delimited Release

Information flow examples with delimited release properties.

- **avg_salaries_no_dr**: Forall-forall-exists spec without delimited release.
- **avg_salaries**: Forall-forall-exists spec with delimited release.
- **conditional_leak**: Conditional information leak.
- **conditional_no_dr**: Conditional property without delimited release.
- **median**: Median computation.
- **parity_fun**: Parity function.
- **parity_no_dr**: Parity without delimited release.
- **parity**: Parity with delimited release.
- **parity2**: Parity variant.
- **wallet_no_dr**: Wallet example without delimited release.
- **wallet**: Wallet example with delimited release.

#### Flaky Tests

Existential-existential specs: `{true} prod_prog {!(success1 == success2)}`.

- **http_request**: HTTP request flakiness.
- **sleep_and_continue**: Sleep and continue flakiness.

#### GNI

Generalized noninterference properties.

- **denning1**: Denning's information flow example 1.
- **denning2**: Denning's information flow example 2.
- **denning3**: Denning's information flow example 3.
- **model_leak**: Model information leak with existential procedure call.
- **nondet_leak2**: Nondeterministic leak with existential procedure call.
- **nondet_nonleak**: Nondeterministic nonleak with existential procedure call.
- **nondet_nonleak2**: Nondeterministic nonleak variant with conditional choice variable instantiation.
- **simple_leak**: Simple information leak.
- **simple_nonleak**: Simple nonleak example.
- **smith1**: Smith's information flow example.

#### Param Usage

Parameter usage properties; most specs are forall-forall-exists-exists type.

- **coin_unused**: Unused coin parameter; four-run property.
- **det_unused**: Unused deterministic parameter.
- **even_odd**: Even-odd parameter usage.
- **nondet_unused**: Unused nondeterministic parameter; four-run property.
- **nondet_used**: Used nondeterministic parameter; four-run property.
- **semantically_unused**: Semantically unused parameter; four-run property.
- **three_used**: Three-parameter usage; six-run property.
