# All Exists Examples

Examples mentioned as invalid should fail to verify.

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

- **Fizzbuzz**
- **Simple_IO**
- **Simple_Vector**

### Itzhaky

Relational verification from [Itzhaky et al. ESOP 2024](https://easychair.org/publications/preprint_download/jKLf). Demonstrates reasoning about programs with multiple execution paths and nondeterministic values.

### Hypa

Examples from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa).

- **asynch_gni**
- **compiler_opt**
- **compiler_opt2**
- **counter_diff**
- **non_det_add**
- **p1_gni**
- **p2_gni**
- **p3_gni**
- **p4_gni**
- **paper_example_fig3**
- **refine**
- **refine2**
- **smaller**

#### K-Safety

K-safety properties from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/K_safety).

- **Coll_Item_Sym**
- **Counter_Det**
- **Double_Square_NI**
- **Fig2**

### PCSat

Examples from [ForEx benchmarks](https://github.com/ravenbeutner/ForEx/tree/main/benchmarks/pcsat).

- **paper_gni_example**
- **ti_gni_hff**
- **ti_gni_hft**
- **ti_gni_htt**
- **ts_gni_hff**
- **ts_gni_hft**
- **ts_gni_htt**

### Sumpub

Information flow case study verifying that a program summing public elements in
a list with public and non-public elements does not leak information about
non-public values. Existential property over two runs.

### Tabulate

Example showing how specs in region logic can be formulated for relational reasoning without encapsulation.

### RHLE

Examples from [ORHLE experiments](https://github.com/rcdickerson/orhle/tree/main/experiments). Function calls modeled using havoc-assume; existential specs used for right program.

#### API Refinement

- **add3_shuffled**: Invalid.
- **add3_sorted**
- **conditional_nonrefinement**: Invalid.
- **conditional_refinement**
- **conditional_refinement_sync_calls**
- **loop_nonrefinement**: Invalid.
- **loop_refinement**
- **loop_refinement2**
- **perm_inv_refinement**
- **simple_nonrefinement**: Invalid.
- **simple_refinement**

#### Delimited Release

Information flow examples with delimited release properties.

- **parity_fun**
- **parity_no_dr**: Invalid.
- **parity**
- **parity2**
- **wallet_no_dr**: Invalid.
- **wallet**

#### GNI

Generalized noninterference properties.

- **denning1**
- **denning2**: Invalid.
- **denning3**: Invalid.
- **nondet_leak**: Invalid.
- **nondet_leak2**: Invalid.
- **nondet_nonleak**: Nondeterministic nonleak with existential procedure call.
- **nondet_nonleak2**: Nondeterministic nonleak variant with conditional choice variable instantiation.
- **simple_leak**: Invalid.
- **simple_nonleak**
- **smith1**: Invalid.

#### Param Usage

- **det_unused**
- **even_odd**: Invalid.
