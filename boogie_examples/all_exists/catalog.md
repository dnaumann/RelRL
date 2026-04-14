# Boogie example catalog

- BoogieExamples.bpl
- ccr.bpl
- Conditional_Loop.bpl
- Conditional_Loop_LockstepAttempt.bpl
- data.bpl
- factorial.bpl
- hiccupSum.bpl
- Itzhaky.bpl
- lmcsExample.bpl

## Hypra

- lowError

## Veracity

Veracity challenge problems that were not verifiable using the Veracity framework. See https://github.com/veracity-lang/veracity/

- fizzbuzz
- simple_vector
- simple_io

## Hypa

https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa

- asynch_gni
- compiler_opt
- compiler_opt2
- counter_diff
- non_det_add
- p1_gni
- p2_gni
- p3_gni
- p4_gni
- paper_example
- refine
- refine2
- smaller

### K-Safety

K-safety properties from https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/K_safety

- Coll_Item_Sym
- Counter_Det
- Double_Square_NI
- Fig2

## PCSat

https://github.com/ravenbeutner/ForEx/tree/main/benchmarks/pcsat

- paper_gni_example
- ti_gni_hff
- ti_gni_hft
- ti_gni_htt
- ts_gni_hff
  - same as ti_gni_hff
- ts_gni_hft
- ti_gni_htt

## RHLE

https://github.com/rcdickerson/orhle/tree/main/experiments

Function call modelled using havoc assume. Existential specs are used for the right program.

### API Refinement

- add3_shuffled
- add3_sorted
- conditional_nonrefinement
- conditional_refinement
- loop_nonrefinement
- loop_refinement
- loop_refinement2
- perm_inv_refinement
- simple_nonrefinement
- simple_refinement

### Blackjack

all are unary existential property.

- do_nothing
  - {2 <= handValue && handValue <= 20} biprog {handValue == 21}
  - no body
  - invalid
- draw_once
  - {2 <= handValue && handValue <= 20} biprog {handValue == 21}
  - invalid
  - existential procedure call
- draw_until_21
  - {2 <= handValue && handValue <= 20} biprog {handValue == 21}
  - valid
  - existential procedure call
    - interesting choice variable instantiation
  - loop with invariant {handValue <= 21>}


### Delimited Release

- avg_salaries_no_dr
  - forall forall exists spec.
- avg_salaries
  - forall forall exists spec.
- conditional_leak
  - forall forall exists spec.
- conditional_no_dr
  - forall forall exists spec.
- median
- parity_fun
- parity_no_dr
- parity
- parity2
- wallet_no_dr
- wallet

### Flaky Tests

Has exists exists specs, {true} prod_prog {! (success1 == success2)}

- http_request
- sleep_and_continue

### GNI

- denning1
- denning2
- denning3
- model_leak
  - existential procedure call.
- nondet_leak2
  - existential procedure call.
- nondet_nonleak
  - existential procedure call.
- nondet_nonleak2
  - existential procedure call.
    - conditional choicevar instantiation.
- simple_leak
- simple_nonleak
- smith1

### Param Usage

Most specs are forall forall exists exists type.

- coin_unused
  - four run property
- det_unused
- even_odd
- nondet_unused
  - four run property
- nondet_used
  - four run property
- semantically_unused
  - four run property
- three_used
  - six run property
