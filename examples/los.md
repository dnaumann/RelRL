# Lines of Spec (los) Summary

**Counting Rule:** A line counts as one line of spec if, after stripping leading whitespace, it begins with one of the recognized annotation keywords.

**Categories (table columns):**
- **Spec** — `requires`, `ensures`, `effects`, `reads`, `writes`
- **Loop** — `invariant`, `variant`
- **Pred** — `predicate`, `coupling`
- **Lemma** — `lemma`, `axiom`
- **Assert** — `assert`, `Assert`, `assume`, `Assume`, `{{...}}`
- **Havoc** — `HavocR`

**Excluded:** Alignment syntax (`|_`, `_|`, `<|`, `|>`, `[<`, `>]`, `[>`, `<]`), comments, and work-in-progress files (`wip.rl`).

**Scope:** All `.rl` files under `examples/`. Each example aggregates every `.rl` file in its directory (e.g. the multiple modules of `stack`, `Kruskal`, `SSSP`). Generated automatically by `count_los.py`.

---

## All-All Examples (Unary Equivalence)

| Example | Spec | Loop | Pred | Lemma | Assert | Havoc | Total |
|---------|------:|------:|------:|------:|------:|------:|------:|
| all_all/Cell | 54 | 0 | 1 | 1 | 1 | 0 | 57 |
| all_all/Kruskal | 64 | 37 | 8 | 2 | 10 | 0 | 121 |
| all_all/SSSP | 216 | 58 | 7 | 7 | 24 | 0 | 312 |
| all_all/Veracity/Dihedral | 26 | 30 | 0 | 0 | 13 | 0 | 69 |
| all_all/Veracity/Fizzbuzz | 27 | 71 | 0 | 0 | 10 | 0 | 108 |
| all_all/Veracity/Simple_IO | 20 | 52 | 0 | 0 | 4 | 0 | 76 |
| all_all/Veracity/Simple_Vector | 36 | 41 | 0 | 0 | 2 | 0 | 79 |
| all_all/determinism | 6 | 4 | 1 | 0 | 0 | 0 | 11 |
| all_all/equiv-check | 6 | 11 | 0 | 0 | 1 | 0 | 18 |
| all_all/factorial | 7 | 9 | 0 | 0 | 0 | 0 | 16 |
| all_all/fibonacci | 9 | 7 | 0 | 0 | 0 | 0 | 16 |
| all_all/majorization | 6 | 5 | 0 | 1 | 0 | 0 | 12 |
| all_all/monofact | 5 | 4 | 0 | 0 | 0 | 0 | 9 |
| all_all/stack | 88 | 36 | 3 | 0 | 12 | 0 | 139 |
| all_all/sumpub | 10 | 9 | 2 | 4 | 3 | 0 | 28 |
| all_all/swap | 22 | 0 | 0 | 0 | 0 | 0 | 22 |
| all_all/tabulate | 37 | 16 | 1 | 1 | 10 | 0 | 65 |
| all_all/tiling | 11 | 18 | 2 | 0 | 0 | 0 | 31 |
| **Subtotal** | **650** | **408** | **25** | **16** | **90** | **0** | **1189** |

---

## All-Exists Examples (Relational Equivalence/Properties)

| Example | Spec | Loop | Pred | Lemma | Assert | Havoc | Total |
|---------|------:|------:|------:|------:|------:|------:|------:|
| all_exists/CCR | 71 | 0 | 3 | 0 | 0 | 1 | 75 |
| all_exists/Conditional_Loop | 4 | 5 | 0 | 0 | 0 | 1 | 10 |
| all_exists/Forex/Hypa/Asynch_GNI | 3 | 2 | 0 | 0 | 0 | 1 | 6 |
| all_exists/Forex/Hypa/Compiler_Opt | 4 | 2 | 0 | 0 | 0 | 1 | 7 |
| all_exists/Forex/Hypa/Compiler_Opt2 | 3 | 3 | 0 | 0 | 0 | 1 | 7 |
| all_exists/Forex/Hypa/Counter_Diff | 3 | 3 | 0 | 0 | 0 | 1 | 7 |
| all_exists/Forex/Hypa/Non_Det_Add | 3 | 2 | 0 | 0 | 0 | 1 | 6 |
| all_exists/Forex/Hypa/P1_GNI | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/Forex/Hypa/P2_GNI | 3 | 0 | 0 | 0 | 0 | 1 | 4 |
| all_exists/Forex/Hypa/P3_GNI | 1 | 0 | 0 | 0 | 0 | 1 | 2 |
| all_exists/Forex/Hypa/P4_GNI | 1 | 0 | 0 | 0 | 0 | 5 | 6 |
| all_exists/Forex/Hypa/Paper_Example_Fig3 | 3 | 1 | 0 | 0 | 0 | 1 | 5 |
| all_exists/Forex/Hypa/Refine | 10 | 11 | 0 | 0 | 0 | 3 | 24 |
| all_exists/Forex/Hypa/Refine2 | 4 | 11 | 0 | 0 | 0 | 3 | 18 |
| all_exists/Forex/Hypa/Smaller | 3 | 2 | 0 | 0 | 0 | 1 | 6 |
| all_exists/Forex/K_safety/Coll_Item_Sym | 2 | 0 | 0 | 0 | 0 | 0 | 2 |
| all_exists/Forex/K_safety/Counter_Det | 4 | 2 | 0 | 0 | 0 | 0 | 6 |
| all_exists/Forex/K_safety/Double_Square_NI | 4 | 2 | 0 | 0 | 0 | 0 | 6 |
| all_exists/Forex/K_safety/Fig2 | 4 | 2 | 0 | 0 | 0 | 0 | 6 |
| all_exists/Havoc_Test | 5 | 3 | 0 | 0 | 0 | 2 | 10 |
| all_exists/HiccupSum | 2 | 3 | 0 | 0 | 0 | 1 | 6 |
| all_exists/Hypra/LowError | 7 | 0 | 0 | 0 | 0 | 0 | 7 |
| all_exists/Itzhaky | 5 | 10 | 0 | 0 | 0 | 3 | 18 |
| all_exists/PCsat/Paper_GNI_Example | 4 | 6 | 0 | 0 | 2 | 3 | 15 |
| all_exists/PCsat/Ti_GNI_HFF | 2 | 1 | 0 | 0 | 0 | 2 | 5 |
| all_exists/PCsat/Ti_GNI_HFT | 2 | 1 | 0 | 0 | 0 | 1 | 4 |
| all_exists/PCsat/Ti_GNI_HTT | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/PCsat/Ts_GNI_HFF | 2 | 1 | 0 | 0 | 0 | 2 | 5 |
| all_exists/PCsat/Ts_GNI_HFT | 2 | 1 | 0 | 0 | 0 | 1 | 4 |
| all_exists/PCsat/Ts_GNI_HTT | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/RHLE/API_Refinement/Add3_Shuffled | 3 | 0 | 0 | 4 | 0 | 1 | 8 |
| all_exists/RHLE/API_Refinement/Add3_Sorted | 9 | 0 | 4 | 4 | 1 | 2 | 20 |
| all_exists/RHLE/API_Refinement/Conditional_Nonrefinement | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/RHLE/API_Refinement/Conditional_Refinement | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/RHLE/API_Refinement/Conditional_Refinement_Sync_Calls | 3 | 0 | 0 | 0 | 0 | 1 | 4 |
| all_exists/RHLE/API_Refinement/Loop_Nonrefinement | 2 | 1 | 0 | 0 | 0 | 1 | 4 |
| all_exists/RHLE/API_Refinement/Loop_Refinement | 2 | 1 | 0 | 0 | 0 | 1 | 4 |
| all_exists/RHLE/API_Refinement/Loop_Refinement2 | 2 | 1 | 0 | 0 | 0 | 1 | 4 |
| all_exists/RHLE/API_Refinement/Perm_Inv_Refinement | 2 | 0 | 1 | 4 | 0 | 1 | 8 |
| all_exists/RHLE/API_Refinement/Simple_Nonrefinement | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/RHLE/API_Refinement/Simple_Refinement | 2 | 0 | 0 | 0 | 0 | 1 | 3 |
| all_exists/RHLE/Delimited_Release/Parity | 5 | 0 | 0 | 0 | 0 | 0 | 5 |
| all_exists/RHLE/Delimited_Release/Parity2 | 5 | 0 | 0 | 0 | 0 | 0 | 5 |
| all_exists/RHLE/Delimited_Release/Parity_Fun | 5 | 0 | 0 | 0 | 0 | 1 | 6 |
| all_exists/RHLE/Delimited_Release/Parity_No_Dr | 4 | 0 | 0 | 0 | 0 | 0 | 4 |
| all_exists/RHLE/Delimited_Release/Wallet | 6 | 0 | 0 | 0 | 0 | 0 | 6 |
| all_exists/RHLE/Delimited_Release/Wallet_No_Dr | 5 | 0 | 0 | 0 | 0 | 0 | 5 |
| all_exists/RHLE/GNI/Denning1 | 4 | 3 | 0 | 0 | 0 | 0 | 7 |
| all_exists/RHLE/GNI/Denning2 | 4 | 2 | 0 | 0 | 0 | 0 | 6 |
| all_exists/RHLE/GNI/Denning3 | 4 | 2 | 0 | 0 | 0 | 0 | 6 |
| all_exists/RHLE/GNI/Nondet_Leak | 5 | 0 | 0 | 0 | 0 | 1 | 6 |
| all_exists/RHLE/GNI/Nondet_Leak2 | 4 | 0 | 0 | 0 | 0 | 1 | 5 |
| all_exists/RHLE/GNI/Nondet_Nonleak | 5 | 0 | 0 | 0 | 0 | 1 | 6 |
| all_exists/RHLE/GNI/Nondet_Nonleak2 | 4 | 0 | 0 | 0 | 0 | 1 | 5 |
| all_exists/RHLE/GNI/Simple_Leak | 5 | 0 | 0 | 0 | 0 | 0 | 5 |
| all_exists/RHLE/GNI/Simple_Nonleak | 5 | 0 | 0 | 0 | 0 | 0 | 5 |
| all_exists/RHLE/GNI/Smith1 | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| all_exists/RHLE/Param_Usage/Det_Unused | 3 | 0 | 0 | 0 | 0 | 0 | 3 |
| all_exists/RHLE/Param_Usage/Even_Odd | 3 | 0 | 0 | 0 | 0 | 0 | 3 |
| all_exists/Veracity/Fizzbuzz | 27 | 77 | 0 | 0 | 10 | 0 | 114 |
| all_exists/Veracity/Simple_IO | 20 | 52 | 0 | 0 | 4 | 0 | 76 |
| all_exists/Veracity/Simple_Vector | 36 | 42 | 0 | 0 | 4 | 0 | 82 |
| all_exists/stack | 88 | 36 | 3 | 0 | 12 | 0 | 139 |
| all_exists/sumpub | 10 | 11 | 2 | 4 | 3 | 0 | 30 |
| all_exists/tabulate | 37 | 16 | 1 | 1 | 10 | 0 | 65 |
| all_exists/tiling | 14 | 26 | 3 | 0 | 7 | 0 | 50 |
| **Subtotal** | **507** | **344** | **17** | **17** | **53** | **57** | **995** |

---

## Grand Total

| Spec | Loop | Pred | Lemma | Assert | Havoc | Total |
|------:|------:|------:|------:|------:|------:|------:|
| **1157** | **752** | **42** | **33** | **143** | **57** | **2184** |
