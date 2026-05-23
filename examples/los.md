# Lines of Spec (los) Summary

**Counting Rule:** Each line containing a logical assertion keyword at the beginning (after whitespace) counts as one line of spec. Keywords include:
- Spec clauses: `requires`, `ensures`, `effects`, `reads`, `writes`
- Loop/iteration: `invariant`, `variant`
- Named formulas: `predicate`, `lemma`, `axiom`
- Relational: `coupling`
- Assertions: `assert`, `Assert`, `assume`, `Assume`, `HavocR`, `{{...}}`

**Excluded:** Alignment syntax (`|_`, `_|`, `<|`, `|>`, `[<`, `>]`, `[>`, `<]`), comments

**Scope:** Only `.rl` files (not `.mlw` generated WhyML).

---

## All-All Examples (Unary Equivalence)

| Example | Spec Lines |
|---------|-----------|
| Cell | 57 |
| determinism | 11 |
| equiv-check | 18 |
| factorial | 14 |
| fibonacci | 16 |
| Kruskal | 121 |
| majorization | 10 |
| monofact | 4 |
| SSSP | 308 |
| stack | 125 |
| sumpub | 28 |
| swap | 22 |
| tabulate | 64 |
| tiling | 25 |
| Veracity/Dihedral | 55 |
| Veracity/Fizzbuzz | 67 |
| Veracity/Simple_IO | 71 |
| Veracity/Simple_Vector | 65 |

**Total (all_all):** 1,082 lines

---

## All-Exists Examples (Relational Equivalence/Properties)

### Core Examples
| Example | Spec Lines |
|---------|-----------|
| CCR | 107 |
| Conditional_Loop | 9 |
| Havoc_Test | 5 |
| HiccupSum | 5 |
| Hypra/LowError | 6 |
| Itzhaky | 12 |
| sumpub | 28 |
| stack | 125 |
| tabulate | 64 |
| tiling | 31 |
| Veracity/Fizzbuzz | 67 |
| Veracity/Simple_IO | 71 |
| Veracity/Simple_Vector | 65 |

### RHLE Benchmarks

#### API Refinement
| Example | Spec Lines |
|---------|-----------|
| Add3_Shuffled | 7 |
| Add3_Sorted | 18 |
| Conditional_Nonrefinement | 3 |
| Conditional_Refinement | 2 |
| Conditional_Refinement_Sync_Calls | 3 |
| Loop_Nonrefinement | 3 |
| Loop_Refinement | 3 |
| Loop_Refinement2 | 3 |
| Perm_Inv_Refinement | 7 |
| Simple_Nonrefinement | 2 |
| Simple_Refinement | 2 |

#### Delimited Release
| Example | Spec Lines |
|---------|-----------|
| Parity | 4 |
| Parity2 | 4 |
| Parity_Fun | 4 |
| Parity_No_Dr | 4 |
| Wallet | 5 |
| Wallet_No_Dr | 5 |

#### Generalized Noninterference (GNI)
| Example | Spec Lines |
|---------|-----------|
| Denning1 | 7 |
| Denning2 | 6 |
| Denning3 | 5 |
| Nondet_Leak | 6 |
| Nondet_Leak2 | 5 |
| Nondet_Nonleak | 6 |
| Nondet_Nonleak2 | 5 |
| Simple_Leak | 5 |
| Simple_Nonleak | 5 |
| Smith1 | 1 |

#### Param Usage
| Example | Spec Lines |
|---------|-----------|
| Det_Unused | 2 |
| Even_Odd | 2 |

### ForEx Benchmarks

#### PCsat
| Example | Spec Lines |
|---------|-----------|
| Paper_GNI_Example | 8 |
| Ti_GNI_HFF | 5 |
| Ti_GNI_HFT | 4 |
| Ti_GNI_HTT | 3 |
| Ts_GNI_HFF | 5 |
| Ts_GNI_HFT | 4 |
| Ts_GNI_HTT | 3 |

#### Hypa
| Example | Spec Lines |
|---------|-----------|
| Asynch_GNI | 6 |
| Compiler_Opt | 6 |
| Compiler_Opt2 | 6 |
| Counter_Diff | 5 |
| Non_Det_Add | 5 |
| P1_GNI | 3 |
| P2_GNI | 4 |
| P3_GNI | 2 |
| P4_GNI | 6 |
| Paper_Example_Fig3 | 5 |
| Refine | 15 |
| Refine2 | 9 |
| Smaller | 4 |

#### K-Safety
| Example | Spec Lines |
|---------|-----------|
| Coll_Item_Sym | 2 |
| Counter_Det | 6 |
| Double_Square_NI | 6 |
| Fig2 | 6 |

**Total (all_exists):** 915 lines

---

## Summary Statistics

| Category | Spec Lines |
|----------|-----------|
| all_all (unary) | 1,082 |
| all_exists (relational) | 915 |
| **Grand Total** | **1,997** |

**Note:** The `stack copy` directory is a duplicate of `stack` and is not included in this summary.
