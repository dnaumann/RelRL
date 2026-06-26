# Annotation-Burden Catalog (∀∃ benchmarks)

Annotation burden for each benchmark in Table `tab:Catalog` of `oopsla.tex`, across the encodings we measured. Values are read from the per-system generated `.md` summaries. Each source is split into three buckets:

- **S (Spec)** — the specification / contract: `requires`/`ensures` and frame/effects clauses (`effects`/`reads`/`writes`/`modifies`/`diverges`), plus `pre`/`post` and `forall`/`exists` declarations (the `Goal` clauses for PCSat).
- **A (Auxiliary)** — auxiliary `predicate`/`function`/`lemma`/`axiom` declarations (the `Def` predicate clauses for PCSat).
- **I (Internal)** — remaining internal proof annotations: loop invariants/variants, `assert`/`assume`, `havoc` (`I = Total − Spec − Aux`).

`-` means no artifact was collected.

Sources: **RelRL** `examples/los.md`, **WhyML** `examples/los_whyml.md`, **Boogie** `boogie_examples/burden_bpl.md`, **Origin** = source repo's own encoding where measured (ForEx 1–17, PCSat 19–24, RHLE 25–52).

| # | Example | RL S | RL A | RL I | RL T | WhyML S | WhyML A | WhyML I | WhyML T | Bgie S | Bgie A | Bgie I | Bgie T | Org S | Org A | Org I | Org T |
|--:|---------|-----:|-----:|-----:|-----:|--------:|--------:|--------:|--------:|-------:|-------:|-------:|-------:|------:|------:|------:|------:|
| | **ForEx/HyPa** | | | | | | | | | | | | | | | | |
| 1 | Asynch_Opt | 3 | 0 | 3 | 6 | 9 | 6 | 7 | 22 | 2 | 0 | 6 | 8 | 4 | 0 | 0 | 4 |
| 2 | Compiler_Opt | 4 | 0 | 3 | 7 | 11 | 6 | 9 | 26 | 2 | 0 | 7 | 9 | 4 | 0 | 0 | 4 |
| 3 | Compiler_Opt2 | 3 | 0 | 4 | 7 | 11 | 6 | 12 | 29 | 2 | 0 | 8 | 10 | 4 | 0 | 0 | 4 |
| 4 | Counter_Diff | 3 | 0 | 4 | 7 | 10 | 6 | 9 | 25 | 2 | 0 | 5 | 7 | 4 | 0 | 0 | 4 |
| 5 | Non_Det_Add | 3 | 0 | 3 | 6 | 9 | 6 | 7 | 22 | 2 | 1 | 7 | 10 | 4 | 0 | 0 | 4 |
| 6 | P1_GNI | 2 | 0 | 1 | 3 | 8 | 6 | 3 | 17 | 2 | 0 | 4 | 6 | 4 | 0 | 0 | 4 |
| 7 | P2_GNI | 3 | 0 | 1 | 4 | 10 | 6 | 3 | 19 | 3 | 0 | 4 | 7 | 4 | 0 | 0 | 4 |
| 8 | P3_GNI | 1 | 0 | 1 | 2 | 6 | 6 | 3 | 15 | 1 | 0 | 4 | 5 | 4 | 0 | 0 | 4 |
| 9 | P4_GNI | 1 | 0 | 5 | 6 | 6 | 6 | 7 | 19 | 1 | 0 | 12 | 13 | 4 | 0 | 0 | 4 |
| 10 | Paper_Example_Fig3 | 3 | 0 | 2 | 5 | 11 | 6 | 10 | 27 | 2 | 0 | 7 | 9 | 4 | 0 | 0 | 4 |
| 11 | Refine | 10 | 0 | 14 | 24 | 49 | 15 | 53 | 117 | 2 | 0 | 18 | 20 | 4 | 0 | 0 | 4 |
| 12 | Refine2 | 4 | 0 | 14 | 18 | 53 | 15 | 47 | 115 | 2 | 0 | 16 | 18 | 4 | 0 | 0 | 4 |
| 13 | Smaller | 3 | 0 | 3 | 6 | 10 | 6 | 8 | 24 | 2 | 0 | 6 | 8 | 4 | 0 | 0 | 4 |
| | **ForEx/K_Safety** | | | | | | | | | | | | | | | | |
| 14 | Coll_Item_Sym | 2 | 0 | 0 | 2 | 26 | 6 | 1 | 33 | 2 | 0 | 0 | 2 | 4 | 0 | 0 | 4 |
| 15 | Counter_Det | 4 | 0 | 2 | 6 | 23 | 6 | 5 | 34 | 3 | 0 | 2 | 5 | 4 | 0 | 0 | 4 |
| 16 | Double_Square_NI | 4 | 0 | 2 | 6 | 27 | 6 | 7 | 40 | 3 | 0 | 2 | 5 | 4 | 0 | 2 | 6 |
| 17 | Fig_2 | 4 | 0 | 2 | 6 | 25 | 6 | 7 | 38 | 3 | 0 | 2 | 5 | 4 | 0 | 1 | 5 |
| | **PCSat** | | | | | | | | | | | | | | | | |
| 18 | Paper_GNI_Example | 4 | 0 | 11 | 15 | 6 | 6 | 39 | 51 | 3 | 1 | 30 | 34 | - | - | - | - |
| 19 | Ti_GNI_HFF | 2 | 0 | 3 | 5 | 9 | 6 | 8 | 23 | 2 | 0 | 10 | 12 | 3 | 4 | 1 | 8 |
| 20 | Ti_GNI_HFT | 2 | 0 | 2 | 4 | 9 | 6 | 5 | 20 | 2 | 0 | 6 | 8 | 3 | 4 | 1 | 8 |
| 21 | Ti_GNI_HTT | 2 | 0 | 1 | 3 | 8 | 6 | 3 | 17 | 2 | 0 | 4 | 6 | 3 | 4 | 1 | 8 |
| 22 | Ts_GNI_HFF | 2 | 0 | 3 | 5 | 9 | 6 | 8 | 23 | 2 | 0 | 10 | 12 | 4 | 4 | 1 | 9 |
| 23 | Ts_GNI_HFT | 2 | 0 | 2 | 4 | 9 | 6 | 8 | 23 | 3 | 0 | 6 | 9 | 4 | 4 | 2 | 10 |
| 24 | Ts_GNI_HTT | 2 | 0 | 1 | 3 | 9 | 6 | 7 | 22 | 3 | 0 | 4 | 7 | 4 | 4 | 2 | 10 |
| | **RHLE/API_Refinement** | | | | | | | | | | | | | | | | |
| 25 | Add3_Shuffled | 3 | 4 | 1 | 8 | 10 | 10 | 6 | 26 | 3 | 4 | 7 | 14 | 7 | 0 | 1 | 8 |
| 26 | Add3_Sorted | 9 | 8 | 3 | 20 | 10 | 10 | 7 | 27 | 3 | 5 | 6 | 14 | 7 | 0 | 1 | 8 |
| 27 | Conditional_Nonrefinement | 2 | 0 | 1 | 3 | 6 | 6 | 4 | 16 | 2 | 1 | 5 | 8 | 8 | 0 | 1 | 9 |
| 28 | Conditional_Refinement | 2 | 0 | 1 | 3 | 6 | 6 | 4 | 16 | 2 | 1 | 5 | 8 | 8 | 0 | 1 | 9 |
| 29 | Loop_Nonrefinement | 2 | 0 | 2 | 4 | 7 | 6 | 7 | 20 | 2 | 0 | 7 | 9 | 6 | 0 | 3 | 9 |
| 30 | Loop_Refinement | 2 | 0 | 2 | 4 | 7 | 6 | 7 | 20 | 2 | 0 | 7 | 9 | 7 | 0 | 5 | 12 |
| 31 | Loop_Refinement2 | 2 | 0 | 2 | 4 | 7 | 6 | 7 | 20 | 2 | 0 | 7 | 9 | 7 | 0 | 5 | 12 |
| 32 | Perm_Inv_Refinement | 2 | 5 | 1 | 8 | 8 | 12 | 6 | 26 | 3 | 5 | 7 | 15 | 8 | 0 | 1 | 9 |
| 33 | Simple_Refinement | 2 | 0 | 1 | 3 | 6 | 6 | 4 | 16 | 2 | 0 | 6 | 8 | 7 | 0 | 1 | 8 |
| 34 | Simple_Nonrefinement | 2 | 0 | 1 | 3 | 6 | 6 | 4 | 16 | 2 | 0 | 6 | 8 | 7 | 0 | 1 | 8 |
| | **RHLE/Delimited_Release** | | | | | | | | | | | | | | | | |
| 35 | Parity | 5 | 0 | 0 | 5 | 18 | 6 | 1 | 25 | 4 | 0 | 0 | 4 | 4 | 0 | 0 | 4 |
| 36 | Parity2 | 5 | 0 | 0 | 5 | 18 | 6 | 1 | 25 | 4 | 0 | 0 | 4 | 4 | 0 | 0 | 4 |
| 37 | Parity_Fun | 5 | 0 | 1 | 6 | 18 | 6 | 4 | 28 | 4 | 0 | 6 | 10 | 8 | 0 | 0 | 8 |
| 38 | Parity_No_Dr | 4 | 0 | 0 | 4 | 16 | 6 | 1 | 23 | 3 | 0 | 0 | 3 | 4 | 0 | 0 | 4 |
| 39 | Wallet | 6 | 0 | 0 | 6 | 22 | 6 | 1 | 29 | 4 | 0 | 0 | 4 | 4 | 0 | 0 | 4 |
| 40 | Wallet_No_Dr | 5 | 0 | 0 | 5 | 20 | 6 | 1 | 27 | 3 | 0 | 0 | 3 | 4 | 0 | 0 | 4 |
| | **RHLE/GNI** | | | | | | | | | | | | | | | | |
| 41 | Denning1 | 4 | 0 | 3 | 7 | 21 | 6 | 6 | 33 | 3 | 1 | 2 | 6 | 4 | 0 | 2 | 6 |
| 42 | Denning2 | 4 | 0 | 2 | 6 | 21 | 6 | 5 | 32 | 3 | 2 | 2 | 7 | 4 | 0 | 2 | 6 |
| 43 | Denning3 | 4 | 0 | 2 | 6 | 23 | 6 | 5 | 34 | 4 | 0 | 2 | 6 | 4 | 0 | 2 | 6 |
| 44 | Model_Leak | 5 | 0 | 1 | 6 | 17 | 6 | 4 | 27 | 3 | 0 | 5 | 8 | 8 | 0 | 1 | 9 |
| 45 | Nondet_Leak2 | 4 | 0 | 1 | 5 | 16 | 6 | 4 | 26 | 3 | 0 | 5 | 8 | 8 | 0 | 1 | 9 |
| 46 | Nondet_Nonleak | 5 | 0 | 1 | 6 | 17 | 6 | 4 | 27 | 3 | 0 | 5 | 8 | 8 | 0 | 1 | 9 |
| 47 | Nondet_Nonleak2 | 4 | 0 | 1 | 5 | 16 | 6 | 4 | 26 | 3 | 0 | 5 | 8 | 8 | 0 | 1 | 9 |
| 48 | Simple_Leak | 5 | 0 | 0 | 5 | 17 | 6 | 1 | 24 | 3 | 0 | 0 | 3 | 4 | 0 | 0 | 4 |
| 49 | Simple_Nonleak | 5 | 0 | 0 | 5 | 17 | 6 | 1 | 24 | 3 | 0 | 0 | 3 | 4 | 0 | 0 | 4 |
| 50 | Smith1 | 1 | 0 | 0 | 1 | 6 | 6 | 1 | 13 | 1 | 0 | 0 | 1 | 3 | 0 | 0 | 3 |
| | **RHLE/Param_Usage** | | | | | | | | | | | | | | | | |
| 51 | Det_Unused | 3 | 0 | 0 | 3 | 12 | 6 | 1 | 19 | 2 | 0 | 0 | 2 | 4 | 0 | 0 | 4 |
| 52 | Even_Odd | 3 | 0 | 0 | 3 | 12 | 6 | 1 | 19 | 2 | 0 | 0 | 2 | 4 | 0 | 0 | 4 |
| | **WhyRel** | | | | | | | | | | | | | | | | |
| 53 | tabulate | 37 | 2 | 26 | 65 | 225 | 26 | 76 | 327 | - | - | - | - | - | - | - | - |
| 54 | sumpub | 10 | 6 | 14 | 30 | 75 | 34 | 47 | 156 | - | - | - | - | - | - | - | - |
| 55 | stack | 88 | 3 | 48 | 139 | 679 | 67 | 206 | 952 | - | - | - | - | - | - | - | - |
| 56 | tiling | 14 | 3 | 33 | 50 | 96 | 29 | 76 | 201 | - | - | - | - | - | - | - | - |
| | **Veracity** | | | | | | | | | | | | | | | | |
| 57 | Fizzbuzz | 27 | 0 | 87 | 114 | 87 | 6 | 138 | 231 | 22 | 5 | 53 | 80 | - | - | - | - |
| 58 | Simple_IO | 20 | 0 | 56 | 76 | 68 | 6 | 77 | 151 | 25 | 0 | 58 | 83 | - | - | - | - |
| 59 | Simple_Vector | 36 | 0 | 46 | 82 | 123 | 15 | 103 | 241 | 3 | 0 | 34 | 37 | - | - | - | - |
| | **Additional** | | | | | | | | | | | | | | | | |
| 60 | Itzhaky_Example | 5 | 0 | 13 | 18 | 51 | 15 | 40 | 106 | 2 | 1 | 21 | 24 | - | - | - | - |
| 61 | Conditional_Loop | 4 | 0 | 6 | 10 | 7 | 6 | 14 | 27 | 4 | 0 | 18 | 22 | - | - | - | - |
| 62 | Havoc_Test | 5 | 0 | 5 | 10 | 6 | 6 | 13 | 25 | - | - | - | - | - | - | - | - |
| 63 | CCR_fig_1 | 71 | 3 | 1 | 75 | 323 | 26 | 16 | 365 | 21 | 0 | 5 | 26 | - | - | - | - |
| 64 | hiccupSum | 2 | 0 | 4 | 6 | 9 | 6 | 14 | 29 | 4 | 1 | 26 | 31 | - | - | - | - |
| 65 | lowError | 7 | 0 | 0 | 7 | 13 | 6 | 1 | 20 | 12 | 0 | 0 | 12 | 3 | 0 | 0 | 3 |
| | **Total (measured)** | **504** | **34** | **453** | **991** | **2505** | **592** | **1199** | **4296** | **224** | **28** | **490** | **742** | **255** | **24** | **41** | **320** |
