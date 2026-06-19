#!/usr/bin/env python3
"""Build a consolidated annotation-burden table for the forall-exists benchmark
catalog (Table `tab:Catalog`, ~line 4709 of oopsla.tex).

This reads the *already-generated* per-system `.md` summaries (it does NOT run the
collection scripts). Each summary's table has the example key in the first column
and its Total in the last column; this joins those totals per benchmark.

Sources (generated .md files):
  RelRL   -- examples/los.md                       (.rl source spec)
  WhyML   -- examples/los_whyml.md                  (generated .mlw burden)
  Boogie  -- boogie_examples/burden_bpl.md          (.bpl burden)
  Origin  -- the source repo's own encoding, where measured:
               ForEx   ForEx-main/.../benchmarks/los.md   (HyPa 1-13, K_Safety 14-17)
               pfwnCSP coar-main/.../pfwnCSP/los.md        (PCSat Ti/Ts GNI 19-24)
               RHLE    rhle-benchmarks-main/los.md         (RHLE 25-52)
             WhyRel (53-56), Veracity (57-59) and Additional (60-65) have none.

Each cell is the benchmark's Total (sum over all keyword categories) from that
summary; '-' means we have no artifact for it.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# --- generated .md summaries --------------------------------------------------
RL_MD    = os.path.join(HERE, "los.md")
WHY_MD   = os.path.join(HERE, "los_whyml.md")
BPL_MD   = "/home/jude/RelRL/boogie_examples/burden_bpl.md"
RHLE_MD  = "/home/jude/Downloads/rhle-benchmarks-main/los.md"
FOREX_MD = "/home/jude/Downloads/ForEx-main/ForEx-main/benchmarks/los.md"
CSP_MD   = "/home/jude/Downloads/coar-main/benchmarks/pfwnCSP/los.md"


def parse_md(path):
    """Return {example_key: {column_name: int}} from a generated markdown table.

    The header row (first cell == 'Example') names the columns; subsequent data
    rows are mapped onto those names. Separator, subtotal and grand-total rows are
    skipped (their first cell isn't a real key / doesn't parse).
    """
    result = {}
    if not os.path.exists(path):
        return result, f"missing summary: {path}"
    columns = None
    for line in open(path, encoding="utf-8", errors="replace"):
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if cells and cells[0] == "Example":
            columns = cells
            continue
        if columns is None:
            continue
        key = cells[0]
        if not key or key.startswith("**"):
            continue
        row = {}
        for col, val in zip(columns, cells):
            try:
                row[col] = int(val.replace("*", "").strip())
            except ValueError:
                continue
        if row:
            result[key] = row
    return result, None


warnings = []


def load(path, spec_cols, aux_cols):
    """Load a summary; return (data, spec_cols, aux_cols).

    Spec = sum of spec_cols, Aux = sum of aux_cols, Internal = Total - Spec - Aux.
    """
    d, err = parse_md(path)
    if err:
        warnings.append(err)
    return (d, list(spec_cols), list(aux_cols))


# Each source: (data, Spec/contract columns, Auxiliary columns).
#   Spec = contract (requires/ensures, pre/post, forall/exists; Goal for pfwnCSP)
#   Aux  = auxiliary predicate/lemma/axiom declarations
#   Internal (= Total - Spec - Aux) = loop invariants/variants, asserts, havoc, ...
RL     = load(RL_MD,    ["Spec"], ["Pred", "Lemma"])
WHY    = load(WHY_MD,   ["Spec"], ["Pred", "Lemma"])
BPL    = load(BPL_MD,   ["Spec"], ["Pred", "Lemma"])
RHLEL  = load(RHLE_MD,  ["Spec"], [])
FOREXL = load(FOREX_MD, ["Spec"], [])
CSPL   = load(CSP_MD,   ["Goal"], ["Def"])  # pfwnCSP: Goal=property, Def=predicate defs

# --- the catalog: (#, display name, relrl key, boogie key, (origin_label, src, key)) ---
H = "all_exists/Forex/Hypa"
K = "all_exists/Forex/K_safety"
P = "all_exists/PCsat"
A = "all_exists/RHLE/API_Refinement"
D = "all_exists/RHLE/Delimited_Release"
G = "all_exists/RHLE/GNI"
U = "all_exists/RHLE/Param_Usage"

GROUPS = [
    ("ForEx/HyPa", [
        (1,  "Asynch_Opt",          f"{H}/Asynch_GNI",          "all_exists/Forex/Hypa/asynch_gni.bpl",          ("ForEx", FOREXL, "hypa/asynch_gni.txt")),
        (2,  "Compiler_Opt",        f"{H}/Compiler_Opt",        "all_exists/Forex/Hypa/compiler_opt.bpl",        ("ForEx", FOREXL, "hypa/compiler_opt.txt")),
        (3,  "Compiler_Opt2",       f"{H}/Compiler_Opt2",       "all_exists/Forex/Hypa/compiler_opt2.bpl",       ("ForEx", FOREXL, "hypa/compiler_opt2.txt")),
        (4,  "Counter_Diff",        f"{H}/Counter_Diff",        "all_exists/Forex/Hypa/counter_diff.bpl",        ("ForEx", FOREXL, "hypa/counter_diff.txt")),
        (5,  "Non_Det_Add",         f"{H}/Non_Det_Add",         "all_exists/Forex/Hypa/non_det_add.bpl",         ("ForEx", FOREXL, "hypa/non_det_add.txt")),
        (6,  "P1_GNI",              f"{H}/P1_GNI",              "all_exists/Forex/Hypa/p1_gni.bpl",              ("ForEx", FOREXL, "hypa/p1_gni.txt")),
        (7,  "P2_GNI",              f"{H}/P2_GNI",              "all_exists/Forex/Hypa/p2_gni.bpl",              ("ForEx", FOREXL, "hypa/p2_gni.txt")),
        (8,  "P3_GNI",              f"{H}/P3_GNI",              "all_exists/Forex/Hypa/p3_gni.bpl",              ("ForEx", FOREXL, "hypa/p3_gni.txt")),
        (9,  "P4_GNI",              f"{H}/P4_GNI",              "all_exists/Forex/Hypa/p4_gni.bpl",              ("ForEx", FOREXL, "hypa/p4_gni.txt")),
        (10, "Paper_Example_Fig3",  f"{H}/Paper_Example_Fig3",  "all_exists/Forex/Hypa/paper_example_fig3.bpl",  ("ForEx", FOREXL, "hypa/paper_example_fig3.txt")),
        (11, "Refine",             f"{H}/Refine",              "all_exists/Forex/Hypa/refine.bpl",              ("ForEx", FOREXL, "hypa/refine.txt")),
        (12, "Refine2",            f"{H}/Refine2",             "all_exists/Forex/Hypa/refine2.bpl",             ("ForEx", FOREXL, "hypa/refine2.txt")),
        (13, "Smaller",            f"{H}/Smaller",             "all_exists/Forex/Hypa/smaller.bpl",             ("ForEx", FOREXL, "hypa/smaller.txt")),
    ]),
    ("ForEx/K_Safety", [
        (14, "Coll_Item_Sym",      f"{K}/Coll_Item_Sym",       "all_exists/Forex/K_Safety/coll_item_sym.bpl",   ("ForEx", FOREXL, "k_safety/coll_item_sym.txt")),
        (15, "Counter_Det",        f"{K}/Counter_Det",         "all_exists/Forex/K_Safety/counter_det.bpl",     ("ForEx", FOREXL, "k_safety/counter_det.txt")),
        (16, "Double_Square_NI",   f"{K}/Double_Square_NI",    "all_exists/Forex/K_Safety/double_square_ni.bpl",("ForEx", FOREXL, "k_safety/double_square_ni.txt")),
        (17, "Fig_2",              f"{K}/Fig2",                "all_exists/Forex/K_Safety/fig2.bpl",            ("ForEx", FOREXL, "k_safety/fig2.txt")),
    ]),
    ("ForEx/PCSat", [
        (18, "Paper_GNI_Example",  f"{P}/Paper_GNI_Example",   "all_exists/PCSat/paper_gni_example.bpl",         None),
        (19, "Ti_GNI_HFF",         f"{P}/Ti_GNI_HFF",          "all_exists/PCSat/ti_gni_hff.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TI_GNI_hFF.clp")),
        (20, "Ti_GNI_HFT",         f"{P}/Ti_GNI_HFT",          "all_exists/PCSat/ti_gni_hft.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TI_GNI_hFT.clp")),
        (21, "Ti_GNI_HTT",         f"{P}/Ti_GNI_HTT",          "all_exists/PCSat/ti_gni_htt.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TI_GNI_hTT.clp")),
        (22, "Ts_GNI_HFF",         f"{P}/Ts_GNI_HFF",          "all_exists/PCSat/ts_gni_hff.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TS_GNI_hFF.clp")),
        (23, "Ts_GNI_HFT",         f"{P}/Ts_GNI_HFT",          "all_exists/PCSat/ts_gni_hft.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TS_GNI_hFT.clp")),
        (24, "Ts_GNI_HTT",         f"{P}/Ts_GNI_HTT",          "all_exists/PCSat/ts_gni_htt.bpl",               ("pfwnCSP", CSPL, "cav2021rel/TS_GNI_hTT.clp")),
    ]),
    ("RHLE/API_Refinement", [
        (25, "Add3_Shuffled",            f"{A}/Add3_Shuffled",            "all_exists/RHLE/API_Refinement/add3_shuffled.bpl",            ("RHLE", RHLEL, "api-refinement/add3-shuffled.imp")),
        (26, "Add3_Sorted",              f"{A}/Add3_Sorted",              "all_exists/RHLE/API_Refinement/add3_sorted.bpl",              ("RHLE", RHLEL, "api-refinement/add3-sorted.imp")),
        (27, "Conditional_Nonrefinement",f"{A}/Conditional_Nonrefinement","all_exists/RHLE/API_Refinement/conditional_nonrefinement.bpl",("RHLE", RHLEL, "api-refinement/conditional-nonrefinement.imp")),
        (28, "Conditional_Refinement",   f"{A}/Conditional_Refinement",   "all_exists/RHLE/API_Refinement/conditional_refinement.bpl",   ("RHLE", RHLEL, "api-refinement/conditional-refinement.imp")),
        (29, "Loop_Nonrefinement",       f"{A}/Loop_Nonrefinement",       "all_exists/RHLE/API_Refinement/loop_nonrefinement.bpl",       ("RHLE", RHLEL, "api-refinement/loop-nonrefinement.imp")),
        (30, "Loop_Refinement",          f"{A}/Loop_Refinement",          "all_exists/RHLE/API_Refinement/loop_refinement.bpl",          ("RHLE", RHLEL, "api-refinement/loop-refinement.imp")),
        (31, "Loop_Refinement2",         f"{A}/Loop_Refinement2",         "all_exists/RHLE/API_Refinement/loop_refinement2.bpl",         ("RHLE", RHLEL, "api-refinement/loop-refinement2.imp")),
        (32, "Perm_Inv_Refinement",      f"{A}/Perm_Inv_Refinement",      "all_exists/RHLE/API_Refinement/perm_inv_refinement.bpl",      ("RHLE", RHLEL, "api-refinement/perm-inv-refinement.imp")),
        (33, "Simple_Refinement",        f"{A}/Simple_Refinement",        "all_exists/RHLE/API_Refinement/simple_refinement.bpl",        ("RHLE", RHLEL, "api-refinement/simple-refinement.imp")),
        (34, "Simple_Nonrefinement",     f"{A}/Simple_Nonrefinement",     "all_exists/RHLE/API_Refinement/simple_nonrefinement.bpl",     ("RHLE", RHLEL, "api-refinement/simple-nonrefinement.imp")),
    ]),
    ("RHLE/Delimited_Release", [
        (35, "Parity",        f"{D}/Parity",        "all_exists/RHLE/Delimited_Release/parity.bpl",        ("RHLE", RHLEL, "delimited-release/parity.imp")),
        (36, "Parity2",       f"{D}/Parity2",       "all_exists/RHLE/Delimited_Release/parity2.bpl",       ("RHLE", RHLEL, "delimited-release/parity2.imp")),
        (37, "Parity_Fun",    f"{D}/Parity_Fun",    "all_exists/RHLE/Delimited_Release/parity_fun.bpl",    ("RHLE", RHLEL, "delimited-release/parity-fun.imp")),
        (38, "Parity_No_Dr",  f"{D}/Parity_No_Dr",  "all_exists/RHLE/Delimited_Release/parity_no_dr.bpl",  ("RHLE", RHLEL, "delimited-release/parity-no-dr.imp")),
        (39, "Wallet",        f"{D}/Wallet",        "all_exists/RHLE/Delimited_Release/wallet.bpl",        ("RHLE", RHLEL, "delimited-release/wallet.imp")),
        (40, "Wallet_No_Dr",  f"{D}/Wallet_No_Dr",  "all_exists/RHLE/Delimited_Release/wallet_no_dr.bpl",  ("RHLE", RHLEL, "delimited-release/wallet-no-dr.imp")),
    ]),
    ("RHLE/GNI", [
        (41, "Denning1",        f"{G}/Denning1",        "all_exists/RHLE/GNI/denning1.bpl",        ("RHLE", RHLEL, "gni/denning1.imp")),
        (42, "Denning2",        f"{G}/Denning2",        "all_exists/RHLE/GNI/denning2.bpl",        ("RHLE", RHLEL, "gni/denning2.imp")),
        (43, "Denning3",        f"{G}/Denning3",        "all_exists/RHLE/GNI/denning3.bpl",        ("RHLE", RHLEL, "gni/denning3.imp")),
        (44, "Model_Leak",      f"{G}/Nondet_Leak",     "all_exists/RHLE/GNI/nondet_leak.bpl",     ("RHLE", RHLEL, "gni/nondet-leak.imp")),
        (45, "Nondet_Leak2",    f"{G}/Nondet_Leak2",    "all_exists/RHLE/GNI/nondet_leak2.bpl",    ("RHLE", RHLEL, "gni/nondet-leak2.imp")),
        (46, "Nondet_Nonleak",  f"{G}/Nondet_Nonleak",  "all_exists/RHLE/GNI/nondet_nonleak.bpl",  ("RHLE", RHLEL, "gni/nondet-nonleak.imp")),
        (47, "Nondet_Nonleak2", f"{G}/Nondet_Nonleak2", "all_exists/RHLE/GNI/nondet_nonleak2.bpl", ("RHLE", RHLEL, "gni/nondet-nonleak2.imp")),
        (48, "Simple_Leak",     f"{G}/Simple_Leak",     "all_exists/RHLE/GNI/simple_leak.bpl",     ("RHLE", RHLEL, "gni/simple-leak.imp")),
        (49, "Simple_Nonleak",  f"{G}/Simple_Nonleak",  "all_exists/RHLE/GNI/simple_nonleak.bpl",  ("RHLE", RHLEL, "gni/simple-nonleak.imp")),
        (50, "Smith1",          f"{G}/Smith1",          "all_exists/RHLE/GNI/smith1.bpl",          ("RHLE", RHLEL, "gni/smith1.imp")),
    ]),
    ("RHLE/Param_Usage", [
        (51, "Det_Unused", f"{U}/Det_Unused", "all_exists/RHLE/Param_Usage/det_unused.bpl", ("RHLE", RHLEL, "param-usage/det-unused.imp")),
        (52, "Even_Odd",   f"{U}/Even_Odd",   "all_exists/RHLE/Param_Usage/even_odd.bpl",   ("RHLE", RHLEL, "param-usage/even-odd.imp")),
    ]),
    ("WhyRel", [
        (53, "tabulate", "all_exists/tabulate", None, None),
        (54, "sumpub",   "all_exists/sumpub",   None, None),
        (55, "stack",    "all_exists/stack",    None, None),
        (56, "tiling",   "all_exists/tiling",   None, None),
    ]),
    ("Veracity", [
        (57, "Fizzbuzz",      "all_exists/Veracity/Fizzbuzz",      "all_exists/Veracity/fizzbuzz.bpl",      None),
        (58, "Simple_IO",     "all_exists/Veracity/Simple_IO",     "all_exists/Veracity/simple_io.bpl",     None),
        (59, "Simple_Vector", "all_exists/Veracity/Simple_Vector", "all_exists/Veracity/simple_vector.bpl", None),
    ]),
    ("Additional", [
        (60, "Itzhaky_Example",  "all_exists/Itzhaky",          "all_exists/Itzhaky.bpl",          None),
        (61, "Conditional_Loop", "all_exists/Conditional_Loop", "all_exists/Conditional_Loop.bpl", None),
        (62, "Havoc_Test",       "all_exists/Havoc_Test",       None,                              None),
        (63, "CCR_fig_1",        "all_exists/CCR",              "all_exists/ccr.bpl",              None),
        (64, "hiccupSum",        "all_exists/HiccupSum",        "all_exists/hiccupSum.bpl",        None),
        (65, "lowError",         "all_exists/Hypra/LowError",   "all_exists/Hypra/lowError.bpl",   None),
    ]),
]


def cell(source, key):
    """Return (spec, aux, internal) for a benchmark in a source, or (None,)*3."""
    if key is None:
        return (None, None, None)
    data, spec_cols, aux_cols = source
    row = data.get(key)
    if row is None:
        return (None, None, None)
    total = row.get("Total")
    if total is None:
        total = sum(v for k, v in row.items() if k != "Total")
    spec = sum(row.get(c, 0) for c in spec_cols)
    aux = sum(row.get(c, 0) for c in aux_cols)
    return (spec, aux, total - spec - aux)


def fmt(v):
    return "-" if v is None else str(v)


TAGS = [f"{s}_{c}" for s in ("RL", "WH", "BP", "OR") for c in ("S", "A", "I", "T")]


def quad(triple):
    s, a, i = triple
    return [s, a, i, None if s is None else s + a + i]


def build():
    """Return (records, sums). records is a list of ('group', name) or
    ('row', num, name, vals[16], origin_tool)."""
    records = []
    sums = {k: 0 for k in TAGS}
    for group, rows in GROUPS:
        records.append(("group", group))
        for num, name, rl_key, bpl_key, origin in rows:
            rl, wh, bp = cell(RL, rl_key), cell(WHY, rl_key), cell(BPL, bpl_key)
            if origin is None:
                org_tool, org = "", (None, None, None)
            else:
                org_tool, src, okey = origin
                org = cell(src, okey)
                if org[0] is None:
                    warnings.append(f"#{num} {name}: origin key not found: {okey}")
            vals = quad(rl) + quad(wh) + quad(bp) + quad(org)
            for tag, val in zip(TAGS, vals):
                if val is not None:
                    sums[tag] += val
            if rl[0] is None:
                warnings.append(f"#{num} {name}: RelRL key not found: {rl_key}")
            if bpl_key and bp[0] is None:
                warnings.append(f"#{num} {name}: Boogie key not found: {bpl_key}")
            records.append(("row", num, name, vals, org_tool))
    return records, sums


def render_md(records, sums):
    out = [
        "# Annotation-Burden Catalog (∀∃ benchmarks)",
        "",
        "Annotation burden for each benchmark in Table `tab:Catalog` of `oopsla.tex`, "
        "across the encodings we measured. Values are read from the per-system "
        "generated `.md` summaries. Each source is split into three buckets:",
        "",
        "- **S (Spec)** — the specification / contract: `requires`/`ensures`, "
        "`pre`/`post`, `forall`/`exists` declarations (the `Goal` clauses for pfwnCSP).",
        "- **A (Auxiliary)** — auxiliary `predicate`/`function`/`lemma`/`axiom` "
        "declarations (the `Def` predicate clauses for pfwnCSP).",
        "- **I (Internal)** — remaining internal proof annotations: loop "
        "invariants/variants, `assert`/`assume`, `havoc` (`I = Total − Spec − Aux`).",
        "",
        "`-` means no artifact was collected.",
        "",
        "Sources: **RelRL** `examples/los.md`, **WhyML** `examples/los_whyml.md`, "
        "**Boogie** `boogie_examples/burden_bpl.md`, **Origin** = source repo's own "
        "encoding where measured (ForEx 1–17, pfwnCSP 19–24, RHLE 25–52).",
        "",
        "| # | Example | RL S | RL A | RL I | RL T | WhyML S | WhyML A | WhyML I | WhyML T "
        "| Bgie S | Bgie A | Bgie I | Bgie T | Org S | Org A | Org I | Org T | Origin tool |",
        "|--:|---------|-----:|-----:|-----:|-----:|--------:|--------:|--------:|--------:"
        "|-------:|-------:|-------:|-------:|------:|------:|------:|------:|-------------|",
    ]
    blank = "| | **%s** " + "| " * len(TAGS) + "|"
    for rec in records:
        if rec[0] == "group":
            out.append(blank % rec[1])
        else:
            _, num, name, vals, tool = rec
            out.append(f"| {num} | {name} | " + " | ".join(fmt(v) for v in vals)
                       + f" | {tool} |")
    out.append("| | **Total (measured)** | "
               + " | ".join(f"**{sums[t]}**" for t in TAGS) + " | |")
    return "\n".join(out)


def tex_escape(s):
    return s.replace("_", r"\_").replace("&", r"\&")


def render_tex(records, sums):
    ncol = 2 + len(TAGS) + 1  # # , Example, 16 numbers, Tool
    out = [
        "% Annotation-burden catalog for the forall-exists benchmarks.",
        "% Auto-generated by make_catalog_table.py --latex (reads per-system los .md).",
        "% S=Spec (contract), A=Auxiliary (predicate/lemma/axiom), I=Internal",
        "% (loop invariants/asserts/havoc), T=Total. '-' = no artifact collected.",
        r"\begin{table}[h!]",
        r"\centering",
        r"\caption{Annotation burden across encodings for the $\forall\exists$ "
        r"benchmarks of Table~\ref{tab:Catalog}. For each tool: S=spec (contract), "
        r"A=auxiliary predicate/lemma/axiom declarations, I=internal proof "
        r"annotations (loop invariants/variants, asserts, havoc), T=total. "
        r"Origin is the source repo's own encoding where measured "
        r"(ForEx, pfwnCSP, RHLE).}",
        r"\label{tab:burden}",
        r"\resizebox{\textwidth}{!}{%",
        r"\begin{tabular}{rl|rrrr|rrrr|rrrr|rrrr|l}",
        r"\hline",
        r"& & \multicolumn{4}{c|}{\textbf{RelRL}} & \multicolumn{4}{c|}{\textbf{WhyML}}"
        r" & \multicolumn{4}{c|}{\textbf{Boogie}} & \multicolumn{4}{c|}{\textbf{Origin}}"
        r" & \\",
        r"\textbf{\#} & \textbf{Example} & S & A & I & T & S & A & I & T & S & A & I & T"
        r" & S & A & I & T & \textbf{Tool} \\",
        r"\hline\hline",
    ]
    for rec in records:
        if rec[0] == "group":
            out.append(r"\multicolumn{%d}{|l|}{\textbf{%s}} \\ \hline"
                       % (ncol, tex_escape(rec[1])))
        else:
            _, num, name, vals, tool = rec
            cells = " & ".join(fmt(v) for v in vals)
            out.append(f"{num} & {tex_escape(name)} & {cells} & {tex_escape(tool)} "
                       r"\\")
    out.append(r"\hline")
    totals = " & ".join(r"\textbf{%d}" % sums[t] for t in TAGS)
    out.append(r"\multicolumn{2}{|l|}{\textbf{Total (measured)}} & " + totals + r" & \\")
    out += [r"\hline", r"\end{tabular}}", r"\end{table}"]
    return "\n".join(out)


def main():
    records, sums = build()
    if "--latex" in sys.argv[1:] or "--tex" in sys.argv[1:]:
        print(render_tex(records, sums))
    else:
        print(render_md(records, sums))
    if warnings:
        print("\n".join(["", "<!-- WARNINGS:"] + warnings + ["-->"]), file=sys.stderr)


if __name__ == "__main__":
    sys.exit(main())
