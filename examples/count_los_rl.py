#!/usr/bin/env python3
"""Count lines of spec (los) in .rl files, per example, broken down by keyword category.

Counting rule (matches examples/los.md):
  A line counts as one line of spec if, after stripping leading whitespace,
  it begins with one of the recognized annotation keywords.

Categories / keywords:
  Spec clauses:   requires, ensures, effects, reads, writes
  Loop/iteration: invariant, variant
  Named formulas: predicate, lemma, axiom
  Relational:     coupling
  Assertions:     assert, Assert, assume, Assume, HavocR, and `{{...}}` blocks

An "example" is the directory that directly contains the .rl file(s); all .rl
files in one directory (e.g. the multiple modules of stack/Kruskal/SSSP) are
summed into a single example.

Excluded files (work-in-progress, not part of the los.md totals): wip.rl
"""

import os
import re
import sys
from collections import defaultdict

CATEGORIES = {
    "Spec":   ["requires", "ensures", "effects", "reads", "writes"],
    "Loop":   ["invariant", "variant"],
    "Pred":   ["predicate", "coupling"],
    "Lemma":  ["lemma", "axiom"],
    "Assert": ["assert", "Assert", "assume", "Assume"],
    "Havoc":  ["HavocR"],
}

CAT_ORDER = ["Spec", "Loop", "Pred", "Lemma", "Assert", "Havoc"]

KEYWORD_CATEGORY = {kw: cat for cat, kws in CATEGORIES.items() for kw in kws}

WORD_RE = re.compile(r"^([A-Za-z]\w*)\b")

EXCLUDE_FILES = {"wip.rl"}


def classify(line):
    """Return the category if the line is a spec line, else None."""
    stripped = line.lstrip()
    if not stripped:
        return None
    if stripped.startswith("{{"):
        return "Assert"
    m = WORD_RE.match(stripped)
    if not m:
        return None
    return KEYWORD_CATEGORY.get(m.group(1))


def gather(root):
    # example dir -> {category -> count}
    examples = defaultdict(lambda: defaultdict(int))

    for dirpath, _dirs, files in os.walk(root):
        rl_files = [f for f in files if f.endswith(".rl") and f not in EXCLUDE_FILES]
        if not rl_files:
            continue
        rel = os.path.relpath(dirpath, root)
        for f in sorted(rl_files):
            with open(os.path.join(dirpath, f), encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    cat = classify(line)
                    if cat:
                        examples[rel][cat] += 1
    return examples


def count_file(path):
    counts = defaultdict(int)
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            cat = classify(line)
            if cat:
                counts[cat] += 1
    return counts


def render_single(path, counts):
    cols = CAT_ORDER + ["Total"]
    row = {c: counts.get(c, 0) for c in CAT_ORDER}
    row["Total"] = sum(counts.values())
    w = max(len(c) for c in cols)
    out = [path, ""]
    for c in cols:
        out.append(f"  {c:<{w}}  {row[c]:>5}")
    return "\n".join(out)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    flags = [a for a in sys.argv[1:] if a.startswith("-")]

    # Per-file mode: one or more .rl paths given as arguments.
    if args:
        blocks = []
        for path in args:
            if not os.path.exists(path):
                print(f"error: file not found: {path}", file=sys.stderr)
                return 1
            counts = count_file(path)
            if "--md" in flags:
                row = {c: counts.get(c, 0) for c in CAT_ORDER}
                row["Total"] = sum(counts.values())
                cols = CAT_ORDER + ["Total"]
                if not blocks:
                    blocks.append("| File | " + " | ".join(cols) + " |")
                    blocks.append("|------|" + "|".join(["------:"] * len(cols)) + "|")
                blocks.append(f"| {path} | " + " | ".join(str(row[c]) for c in cols) + " |")
            else:
                blocks.append(render_single(path, counts))
        print("\n\n".join(blocks) if "--md" not in flags else "\n".join(blocks))
        return

    # Directory mode: scan all .rl files under this script's directory.
    root = os.path.dirname(os.path.abspath(__file__))
    examples = gather(root)

    if "--md" in flags:
        print(render_markdown(examples))
    else:
        print(render_plain(examples))


def _accumulate(examples, names, grand):
    rows = []
    for ex in names:
        counts = examples[ex]
        row = {c: counts.get(c, 0) for c in CAT_ORDER}
        row["Total"] = sum(counts.values())
        for c in CAT_ORDER:
            grand[c] += row[c]
        grand["Total"] += row["Total"]
        rows.append((ex, row))
    return rows


def render_plain(examples):
    name_w = max(len("Example"), max(len(e) for e in examples))
    cols = CAT_ORDER + ["Total"]
    header = f"{'Example':<{name_w}}  " + "  ".join(f"{c:>6}" for c in cols)
    out = [header, "-" * len(header)]
    grand = defaultdict(int)
    for ex, row in _accumulate(examples, sorted(examples), grand):
        cells = [f"{row[c]:>6}" for c in cols]
        out.append(f"{ex:<{name_w}}  " + "  ".join(cells))
    out.append("-" * len(header))
    totals = [f"{grand[c]:>6}" for c in cols]
    out.append(f"{'TOTAL':<{name_w}}  " + "  ".join(totals))
    return "\n".join(out)


def _md_table(examples, names):
    cols = CAT_ORDER + ["Total"]
    lines = ["| Example | " + " | ".join(cols) + " |",
             "|---------|" + "|".join(["------:"] * len(cols)) + "|"]
    grand = defaultdict(int)
    for ex, row in _accumulate(examples, names, grand):
        cells = [str(row[c]) for c in cols]
        lines.append(f"| {ex} | " + " | ".join(cells) + " |")
    totals = [f"**{grand[c]}**" for c in cols]
    lines.append("| **Subtotal** | " + " | ".join(totals) + " |")
    return "\n".join(lines), grand


def render_markdown(examples):
    groups = [
        ("All-All Examples (Unary Equivalence)",
         sorted(e for e in examples if e.startswith("all_all/"))),
        ("All-Exists Examples (Relational Equivalence/Properties)",
         sorted(e for e in examples if e.startswith("all_exists/"))),
    ]

    out = [
        "# Lines of Spec (los) Summary",
        "",
        "**Counting Rule:** A line counts as one line of spec if, after stripping "
        "leading whitespace, it begins with one of the recognized annotation keywords.",
        "",
        "**Categories (table columns):**",
        "- **Spec** — `requires`, `ensures`, `effects`, `reads`, `writes`",
        "- **Loop** — `invariant`, `variant`",
        "- **Pred** — `predicate`, `coupling`",
        "- **Lemma** — `lemma`, `axiom`",
        "- **Assert** — `assert`, `Assert`, `assume`, `Assume`, `{{...}}`",
        "- **Havoc** — `HavocR`",
        "",
        "**Excluded:** Alignment syntax (`|_`, `_|`, `<|`, `|>`, `[<`, `>]`, `[>`, "
        "`<]`), comments, and work-in-progress files (`wip.rl`).",
        "",
        "**Scope:** All `.rl` files under `examples/`. Each example aggregates every "
        "`.rl` file in its directory (e.g. the multiple modules of `stack`, `Kruskal`, "
        "`SSSP`). Generated automatically by `count_los.py`.",
        "",
        "---",
        "",
    ]

    overall = defaultdict(int)
    for title, names in groups:
        table, grand = _md_table(examples, names)
        for c in CAT_ORDER + ["Total"]:
            overall[c] += grand[c]
        out += [f"## {title}", "", table, "", "---", ""]

    cols = CAT_ORDER + ["Total"]
    out += [
        "## Grand Total",
        "",
        "| " + " | ".join(cols) + " |",
        "|" + "|".join(["------:"] * len(cols)) + "|",
        "| " + " | ".join(f"**{overall[c]}**" for c in cols) + " |",
    ]
    return "\n".join(out)


if __name__ == "__main__":
    sys.exit(main())
