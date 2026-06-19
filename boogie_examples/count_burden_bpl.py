#!/usr/bin/env python3
"""Count annotation burden in the Boogie (.bpl) example files, per example.

NOTE: this directory is called `boogie_examples` and contains Boogie (`.bpl`)
intermediate-verification-language files (there are no Dafny `.dfy` files).

Counting rule (mirrors examples/count_burden_whyml.py / count_los_rl.py):
  A line counts as one annotation if, after stripping leading whitespace (and an
  optional leading `free`), it begins with a Boogie annotation keyword. Multi-line
  clauses count as ONE. Executable statements other than the proof annotations,
  declarations (var/const/type/procedure/...), comments, and block-comment
  contents are excluded.

Categories (table columns), parallel to the .rl / WhyML los tables:
  Spec   -- requires, ensures, modifies   (incl. `free requires` / `free ensures`)
  Loop   -- invariant
  Pred   -- function                       (logic function declarations)
  Lemma  -- axiom
  Assert -- assert, assume
  Havoc  -- havoc                          (nondeterministic havoc; models calls)

Scope: every .bpl file under this directory; each file is one example, grouped by
its top-level category (all_all / all_exists).
"""

import os
import re
import sys
from collections import defaultdict

CATEGORIES = {
    "Spec":   ["requires", "ensures", "modifies"],
    "Loop":   ["invariant"],
    "Pred":   ["function"],
    "Lemma":  ["axiom"],
    "Assert": ["assert", "assume"],
    "Havoc":  ["havoc"],
}
CAT_ORDER = ["Spec", "Loop", "Pred", "Lemma", "Assert", "Havoc"]
KEYWORD_CATEGORY = {kw: cat for cat, kws in CATEGORIES.items() for kw in kws}

WORD_RE = re.compile(r"^([A-Za-z]\w*)\b")


def classify(line):
    stripped = line.lstrip()
    if stripped.startswith("free "):           # free requires / free ensures
        stripped = stripped[len("free "):].lstrip()
    m = WORD_RE.match(stripped)
    if not m:
        return None
    return KEYWORD_CATEGORY.get(m.group(1))


def count_file(path):
    counts = defaultdict(int)
    in_block = False
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if in_block:
                if "*/" in line:
                    in_block = False
                continue
            # ignore a line that opens an unterminated block comment
            stripped = line.lstrip()
            if stripped.startswith("/*") and "*/" not in line:
                in_block = True
                continue
            cat = classify(line)
            if cat:
                counts[cat] += 1
    return counts


def gather(root):
    examples = {}
    for dirpath, _dirs, files in os.walk(root):
        for f in sorted(files):
            if f.endswith(".bpl"):
                rel = os.path.relpath(os.path.join(dirpath, f), root)
                examples[rel] = count_file(os.path.join(dirpath, f))
    return examples


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
        out.append(f"{ex:<{name_w}}  " + "  ".join(f"{row[c]:>6}" for c in cols))
    out.append("-" * len(header))
    out.append(f"{'TOTAL':<{name_w}}  " + "  ".join(f"{grand[c]:>6}" for c in cols))
    return "\n".join(out)


def _md_table(examples, names):
    cols = CAT_ORDER + ["Total"]
    lines = ["| Example | " + " | ".join(cols) + " |",
             "|---------|" + "|".join(["------:"] * len(cols)) + "|"]
    grand = defaultdict(int)
    for ex, row in _accumulate(examples, names, grand):
        lines.append(f"| {ex} | " + " | ".join(str(row[c]) for c in cols) + " |")
    lines.append("| **Subtotal** | " + " | ".join(f"**{grand[c]}**" for c in cols) + " |")
    return "\n".join(lines), grand


def render_markdown(examples):
    groups = [
        ("All-All (Unary Equivalence)",
         sorted(e for e in examples if e.startswith("all_all" + os.sep))),
        ("All-Exists (Relational Equivalence/Properties)",
         sorted(e for e in examples if e.startswith("all_exists" + os.sep))),
    ]
    out = [
        "# Boogie (.bpl) — Annotation Burden Summary",
        "",
        "**Counting Rule:** A line counts as one annotation if, after stripping "
        "leading whitespace (and an optional `free`), it begins with a Boogie "
        "annotation keyword (multi-line clauses count as one). Comments and "
        "non-annotation statements/declarations are excluded.",
        "",
        "**Categories (table columns):**",
        "- **Spec** — `requires`, `ensures`, `modifies` (incl. `free requires`/`free ensures`)",
        "- **Loop** — `invariant`",
        "- **Pred** — `function`",
        "- **Lemma** — `axiom`",
        "- **Assert** — `assert`, `assume`",
        "- **Havoc** — `havoc`",
        "",
        "**Scope:** All `.bpl` files (one example each). Generated by `count_burden_bpl.py`.",
        "",
        "---",
        "",
    ]
    overall = defaultdict(int)
    cols = CAT_ORDER + ["Total"]
    for title, names in groups:
        if not names:
            continue
        table, grand = _md_table(examples, names)
        for c in cols:
            overall[c] += grand[c]
        out += [f"## {title}", "", table, "", "---", ""]
    out += [
        "## Grand Total",
        "",
        "| " + " | ".join(cols) + " |",
        "|" + "|".join(["------:"] * len(cols)) + "|",
        "| " + " | ".join(f"**{overall[c]}**" for c in cols) + " |",
    ]
    return "\n".join(out)


def main():
    root = os.path.dirname(os.path.abspath(__file__))
    examples = gather(root)
    if "--md" in sys.argv[1:]:
        print(render_markdown(examples))
    else:
        print(render_plain(examples))


if __name__ == "__main__":
    sys.exit(main())
