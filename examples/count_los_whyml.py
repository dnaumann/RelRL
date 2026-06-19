#!/usr/bin/env python3
"""Count annotation burden in the *generated* WhyML (.mlw) files, per example.

For each example, the generated WhyML file is the one produced by WhyRel: the
target of the Makefile rule whose recipe runs `$(WHYREL) ... -o $@ ...`. This
script discovers that target per example (resolving simple Makefile variables
such as `$(PROG)`), then counts annotation lines in the generated file.

Counting rule (mirrors examples/count_los_rl.py):
  A line counts as one annotation if, after stripping leading whitespace, it
  begins with a WhyML annotation keyword. Multi-line clauses (e.g. an `ensures {
  match ... }`) count as ONE -- only the keyword-initiated line is counted. This
  excludes formula continuation lines (e.g. a wrapped `forall ...`), executable
  code, and module/use/type boilerplate.

Categories (table columns), parallel to the .rl los categories:
  Spec   -- requires, ensures, reads, writes, diverges, raises, returns
  Loop   -- invariant, variant   (loop invariants/variants + type invariants)
  Pred   -- predicate, function  (logic predicate / function declarations)
  Lemma  -- lemma, axiom, goal
  Assert -- assert, assume, check

Scope: every example directory under examples/ that has a Makefile producing a
WhyML file. Generated files that do not exist on disk are reported and skipped.
"""

import os
import re
import sys
from collections import defaultdict

CATEGORIES = {
    "Spec":   ["requires", "ensures", "reads", "writes", "diverges", "raises", "returns"],
    "Loop":   ["invariant", "variant"],
    "Pred":   ["predicate", "function"],
    "Lemma":  ["lemma", "axiom", "goal"],
    "Assert": ["assert", "assume", "check"],
}
CAT_ORDER = ["Spec", "Loop", "Pred", "Lemma", "Assert"]
KEYWORD_CATEGORY = {kw: cat for cat, kws in CATEGORIES.items() for kw in kws}

WORD_RE = re.compile(r"^([A-Za-z]\w*)\b")
VAR_RE = re.compile(r"^\s*([A-Za-z_]\w*)\s*[:?]?=\s*(.*?)\s*$")
RULE_RE = re.compile(r"^([^\t#:=]+\.mlw)\s*:")


def resolve_vars(text, variables):
    for _ in range(5):
        m = re.search(r"\$\((\w+)\)", text)
        if not m:
            break
        text = text.replace(m.group(0), variables.get(m.group(1), ""))
    return text


def generated_target(makefile):
    """Return the WhyML filename produced by `whyrel -o` in this Makefile."""
    lines = open(makefile, encoding="utf-8", errors="replace").read().splitlines()
    variables = {}
    for ln in lines:
        if ln.startswith("\t") or ln.lstrip().startswith("#"):
            continue
        m = VAR_RE.match(ln)
        if m:
            variables[m.group(1)] = m.group(2)
    for i, ln in enumerate(lines):
        if ln.startswith("\t") or ln.lstrip().startswith("#"):
            continue
        m = RULE_RE.match(ln)
        if not m:
            continue
        recipe = []
        j = i + 1
        while j < len(lines) and lines[j].startswith("\t"):
            recipe.append(lines[j])
            j += 1
        if any("WHYREL" in r and "-o" in r for r in recipe):
            return resolve_vars(m.group(1).strip(), variables)
    return None


def classify(line):
    stripped = line.lstrip()
    m = WORD_RE.match(stripped)
    if not m:
        return None
    return KEYWORD_CATEGORY.get(m.group(1))


def count_file(path):
    counts = defaultdict(int)
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            cat = classify(line)
            if cat:
                counts[cat] += 1
    return counts


def gather(root):
    examples = {}
    missing = []
    for dirpath, _dirs, files in os.walk(root):
        if "Makefile" not in files or os.path.abspath(dirpath) == os.path.abspath(root):
            continue
        target = generated_target(os.path.join(dirpath, "Makefile"))
        if not target:
            continue
        gen_path = os.path.join(dirpath, target)
        rel = os.path.relpath(dirpath, root)
        if not os.path.exists(gen_path) or os.path.getsize(gen_path) == 0:
            missing.append(os.path.relpath(gen_path, root))
            continue
        examples[rel] = count_file(gen_path)
    return examples, missing


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


def render_plain(examples, missing):
    name_w = max(len("Example"), max(len(e) for e in examples))
    cols = CAT_ORDER + ["Total"]
    header = f"{'Example':<{name_w}}  " + "  ".join(f"{c:>6}" for c in cols)
    out = [header, "-" * len(header)]
    grand = defaultdict(int)
    for ex, row in _accumulate(examples, sorted(examples), grand):
        out.append(f"{ex:<{name_w}}  " + "  ".join(f"{row[c]:>6}" for c in cols))
    out.append("-" * len(header))
    out.append(f"{'TOTAL':<{name_w}}  " + "  ".join(f"{grand[c]:>6}" for c in cols))
    if missing:
        out.append("")
        out.append(f"Skipped (generated file not on disk): {', '.join(missing)}")
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


def render_markdown(examples, missing):
    groups = [
        ("All-All (Unary Equivalence)",
         sorted(e for e in examples if e.startswith("all_all" + os.sep))),
        ("All-Exists (Relational Equivalence/Properties)",
         sorted(e for e in examples if e.startswith("all_exists" + os.sep))),
    ]
    out = [
        "# Generated WhyML — Annotation Burden Summary",
        "",
        "**Counting Rule:** A line counts as one annotation if, after stripping "
        "leading whitespace, it begins with a WhyML annotation keyword "
        "(multi-line clauses count as one). The generated `.mlw` per example is the "
        "`whyrel -o` target named in its Makefile.",
        "",
        "**Categories (table columns):**",
        "- **Spec** — `requires`, `ensures`, `reads`, `writes`, `diverges`, `raises`, `returns`",
        "- **Loop** — `invariant`, `variant`",
        "- **Pred** — `predicate`, `function`",
        "- **Lemma** — `lemma`, `axiom`, `goal`",
        "- **Assert** — `assert`, `assume`, `check`",
        "",
        "**Scope:** Generated WhyML files only. Generated by `count_burden_whyml.py`.",
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
    if missing:
        out += ["", f"_Skipped (generated file not on disk): {', '.join(missing)}_"]
    return "\n".join(out)


def main():
    root = os.path.dirname(os.path.abspath(__file__))
    examples, missing = gather(root)
    if not examples:
        print("No generated WhyML files found.", file=sys.stderr)
        return 1
    if "--md" in sys.argv[1:]:
        print(render_markdown(examples, missing))
    else:
        print(render_plain(examples, missing))


if __name__ == "__main__":
    sys.exit(main())
