#!/usr/bin/env python3
"""Reformat Boogie (.bpl) files so every annotation keyword starts its own line.

The line-based annotation counter (count_burden_bpl.py) only counts a keyword
when it is the first token on a line. Hand-written Boogie often packs several
annotations onto one physical line, e.g.

    { havoc z1; y1 := y1 - 1; }
    havoc r; assume 0 <= r && r < 11;
    requires x >= 0; ensures r == 2 * x * x;

This rewrites such lines so each keyword (`havoc`, `assert`, `assume`, `requires`,
`ensures`, `modifies`, `invariant`, `function`, `axiom`) begins a new line:

    {
    havoc z1; y1 := y1 - 1; }
    havoc r;
    assume 0 <= r && r < 11;
    requires x >= 0;
    ensures r == 2 * x * x;

Inserting newlines before statement/clause keywords is semantics-preserving for
Boogie (statements end with `;`, layout is insignificant). Keywords inside `//`
and `/* ... */` comments, and a keyword right after `free`, are left untouched.

Usage:
    reformat_keywords.py --dry FILE...   # show how many splits per file, no write
    reformat_keywords.py FILE...         # rewrite the files in place
    reformat_keywords.py                 # rewrite all .bpl under this directory
"""

import os
import re
import sys

KEYWORDS = ["requires", "ensures", "modifies", "invariant",
            "assert", "assume", "havoc", "function", "axiom"]
KW_RE = re.compile(r"\b(" + "|".join(KEYWORDS) + r")\b")


def comment_start(code):
    """Index where a trailing comment begins on this (non-block) line, or len."""
    idxs = [i for i in (code.find("//"), code.find("/*")) if i != -1]
    return min(idxs) if idxs else len(code)


def reformat_line(line):
    """Return the (possibly multi-line) reformatting of one code line, and the
    number of splits introduced."""
    nl = "\n" if line.endswith("\n") else ""
    body = line[:-1] if nl else line

    cstart = comment_start(body)
    code, tail = body[:cstart], body[cstart:]

    indent = code[:len(code) - len(code.lstrip())]
    first_tok = len(indent)  # index of the first non-space char

    # Collect keyword starts to split on: any keyword not the first token and
    # not immediately preceded by `free `.
    splits = []
    for m in KW_RE.finditer(code):
        if m.start() == first_tok:
            continue
        before = code[:m.start()].rstrip()
        if before.endswith("free"):
            continue
        splits.append(m.start())

    if not splits:
        return line, 0

    segments = []
    prev = 0
    for s in splits:
        segments.append(code[prev:s].rstrip())
        prev = s
    segments.append(code[prev:])
    new_code = ("\n" + indent).join(segments)
    return new_code + tail + nl, len(splits)


def reformat_text(text):
    out = []
    splits = 0
    in_block = False
    for line in text.splitlines(keepends=True):
        s = line.lstrip()
        if in_block:
            out.append(line)
            if "*/" in line:
                in_block = False
            continue
        if s.startswith("/*") and "*/" not in line:
            in_block = True
            out.append(line)
            continue
        new, n = reformat_line(line)
        splits += n
        out.append(new)
    return "".join(out), splits


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    dry = "--dry" in sys.argv[1:]

    if args:
        files = args
    else:
        root = os.path.dirname(os.path.abspath(__file__))
        files = []
        for dp, _d, fs in os.walk(root):
            files += [os.path.join(dp, f) for f in fs if f.endswith(".bpl")]
        files.sort()

    total = 0
    for path in files:
        text = open(path, encoding="utf-8", errors="replace").read()
        new, n = reformat_text(text)
        total += n
        if n and not dry:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(new)
        if n:
            print(f"{'would split' if dry else 'split':>12} {n:>3}  "
                  f"{os.path.relpath(path)}")
    print(f"\nTotal splits: {total}" + ("  (dry run, no files written)" if dry else ""))


if __name__ == "__main__":
    sys.exit(main())
