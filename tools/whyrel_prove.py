#!/usr/bin/env python3
"""whyrel-prove: portfolio batch discharge for WhyRel-generated .mlw files.

Runs `why3 prove -a split_vc` under a portfolio of provers, merges per-goal
results (goals are identified by their position in why3's deterministic task
order), and reports:
  - a per-prover and union summary table,
  - every portfolio-unproven goal with its source location and subgoal
    explanation, ready for the A/B/C triage:
      (A) countermodel  -> spec/code wrong (fix invariant/spec)
      (B) timeout       -> decompose: source Assert / seeded lemma instance
      (C) fast unknown  -> missing fact: source or theory lemma

Usage:
  whyrel_prove.py prog.mlw -L . -L ../../../stdlib [-T THEORY] [-t 60]
                  [-P z3 -P alt-ergo -P cvc5] [--sequential] [--json out.json]
"""

import argparse
import json
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

DEFAULT_PROVERS = ["alt-ergo", "cvc5", "z3"]

GOAL_RE = re.compile(
    r'^File "(?P<file>[^"]+)", (?P<loc>line \d+.*?):\s*$'
)
SUBGOAL_RE = re.compile(r"^Sub-goal (?P<expl>.*?) of goal (?P<vc>\S+)\.$")
GOALNAME_RE = re.compile(r"^Goal (?P<vc>\S+)\.$")
RESULT_RE = re.compile(
    r"^Prover result is: (?P<status>\w+)"
    r"(?: \((?P<time>[0-9.]+)s(?:, (?P<steps>\d+) steps)?\))?"
)


def run_prover(mlw, prover, args):
    cmd = ["why3", "prove", mlw, "-P", prover, "-t", str(args.timeout)]
    for inc in args.libdirs:
        cmd += ["-L", inc]
    if args.theory:
        cmd += ["-T", args.theory]
    if args.split:
        cmd += ["-a", "split_vc"]
    try:
        out = subprocess.run(
            cmd, capture_output=True, text=True, timeout=args.wall_limit
        )
        text = out.stdout + out.stderr
    except subprocess.TimeoutExpired as e:
        text = (e.stdout or "") + (e.stderr or "")
        print(f"[whyrel-prove] WARNING: {prover} hit wall limit; "
              f"partial results used", file=sys.stderr)
        return parse_output(text)
    goals = parse_output(text)
    if out.returncode != 0 and not goals:
        # why3 failed before producing any task (parse/type/effect error);
        # 0 goals here must not be reported as 0/0 success.
        errs = [l for l in out.stderr.splitlines()
                if l.strip() and not l.startswith("Warning")]
        msg = "\n  ".join(errs[-5:]) if errs else "(no diagnostic on stderr)"
        sys.exit(f"[whyrel-prove] ERROR: why3 prove -P {prover} failed to "
                 f"load {mlw} (exit {out.returncode}):\n  {msg}")
    return goals


def parse_output(text):
    """Return list of goal dicts in why3's (deterministic) task order."""
    goals, cur = [], None
    for line in text.splitlines():
        m = GOAL_RE.match(line)
        if m:
            cur = {"file": m["file"], "loc": m["loc"], "expl": "", "vc": ""}
            continue
        m = SUBGOAL_RE.match(line)
        if m and cur is not None:
            cur["expl"], cur["vc"] = m["expl"], m["vc"]
            continue
        m = GOALNAME_RE.match(line)
        if m and cur is None:
            cur = {"file": "", "loc": "", "expl": "", "vc": m["vc"]}
        if m and cur is not None and not cur["vc"]:
            cur["vc"] = m["vc"]
            continue
        m = RESULT_RE.match(line)
        if m and cur is not None:
            cur["status"] = m["status"]
            cur["time"] = float(m["time"]) if m["time"] else None
            goals.append(cur)
            cur = None
    return goals


def merge(results):
    """results: {prover: [goal,...]} -> unified per-goal table.

    Goals are merged positionally; why3 emits tasks in a deterministic order
    for a fixed .mlw + transformation, so index i is the same goal in every
    prover's list. Falls back gracefully if lists have unequal lengths
    (e.g. a prover crashed mid-run): the union is computed over the prefix.
    """
    provers = list(results)
    n = max(len(g) for g in results.values())
    table = []
    for i in range(n):
        row = None
        per = {}
        for p in provers:
            gs = results[p]
            if i < len(gs):
                per[p] = gs[i]
                if row is None:
                    row = {k: gs[i][k] for k in ("file", "loc", "expl", "vc")}
        statuses = {p: per[p]["status"] for p in per}
        valid_by = [p for p, s in statuses.items() if s == "Valid"]
        best = None
        if valid_by:
            best = min(valid_by, key=lambda p: per[p]["time"] or 1e9)
        row.update(
            statuses=statuses,
            proved=bool(valid_by),
            valid_by=valid_by,
            best=best,
            best_time=per[best]["time"] if best else None,
        )
        table.append(row)
    return table


def triage_hint(row):
    sts = set(row["statuses"].values())
    if "Unknown" in sts:
        return ("A/C? countermodel or missing fact: inspect with "
                "--check-ce; if no CE, add the missing lemma (C)")
    return ("B/C: portfolio-wide timeout. Try 10x budget; if still stuck, "
            "seed a source Assert with the literal instance of the needed "
            "fact, or add a theory lemma (prove it once)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mlw")
    ap.add_argument("-L", dest="libdirs", action="append", default=[])
    ap.add_argument("-T", dest="theory", default=None)
    ap.add_argument("-t", dest="timeout", type=int, default=60)
    ap.add_argument("-P", dest="provers", action="append", default=None)
    ap.add_argument("--no-split", dest="split", action="store_false")
    ap.add_argument("--sequential", action="store_true",
                    help="run provers one after another (clean timings)")
    ap.add_argument("--wall-limit", type=int, default=7200)
    ap.add_argument("--json", dest="json_out", default=None)
    args = ap.parse_args()
    provers = args.provers or DEFAULT_PROVERS

    results = {}
    if args.sequential:
        for p in provers:
            results[p] = run_prover(args.mlw, p, args)
    else:
        with ThreadPoolExecutor(max_workers=len(provers)) as ex:
            futs = {p: ex.submit(run_prover, args.mlw, p, args)
                    for p in provers}
            results = {p: f.result() for p, f in futs.items()}

    table = merge(results)
    total = len(table)
    proved = sum(1 for r in table if r["proved"])

    print(f"\n== whyrel-prove: {args.mlw}"
          + (f" -T {args.theory}" if args.theory else ""))
    for p in provers:
        ok = sum(1 for r in table if r["statuses"].get(p) == "Valid")
        print(f"   {p:>10}: {ok}/{total}")
    print(f"   {'UNION':>10}: {proved}/{total}"
          + ("  -- all goals discharged" if proved == total else ""))

    attribution = {}
    for r in table:
        if r["proved"] and len(r["valid_by"]) == 1:
            attribution[r["valid_by"][0]] = (
                attribution.get(r["valid_by"][0], 0) + 1)
    if attribution:
        uniq = ", ".join(f"{p}: {n}" for p, n in sorted(attribution.items()))
        print(f"   uniquely proved by -- {uniq}")

    unproved = [r for r in table if not r["proved"]]
    if unproved:
        print(f"\n-- {len(unproved)} unproven goal(s):")
        for r in unproved:
            sts = " ".join(f"{p}={s}" for p, s in r["statuses"].items())
            print(f"   {r['loc']}")
            print(f"     [{r['expl'] or r['vc']}]  {sts}")
            print(f"     hint: {triage_hint(r)}")

    if args.json_out:
        with open(args.json_out, "w") as f:
            json.dump({"file": args.mlw, "theory": args.theory,
                       "timeout": args.timeout, "provers": provers,
                       "total": total, "proved": proved,
                       "goals": table}, f, indent=1)
        print(f"\n(json written to {args.json_out})")

    sys.exit(0 if proved == total else 1)


if __name__ == "__main__":
    main()
