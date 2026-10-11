#!/usr/bin/env python3
"""Print prover timing stats per module (Why3 theory) for a saved Why3 session.

Usage:
  examples/session_times.py SESSION [SESSION ...] [--by-prover]

SESSION is a session directory (e.g. examples/all_exists/tiling/prog) or a
why3session.xml file inside one.

Times are the prover times recorded in why3session.xml when each goal was last
run; run `why3 replay -f SESSION` first to refresh them. Time spent applying
transformations (split_vc, inline_goal, ...) is not recorded by Why3.

Columns:
  VCs      -- top-level goals in the module
  Proved   -- how many of those goals Why3 marks as proved
  Attempts -- prover calls recorded (includes calls under transformations)
  Valid(s) -- total time of attempts that returned "valid"
  All(s)   -- total time of all attempts, including failed/timed-out ones
  Max(s)   -- slowest single attempt
"""

import argparse
import gzip
import os
import sys
import xml.etree.ElementTree as ET


def load_session(path):
    if os.path.isdir(path):
        for name in ("why3session.xml", "why3session.xml.gz"):
            candidate = os.path.join(path, name)
            if os.path.exists(candidate):
                path = candidate
                break
        else:
            sys.exit(f"error: no why3session.xml in {path}")
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rb") as f:
        return ET.parse(f).getroot()


def prover_names(root):
    return {p.get("id"): f'{p.get("name")} {p.get("version")}'
            for p in root.findall("prover")}


def attempts(elem):
    """Yield (prover id, status, time) for every proof attempt under elem."""
    for proof in elem.iter("proof"):
        result = proof.find("result")
        if result is None:  # attempt scheduled but never run
            continue
        yield proof.get("prover"), result.get("status"), float(result.get("time", 0))


def stats(rows):
    times = [t for _, _, t in rows]
    return (len(rows),
            sum(t for _, s, t in rows if s == "valid"),
            sum(times),
            max(times, default=0.0))


def module_rows(root, by_prover):
    provers = prover_names(root)
    files = root.findall("file")
    for f in files:
        fname = f.get("name")
        if fname is None:
            path = f.find("path")
            fname = path.get("name") if path is not None else "?"
        for th in f.findall("theory"):
            name = th.get("name")
            if len(files) > 1:
                name = f"{os.path.basename(fname)}:{name}"
            goals = th.findall("goal")
            proved = sum(g.get("proved") == "true" for g in goals)
            rows = list(attempts(th))
            if by_prover:
                for pid in sorted({p for p, _, _ in rows}, key=int):
                    sub = [r for r in rows if r[0] == pid]
                    yield (name, provers.get(pid, pid), len(goals), proved) + stats(sub)
            else:
                yield (name, None, len(goals), proved) + stats(rows)


def print_table(title, rows, by_prover):
    header = ["Module"] + (["Prover"] if by_prover else []) + \
             ["VCs", "Proved", "Attempts", "Valid(s)", "All(s)", "Max(s)"]
    body = []
    for name, prover, vcs, proved, n, valid, allt, mx in rows:
        body.append([name] + ([prover] if by_prover else []) +
                    [str(vcs), str(proved), str(n),
                     f"{valid:.2f}", f"{allt:.2f}", f"{mx:.2f}"])
    if not by_prover and rows:
        body.append(["TOTAL",
                     str(sum(r[2] for r in rows)), str(sum(r[3] for r in rows)),
                     str(sum(r[4] for r in rows)),
                     f"{sum(r[5] for r in rows):.2f}",
                     f"{sum(r[6] for r in rows):.2f}",
                     f"{max(r[7] for r in rows):.2f}"])
    ntext = 2 if by_prover else 1
    widths = [max(len(row[i]) for row in [header] + body) for i in range(len(header))]

    def fmt(row):
        return "  ".join(c.ljust(w) if i < ntext else c.rjust(w)
                         for i, (c, w) in enumerate(zip(row, widths)))

    print(title)
    print(fmt(header))
    print("  ".join("-" * w for w in widths))
    for i, row in enumerate(body):
        if not by_prover and i == len(body) - 1:
            print("  ".join("-" * w for w in widths))
        print(fmt(row))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("sessions", nargs="+", metavar="SESSION",
                    help="session directory or why3session.xml file")
    ap.add_argument("--by-prover", action="store_true",
                    help="split each module's stats by prover")
    args = ap.parse_args()
    for i, path in enumerate(args.sessions):
        if i:
            print()
        rows = list(module_rows(load_session(path), args.by_prover))
        print_table(path, rows, args.by_prover)


if __name__ == "__main__":
    main()
