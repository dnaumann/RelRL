#!/usr/bin/env python3
"""Run WhyRel's default proof command on valid Hypra, RHLE, Itzhaky, and PCsat candidates.

Exclude specifications documented as invalid in examples/all_exists/README.md.
Valid candidates remain included even if automatic proof currently fails.

Run from any directory: python3 /path/to/RelRL/test_whyrel_prove.py
Requires a built bin/whyrel and configured Alt-Ergo/Z3 provers.
"""

from collections import Counter
from pathlib import Path
import os
import re
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
EXAMPLES = ROOT / "examples" / "all_exists"
GROUPS = ("Hypra", "RHLE", "Itzhaky", "PCsat")

# Explicit exclusions from examples/all_exists/README.md, rather than filtering
# by solver results or occurrences of "false" in the source (which may be valid).
INVALID_EXAMPLES = frozenset({
    "RHLE/API_Refinement/Add3_Shuffled",
    "RHLE/API_Refinement/Conditional_Nonrefinement",
    "RHLE/API_Refinement/Loop_Nonrefinement",
    "RHLE/API_Refinement/Simple_Nonrefinement",
    "RHLE/Delimited_Release/Parity_No_Dr",
    "RHLE/Delimited_Release/Wallet_No_Dr",
    "RHLE/GNI/Denning2",
    "RHLE/GNI/Denning3",
    "RHLE/GNI/Nondet_Leak",
    "RHLE/GNI/Nondet_Leak2",
    "RHLE/GNI/Simple_Leak",
    "RHLE/GNI/Smith1",
    "RHLE/Param_Usage/Even_Odd",
})


def candidate_sources():
    """Return proof candidates and the documented-invalid sources skipped."""
    sources = sorted(source for group in GROUPS
                     for source in (EXAMPLES / group).rglob("*.rl"))
    candidates, skipped = [], []
    for source in sources:
        example = source.parent.relative_to(EXAMPLES).as_posix()
        (skipped if example in INVALID_EXAMPLES else candidates).append(source)
    return candidates, skipped


def stop_process(process):
    """Stop WhyRel and its children, including any active prover processes."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return process.communicate()


def proof_counts(output):
    """Keep separate pass counts; partial solver results are not combined."""
    counts = {}
    prover = None
    for line in output.splitlines():
        if line.startswith("Running "):
            prover = "Alt-Ergo" if "Alt-Ergo,," in line else "Z3"
            counts[prover] = Counter()
        match = re.match(r"Prover result is: ([^(\n]+)", line)
        if match and prover:
            counts[prover][match.group(1).strip().rstrip(".")] += 1
    return counts


def run_example(source):
    started = time.monotonic()
    command = [str(ROOT / "bin" / "whyrel"), "prove", "-all-exists", str(source)]
    try:
        process = subprocess.Popen(
            command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, errors="replace", start_new_session=True,
        )
    except OSError as error:
        return "ERROR", {}, 0.0, str(error)
    try:
        output, diagnostics = process.communicate()
        status = {0: "FULLY PROVED", 2: "NOT FULLY PROVED"}.get(
            process.returncode, "ERROR"
        )
    except KeyboardInterrupt:
        stop_process(process)
        raise
    counts = proof_counts(output)
    details = []
    for prover, answers in counts.items():
        failures = ", ".join(
            f"{answer}: {count}" for answer, count in sorted(answers.items())
            if answer != "Valid"
        )
        if failures:
            details.append(f"{prover}: {failures}")
    if status == "ERROR":
        details.append(f"exit {process.returncode}")
        details.append(diagnostics.strip() or output.strip() or "No diagnostics")
    elif not any(counts.values()):
        details.append("No VC results reported")
    return status, counts, time.monotonic() - started, "; ".join(details)


def print_summary(results):
    width = max([len("Example")] + [len(name) for name, _ in results])
    print("\nValid/total VCs for each prover pass; '-' means not run.")
    print(f"{'Example':<{width}}  {'Status':<16}  {'Alt-Ergo':>9}  {'Z3':>9}  {'Seconds':>8}")
    print("-" * (width + 52))
    for name, (status, counts, elapsed, details) in results:
        def count(prover):
            if prover not in counts:
                return "-"
            answers = counts[prover]
            return f"{answers['Valid']}/{sum(answers.values())}"
        print(f"{name:<{width}}  {status:<16}  {count('Alt-Ergo'):>9}  {count('Z3'):>9}  {elapsed:8.1f}")
        if details:
            for line in details.splitlines():
                print(f"  {line}")
    totals = Counter(result[0] for _, result in results)
    print("\n" + ", ".join(f"{status}: {number}" for status, number in sorted(totals.items())))
    print("FULLY PROVED means whyrel prove exited 0: one prover proved every VC.")
    print("Complementary partial proofs are not merged. ERROR is not a proof failure.")


def main():
    executable = ROOT / "bin" / "whyrel"
    if not executable.is_file() or not os.access(executable, os.X_OK):
        print(f"Build WhyRel first with make: executable unavailable at {executable}", file=sys.stderr)
        return 1
    missing = [group for group in GROUPS if not (EXAMPLES / group).is_dir()]
    if missing:
        print(f"Missing example directories: {', '.join(missing)}", file=sys.stderr)
        return 1
    # Keep all variants of valid examples, including Add3_Sorted/prog_vars.rl.
    sources, skipped = candidate_sources()
    print(f"Testing {len(sources)} candidates; skipping {len(skipped)} documented-invalid programs.")
    for source in skipped:
        print(f"  SKIPPED (invalid specification): {source.relative_to(EXAMPLES)}")
    results = []
    interrupted = False
    try:
        for index, source in enumerate(sources, 1):
            name = str(source.relative_to(EXAMPLES))
            print(f"[{index}/{len(sources)}] {name}", flush=True)
            result = run_example(source)
            results.append((name, result))
            print(f"  {result[0]} ({result[2]:.1f}s)", flush=True)
    except KeyboardInterrupt:
        interrupted = True
        print("\nInterrupted; showing completed examples only.")
    print_summary(results)
    if interrupted:
        return 130
    return 0 if all(result[0] == "FULLY PROVED" for _, result in results) else 1


if __name__ == "__main__":
    sys.exit(main())
