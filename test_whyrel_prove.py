#!/usr/bin/env python3
"""Run WhyRel's default proof command on every all-exists example.

Documented-invalid specifications are tested as negative controls. The stack
example is compiled as one program from its six source files. Results and logs
are saved in experiments/all_exists_proofs for focused follow-up. Failed prover
passes stop at the first failed VC; their counts are partial.

Run from any directory: python3 /path/to/RelRL/test_whyrel_prove.py
Requires a built bin/whyrel and configured Alt-Ergo/Z3 provers.
"""

from collections import Counter
from pathlib import Path
import os
import hashlib
import json
import re
import signal
import shlex
import tempfile
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
EXAMPLES = ROOT / "examples" / "all_exists"
REPORTS = ROOT / "experiments" / "all_exists_proofs"
STACK_FILES = ("stack.rl", "arraystack.rl", "liststack.rl", "relstack.rl", "client.rl", "cell.rl")

# Negative controls from examples/all_exists/README.md, rather than filtering
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


def example_sources(source):
    """Keep the stack compilation unit consistent with its Makefile."""
    if source == EXAMPLES / "stack" / "stack.rl":
        return [source.parent / name for name in STACK_FILES]
    return [source]


def is_invalid(source):
    return source.parent.relative_to(EXAMPLES).as_posix() in INVALID_EXAMPLES


def candidate_sources():
    """Discover all programs, including negative controls and WIP variants."""
    fragments = {EXAMPLES / "stack" / name for name in STACK_FILES[1:]}
    sources = sorted(source for source in EXAMPLES.rglob("*.rl")
                     if source not in fragments)
    return sources, []


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


def run_pass(command):
    """A failed VC rules out a complete pass; stop without proving the rest."""
    lines = []
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as diagnostics:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
            stderr=diagnostics, text=True, errors="replace", start_new_session=True)
        stopped = False
        try:
            for line in process.stdout:
                lines.append(line)
                if line.startswith("Prover result is:") and not line.startswith("Prover result is: Valid"):
                    stopped = True
                    tail, _ = stop_process(process)
                    lines.append(tail or "")
                    break
            process.wait()
        except BaseException:
            stop_process(process)
            raise
        finally:
            process.stdout.close()
        diagnostics.seek(0)
        return (2 if stopped else process.returncode), "".join(lines), diagnostics.read(), stopped


def run_example(source):
    started = time.monotonic()
    REPORTS.mkdir(parents=True, exist_ok=True)
    # Retain the translation for the Z3 fallback after stopping Alt-Ergo early.
    with tempfile.TemporaryDirectory(prefix="whyrel-proof-test-") as directory:
        generated = Path(directory) / "prog.mlw"
        command = [str(ROOT / "bin" / "whyrel"), "prove", "-all-exists",
                   *map(str, example_sources(source)), "-o", str(generated)]
        try:
            code, output, diagnostics, stopped = run_pass(command)
            if stopped:
                # Reuse the exact default command printed by WhyRel; change only
                # the prover as WhyRel's normal fallback would do.
                commands = [shlex.split(line[len("Running "):]) for line in output.splitlines()
                            if line.startswith("Running ")]
                fallback = commands[-1]
                if "Alt-Ergo,," in fallback:
                    fallback[fallback.index("Alt-Ergo,,")] = "Z3,,"
                    code, extra, errors, _ = run_pass(fallback)
                    output += "Running " + shlex.join(fallback) + "\n" + extra
                    diagnostics += errors
            status = {0: "FULLY PROVED", 2: "NOT FULLY PROVED"}.get(code, "ERROR")
        except OSError as error:
            return "ERROR", {}, time.monotonic() - started, str(error)
    log = REPORTS / (source.relative_to(EXAMPLES).as_posix().replace("/", "__") + ".log")
    log.write_text("Command: " + repr(command) + "\n" + output + "\nDiagnostics:\n" + diagnostics)
    if is_invalid(source):
        status = {"FULLY PROVED": "UNEXPECTEDLY PROVED",
                  "NOT FULLY PROVED": "EXPECTED UNPROVED"}.get(status, status)
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
        details.append(f"exit {code}")
        details.append(diagnostics.strip() or output.strip() or "No diagnostics")
    elif not any(counts.values()):
        details.append("No VC results reported")
    return status, counts, time.monotonic() - started, "; ".join(details)


def print_summary(results):
    width = max([len("Example")] + [len(name) for name, _ in results])
    print("\nValid/attempted VCs; failed passes stop at their first failed VC; '-' means not run.")
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
    candidates = [result for name, result in results if not is_invalid(EXAMPLES / name)]
    print(f"Automatically proved {sum(r[0] == 'FULLY PROVED' for r in candidates)}/{len(candidates)} programs excluding negative controls.")
    print("FULLY PROVED means one prover proved every VC with WhyRel's default flags.")


def main():
    executable = ROOT / "bin" / "whyrel"
    if not executable.is_file() or not os.access(executable, os.X_OK):
        print(f"Build WhyRel first with make: executable unavailable at {executable}", file=sys.stderr)
        return 1
    if not EXAMPLES.is_dir():
        print(f"Missing example directory: {EXAMPLES}", file=sys.stderr)
        return 1
    sources, _ = candidate_sources()
    negative = sum(is_invalid(source) for source in sources)
    print(f"Testing {len(sources)} programs, including {negative} documented-invalid negative controls.")
    REPORTS.mkdir(parents=True, exist_ok=True)
    results = []
    interrupted = False
    try:
        for index, source in enumerate(sources, 1):
            name = str(source.relative_to(EXAMPLES))
            print(f"[{index}/{len(sources)}] {name}", flush=True)
            result = run_example(source)
            results.append((name, result))
            records = []
            for example, (status, counts, elapsed, details) in results:
                inputs = example_sources(EXAMPLES / example)
                records.append(dict(example=example, expected_invalid=is_invalid(EXAMPLES / example),
                    source_sha256={str(p.relative_to(EXAMPLES)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in inputs},
                    status=status, counts=counts, seconds=elapsed, details=details,
                    failed_pass_counts_are_partial=True))
            (REPORTS / "results.json").write_text(json.dumps(records, indent=2) + "\n")
            print(f"  {result[0]} ({result[2]:.1f}s)", flush=True)
    except KeyboardInterrupt:
        interrupted = True
        print("\nInterrupted; showing completed examples only.")
    print_summary(results)
    if interrupted:
        return 130
    return 0 if all(result[0] in ("FULLY PROVED", "EXPECTED UNPROVED")
                    for _, result in results) else 1


if __name__ == "__main__":
    sys.exit(main())
