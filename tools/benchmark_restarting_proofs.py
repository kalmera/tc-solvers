#!/usr/bin/env python3
"""Recompile restarting proof targets serially and report time/source/vo sizes.

The compact targets currently prove a subset of the reference guarantees.
This is a development measurement, not a comparison of complete replacements.
Dependencies should already be built with `make proof-tests`.
"""

import argparse
import hashlib
import json
from pathlib import Path
import statistics
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
REFERENCE = [
    "rocq/solvers/slr/restarting/Restarting.v",
    "rocq/solvers/slr/restarting/proofs/Correctness.v",
    "rocq/solvers/slr/restarting/proofs/NarrowingStabilityProof.v",
    "rocq/solvers/slr/restarting/proofs/LeastSolutionProof.v",
    "rocq/solvers/slr/restarting/proofs/FixedPoint.v",
    "rocq/solvers/slr/restarting/Theorems.v",
]
COMPACT = [
    "rocq/solvers/slr/restarting_compact/Restarting.v",
    "rocq/solvers/slr/restarting_compact/Proofs.v",
    "rocq/solvers/slr/restarting_compact/tests/Audit.v",
]


def measure(paths, repetitions):
    samples = {path: [] for path in paths}
    for _ in range(repetitions):
        for path in paths:
            started = time.perf_counter()
            result = subprocess.run(
                ["rocq", "compile", "-Q", "rocq", "TcSolvers", path],
                cwd=ROOT, capture_output=True, text=True,
            )
            duration = time.perf_counter() - started
            if result.returncode:
                raise RuntimeError(f"{path} failed:\n{result.stdout}{result.stderr}")
            samples[path].append(duration)
    rows = []
    for path, durations in samples.items():
        source = ROOT / path
        rows.append({
            "path": path,
            "source_lines": len(source.read_text().splitlines()),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "vo_bytes": source.with_suffix(".vo").stat().st_size,
            "wall_seconds": durations,
            "median_wall_seconds": statistics.median(durations),
        })
    totals = [sum(samples[path][sample] for path in paths) for sample in range(repetitions)]
    return {
        "files": rows,
        "source_lines": sum(row["source_lines"] for row in rows),
        "vo_bytes": sum(row["vo_bytes"] for row in rows),
        "total_wall_seconds": totals,
        "median_total_wall_seconds": statistics.median(totals),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--which", choices=("both", "reference", "compact"), default="both")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error("--repeat must be positive")
    if (ROOT / REFERENCE[0]).read_bytes() != (ROOT / COMPACT[0]).read_bytes():
        parser.error("the compact algorithm differs from its reference")
    version = subprocess.run(["rocq", "--version"], check=True, capture_output=True, text=True).stdout.strip()
    report = {
        "status": "partial_regeneration",
        "scope_warning": "The compact proofs do not yet replace all reference guarantees.",
        "method": "Fresh serial compiler processes; existing dependencies and filesystem cache.",
        "rocq_version": version,
        "repetitions": args.repeat,
    }
    for name, paths in (("reference", REFERENCE), ("compact", COMPACT)):
        if args.which in ("both", name):
            print(f"Measuring {name} ({len(paths)} files, {args.repeat} repetitions)", flush=True)
            report[name] = measure(paths, args.repeat)
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
