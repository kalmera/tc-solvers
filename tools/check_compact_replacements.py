#!/usr/bin/env python3
"""Compile reference public clients with compact imports, without changing bodies.

Run inside the configured opam switch after `make proof-tests`. All generated
clients and compiler output stay in a temporary directory. Generic public
contract clients are checked against both namespaces; existing solver clients
are checked with only their imports/module paths substituted.
"""

from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPLACEMENTS = {
    "solvers.slr.restarting.": "solvers.slr.restarting_compact.",
    "solvers.slr.narrowing_fixed_point.": "solvers.slr.narrowing_fixed_point_compact.",
}


def compile_client(directory, name, source):
    target = directory / f"{name}.v"
    target.write_text(source)
    result = subprocess.run(
        ["rocq", "compile", "-Q", "rocq", "TcSolvers", "-Q", str(directory),
         "TcReplacementClients", str(target)],
        cwd=ROOT, capture_output=True, text=True,
    )
    if result.returncode:
        raise RuntimeError(f"{name}:\n{result.stdout}{result.stderr}")
    if result.stderr:
        print(result.stderr, end="")
    print(f"PASS {name}", flush=True)


def main():
    for original, compact in [
        ("restarting/Restarting.v", "restarting_compact/Restarting.v"),
        ("narrowing_fixed_point/Base.v", "narrowing_fixed_point_compact/Base.v"),
    ]:
        if (ROOT / "rocq/solvers/slr" / original).read_bytes() != (
            ROOT / "rocq/solvers/slr" / compact
        ).read_bytes():
            raise RuntimeError(f"Algorithm copy differs: {compact}")
    with tempfile.TemporaryDirectory(prefix="tc-compact-replacements-") as tmp:
        directory = Path(tmp)
        for solver in ("restarting", "narrowing_fixed_point"):
            source = (ROOT / f"rocq/solvers/slr/{solver}_compact/tests/PublicInterface.v").read_text()
            # Audits run in proof-tests; this check concerns the generic API.
            source = "\n".join(line for line in source.splitlines()
                               if not line.startswith("Print Assumptions")) + "\n"
            compile_client(directory, f"{solver}_compact_public", source)
            source = source.replace(f"solvers.slr.{solver}_compact.", f"solvers.slr.{solver}.")
            compile_client(directory, f"{solver}_reference_public", source)
        clients = {
            "spawn_closure": "narrowing_fixed_point/tests/SpawnClosure.v",
            "narrowing_runtime": "narrowing_fixed_point/tests/Instances.v",
            "ordinary_recomputation": "restarting/tests/OrdinaryFixedPoint.v",
        }
        for name, path in clients.items():
            source = (ROOT / "rocq/solvers/slr" / path).read_text()
            # Chain is shared test data, not a solver implementation.
            for original, compact in REPLACEMENTS.items():
                source = source.replace(original, compact)
            source = source.replace(
                "solvers.slr.narrowing_fixed_point_compact.tests.Chain",
                "common.instances.Chain",
            )
            compile_client(directory, name, source)
    print("Public interfaces and unchanged reference client bodies pass.")


if __name__ == "__main__":
    main()
