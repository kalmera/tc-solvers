# Independent narrowing-fixedpoint proof regeneration

This copy regenerates the narrowing-fixedpoint proofs while preserving the
reference solver's runtime. The original solver remains available unchanged.

The production dependency graph is local:

```text
Base.v → Foundation.v ──────────┐
Base.v → NarrowingFixedPoint.v ─┴→ Proofs.v → Precision.v → Theorems.v
```

All other imports are common contracts, semantics, collections, and discovery
order laws. No production file imports another solver or its proofs.

`Base.v` is byte-identical to the reference core. `Foundation.v` is an authorized
local copy of the regenerated generic reasoning, trimmed to the certificates
used here. Its interfaces take state invariants instead of reachability in the
core machine. The narrowing machine has its own transition, execution, and
termination proofs in `Proofs.v`; its precision proofs are written afresh in
`Precision.v`.

`Theorems.v` exposes these guarantees:

- `Correctness`: semantic termination, sufficient fuel, and successful/total
  correctness for generic UPDATE instances, including side effects and spawns.
- `LeastSolutionMake`: total leastness under upper-bound update laws,
  monotonicity, and source strictness.
- `Make`: OneBox owner fallback avoidance for monotone systems, including side
  effects and spawns, under either controlled-owner recomputation policy.
- `Make`: successful narrowing fixedness and total correctness with fixedness
  when `Features.recompute_controlled = true`. The narrowing input is the direct
  result joined with the stored incoming aggregate.

Precision uses historical observations to bound all later reads and side
publications during a narrowing wave. Fixedness retains the local equation at
quiet commits until the final store. Neither argument assumes idempotency.

Build the independent stack and its concrete assumption audits with:

```sh
opam exec --switch=5.4.0 -- make narrowing-fixed-point-compact
```

`tests/Audit.v` shares one OneBox proof instance and separately audits the
reference public stack's JoinUpdate leastness instance. All 16 assumption
prints are closed. Runtime regressions cover slow narrowing without a direct
self-read and source repair when another contribution masks a changed cell.

`tests/RuntimeIdentity.v` is the sole comparison-only import of the reference
solver. It proves the copied transition, fuel execution, and solver result
definitionally identical. It is checked by `make proof-tests`, and excluded
from the independent build and performance comparison.

The independent source-only build contains common modules and this copy, with
no other solver source or compiled artifact. Its audit is also checked with
`rocq check`. The repository proof-test target checks runtime identity and the
existing regressions separately.

A full-coverage clean comparison on this host used Rocq 9.1.1, OCaml 5.4.0,
and `make -j2`. Both trees started without compiled artifacts and included the
same common sources and concrete OneBox/JoinUpdate laws. The reference target
was `narrowing_fixed_point/Theorems.vo`; the compact targets were
`Theorems.vo` and `tests/Audit.vo` in this directory.

| Measure | Reference | Compact |
| --- | ---: | ---: |
| Clean build wall time | 151.8 s | 87.0 s |
| Solver sources, including public audits | 9 | 7 |
| Solver source lines | 45,945 | 9,614 |
| Solver `.vo` logical size | 352.5 MiB | 9.6 MiB |

This single clean run was 43% faster, with 79% fewer source lines and
97.3% less compiled solver data. Sizes exclude common modules; wall times
include them. Timing varies by host and load. Production uses six source files;
`tests/Audit.v` adds the seventh measured file.
