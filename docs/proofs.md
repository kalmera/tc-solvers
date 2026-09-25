# Definitions and public results

The Rocq namespace is `TcSolvers`. Each SLR solver has its algorithm and public
`Theorems.v` in `rocq/solvers/slr/<solver>/`; internal proofs and constructive
example systems remain beside it. Shared concrete instances live in
`rocq/common/instances/`.

| Solver directory | Algorithm | Public results |
| --- | --- | --- |
| `simple` | `Simple.v` | Total correctness; leastness under upper-bound-preserving updates |
| `restarting` | `Restarting.v` | Total correctness for all four feature settings; leastness under upper-bound-preserving updates |
| `narrowing_fixed_point` | `NarrowingFixedPoint.v` | Total correctness; leastness under upper-bound-preserving updates; narrowing fixpoint |

Public theorem interfaces expose the definitions necessary to read their statements.
Simple and Restarting expose `Make` and `LeastSolutionMake`, with explicit rank
policies and laws. Narrowing Fixed Point exposes `Correctness` for arbitrary
updates, `Make` for OneBox narrowing fixedness, and `LeastSolutionMake` for
upper-bound-preserving updates. Concrete first-discovery and finite-height join
choices are assembled in `Instances`, rather than additional public wrappers.
Common domain, collection, update, and finite-support laws are in `rocq/common/`.
Rank discovery and shared SLR control are in `rocq/solvers/slr/common/`.
For example:

```coq
From TcSolvers Require Import solvers.slr.simple.Theorems.
```

Termination uses finite support and update-change credits. Leastness additionally
requires operational monotonicity, source strictness outside the roots, and
upper-bound-preserving updates, instantiated by finite-height join iteration.
The narrowing-fixpoint result additionally assumes operational monotonicity,
direct-widening upper bounds, narrowing bounds, and `WIDEN_STABILITY`: if
`input` is below `old`, then `widen old input` is equivalent to `old`.

`make proofs` checks the proof units and public theorem audits. The additional
concrete example systems and counterexample are checked with `make proof-tests`.
Each `Theorems.v` instantiates its public results in an `Instances` module using
the shared five-element `Chain` domain.
Compiling the file prints a labelled marker followed by Rocq's actual
`Print Assumptions` output, for example:

```text
SLR-TC_S total correctness proven with assumptions:
Closed under the global context
```

Reports cover total correctness and leastness for all three solvers, plus
narrowing fixedness for SLR-TC_N. The concrete audits use first-discovery ranks
where applicable and enable both feature flags; the public theorems remain
generic. `Closed under the global context` means these instantiated proofs have
no axiom dependencies; finite support and other theorem premises still apply.
Markers appear when files are recompiled, not when an incremental build is
already up to date.

Restarting's auxiliary narrowing theorem and counterexample remain available as
supporting results, not additional solver implementations.
