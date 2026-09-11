# Definitions and public results

The Rocq namespace is `TcSolvers`. Each SLR solver has its algorithm and public
`Theorems.v` in `rocq/solvers/slr/<solver>/`; internal proofs and constructive
instances remain beside it.

| Solver directory | Algorithm | Public results |
| --- | --- | --- |
| `simple` | `Simple.v` | Total correctness; finite-height join leastness |
| `restarting` | `Restarting.v` | Total correctness for all four feature settings; finite-height join leastness |
| `narrowing_fixed_point` | `NarrowingFixedPoint.v` | Total correctness; finite-height join leastness; narrowing fixpoint |

Public theorem files include the definitions necessary to read their statements.
Common domain, collection, update, and finite-support laws are in `rocq/common/`.
Rank discovery and shared SLR control are in `rocq/solvers/slr/common/`.
For example:

```coq
From TcSolvers Require Import solvers.slr.simple.Theorems.
```

Termination uses finite support and update-change credits. Leastness additionally
requires operational monotonicity, source strictness outside the roots, and
upper-bound-preserving updates, instantiated by finite-height join iteration.
The narrowing-fixpoint result has its own operational monotonicity and
widening/narrowing laws; its public theorem is authoritative.

`make proofs` checks all imported units and instances. The existing instance
checks print their assumptions; the completed results are constructive.
Restarting's auxiliary narrowing theorem and counterexample remain available as
supporting results, not additional solver implementations.
