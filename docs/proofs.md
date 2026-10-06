# Definitions and public results

The Rocq namespace is `TcSolvers`. Each SLR solver has its algorithm and public
`Theorems.v` in `rocq/solvers/slr/<solver>/`; internal proofs and constructive
example systems remain beside it. Shared concrete instances live in
`rocq/common/instances/`.

| Solver directory | Algorithm | Public results |
| --- | --- | --- |
| `simple` | `Simple.v` | Total correctness; leastness under upper-bound-preserving updates |
| `restarting` | `Restarting.v` | Total correctness for all eight feature settings; leastness; ordinary-system absence of fallback; narrowing fixedness with controlled-owner recomputation |
| `narrowing_fixed_point` | `NarrowingFixedPoint.v` | Total correctness; leastness under upper-bound-preserving updates; narrowing fixpoint |

Each public correctness interface follows the paper's order: `semantic_termination`,
`sufficient_fuel`, `successful_run_correct`, then `total_correct` as a corollary
combining sufficient fuel with successful-run correctness.
Public theorem interfaces expose the definitions necessary to read their statements.
Simple and Restarting expose `Make` and `LeastSolutionMake`, with explicit rank
policies and laws. Narrowing Fixed Point exposes `Correctness` for arbitrary
updates, `Make` for OneBox narrowing fixedness, and `LeastSolutionMake` for
upper-bound-preserving updates. Restarting additionally exposes `OrdinaryFixedPointMake`.
Both fixedness interfaces expose `WithLaws.WithCollections.successful_run_fixed`,
which adds narrowing fixedness to the successful run supplied by `total_correct`.
They expose `solved`, `replay`, `correct_final_state`, `monotonic_system`, and
`narrowing_fixed`. Fixedness includes replay existence and applies to every
final-state replay of every solved owner, including non-roots.
Restarting separately requires `no_side_effects`; spawns are allowed. Its
successful-run fixedness theorem also requires finite support; Narrowing Fixed
Point needs finite support only for total correctness.
Both use first-discovery ranking and repeat changed controlled-owner updates.
Restarting requires `recompute_controlled = true` for ordinary fixedness.
Only Narrowing Fixed Point additionally requires `WIDEN_STABILITY` and
includes incoming side contributions in its fixedness equation.

Restarting's `OrdinaryFixedPointMake.WithLaws.WithCollections` also exposes
`ordinary_avoids_fallback`: finite support, `monotonic_system`, and
`no_side_effects` imply `avoids_fallback tf roots`. This means that every
configuration reachable from `R.initial_config roots` has
`control_avoids_fallback`: every active and suspended owner frame has a phase
other than `U.Widen`. It covers the whole run, including unfinished prefixes,
and requires neither successful termination nor `recompute_controlled = true`.
All eight feature settings satisfy this property with first-discovery ranking;
ordinary systems may still spawn unknowns. Initial `BoxW` widening and restarts
into `BoxW` are allowed; the theorem excludes the permanent fallback `Widen`.

The shared statement vocabulary is defined in `common/SolverSpecifications.v`.
`correct_final_state` requires every root to be materialized and every
materialized unknown to satisfy `owner_post_solution`. Each constraint has a
replay, satisfies its direct and side-contribution bounds, and has every spawn
at the final valuation materialized. This covers spawned descendants as well
as the roots. `common/ConstraintSemantics.v` likewise requires `post_solution_on`
to include every observed spawn in its covered set.
It supplies solvedness, replay, final-state correctness, operational monotonicity,
absence of side effects, and narrowing fixedness parameterized by its input.
The theorem files include these definitions and state the main results;
Restarting's internal observation conversion stays in its fixedness proof.
Common domain, collection, update, and finite-support laws are also in `rocq/common/`.
Rank discovery and shared SLR control are in `rocq/solvers/slr/common/`.
For example:

```coq
From TcSolvers Require Import solvers.slr.simple.Theorems.
```

Termination uses finite support and update-change credits. Leastness additionally
requires operational monotonicity, source strictness outside the roots, and
upper-bound-preserving updates, instantiated by finite-height join iteration.
The Narrowing Fixed Point result additionally assumes operational monotonicity,
direct-widening upper bounds, narrowing bounds, and `WIDEN_STABILITY`: if
`input` is below `old`, then `widen old input` is equivalent to `old`.

A controlled owner's update reads its previous value even when its RHS does not
read the owner. When this update changes the value, Narrowing Fixed Point queues
the owner for another evaluation with the returned phase. Restarting exposes the
same behavior through `recompute_controlled`, enabled in `AllEnabledFeatures`.
Fixedness follows from the eventual stable commit. Generic correctness,
termination, and join leastness hold with either setting. Recorded reader
wakeups and side-source repairs remain active.

`make proofs` checks the generic proof units and all three public theorem files.
Each facade retains concrete `Instances` and labelled `Print Assumptions`
output (`Closed under the global context`). The fixedness audits use the shared
chain instance with slow narrowing, which needs several updates to stabilize.
`make proof-tests` checks executable regression systems, reader wakeups,
effectful fanout, and recursive spawn closure. A missing-spawn regression shows
that numerical satisfaction alone does not form a post-solution.
The examples do not re-instantiate the full fixedness proof for each system.

Restarting's internal narrowing-stability proof supports the public no-fallback
theorem. The fixed-rank counterexample explains why the public theorem uses
first-discovery ranking.
