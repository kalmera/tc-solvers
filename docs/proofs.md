# Definitions and public results

The Rocq namespace is `TcSolvers`. Each SLR solver has its algorithm and public
`Theorems.v` in `rocq/solvers/slr/<solver>/`; internal proofs and constructive
example systems remain beside it. Shared concrete instances live in
`rocq/common/instances/`.

| Solver directory | Algorithm | Public results |
| --- | --- | --- |
| `simple` | `Simple.v` | Total correctness; leastness under upper-bound-preserving updates |
| `restarting` | `Restarting.v` | Total correctness for all four feature settings; leastness; ordinary-system narrowing fixedness under value idempotency |
| `narrowing_fixed_point` | `NarrowingFixedPoint.v` | Total correctness; leastness under upper-bound-preserving updates; narrowing fixpoint |

Public theorem interfaces expose the definitions necessary to read their statements.
Simple and Restarting expose `Make` and `LeastSolutionMake`, with explicit rank
policies and laws. Narrowing Fixed Point exposes `Correctness` for arbitrary
updates, `Make` for OneBox narrowing fixedness, and `LeastSolutionMake` for
upper-bound-preserving updates. Restarting additionally exposes `OrdinaryFixedPointMake`.
Both fixedness interfaces use `WithLaws.WithCollections.total_correct_and_fixed`
and expose `solved`, `replay`, `correct_final_state`, `monotonic_system`, and
`narrowing_fixed`. Fixedness includes replay existence and applies to every
final-state replay of every solved owner, including non-roots.
Restarting separately requires `no_side_effects`; spawns are allowed.
Both use first-discovery ranking and ordinary value idempotency of the combined
update. Only Narrowing Fixed Point additionally requires `WIDEN_STABILITY` and
includes incoming side contributions in its fixedness equation.
The public theorem files define their statement vocabulary beside their theorems.
Common domain, collection, update, and finite-support laws are in `rocq/common/`.
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

The Narrowing Fixed Point solver omits the synthetic controlled-owner requeue.
Both fixedness functors take the shared `VALUE_IDEMPOTENT V D U` law from
`common/UpdateIdempotency.v`: replaying an
ordinary update with its resulting phase and value, and the same input, must
return an equivalent value. The phase itself may change. The law covers the
combined OneBox update, not just narrowing, and imposes no condition on side
updates. Generic correctness, termination, and join leastness do not need it.
Actual reader wakeups, including self-reads, and side-source repairs remain.

`make proofs` checks the generic proof units and all three public theorem files.
Each facade retains concrete `Instances` and labelled `Print Assumptions`
output (`Closed under the global context`). Narrowing Fixed Point shares one
OneBox instance between its correctness and fixedness audits; the idempotent
chain is a common instance, not a dependency on tests. `make proof-tests` checks
the separate examples and counterexample. The new regression checks execute the
solver and verify three RHS completions instead of a redundant fourth, phase
changes under value idempotency, genuine self-read wakeups, and effectful fanout.
They do not re-instantiate the full fixedness proof for each example.

Restarting's auxiliary narrowing theorem and counterexample remain available as
supporting results, not additional solver implementations.
