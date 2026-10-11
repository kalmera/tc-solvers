# Definitions and public results

The Rocq namespace is `TcSolvers`. Each SLR solver has its algorithm and public
`Theorems.v` in `rocq/solvers/slr/<solver>/`; internal proofs and constructive
example systems remain beside it. Shared concrete instances live in
`rocq/common/instances/`.

| Solver directory | Algorithm | Public results |
| --- | --- | --- |
| `simple` | `Simple.v` | Total correctness; leastness under upper-bound-preserving updates |
| `restarting` | `Restarting.v` | Total correctness for all eight feature settings; leastness; ordinary-system absence of fallback; narrowing fixedness with controlled-owner recomputation |
| `plus_restarting` | `PlusRestarting.v` | Total correctness and join leastness for both recomputation settings; ordinary FIFO-spawn fallback avoidance; narrowing fixedness with controlled-owner recomputation |
| `narrowing_fixed_point` | `NarrowingFixedPoint.v` | Total correctness for all eight feature settings; leastness; monotone-system owner fallback avoidance; narrowing fixedness with controlled-owner recomputation |
| `reluctant_restarting` | `ReluctantRestarting.v` | Partial and total correctness; leastness |
| `dormant_restarting` | `DormantRestarting.v` | Partial and total correctness; leastness with dormant bottom values |
| `dirty_read_restarting` | `DirtyReadRestarting.v` | Partial and total correctness; leastness with dirty reads |
| `deferred_simple` | `DeferredSimple.v` | Total correctness and leastness for immediate and FIFO-deferred spawning |

Every solver uses the same basic correctness specification in
`common/SolverSpecifications.v`; `common/SolverContracts.v` reuses those
predicates and adds proof records and theorem consequences. The shared state
view needs only a state type, semantic lookup, and a total valuation, with no
map implementation. `correct_final_state` requires every root to be
solved and every solved owner to satisfy `owner_post_solution`: its constraint
has a replay, satisfies its direct and side-effect bounds, and every spawn
observed at the final valuation is also solved. This covers spawned descendants
and dormant bottom values. Solvedness and replay use semantic lookup rather
than requiring a physical map entry. Numerical replay alone is insufficient.
`common/ConstraintSemantics.v` likewise includes spawn closure in
`post_solution_on`.

`common/SolverInterfaces.v` contains the law-free `SEMANTICS`, `SOLVER_VIEW`,
and `EXECUTION` signatures, grouped by `SOLVER`. Each solver owns these three
submodules over one machine instance. The sibling `<Solver>Interface.v` exposes
a law-free `Make`; Plus Restarting retains its existing algorithm-owned
`Interface`. The sibling files keep proof semantics out of library extraction.
These interfaces can be bound to the specifications without importing solver
proofs or supplying update, domain, or collection laws. Narrowing Fixed Point
also exposes `NarrowingFixedPointInterface.WithCore` for a supplied core and
ranking policy. Internal proofs reuse these views and their execution relations.
Public theorem functors export them as `Solver` and bind the shared specification
with:

```coq
Module Spec := SolverContracts.ForSolver P.V P.D Solver.
```

`Correctness`, `Termination`, `Leastness`, `Fixedness`, and `FallbackAvoidance`
are independent proof records in `Prop`. Their types are declared outside the
specification functor, so separately compiled clients can consume certificates
without creating incompatible record types. A `SOUND` module supplies
correctness, `VERIFIED` adds termination, and `VERIFIED_LEAST` adds leastness.
`Spec.SoundConsequences`, `Spec.Consequences`, and `Spec.LeastConsequences` export
the corresponding public results, including total correctness, owner satisfaction,
and total leastness. Fixedness records specify the narrowing operation and
input function; precision records carry explicit system preconditions.

All eight solvers expose `Theorems.Make P` and `Theorems.LeastSolutionMake P`.
Each exports `Solver`, `Spec`, and `Certificates`. `Make` also exports
`successful_run_correct`, `semantic_termination`, `sufficient_fuel`, and
`total_correct`; leastness exports `successful_run_least` and
`total_least_solution`. Reluctant, Dormant, and Dirty-Read Restarting additionally
expose `PartialMake` using only soundness laws. Proof implementations remain
under `Internal` or `Total.Internal`. Leastness wrappers reuse the total
certificates for their machine: through `Make P` when the proofs share one
factory, or through the leastness proof's existing total-proof submodule.
The executable functors remain extraction roots.

`common/SolverParameters.v`, exported with the specification, contains all
parameter signatures. Each theorem functor takes one bundle and requires only
its relevant capabilities:

| Solver | Correctness parameters | Leastness parameters |
| --- | --- | --- |
| Simple, Restarting | `RANKED_UPDATE_PARAMETERS` | `RANKED_LEAST_SOLUTION_PARAMETERS` |
| Narrowing Fixed Point | `FINITE_UPDATE_PARAMETERS` | `FINITE_LEAST_SOLUTION_PARAMETERS` |
| Reluctant Restarting | `RANKED_TOTAL_CORRECTNESS_PARAMETERS` | `RANKED_SIDE_LEAST_SOLUTION_PARAMETERS` |
| Dormant, Dirty-Read, Plus Restarting | `TOTAL_CORRECTNESS_PARAMETERS` | `LEAST_SOLUTION_PARAMETERS` |
| Deferred Simple | `ASCENDING_TOTAL_CORRECTNESS_PARAMETERS` | `ASCENDING_LEAST_SOLUTION_PARAMETERS` |

The ascending bundle uses `ASUL` for ascending side-update credit; restarting
bundles use `SUL` for restarting credit. Ranked bundles include a discovery
policy and its stable/finite laws. The partial-correctness bundles require only
ordinary and side-update soundness. Feature signatures also live in the common
area.

`common/instances/SolverBundles.v` provides `FiniteHeightParameters`, which
constructs join updates, reluctant side updates, ranking, and their laws from
a finite-height domain and collection laws. `ChainParameters Features` adds the
shared finite chain's OneBox update and narrowing laws. One concrete bundle can
therefore supply correctness, leastness, and fixedness:

```coq
From TcSolvers Require Import solvers.slr.restarting.Theorems.
Module Parameters := ChainParameters SolverFeatures.AllEnabledFeatures.
Module Correct := Theorems.Make Parameters.
Module Least := Theorems.LeastSolutionMake Parameters.
Module Ordinary := Theorems.OrdinaryFixedPointMake Parameters.
Check Correct.Certificates.correctness.
Check Correct.total_correct.
```

Restarting and Plus Restarting expose `OrdinaryFixedPointMake` with
`ORDINARY_FIXED_POINT_PARAMETERS`. Narrowing Fixed Point exposes
`FixedPointMake` with `STABLE_FIXED_POINT_PARAMETERS`, which additionally
requires `WIDEN_STABILITY`. The same bundle supplies the existing `FixedU`
OneBox update, preserving its phase type across the policy and laws. Precision
proofs live in `Proofs.FixedPoint`; the public interface has no staged
law/collection facade.

Restarting's fallback-avoidance certificate assumes monotonicity and no side
effects. Spawns are allowed, and finite support is unnecessary. It covers every reachable
prefix and requires no controlled-owner recomputation. Fixedness additionally
requires `recompute_controlled = true` and uses the replayed direct input.

Narrowing Fixed Point's fallback-avoidance certificate assumes only operational
monotonicity and allows side effects and spawns, without finite support.
Fixedness additionally requires `recompute_controlled = true`; its equation
joins the replayed direct input with stored incoming side contributions. Its
fallback invariant covers owner frames rather than side-cell phases.

All shared consequences and solver certificates are proved. The separately
compiled `common/tests/SolverInterfaces.v` client binds all eight algorithm
interfaces to the shared predicates without solver proof files or law arguments.
The separately compiled `common/tests/PublicTheorems.v` client consumes the same
full correctness and leastness certificates from all eight solvers and derives
spawn closure through the common interface. It also checks generic parameter
bundles and the deferred solvers' feature variants. Dormant and Dirty-Read
theorem tests share their alternative finite-domain bundle in
`common/tests/ToySolverFixture.v`. Executable regressions cover recursive
and already solved spawns, including both Deferred Simple spawn modes, and
reject a state whose numerical bounds hold while its spawn is missing.

The Reluctant, Dormant, Dirty-Read, and Deferred Simple replay proofs track
executed spawns with a fixed predicate. Scheduler accounting proves that every
executed spawn remains solved or scheduled until the final quiescent state.
Instantiating the predicate with final-state solvedness then closes each
completed owner's replay. Dirty reads use a structural evaluation prefix to
preserve these obligations when publishing a pending value early.

`common/DefaultUpdate.v` formalizes the catching-up Goblint default policy:
ordinary values copy once before entering a widening/narrowing box, while side
contributions start in permanent widening. Widening receives `join old input`,
as in `catching_up/goblint_qsolver_update.ml`. `DefaultUpdateLaws.WithLaws`
extends the joined box's update laws with a bound on its entry credit; the copy
uses one more credit than that bound. It requires no value-idempotency law.

`common/instances/DefaultUpdate.v` supplies `ThresholdDefaultUpdate`, with all
ordinary and reluctant side-update laws on the infinite-height threshold domain.
`solvers/slr/reluctant_restarting/DefaultUpdate.v` supplies
`ThresholdReluctantRestartingDefault`, including the stronger side-update
contract used by the restarting variants. Executable regressions and concrete
`Print Assumptions` audits are in the common and deferred solver test directories.

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
read the owner. With `recompute_controlled = true`, Restarting, Narrowing Fixed
Point, and Plus Restarting queue a changed
controlled owner for another evaluation with the returned phase. The option is
enabled in `AllEnabledFeatures`. `ReaderWakeupsOnlyFeatures` disables it.
Fixedness follows from the eventual stable commit. Generic correctness,
termination, and join leastness hold with either setting. Recorded reader
wakeups and side-source repairs remain active.

Plus Restarting's bundled `OrdinaryFixedPointMake` takes domain,
widening/narrowing, and update laws, without a value-idempotency module.
Its internal `Proofs.v` shares one machine instance across execution semantics,
invariants, and optional law modules. Termination combines repeated-round credit
descent, induction on discovery rank, and finite outer scheduling.
Its public `fallback_avoidance` and `successful_run_fixed` results
require no finite-support premise. Fallback avoidance requires
`defer_spawns = true`, monotonicity, and absence of side effects, independently
of `recompute_controlled`. Fixedness additionally requires
`recompute_controlled = true`. The replay equation follows from fixedness
without finite support, as checked by `common/tests/PublicTheorems.v`.
These successful-run results require only side-policy soundness.
Commit history permits a pending owner to need
further narrowing; once the work queue is empty, its final commit is stable.
The stutter-closure update law establishes fixedness of that stable commit.

`make proofs` checks the generic proof units and all public theorem files.
Each facade retains concrete `Instances` using the shared finite chain, whose
slow narrowing needs several updates to stabilize.
`make proof-tests` checks executable regression systems, reader wakeups,
effectful fanout, and recursive spawn closure. A missing-spawn regression shows
that numerical satisfaction alone does not form a post-solution.
The examples do not re-instantiate the full fixedness proof for each system.
Each `Theorems.v` reports assumptions for its main public results, with an
`idtac` label before each `Print Assumptions` command. All solvers report total
correctness and the leastness certificate; Restarting, Plus Restarting, and Narrowing Fixed Point
additionally report ordinary fallback avoidance and narrowing fixedness. Plus
Restarting checks total correctness, the leastness and fallback-avoidance
certificates, and the instantiated ordinary fixedness certificate. These reports
include dependencies on intermediate lemmas. `Print Assumptions` is informational;
it does not fail the build if an assumption appears.
Regression clients omit repeated reports for internal lemmas. Dirty-Read's toy
theorem client retains reports for its alternative domain and restart settings.

Independent validation with `rocq check` is useful after substantial proof or
module changes and before merging. It checks compiled libraries separately
from ordinary compilation and can be run manually when needed.

Restarting's internal narrowing-stability proof supports the public no-fallback
theorem. The fixed-rank counterexample explains why the public theorem uses
first-discovery ranking.
