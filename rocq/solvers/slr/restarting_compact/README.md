# Independent restarting proof regeneration

This stack is prepared as a replacement for the reference solver's public
algorithm and theorem interfaces. Change the namespace from `restarting` to
`restarting_compact`; the public functor parameters, theorem names, and theorem
argument order are preserved. The original entry points and extraction roots
remain in place for the eventual integration.

`Restarting.v` is a byte-for-byte copy of the reference algorithm. `Proofs.v`
contains newly written proofs and imports only shared contracts/semantics and
this copy of the algorithm. It imports no reference restarting proofs or
narrowing-fixpoint proofs. Reading the reference informed the obligations;
its proof files were not copied.

There are three production files. `Proofs.v` contains the generic reasoning;
`Theorems.v` exposes the reference-compatible `Make`, `LeastSolutionMake`, and
`OrdinaryFixedPointMake` interfaces and the existing `Instances` names. Each
public instance uses one proof functor. The ordinary facade discharges the
first-discovery and OneBox phase laws generically, so clients supply exactly
the reference law parameters. Audits reuse these concrete instances.

`Sem` retains the state-oriented replay and execution vocabulary. Public
correctness uses the shared specification, including spawn closure. Internal
proof helpers are implementation details and need not have the reference
proof stack's names.

## Public results

| Result | Scope |
| --- | --- |
| `semantic_termination`, `sufficient_fuel` | Finite systems, stable discovery ranks, constructive update credit |
| `successful_run_correct` | Every successful run; no finite-system premise |
| `total_correct` | Finite systems |
| `successful_run_least`, `total_least_solution` | Finite monotone systems, source strictness, upper-bound update law |
| `ordinary_avoids_fallback` | Every reachable ordinary monotone prefix, first-discovery policy, both recomputation settings |
| `successful_run_fixed` | Ordinary monotone successful runs, first-discovery policy, safe phases implementing narrowing, controlled-owner recomputation enabled |
| `total_fixed` | Finite ordinary monotone systems; returns correctness and narrowing fixedness together |

The generic ordinary prefix and successful-run results do not need the
reference statements' finite-system premise. The facade preserves the old
statements and exposes the stronger forms as
`ordinary_avoids_fallback_unbounded` and `successful_run_fixed_unbounded`.
Fixedness uses the direct RHS result, and
includes replay existence so an incomplete store cannot satisfy it vacuously.
No idempotency assumption is used.

`first_discovery_laws` requires that observation introduces only its target
and assigns a fresh target above existing ranks. These are explicit optional
laws, since generic termination and correctness also support stateless ranks.
`ordinary_phase_laws` specifies safe phases, narrowing phases, admissible
updates, and descending update bounds. The audit specializes these laws to
`OneBoxUpdate`: safe means `BoxW` or `BoxN`, and narrowing means `BoxN`.
`control_avoids_fallback` checks every active and suspended frame recursively.

## Proof structure

Store/reference invariants, observations, execution paths, and public results
share the same machine instance. Completed observations connect partial-store
replay with the post-solution specification, including spawn closure. A frame
cursor records a prefix of its constraint; its side ledger connects raw
observations with accumulated contributions.

Termination uses a lexicographic budget of missing materializations,
promotion reserve, and combined incoming/outgoing update credit. Higher
recursive episodes preserve the suspended parent's phase and cannot increase
its budget. A rerun beginning with only lower owners queued spends credit.
Well-founded induction finishes rounds, discovery-rank induction finishes
episodes, and root seeding plus outer draining finishes the solver.

For ordinary systems, every previously discovered owner is materialized.
Fresh recursive episodes preserve a reader boundary: lower readers watch
only lower values, so changes in the fresh region cannot add lower work.
A small certificate on suspended reads/spawns preserves the gap between the
parent and fresh child. This proves that every RHS evaluation and commit has
only lower owners queued, without retaining full trace origins.

A narrowing frame carries a post-solution frontier for itself and higher
discovered owners. Monotonicity preserves that frontier as values descend;
read and spawn coverage rule out fresh discovery under it. Consequently
narrowing receives descending inputs and cannot enter fallback widening.
Finally, the precision invariant retains a quiet commit's narrowing equation
for idle owners and owners draining their queues. It reuses the observation
and wakeup invariants, carrying the equation to the final store.

## Validation

There are no admissions, new axioms, or reference-proof imports. The eight
assumption audits report `Closed under the global context`; they cover total
correctness, total leastness, both ordinary fallback policies, final fixedness,
and total fixedness. `tests/PublicInterface.v` additionally audits the five
reference public instance guarantees and checks generic clients using the
original parameter lists and theorem argument order.

`make check-compact-replacements` compiles the same generic clients against
both namespaces, then recompiles the existing runtime and spawn-closure
clients with only their solver namespaces changed. All seven client checks
pass. A fresh source-only tree containing common modules and the two compact
stacks also builds; independent `rocq check` verifies both public facades.

Concrete regressions cover accumulated side effects, a controlling back read,
spawn closure, and update-credit consumption. The ordinary regression has no
direct self-read: a higher owner controls it, and slow narrowing needs several
owner recomputations to reach `One`. With recomputation enabled, its result is
proved narrowing-fixed by the new theorem. Reader wakeups alone terminate at
`Top`, whose next narrowing result is `Three`, demonstrating the need for the
conditional recomputation policy.

```sh
opam exec --switch=5.4.0 -- make restarting-compact
opam exec --switch=5.4.0 -- make check-compact-replacements
opam exec --switch=5.4.0 -- python3 tools/benchmark_restarting_proofs.py --repeat 3
```

## Size and time

The benchmark checks algorithm identity and recompiles targets in fresh,
serial Rocq compiler processes with existing shared dependencies and
filesystem caches. It records source hashes, line counts, compiled object
sizes, and per-file wall times. Its status is `matching_public_guarantees`;
internal helper statements differ between the two developments.

Before adding the reference-compatible facade, on Rocq 9.1.1 / OCaml 5.4.0,
three fresh runs gave:

| Complete stack | Reference | Compact |
| --- | ---: | ---: |
| Compilation targets | 6 | 3 |
| Source lines | 33,277 | 7,770 |
| Compiled object bytes | 51,323,366 | 4,669,015 |
| Median compilation time | 23.22 s | 6.36 s |

At matching public theorem coverage, the compact stack compiled **3.65 times
faster** and produced **90.9% fewer compiled bytes**. Its single proof unit is
6,705 lines, 3,486,061 compiled bytes, and compiled in a median 4.45 seconds.
The audit is 179 lines and compiled in a median 1.78 seconds. These measurements
include the concrete ordinary instances for both recomputation policies.

These historical measurements covered the same mathematical guarantees,
using the generic proof interface. The benchmark now also includes
`Theorems.v` and its reference-compatible concrete instances. It reports each
run and source checksum. Times depend on the host and caches.
