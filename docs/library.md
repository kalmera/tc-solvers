# Generic solver library

Install `tc-solvers` or run `make ocaml`, then add `(libraries tc-solvers)` to
Dune. The public module is `Tc_solvers`; runtime dependencies are OCaml 5.4 and
Stdlib. Rocq is needed only for regeneration and proof checking.

## Instantiate a solver

```ocaml
module V = struct
  type t = int
  let equal = Int.equal
  let hash = Hashtbl.hash
end
module D = struct
  type t = int
  let bottom = 0
  let join = max
  let leq = ( <= )
  let widen _ _ = 5
  let narrow old input = max input (old - 1)
end
module U = Tc_solvers.Update.TwoCopy (V) (D)
module Solver = Tc_solvers.Slr.Simple.Make (V) (D) (U)

let system = function
  | 0 -> Some (fun get side spawn ->
      spawn 2;
      side 1 2;
      max 1 (get 2))
  | 2 -> Some (fun _ _ _ -> 1)
  | _ -> None

let solution = Solver.solve system [0]
let side_value = Solver.value solution 1  (* 2 *)
```

This example domain is the finite chain 0 through 5; clients must keep its
values within that range. Complete runnable examples for all three families
are in `examples/library/`.

`Slr.Restarting.Make (V) (D) (U) (Features)` accepts three compile-time booleans:
`side_effect_phase_reset`, `dead_side_elimination`, and `recompute_controlled`.
All eight combinations are supported. Enable `recompute_controlled` to repeat a
changed controlled-owner update even when its RHS does not read itself.
`Slr.Narrowing_fixed_point.Make_with_features (V) (D) (U) (Features)` accepts
these same three booleans. `Slr.Narrowing_fixed_point.Make (V) (D) (U)` keeps all
three enabled by default.
Hash tables and the bitmap worklist are internal. The first-discovery order
and maximum-rank-first work processing match the existing callback adapters.

## Plus Restarting (SLR-TC+)

`Slr.Plus_restarting` provides a separate, standalone API for dynamic constraint
trees. It exposes no extracted configuration, Goblint type, presentation string,
serialization format or retained trace. For example:

```ocaml
module V = struct
  type t = int
  let equal = Int.equal
  let hash = Hashtbl.hash
  let compare = Int.compare
end
module U = Tc_solvers.Update.TwoCopy (V) (D)
module SU = Tc_solvers.Update.SideJoin (V) (D)
module Solver = Tc_solvers.Slr.Plus_restarting.Make (V) (D) (U) (SU)

let system = function
  | 0 -> Solver.Spawn (2, Solver.Get (1, fun input ->
      Solver.Side (3, input, Solver.Ret input)))
  | 1 -> Solver.Ret 1
  | _ -> Solver.Ret D.bottom

let on_event { Tc_solvers.transition; event } = match event with
  | Tc_solvers.Value_change { variable; old_value; value } ->
      ignore (transition, variable, old_value, value)  (* client-owned reporting *)
  | _ -> ()

let solution = Solver.solve ~on_event system [0]
```

`Get` supplies the observed value to its continuation. `Side` and `Spawn` retain
their sequential position; `Ret` supplies the direct result. Every system lookup
returns a constraint tree, including `Ret bottom` for an equation without a
direct contribution. The library preserves the Plus reference's pure-bottom
probing, dirty reads, recursive episodes, priority draining and FIFO-deferred
spawns. Ordinary and side policies are independent: `SIDE_UPDATE.update` receives
source, target, phase, old contribution, cumulative input and incoming aggregate.
`Update.SideJoin` supplies the join-based policy. Side phases and contribution
writes are retained even for equivalent values; an ordinary policy's returned
phase is retained when its result is equivalent to the old stored value.

The default enables all four policies. `Make_with_features (V) (D) (U) (SU)
(Features)` accepts the existing three `FEATURES` fields and `defer_spawns`.
Clients choose their configuration explicitly when their semantics require it.
For example, a client can enable `recompute_controlled` and `defer_spawns` and
disable `side_effect_phase_reset` and `dead_side_elimination`.

Plus uses `ORDERED_VAR`: hashing and equality identify arbitrary typed variables;
`compare = 0` must agree with equality. The ordering defines reader, contribution
and dead-target traversal, as in reference executions with ordered maps/sets.
It does not define discovery priority. Discovery assigns increasing dense ranks
through a hash table and cached count, and a bitmap worklist selects the greatest
rank. Duplicate insertion, membership and cancellation use bits rather than list
scans. Deferred spawn requests use a FIFO and an ordered deduplication set. No
rank is assigned merely by requesting a deferred spawn or probing a dormant
bottom equation. These details preserve scheduling and widening order. Different
reference collection traversal orders are not promised to have identical traces.

`solve ?aggregate_cache ?on_event ?max_steps system roots` returns an abstract solution. Its
`completion` is `Complete` or `Step_limit`; `statistics` reports transitions,
evaluations, discoveries and observer exceptions. A limit returns a marked
partial store, never an unmarked successful result. `max_steps` counts Plus
reference transitions in this implementation, not elapsed time or callback
instructions; it cannot interrupt a nonterminating client callback. No initial
binding argument is provided by this first Plus API; clients express inputs in
their equations. The existing solver families retain their initial-binding API.

Enable the side-only incoming aggregate cache with
`Solver.solve ~aggregate_cache:true system roots`. It defaults to false, retaining
the existing ordered full-fold behavior. With caching enabled, each immutable
contribution row holds its aggregate. Reads reuse that value. Replacing a stored
contribution `old` with the policy result `next` uses `join old_aggregate next`
when `leq old next`; absorption reuses the old aggregate if `next` is already
below it. Otherwise a decrease or incomparable replacement recomputes the updated
row in the original ordered fold. The target's direct RHS result is never included in this cache.
Dead-side withdrawals pass through the same policy and replacement operation;
they are stored contributions, not physical key deletion. Resetting phases or
reset registrations does not change contributions or invalidate the aggregate.

The old row/cache remains valid when a new row is written, including the
before/after aggregate comparison in publication. No global memoization table or
historical-map registry is used. Policy calls, returned phases, contribution
writes, events and scheduling still execute when values compare equivalent.
`SU.update` receives the pre-replacement aggregate, and the cache is updated from
its actual returned contribution, rather than from the raw `Side` input.

Enabling this option requires a join semilattice modulo mutual `leq`: join is
associative, commutative and idempotent, bottom is an identity, and absorption
agrees with the order. The existing Rocq `DOMAIN_LAWS` requires bottom leastness,
join upper bounds and leastness (which imply identity, idempotency and absorption),
and states commutativity and associativity explicitly. The OCaml `DOMAIN` type
alone cannot enforce those laws. Merely producing an upper bound is insufficient.
Domain operations, transfer continuations and policies must respect equivalence,
including policies' future phase behavior. Cached representatives, join-call
counts and grouping can differ from the full fold. For valid clients, typed event
values correspond up to equivalence, with the same event kinds, transition
indices, discovery order, scheduling and completion. Leave caching disabled for
clients which depend on representatives or domain-operation counts.

`on_event` receives an envelope `{ transition : int; event : event }`, rather
than the event variant alone. `transition` is the zero-based index of the Plus
reference transition executing the operation, using the same counter as
`max_steps` and `statistics.steps`. Several events can share an index; callback
order determines their order within the transition. A budget of N permits only
indices 0 through N-1, with no events for transitions that were not executed.
At budget zero there are no callbacks. Observation adds no machine transitions.

Events include evaluation start/result, requested and completed reads, raw side emissions,
spawns, rank discoveries, materialization, published value changes and side-policy
updates. Value changes provide old/new values directly. Side updates additionally
provide source, target and cumulative input, including dead-side withdrawals.
`Read_request { owner; target }` is emitted exactly once when executing `Get`,
before resolving its target or starting child work. The existing
`Read { owner; target; value }` completes the read when the value becomes
available, possibly in a later transition. An immediate read can request and
complete in the same transition. A partial solve can have requests without
completions: clients should collect demanded dependencies from `Read_request`.
These demands are distinct from the solver's current internal reader registrations.
Hooks run synchronously at these operations; they require no store scans or extra
domain comparisons. Disabled hooks construct no events. The library retains no
event history and imposes no retention limit; clients control recording and
serialization without truncating the live stream. Observers must not mutate
values, keys, policies or the system. Observer exceptions are counted and isolated
so reporting failures do not change solving; system/domain/policy exceptions
propagate. Observation takes time and does not provide concurrency guarantees.

`value`, `mem`, `iter` and ordered `bindings` inspect results without exposing
mutable engine tables. `bindings` is a stable snapshot; domain values must be
immutable. Stored bottom counts as a binding; a rankless dormant-bottom equation
can return bottom without a stored binding. Independent and nested solves do not
modify earlier results or events. This entry point intentionally shares neither
the Basic Restarting consistent-evaluation feature nor its proof work.

## Callbacks and results

A system maps a variable to an optional callback. Its arguments are `get`,
`side`, and `spawn`: read another value, contribute to another variable, or
request another variable's solution. The return value is the direct result.
`None` describes a variable without a transfer function; it can still receive
side effects or initial contributions.

Callbacks run synchronously, may be replayed, and must not retain or invoke
these callback arguments after returning. System lookup may also repeat;
its transfer behavior must remain stable during a solve. Do not mutate values
or keys after supplying them. Hashing must agree with equality, and equality
must be stable. Mutable solver state belongs to one invocation; nested and
successive solves are independent. A single invocation is not a concurrent
callback interface. Callback exceptions propagate to the caller.

`solve ~initial:[variable, value; ...] system roots` creates fresh state. Repeated
initial entries are joined, and initial values remain constant contributions
during every evaluation. Roots are handled left to right, draining discovered
work before the next root; initial variables not already reached are seeded
afterward. Repeated side contributions from one source to one target are joined
within an evaluation.

Solutions are abstract. `value solution variable` returns bottom when absent;
`mem` distinguishes absence from a stored bottom. `iter` visits stored bindings
in unspecified hash-table order. A new solve cannot modify an earlier solution.
These callback entry points have no incremental state, public fuel argument,
observation hooks or implicit I/O. Plus has the observation and limit API above.
Execution retains the adapters' host stack/memory limits and internal seed-fuel
limit; termination depends on the client contracts, not an API timeout.

## Updates and proof contracts

An update is an explicit module argument satisfying `Tc_solvers.UPDATE`, with
`variable = V.t`, `value = D.t`, its own `phase`, and these functions:

```ocaml
val initial_phase : bool -> variable -> phase
val update : bool -> variable -> phase -> value -> value -> phase * value
```

The boolean marks side updates; the final two arguments are the old value and
new input. Ordinary updates receive the owner variable, and side updates receive
the target variable. Phases belong to the algorithm's ordinary/side state and
may reset according to the selected solver configuration.

`Update.TwoCopy (V) (D)` is the suggested starting policy: two direct copies,
then a widening/narrowing box, with widening-only fallback after growth resumes
in narrowing. `Update.WidenNarrow (V) (D)` starts directly in that box.
Both require `BOX_DOMAIN` and call `widen old input`.
`Update.Join (V) (D)` needs only `DOMAIN` and joins old with input. Custom policies
use the same interface; no particular policy is selected implicitly.

Domain equivalence is mutual `leq`. Clients must satisfy the domain, update,
finite-support, and transfer laws in the corresponding Rocq theorem. Join
leastness additionally requires finite height, operational monotonicity, and
source strictness outside roots. The proved narrowing-fixed-point instance uses
the zero-copy box, direct-widening upper bounds, and covered-input stability:
`leq input old` implies that `widen old input` is equivalent to `old`.
Changed controlled owners are evaluated again with the returned phase because
the update itself depends on the previous value. Both solvers expose
`recompute_controlled`; their narrowing-fixedness theorems require this option
to be enabled. Restarting additionally requires no side effects. Narrowing
Fixed Point's owner fallback-avoidance theorem allows side effects and holds
with recomputation enabled or disabled. Selecting the suggested two-copy policy does not
instantiate the OneBox fixedness theorem.

The mutable runtime has no mechanized refinement proof. Differential tests
for the callback library cover eleven configurations and three
policies. Existing differences from extracted references are checked as
exact baselines in `tests/library/differential.ml`; all tested join and Narrowing
Fixed Point cases agree with their extracted references.

The private Plus core preserves the extracted reference control while replacing
rank, queue and FIFO representations. Its current checks compare complete policy
calls, discovery/evaluation order, transition counts, stores and bounded prefixes
against the unchanged reference: 531 cases across all 16 configurations and three
ordinary policies, with join and shrinking side updates. Each case also compares
full-fold and aggregate-cache modes, including complete typed event streams and
partial runs. API checks cover incomparable and masked decreases, dead-side
withdrawals, post-policy values and equivalent representatives. An isolated test
of the private generated source verifies pre-update policy aggregates, old-state
reads, zero-join cached reads, phase resets and collection of replaced maps.
These checks reuse existing test files. This is regression
evidence, not a new runtime proof. The full runtime proof remains on hold.
The same checks compare transition-indexed read requests/completions at partial
budgets, including 20 transitions. An API regression records nine requests and
two completions at that boundary and checks the full-run event prefix, immediate
read ordering, zero-budget silence and independent nested-solve counters.

## Development

Edit public interfaces and wrappers in `ocaml/library/`. Generated cores come
from the existing callback adapters through checked frontend-only transformations
in `ocaml/library/generate.py`; edit the original algorithm templates for algorithm
changes. `make library` regenerates from committed adapters; `make regenerate`
rebuilds the complete chain. The generic worklist is always bitmap, independent
of the worklist selected for Goblint. Tests verify generation boundaries and the
library's isolated installation without external solver dependencies.

Plus is generated from committed `PlusRestartingRuntime.ml` through checked
collection and hook substitutions in that same generator. Its generated core is
private and is installed without any dependency on the extracted reference
package. No proof regeneration is needed for this library-only work.

In a local native-code discovery benchmark with 8,000 non-bottom roots and
ordered maps/sets, the reference took 0.297 seconds and the library 0.0067 seconds
(about 44 times faster). Key-equality calls fell from 63,992,000 to 23,758; sizes
1,000, 2,000 and 4,000 showed quadratic versus approximately linear discovery
growth. This isolates the discovery bottleneck and is not an analysis-level
performance claim. Ordered maps remain; aggregate folding can now be replaced
by the opt-in cache described above.

A separate native-code side-aggregate benchmark uses an integer max domain,
1,400 sources, one target and three emissions per source. Full-fold mode takes
0.137 seconds, 8,832,460 joins and 620.22 MiB cumulative allocation; caching takes
0.00267 seconds, 8,464 joins and 14.43 MiB allocation. Both execute 15,624
transitions. Peak OCaml GC heap is 2.79 versus 1.15 MiB (not process RSS).
Doubling to 2,800 sources gives 35,304,360 versus 16,864 joins, showing quadratic
versus linear join growth for this fixture. This synthetic benchmark is not an
RTEMS/Põder analysis result. The cached joins satisfy the same semilattice laws
as the full-fold domain; no solver proof or extracted reference was changed.
