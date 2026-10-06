# Independent restarting proof regeneration

This is an **unfinished proof regeneration**, not yet a replacement for
`../restarting`. The reference solver and its public theorems remain unchanged.

`Restarting.v` is a byte-for-byte copy of the reference algorithm. `Proofs.v`
contains newly written proofs and imports only shared contracts/semantics and
this copy of the algorithm. It does not import reference restarting proofs or
proofs of the narrowing-fixpoint variant. Looking at the reference informed the
choice of obligations; its proof files were not copied.

There are two production files and one concrete audit file. All generic
reasoning shares one `Proofs.Make` instance. Optional upper-bound update laws
are section parameters rather than a second instantiation of the entire proof
functor. Concrete instantiation and `Print Assumptions` live in
`tests/Audit.v`, outside the generic unit. A separate theorem facade would
currently add no value and risk duplicating module contents.

## Checked results

- Fuelled execution and finite paths describe the same successful runs.
- Every step preserves discovery validity, store references, queue ordering,
  and queue uniqueness. This invariant is parameterized by a support
  predicate; taking it to be `True` removes the need for finite support.
- Active recursive owners are strictly ordered and distinct, even without a
  finite-system assumption. Finite generation and rank bounds are proved
  separately for use in termination.
- Materialization persists; every root is materialized on success.
- Structurally ordinary systems keep empty incoming contribution tables.
- Monotone finite systems stay below any post-solution when the update
  preserves upper bounds. The proof uses a predicate on residual code, without
  a full history of earlier observations.
- Structural observations at a valuation are unique and correspond to
  partial-store replay. Completed observations yield post-solutions, including
  spawn closure, when the incoming aggregate bounds hold.
- Reader registration survives reads; a value change invalidates its watched
  observations by queueing their owners. A frame cursor retains a prefix of
  its original constraint, with a ledger connecting raw effects to accumulated
  side inputs. The machine preserves these observations through recursion,
  dead-side cleanup, commit, draining, and episode close.
- `successful_run_correct` has the same statement as the reference theorem:
  every successful run produces a correct final state, including all spawned
  owners. It requires no finite-system assumption.
- With controlled-owner recomputation enabled, a quiet controlled commit must
  stutter. When its phase implements narrowing on descending inputs, it is a
  narrowing fixpoint at that commit. This uses no idempotency assumption; it
  is a local result and still needs to be retained to the final store.
- Correct final states extend to the finite support under source strictness.
  Combining this fact with the independent upper-bound proof gives
  `successful_run_least`, which assumes source strictness, monotonicity, finite
  support, and an upper-bound update law. It has no correctness premise.
- Every reachable reset registration has its scope at or below its source
  and strictly below its target. Closing a higher recursive owner preserves
  the parent owner's incoming and outgoing cell credit.
- Controlled status persists. Every reader of an uncontrolled owner is
  strictly below that owner, so its direct assignment preserves a queue that
  is already below the owner. This covers both recomputation settings.
- Changed side aggregates consume credit in the updated cell. Incoming and
  outgoing credit are combined in one sum. The round budget is lexicographic:
  missing materializations, promotion reserve, and combined side/ordinary
  credit, with a separate allowance for the first round. Its order is well
  founded. Reads, side writes, and commits cannot increase the local budget;
  new materializations, promotions, incident side changes, and controlled
  value changes decrease it. Higher-owner closes preserve it.
- Assuming completion of strictly higher episodes, structural induction
  carries RHS evaluation and dead-side cleanup to a commit. A separate
  induction on the queue's rank ceiling carries draining to either episode
  return or a fresh evaluation of the same owner. `round_reaches_boundary`
  combines these results. Its higher-episode premise is still explicit.

All new proofs end with `Qed`; there are no admitted goals or new axioms.
The fourteen assumption audits report `Closed under the global context`.
The concrete regression also checks two accumulated side effects, a controlling
back read, and spawn closure, then derives correctness from the new theorem.
Budget regressions check an incoming side change without owner promotion,
new materialization, and an already materialized owner.

## Remaining obligations before replacement or merge as a finished solver

1. Finish finite-system termination. Preserve the budget across whole
   recursive episode segments and prove that a fresh same-owner evaluation
   after the first round pays for its queue entry. Then combine the checked
   round order with owner rank induction, discharge the higher-episode
   premise, and finish root seeding and outer draining. Derive sufficient
   fuel and total correctness.
2. Prove ordinary monotone fallback avoidance for both recomputation settings.
3. Prove ordinary narrowing fixedness when controlled-owner recomputation is
   enabled. Do not introduce an idempotency assumption.
4. Restate the remaining public guarantees and audit their concrete instances.
   Then compare proof size and time at matching theorem coverage.

The existing results do not imply these remaining guarantees. In particular,
`termination_iff_fuel` proves equivalence, not that either side always exists.
The correctness and leastness theorems concern successful runs; they do not
establish that every finite system has a successful run.
Likewise, the local budget laws and `round_reaches_boundary` do not yet prove
that every same-owner rerun decreases the budget or that higher episodes
always finish.

## Build and measurement

```sh
opam exec --switch=5.4.0 -- make restarting-compact
opam exec --switch=5.4.0 -- make proof-tests
opam exec --switch=5.4.0 -- python3 tools/benchmark_restarting_proofs.py --repeat 3
```

The benchmark uses fresh serial Rocq compiler processes with existing shared
dependencies and filesystem caches. It checks algorithm identity and reports
source hashes, line counts, compiled object sizes, and wall times per file.
It labels compact measurements as partial regeneration, so they cannot be
mistaken for measurements of an equivalent finished proof stack.

On Rocq 9.1.1 / OCaml 5.4.0, one reference measurement took 24.54 seconds and
produced 51,323,366 bytes of compiled objects across six targets. Its public
theorem unit alone produced 23,968,527 bytes. The current compact subset has
4,565 proof lines; across three runs the median was 3.25 seconds for `Proofs.v`
and 4.68 seconds including the algorithm and audit. Its three compiled objects
total 2,778,180 bytes. The proof unit itself is 2,297,198 bytes. These numbers
show the current development baseline; they do **not** establish a speedup
for a completed replacement.
