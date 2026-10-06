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
- Every step preserves finite support, discovery validity, store references,
  queue ordering, and queue uniqueness.
- Active recursive owners are strictly ordered and distinct.
- Materialization persists; every root is materialized on success.
- Structurally ordinary systems keep empty incoming contribution tables.
- Monotone finite systems stay below any post-solution when the update
  preserves upper bounds. The proof uses a predicate on residual code, without
  a full history of earlier observations.
- Structural observations at a valuation are unique and correspond to
  partial-store replay. Completed observations yield post-solutions, including
  spawn closure, when the incoming aggregate bounds hold.
- Reader registration survives reads; a value change invalidates its watched
  observations by queueing their owners. A quiet commit produces a completed
  observation from its evaluated observation.
- With controlled-owner recomputation enabled, a quiet controlled commit must
  stutter. When its phase implements narrowing on descending inputs, it is a
  narrowing fixpoint at that commit. This uses no idempotency assumption; it
  is a local result and still needs to be retained to the final store.
- Correct final states extend to the finite support under source strictness.
  Combining this fact with the independent upper-bound proof gives leastness
  **with an explicit final-correctness premise**.

All new proofs end with `Qed`; there are no admitted goals or new axioms.
The concrete assumption audits report `Closed under the global context`.

## Remaining obligations before replacement or merge as a finished solver

1. Preserve evaluated/completed observations throughout the complete machine,
   including suspended frames, side-input accumulation, dead-side cleanup,
   queue removal, and episode close. Derive `successful_run_correct` without
   a correctness premise.
2. Prove finite-system termination. Use owner rank induction and a round
   measure accounting for materialization, promotion, ordinary update credit,
   and side-cell credit/resets. Derive sufficient fuel and total correctness.
3. Prove ordinary monotone fallback avoidance for both recomputation settings.
4. Prove ordinary narrowing fixedness when controlled-owner recomputation is
   enabled. Do not introduce an idempotency assumption.
5. Restate the complete public guarantees and audit their concrete instances.
   Then compare proof size and time at matching theorem coverage.

The existing results do not imply these remaining guarantees. In particular,
`termination_iff_fuel` proves equivalence, not that either side always exists;
`correct_successful_run_least` explicitly assumes final correctness.

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
2,440 proof lines; across three runs the median was 1.69 seconds for `Proofs.v`
and 2.59 seconds including the algorithm and audit. Its three compiled objects
total 1,524,367 bytes. These numbers show the current development baseline;
they do **not** establish a speedup for a completed replacement.
