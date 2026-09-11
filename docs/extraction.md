# Extraction and OCaml clients

`rocq/extraction/` contains extraction directives. `make regenerate` compiles
these with the validated toolchain, writes `ocaml/extracted/`, and regenerates
Goblint adapters. CI requires the result to match the committed generated files.
The OCaml package builds those files without invoking Rocq.

| Dune library | OCaml entry module |
| --- | --- |
| `tc-solvers.extracted.slr.simple` | `Tc_solvers_extracted_simple.Simple` |
| `tc-solvers.extracted.slr.restarting` | `Tc_solvers_extracted_restarting.Restarting` |
| `tc-solvers.extracted.slr.narrowing_fixed_point` | `Tc_solvers_extracted_narrowing_fixed_point.NarrowingFixedPointRuntime` |

Simple and Restarting provide `FirstDiscovery` functors; Narrowing Fixed Point
provides `Solver`. Each exposes fuel-bounded execution returning `None` when fuel
is insufficient. The examples include discovered side-effect targets.

Extraction erases proofs, not client obligations. Domain order/join, collection
operations, update policies, finite support, and transfer behavior must satisfy
the corresponding Rocq contracts. Some erased module arguments become empty
OCaml modules; update-credit functions remain computational arguments. Supplying
an arbitrary credit function does not establish the termination contract.
The integer representation of naturals requires values to remain in range.
Host stack and memory limits remain practical execution constraints.

The specialized Goblint adapters use extracted callback control and handwritten
mutable state operations. Their assumptions additionally cover stable key
identity, lawful hash tables and queues, value immutability, and domain-equivalence
checks. Initial values are retained as constant contributions in every candidate.
They run Goblint postsolving after solving and ignore incremental old data.

Narrowing adapter differential tests compare generated and inlined control with
the full extracted machine, including initial contributions and update policies.
These are implementation checks, not a mechanized adapter-refinement proof.
The proved narrowing-fixpoint instance uses the zero-copy update.
