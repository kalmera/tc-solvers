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
changed controlled-owner update even when its RHS does not read itself. `Slr.Narrowing_fixed_point.Make (V) (D) (U)` enables both policies.
Hash tables and the bitmap worklist are internal. The first-discovery order
and maximum-rank-first work processing match the existing callback adapters.

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
There is no incremental state, public fuel argument, tracing, or implicit I/O.
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
the update itself depends on the previous value. Narrowing Fixed Point always
performs this recomputation. Restarting exposes `recompute_controlled`; its
ordinary narrowing-fixedness theorem requires this option to be enabled and
requires no side effects. Selecting the suggested two-copy policy does not
instantiate the OneBox fixedness theorem.

Only callback control is extracted; the mutable runtime has no mechanized
refinement proof. Differential tests cover all ten configurations and three
policies. Existing differences from extracted references are checked as
exact baselines in `tests/library/differential.ml`; all tested join and Narrowing
Fixed Point cases agree with their extracted references.

## Development

Edit public interfaces and wrappers in `ocaml/library/`. Generated cores come
from the existing callback adapters through checked frontend-only transformations
in `ocaml/library/generate.py`; edit the original algorithm templates for algorithm
changes. `make library` regenerates from committed adapters; `make regenerate`
rebuilds the complete chain. The generic worklist is always bitmap, independent
of the worklist selected for Goblint. Tests verify generation boundaries and the
library's isolated installation without external solver dependencies.
