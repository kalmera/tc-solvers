# Plus Restarting (SLR-TC+)

Plus Restarting is the SLR-TC+ solver: Dirty-Read Restarting with configurable
FIFO-deferred spawning and controlled-owner recomputation. `AllEnabledFeatures` enables both;
`ReaderWakeupsOnlyFeatures` keeps FIFO spawning and disables recomputation.

Generic correctness, termination, and join leastness hold with either
recomputation setting. For ordinary monotone systems without side effects,
FIFO spawning avoids fallback. Narrowing fixedness additionally requires
controlled-owner recomputation, using the usual update laws without value
idempotency. See `Theorems.v` and the theorem map in `docs/proofs.md`.

`PlusRestarting.Interface` wraps one executable core and exports the
law-free `Sem`, `View`, and `Execution` submodules of the shared `SOLVER`
signature. `Proofs.v` reuses its transfer and execution semantics for invariant
proofs. Its optional law modules establish leastness, ordinary-system precision,
and termination. Finite termination uses repeated-round credit descent, discovery
rank induction, and finite outer scheduling. `Theorems.v` exposes these results
through the public functors and concrete instances.

`Theorems.v` contains the compact hybrid public interface. Its bundled
`Make`, `LeastSolutionMake`, and `OrdinaryFixedPointMake` functors export the
solver-owned `Solver` views, common `Spec` statements, and proved certificates.
The shared consequence lemmas and all Plus Restarting certificates are
proved. `Proofs.v` contains the OneBox precision lemmas as well as the machine
invariants; the public file contains no legacy staged facade.

Total correctness, leastness, and ordinary fixedness each accept one bundle
of implementation inputs and laws. `Theorems.Instances.Parameters` supplies
all three, through `Theorems.Make P`, `Theorems.LeastSolutionMake P`, and
`Theorems.OrdinaryFixedPointMake P`. Their signatures require only the fields
needed for each capability and live in `common/SolverParameters.v`, alongside
the shared spec and contracts. `common/instances/SolverBundles.v` supplies
`ChainParameters Features`, including the join policy and the existing OneBox
update `FixedU`. These common files import no solver or theorem implementation.
