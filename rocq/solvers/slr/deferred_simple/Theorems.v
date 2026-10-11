From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.deferred_simple.DeferredSimpleInterface.
From TcSolvers Require Import solvers.slr.deferred_simple.proofs.TotalCorrectness.
Set Implicit Arguments.

Module Make (P : ASCENDING_TOTAL_CORRECTNESS_PARAMETERS).
  Module Internal := TotalCorrectness.Make P.V P.D P.U P.SU P.S P.M P.Features
    P.DL P.OUL P.ASUL P.SL P.ML.
  Module Solver := Internal.Library.Total.C.Solver.
  Module Spec := Internal.PublicSpec.
  Module Certificates := Internal.Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
End Make.

Module LeastSolutionMake (P : ASCENDING_LEAST_SOLUTION_PARAMETERS).
  Module Internal := TotalCorrectness.Make P.V P.D P.U P.SU P.S P.M P.Features
    P.DL P.OUL P.ASUL P.SL P.ML.
  Module Least := Internal.Library.LeastSolution P.UBL P.SUBL.
  Module Solver := Internal.Library.Total.C.Solver.
  Module Spec := Internal.PublicSpec.
  Module Certificates <: Spec.VERIFIED_LEAST.
    Include Internal.Certificates.
    Theorem leastness : Spec.Leastness.
    Proof. constructor. exact Least.solve_fuel_least_solution. Qed.
  End Certificates.
  Module Results := Spec.LeastConsequences Certificates.
  Include Results.
End LeastSolutionMake.

Module Instances.
  Module Parameters := ChainParameters SolverFeatures.AllEnabledFeatures.
  Module E := Chain.
  Module Correct := Make Parameters.
  Module Least := LeastSolutionMake Parameters.
End Instances.

Goal True. idtac "FIFO-Deferred Simple total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "FIFO-Deferred Simple leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.
