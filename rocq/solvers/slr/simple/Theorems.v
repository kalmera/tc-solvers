From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.simple.SimpleInterface.
From TcSolvers Require Import solvers.slr.simple.proofs.Correctness
  solvers.slr.simple.proofs.LeastSolutionProof.
Set Implicit Arguments.

Module Make (P : RANKED_UPDATE_PARAMETERS).
  Module Internal := Correctness.Make P.V P.D P.U P.S P.M P.Rk P.RankLaws P.RankFinite P.DL P.UL P.SL P.ML.
  Module Solver := Internal.Sem.Solver.
  Module Spec := Internal.PublicSpec.
  Module Certificates := Internal.Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
End Make.

Module LeastSolutionMake (P : RANKED_LEAST_SOLUTION_PARAMETERS).
  Module Internal := LeastSolutionProof.Make P.V P.D P.U P.S P.M P.Rk P.RankLaws P.RankFinite P.DL P.UL P.UBL P.SL P.ML.
  Module Solver := Internal.Total.Sem.Solver.
  Module Spec := Internal.Total.PublicSpec.
  Module Certificates <: Spec.VERIFIED_LEAST.
    Include Internal.Total.Certificates.
    Theorem leastness : Spec.Leastness.
    Proof. constructor. exact Internal.solve_fuel_least_solution. Qed.
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

Goal True. idtac "SLR-TC_S total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_S leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.
