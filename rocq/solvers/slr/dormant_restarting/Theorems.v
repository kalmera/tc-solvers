From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.dormant_restarting.DormantRestartingInterface.
From TcSolvers Require Import solvers.slr.common.FirstActivation
  solvers.slr.dormant_restarting.proofs.PartialCorrectness
  solvers.slr.dormant_restarting.proofs.Termination
  solvers.slr.dormant_restarting.proofs.LeastSolutionProof.
Set Implicit Arguments.

Module PartialMake (P : PARTIAL_CORRECTNESS_PARAMETERS).
  Module Rk := ListDiscoveryOrder P.V.
  Module RankLaws := FirstActivationLaws P.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws P.V.
  Module DormantRankLaws := FirstActivationLaws P.V.
  Module Internal := PartialCorrectness.Make P.V P.D P.U P.SU P.S P.M
    Rk P.Features RankLaws P.DL P.OSL P.SSL P.SL P.ML.
  Module Solver := Internal.Solver.
  Module Spec := SolverContracts.ForSolver P.V P.D Solver.
  Module Certificates <: Spec.SOUND.
    Theorem correctness : Spec.Correctness.
    Proof. constructor. exact Internal.successful_run_correct. Qed.
  End Certificates.
  Module Results := Spec.SoundConsequences Certificates.
  Include Results.
End PartialMake.

Module Make (P : TOTAL_CORRECTNESS_PARAMETERS).
  Module Rk := ListDiscoveryOrder P.V.
  Module RankLaws := FirstActivationLaws P.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws P.V.
  Module DormantRankLaws := FirstActivationLaws P.V.
  Module Internal := Termination.Make P.V P.D P.U P.SU P.S P.M
    Rk P.Features RankLaws RankFinite DormantRankLaws P.DL P.OUL P.SUL P.SL P.ML.
  Module Solver := Internal.Partial.Solver.
  Module Spec := Internal.PublicSpec.
  Module Certificates := Internal.Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
End Make.

Module LeastSolutionMake (P : LEAST_SOLUTION_PARAMETERS).
  Module Rk := ListDiscoveryOrder P.V.
  Module RankLaws := FirstActivationLaws P.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws P.V.
  Module DormantRankLaws := FirstActivationLaws P.V.
  Module Internal := LeastSolutionProof.Make P.V P.D P.U P.SU P.S P.M
    Rk P.Features RankLaws RankFinite DormantRankLaws P.DL P.OUL P.SUL P.UBL P.SUBL P.SL P.ML.
  Module Solver := Internal.Total.Partial.Solver.
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

Goal True. idtac "Dormant Restarting total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "Dormant Restarting leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.
