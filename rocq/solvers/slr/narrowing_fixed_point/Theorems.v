From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.narrowing_fixed_point.NarrowingFixedPointInterface.
From TcSolvers Require Import solvers.slr.narrowing_fixed_point.Proofs.
Set Implicit Arguments.

Module Make (P : FINITE_UPDATE_PARAMETERS).
  Module Internal := Proofs.Make P.V P.D P.U P.S P.M P.Features P.DL P.UL P.SL P.ML.
  Module Solver := Internal.Solver.
  Module Spec := SolverContracts.ForSolver P.V P.D Solver.
  Module Certificates <: Spec.VERIFIED.
    Theorem correctness : Spec.Correctness.
    Proof. constructor. exact Internal.successful_run_correct. Qed.
    Theorem termination : Spec.Termination.
    Proof. constructor; [exact Internal.semantic_termination |exact Internal.sufficient_fuel]. Qed.
  End Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
End Make.

Module LeastSolutionMake (P : FINITE_LEAST_SOLUTION_PARAMETERS).
  Module Total := Make P.
  Module Solver := Total.Solver.
  Module Spec := Total.Spec.
  Module Certificates <: Spec.VERIFIED_LEAST.
    Include Total.Certificates.
    Theorem leastness : Spec.Leastness.
    Proof. constructor. intros fuel tf roots finite final Hstrict Hmono Hrun.
      exact (@Total.Internal.successful_run_least P.UBL.update_preserves_upper_bound fuel tf roots finite final Hstrict Hmono Hrun).
    Qed.
  End Certificates.
  Module Results := Spec.LeastConsequences Certificates.
  Include Results.
End LeastSolutionMake.

Module FixedPointMake (P : STABLE_FIXED_POINT_PARAMETERS).
  Module Internal := Proofs.FixedPoint P.
  Module Solver := Internal.P.Solver.
  Module Spec := SolverContracts.ForSolver P.V P.D Solver.
  Module Certificates <: Spec.VERIFIED.
    Theorem correctness : Spec.Correctness.
    Proof. constructor. exact Internal.P.successful_run_correct. Qed.
    Theorem termination : Spec.Termination.
    Proof. constructor; [exact Internal.P.semantic_termination |exact Internal.P.sufficient_fuel]. Qed.
  End Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
  Definition monotone_system tf (_roots : list P.V.t) := Spec.monotonic_system tf.
  Definition safe c := Internal.control_avoids_fallback (Internal.R.cfg_control c).
  Definition aggregate_input final owner direct := P.D.join direct (Internal.R.aggregate final owner).
  Theorem fallback_avoidance : Spec.FallbackAvoidance monotone_system safe.
  Proof. constructor. exact Internal.monotonic_avoids_fallback. Qed.
  Theorem fixedness : P.Features.recompute_controlled = true ->
    Spec.Fixedness monotone_system P.WN.narrow aggregate_input.
  Proof. intros Hon. constructor. exact (Internal.successful_run_fixed Hon). Qed.
  Definition monotonic_avoids_fallback := Spec.avoids_fallback fallback_avoidance.
  Definition successful_run_fixed Hon := Spec.successful_run_fixed (fixedness Hon).
End FixedPointMake.

Module Instances.
  Module Parameters := ChainParameters SolverFeatures.AllEnabledFeatures.
  Module E := Chain.
  Module Correct := Make Parameters.
  Module Least := LeastSolutionMake Parameters.
  Module Fixed := FixedPointMake Parameters.
  Definition ordinary_fixedness := Fixed.fixedness eq_refl.
End Instances.

Goal True. idtac "SLR-TC_N total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_N leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.

Goal True. idtac "SLR-TC_N monotone-system owner fallback avoidance proven with assumptions:". Abort.
Print Assumptions Instances.Fixed.fallback_avoidance.

Goal True. idtac "SLR-TC_N narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.ordinary_fixedness.
