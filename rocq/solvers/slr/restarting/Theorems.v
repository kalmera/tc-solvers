From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.restarting.RestartingInterface.
From TcSolvers Require Import solvers.slr.restarting.Proofs.
Set Implicit Arguments.

Module Make (P : RANKED_UPDATE_PARAMETERS).
  Module Internal := Proofs.Make P.V P.D P.U P.S P.M P.Rk P.Features P.RankLaws P.RankFinite P.DL P.UL P.SL P.ML.
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

Module LeastSolutionMake (P : RANKED_LEAST_SOLUTION_PARAMETERS).
  Module Total := Make P.
  Module Solver := Total.Solver.
  Module Spec := Total.Spec.
  Module Certificates <: Spec.VERIFIED_LEAST.
    Include Total.Certificates.
    Theorem leastness : Spec.Leastness.
    Proof. constructor. intros fuel tf roots finite final Hstrict Hmono Hrun.
      exact (@Total.Internal.successful_run_least fuel tf roots finite final
        P.UBL.update_preserves_upper_bound Hstrict Hmono Hrun).
    Qed.
  End Certificates.
  Module Results := Spec.LeastConsequences Certificates.
  Include Results.
End LeastSolutionMake.

Module OrdinaryFixedPointMake (P : ORDINARY_FIXED_POINT_PARAMETERS).
  Module Internal := Proofs.OrdinaryFixedPoint P.
  Module Solver := Internal.Core.Solver.
  Module Spec := SolverContracts.ForSolver P.V P.D Solver.
  Definition ordinary_system tf (_roots : list P.V.t) :=
    Spec.monotonic_system tf /\ Spec.no_side_effects tf.
  Definition safe c := Internal.control_avoids_fallback (Internal.Core.R.cfg_control c).
  Definition direct_input (_final : Solver.View.state) (_owner : P.V.t) (direct : P.D.t) := direct.
  Theorem fallback_avoidance : Spec.FallbackAvoidance ordinary_system safe.
  Proof. constructor. intros tf roots [Hmono Hpure] c Hreach.
    exact (@Internal.ordinary_avoids_fallback tf roots Hmono Hpure c Hreach).
  Qed.
  Theorem fixedness : P.Features.recompute_controlled = true ->
    Spec.Fixedness ordinary_system P.WN.narrow direct_input.
  Proof. intros Hon. constructor. intros fuel tf roots final [Hmono Hpure] Hrun.
    exact (@Internal.successful_run_fixed fuel tf roots final Hon Hmono Hpure Hrun).
  Qed.
  Definition ordinary_avoids_fallback := Spec.avoids_fallback fallback_avoidance.
  Definition successful_run_fixed Hon := Spec.successful_run_fixed (fixedness Hon).
End OrdinaryFixedPointMake.

Module Instances.
  Module Parameters := ChainParameters SolverFeatures.AllEnabledFeatures.
  Module ReaderFeatures <: RESTARTING_FEATURES.
    Definition recompute_controlled := false.
    Definition defer_spawns := true.
    Definition restart_side_phases := true.
    Definition eliminate_dead_sides := true.
  End ReaderFeatures.
  Module ReaderParameters := ChainParameters ReaderFeatures.
  Module E := Chain.
  Module Correct := Make Parameters.
  Module Least := LeastSolutionMake Parameters.
  Module Ordinary := OrdinaryFixedPointMake Parameters.
  Module OrdinaryReaderWakeups := OrdinaryFixedPointMake ReaderParameters.
  Definition ordinary_fixedness := Ordinary.fixedness eq_refl.
End Instances.

Goal True. idtac "SLR-TC_R total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_R leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.

Goal True. idtac "SLR-TC_R ordinary fallback avoidance proven with assumptions:". Abort.
Print Assumptions Instances.Ordinary.fallback_avoidance.

Goal True. idtac "SLR-TC_R ordinary narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.ordinary_fixedness.
