From TcSolvers Require Export common.SolverContracts common.instances.SolverBundles
  solvers.slr.plus_restarting.PlusRestarting.
From TcSolvers Require Import solvers.slr.plus_restarting.Proofs.

Set Implicit Arguments.

(** Bundled public proofs over the solver-owned views and common specifications. *)
Module Make (P : TOTAL_CORRECTNESS_PARAMETERS).
  Module Internal := Proofs.Make P.V P.D P.U P.SU P.S P.M P.Features
    P.DL P.OUL P.SUL P.SL P.ML.
  Module Solver := Internal.Solver.
  Module Spec := SolverContracts.ForSolver P.V P.D Solver.
  Module Termination := Internal.EpisodeCredits P.OUL P.SUL.
  Module Certificates <: Spec.VERIFIED.
    Theorem correctness : Spec.Correctness.
    Proof. constructor. exact Internal.successful_run_correct. Qed.
    Theorem termination : Spec.Termination.
    Proof.
      constructor.
      - exact Termination.finite_system_terminates.
      - exact Termination.finite_system_has_fuel.
    Qed.
  End Certificates.
  Module Results := Spec.Consequences Certificates.
  Include Results.
End Make.

Module LeastSolutionMake (P : LEAST_SOLUTION_PARAMETERS).
  Module Total := Make P.
  Module Upper := Total.Internal.UpperBounds P.UBL P.SUBL.
  Module Solver := Total.Solver.
  Module Spec := Total.Spec.
  Module Certificates <: Spec.VERIFIED_LEAST.
    Include Total.Certificates.
    Theorem leastness : Spec.Leastness.
    Proof. constructor. exact Upper.successful_run_least. Qed.
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
  Definition safe c := Internal.control_avoids_fallback (Solver.R.cfg_control c).
  Definition direct_input (_final : Solver.View.state) (_owner : P.V.t) (direct : P.D.t) := direct.
  Theorem fallback_avoidance : P.Features.defer_spawns = true ->
    Spec.FallbackAvoidance ordinary_system safe.
  Proof.
    intros Hdefer. constructor.
    intros tf roots [Hmono Hpure] c Hreach.
    exact (@Internal.ordinary_avoids_fallback tf roots Hdefer Hmono Hpure c Hreach).
  Qed.
  Theorem fixedness : P.Features.recompute_controlled = true ->
    P.Features.defer_spawns = true ->
    Spec.Fixedness ordinary_system P.WN.narrow direct_input.
  Proof.
    intros Hon Hdefer. constructor.
    intros fuel tf roots final [Hmono Hpure] Hrun.
    exact (@Internal.successful_run_narrowing_fixed fuel tf roots final Hon Hdefer Hmono Hpure Hrun).
  Qed.
  Definition ordinary_avoids_fallback Hdefer := Spec.avoids_fallback (fallback_avoidance Hdefer).
  Definition successful_run_fixed Hon Hdefer := Spec.successful_run_fixed (fixedness Hon Hdefer).
End OrdinaryFixedPointMake.

Module Instances.
  Module Parameters := ChainParameters PlusRestarting.AllEnabledFeatures.
  Module ReaderParameters := ChainParameters PlusRestarting.ReaderWakeupsOnlyFeatures.
  Module E := Chain.
  Module Correct := Make Parameters.
  Module Least := LeastSolutionMake Parameters.
  Module Ordinary := OrdinaryFixedPointMake Parameters.
  Module OrdinaryReaderWakeups := OrdinaryFixedPointMake ReaderParameters.
  Definition ordinary_fixedness := Ordinary.fixedness eq_refl eq_refl.
  Definition ordinary_fallback_avoidance := Ordinary.fallback_avoidance eq_refl.
  Definition reader_fallback_avoidance := OrdinaryReaderWakeups.fallback_avoidance eq_refl.
End Instances.

Goal True. idtac "Plus Restarting (SLR-TC+) total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "Plus Restarting (SLR-TC+) leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.Certificates.leastness.

Goal True. idtac "Plus Restarting (SLR-TC+) ordinary fallback avoidance proven with assumptions:". Abort.
Print Assumptions Instances.Ordinary.fallback_avoidance.

Goal True. idtac "Plus Restarting (SLR-TC+) ordinary narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.ordinary_fixedness.
