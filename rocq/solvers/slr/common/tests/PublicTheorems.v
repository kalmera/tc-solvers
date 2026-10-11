From Stdlib Require Import List.
From TcSolvers Require Import common.SolverContracts common.instances.SolverBundles.
From TcSolvers Require solvers.slr.simple.Theorems solvers.slr.restarting.Theorems
  solvers.slr.narrowing_fixed_point.Theorems solvers.slr.reluctant_restarting.Theorems
  solvers.slr.dormant_restarting.Theorems solvers.slr.dirty_read_restarting.Theorems
  solvers.slr.deferred_simple.Theorems solvers.slr.plus_restarting.Theorems.

Import ListNotations.
Set Implicit Arguments.

(* A client knows only the common module interfaces and proof records. *)
Module Client (V : VAR) (D : DOMAIN) (Sem : SolverContracts.SEMANTICS V D)
  (View : SolverContracts.SOLVER_VIEW V D Sem)
  (Execution : SolverContracts.EXECUTION V D Sem View).
  Module Spec := SolverContracts.Make V D Sem View Execution.
  Module WithCertificates (Certificates : Spec.VERIFIED).
    Definition soundness : Spec.Soundness :=
      Spec.successful_run_correct Certificates.correctness.
    Definition semantic_termination : Spec.SemanticTermination :=
      Spec.semantic_termination Certificates.termination.
    Definition sufficient_fuel : Spec.SufficientFuel :=
      Spec.sufficient_fuel Certificates.termination.
    Definition total_correct : Spec.TotalCorrectness :=
      Spec.total_correct_from Certificates.correctness Certificates.termination.
    Lemma spawned_variables_solved fuel tf roots final :
      View.solve_fuel fuel tf roots = Some final ->
      forall owner, Spec.solved final owner ->
      forall result, Sem.observes_at (View.sigma_value final) (tf owner) result ->
      forall target, In target (Sem.observed_spawns result) -> Spec.solved final target.
    Proof.
      intros Hrun owner Hsolved result Hobs target Hin.
      destruct (soundness Hrun) as [_ Howners].
      exact (proj2 (proj2 (Howners owner Hsolved)) result Hobs target Hin).
    Qed.
    Definition total_least (leastness : Spec.Leastness) : Spec.TotalLeastness :=
      Spec.total_least_from Certificates.termination leastness.
  End WithCertificates.
  Definition fixedness pre narrow input (certificate : Spec.Fixedness pre narrow input)
    : Spec.SuccessfulRunFixedness pre narrow input := Spec.successful_run_fixed certificate.
  Definition fallback_avoidance pre safe (certificate : Spec.FallbackAvoidance pre safe)
    : Spec.FallbackFree pre safe := Spec.avoids_fallback certificate.
End Client.

(* The client receives the semantic and execution submodules from the solver. *)
Module SolverClient (V : VAR) (D : DOMAIN) (Solver : SOLVER V D).
  Include Client V D Solver.Sem Solver.View Solver.Execution.
End SolverClient.

(* One common bundle supplies every public proof capability. *)
Module BundledClient (P : COMPLETE_PARAMETERS).
  Module Correct := TcSolvers.solvers.slr.plus_restarting.Theorems.Make P.
  Module Consumer := SolverClient P.V P.D Correct.Solver.
  Module Results := Consumer.WithCertificates Correct.Certificates.
  Definition total_correct : Consumer.Spec.TotalCorrectness := Results.total_correct.
  Module Least := TcSolvers.solvers.slr.plus_restarting.Theorems.LeastSolutionMake P.
  Module LeastConsumer := SolverClient P.V P.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition total_least : LeastConsumer.Spec.TotalLeastness :=
    LeastResults.total_least Least.Certificates.leastness.
  Module Fixed := TcSolvers.solvers.slr.plus_restarting.Theorems.OrdinaryFixedPointMake P.
  Module FixedConsumer := SolverClient P.V P.D Fixed.Solver.
  Definition fallback Hdefer := FixedConsumer.fallback_avoidance (Fixed.fallback_avoidance Hdefer).
  Definition fixedness Hon Hdefer := FixedConsumer.fixedness (Fixed.fixedness Hon Hdefer).
  Definition public_total_correct : Consumer.Spec.TotalCorrectness := Correct.total_correct.
  Definition public_total_least : LeastConsumer.Spec.TotalLeastness := Least.total_least_solution.
  Definition public_fallback := Fixed.ordinary_avoids_fallback.
  Definition public_fixed := Fixed.successful_run_fixed.
End BundledClient.

Module BundledTests := BundledClient
  TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.Parameters.
Module E := TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.E.

Module DeferredTests.
  Import TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.Correct.
  Module Consumer := SolverClient E.V E.D Solver.
  Module Results := Consumer.WithCertificates Certificates.
  Definition total_statement : Consumer.Spec.TotalCorrectness := total_correct.
  Definition lookup_binding (final : Solver.View.state) owner :
    Solver.View.lookup final owner = Solver.R.semantic_lookup final owner := eq_refl.
End DeferredTests.

Module SimpleTests.
  Import TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.
  Module Consumer := SolverClient E.V E.D Solver.
  Module Results := Consumer.WithCertificates Certificates.
  Definition soundness_statement (H : Spec.Soundness) :
    forall fuel tf roots final,
      Solver.View.solve_fuel fuel tf roots = Some final ->
      Spec.correct_final_state tf roots final := H.
End SimpleTests.

Module LeastTests.
  Import TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.Least.
  Module Consumer := SolverClient E.V E.D Solver.
  Module Results := Consumer.WithCertificates Certificates.
  Definition total_least_certificate : Consumer.Spec.TotalLeastness :=
    Results.total_least Certificates.leastness.
End LeastTests.

Module OrdinaryTests.
  Import TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.Ordinary.
  Module Consumer := SolverClient E.V E.D Solver.
  Definition fixed_certificate := Consumer.fixedness (fixedness eq_refl eq_refl).
  Definition fallback_certificate := Consumer.fallback_avoidance (fallback_avoidance eq_refl).
End OrdinaryTests.

Module ReaderTests.
  Import TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.OrdinaryReaderWakeups.
  Module Consumer := SolverClient E.V E.D Solver.
  Definition fallback_certificate := Consumer.fallback_avoidance (fallback_avoidance eq_refl).
End ReaderTests.

(* The same client requires the complete basic certificate from every solver. *)
Module RestartingTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.restarting.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.restarting.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End RestartingTests.

Module NarrowingTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End NarrowingTests.

Module ReluctantTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End ReluctantTests.

Module DormantTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End DormantTests.

Module DirtyReadTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End DirtyReadTests.

Module DeferredSimpleTests.
  Module Public.
    Module Solver := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.Solver.
    Module Certificates := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.Certificates.
  End Public.
  Module Consumer := SolverClient E.V E.D Public.Solver.
  Module Results := Consumer.WithCertificates Public.Certificates.
  Definition correctness : Consumer.Spec.Correctness := Public.Certificates.correctness.
  Module Least.
    Module Solver := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Least.Solver.
    Module Certificates := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Least.Certificates.
  End Least.
  Module LeastConsumer := SolverClient E.V E.D Least.Solver.
  Module LeastResults := LeastConsumer.WithCertificates Least.Certificates.
  Definition leastness : LeastConsumer.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least := LeastResults.total_least leastness.
End DeferredSimpleTests.

(* Additional feature settings and replay fixedness without finite support. *)
Module PlusRestartingVariants.
Import TcSolvers.solvers.slr.plus_restarting.Theorems.Instances.
Module ReaderCorrect := TcSolvers.solvers.slr.plus_restarting.Theorems.Make ReaderParameters.
Module Immediate <: TcSolvers.solvers.slr.plus_restarting.PlusRestarting.FEATURES.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := true.
  Definition recompute_controlled := true.
  Definition defer_spawns := false.
End Immediate.
Module ImmediateParameters := ChainParameters Immediate.
Module ImmediateCorrect := TcSolvers.solvers.slr.plus_restarting.Theorems.Make ImmediateParameters.

Definition one (_owner : E.V.t) : Correct.Solver.Sem.rhs :=
  Correct.Solver.Syntax.Ret E.D.One.
Definition one_finite : Correct.Solver.Sem.finite_system one [0].
Proof.
  refine (@Correct.Solver.TransferSemantics.Build_finite_system one [0] [0] _ _ _).
  - repeat constructor; simpl; tauto.
  - intros owner Hin; exact Hin.
  - intros owner Hin; constructor.
Defined.
Example one_total_correct :
  exists fuel final, Correct.Solver.View.solve_fuel fuel one [0] = Some final /\
    Correct.Spec.correct_final_state one [0] final.
Proof. exact (Correct.total_correct one_finite). Qed.

(* The generic fixedness specification also yields the replay equation. *)
Theorem deferred_ordinary_fixed_replay : forall fuel tf roots final owner direct reads effects,
  Ordinary.Spec.monotonic_system tf -> Ordinary.Spec.no_side_effects tf ->
  Ordinary.Solver.View.solve_fuel fuel tf roots = Some final ->
  Ordinary.Spec.solved final owner ->
  Ordinary.Spec.replay final (tf owner) direct reads effects ->
  E.D.leq (E.WN.narrow (Ordinary.Solver.View.sigma_value final owner) direct)
    (Ordinary.Solver.View.sigma_value final owner) = true /\
  E.D.leq (Ordinary.Solver.View.sigma_value final owner)
    (E.WN.narrow (Ordinary.Solver.View.sigma_value final owner) direct) = true.
Proof.
  intros fuel tf roots final owner direct reads effects Hmono Hpure Hrun Howner Heval.
  exact (proj2 (@Ordinary.successful_run_fixed eq_refl eq_refl
    fuel tf roots final (conj Hmono Hpure) Hrun owner Howner) direct reads effects Heval).
Qed.
End PlusRestartingVariants.

(* Separate compilation exercises substitution of the bundled parameters and
    the solver-owned interfaces, including the full spawn-closed certificate. *)
Module DeferredSimpleClient (P : ASCENDING_LEAST_SOLUTION_PARAMETERS).
  Module Public := TcSolvers.solvers.slr.deferred_simple.Theorems.Make P.
  Module Least := TcSolvers.solvers.slr.deferred_simple.Theorems.LeastSolutionMake P.
  Definition correctness : Public.Spec.Correctness := Public.Certificates.correctness.
  Definition total_correct : Public.Spec.TotalCorrectness := Public.total_correct.
  Definition semantic_termination := Public.semantic_termination.
  Definition sufficient_fuel := Public.sufficient_fuel.
  Definition leastness : Least.Spec.Leastness := Least.Certificates.leastness.
  Definition total_least_solution := Least.total_least_solution.
End DeferredSimpleClient.
Module DeferredSimpleGeneric := DeferredSimpleClient
  TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Parameters.
