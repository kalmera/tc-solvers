From Stdlib Require Import List.
From TcSolvers Require Import
  common.instances.Chain
  common.Assumptions common.BoxUpdate common.FiniteHeight
  solvers.slr.narrowing_fixed_point.proofs.Replay
  solvers.slr.narrowing_fixed_point.proofs.FixedPoint
  solvers.slr.narrowing_fixed_point.proofs.LeastSolution.

Import ListNotations.
Set Implicit Arguments.

Module Correctness (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Replay.Make V D U S M Features DL UL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.
  Module N := Internal.Front.N.

  Definition solved (final : R.state) (owner : V.t) : Prop :=
    exists value, M.lookup (R.sigma final) owner = Some value.

  Definition replay (final : R.state) :=
    Sem.rhs_eval_with (fun target => M.lookup (R.sigma final) target).

  Definition owner_post_solution (tf : R.ConstraintSystem.system)
    (final : R.state) (owner : V.t) : Prop :=
    forall direct reads effects, replay final (tf owner) direct reads effects ->
      D.leq direct (R.sigma_value final owner) = true /\
      (forall target value, In (target,value) effects ->
        D.leq value (R.sigma_value final target) = true).

  Definition correct_final_state (tf : R.ConstraintSystem.system)
    (roots : list V.t) (final : R.state) : Prop :=
    forall owner, In owner roots ->
      solved final owner /\ owner_post_solution tf final owner.

  Theorem total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof.
    intros tf roots finite. destruct (Internal.Termination.sufficient_fuel finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |now apply Internal.successful_run_correct in Hrun].
  Qed.
End Correctness.


(** Reuse the implementation's public vocabulary and theorem directly;
    nested wrapper functors duplicate the large replay proof graph. *)
Module Make := FixedPoint.Make.

Module LeastSolutionMake (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := LeastSolution.Make V D U S M Features DL UL UBL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.
  Module N := Internal.Replay.Front.N.
  Module Strict := Internal.Strict.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.

  Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (@Sem.support tf roots finite) roots ->
    Sem.system_monotone_on tf (@Sem.support tf roots finite) ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (@Sem.support tf roots finite) (R.sigma_value final).
  Proof. exact Internal.total_least_solution. Qed.
End LeastSolutionMake.

(** Concrete audits discharge the module laws; the theorems above remain generic. *)
Module Instances.
  Module E := Chain.
  Module Correct := Correctness E.V E.D E.U E.S E.M
    Base.AllEnabledFeatures E.DL E.UL E.SL E.ML.
  Module Fixed := Make E.V E.D E.WN.
  Module FixedUL := E.UpdateLaws Fixed.U.
  Module FixedLaws := Fixed.WithLaws E.DL E.WNL E.WS FixedUL.
  Module FixedCells := FixedLaws.WithCollections E.S E.M
    Base.AllEnabledFeatures E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M
    Base.AllEnabledFeatures E.DL UL UBL E.SL E.ML.
End Instances.

Goal True. idtac "SLR-TC_N total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_N leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.

Goal True. idtac "SLR-TC_N total correctness and narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.FixedCells.total_correct_and_fixed.
