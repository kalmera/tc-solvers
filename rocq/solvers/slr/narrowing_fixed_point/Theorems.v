From Stdlib Require Import List.
From TcSolvers Require Import
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


Module Make (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Verified := FixedPoint.Make V D WN.
  Module U := Verified.U.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (WS : WIDEN_STABILITY D WN) (UL : UPDATE_LAWS V D U).
    Module VerifiedLaws := Verified.WithLaws DL WNL WS UL.
    Module WithCollections (S : SET V) (M : MAP V)
      (Features : Base.FEATURES) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

      Module Internal := VerifiedLaws.WithCollections S M Features SL ML.
      Module Sem := Internal.Sem.
      Module R := Internal.R.
      Module N := Internal.Replay.Front.N.

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

      Definition monotonic_system (tf : R.ConstraintSystem.system) : Prop :=
        forall owner, Sem.rhs_dependencies_monotone (tf owner) /\
                      Sem.rhs_effects_monotone (tf owner).

      Definition narrowing_fixed (tf : R.ConstraintSystem.system) (final : R.state) : Prop :=
        forall owner, solved final owner ->
          (exists direct reads effects, replay final (tf owner) direct reads effects) /\
          (forall direct reads effects, replay final (tf owner) direct reads effects ->
            UL.equivalent
              (WN.narrow (R.sigma_value final owner)
                (D.join direct (R.aggregate final owner)))
              (R.sigma_value final owner)).

      Theorem total_correct_and_fixed : forall tf roots,
        Sem.finite_system tf roots -> monotonic_system tf ->
        exists fuel final, N.solve_fuel fuel tf roots = Some final /\
          correct_final_state tf roots final /\ narrowing_fixed tf final.
      Proof. exact Internal.total_correct_and_fixed. Qed.
    End WithCollections.
  End WithLaws.
End Make.

Module FiniteHeight (V : VAR) (D : DOMAIN) (S : SET V) (M : MAP V)
  (Features : Base.FEATURES) (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module U := JoinUpdate V D.
  Module UL := JoinUpdateLaws V D DL FH.
  Module UBL := JoinUpdateUpperBoundLaws V D DL.
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
End FiniteHeight.
