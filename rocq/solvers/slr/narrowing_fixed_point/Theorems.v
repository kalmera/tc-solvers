From Stdlib Require Import List.
From TcSolvers Require Import
  common.SolverSpecifications
  common.instances.IdempotentChain
  common.UpdateIdempotency
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

  Module Spec := Internal.Spec.
  Include Spec.

  Definition terminates_to := Internal.Termination.terminates_to.

  Theorem semantic_termination : forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Proof. exact Internal.Termination.solver_terminates. Qed.

  Theorem sufficient_fuel : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final.
  Proof. exact Internal.Termination.sufficient_fuel. Qed.

  Theorem successful_run_correct : forall fuel tf roots final,
    N.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Proof. exact Internal.successful_run_spawn_correct. Qed.

  Corollary total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof.
    intros tf roots finite.
    destruct (sufficient_fuel finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@successful_run_correct fuel tf roots final Hrun).
  Qed.
End Correctness.


(** OneBox fixedness under ordinary value idempotency; feature flags are arbitrary. *)
Module Make (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Fixed := FixedPoint.Make V D WN.
  Module U := Fixed.U.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (WS : WIDEN_STABILITY D WN) (UL : UPDATE_LAWS V D U)
    (IL : VALUE_IDEMPOTENT V D U).
    Module Laws := Fixed.WithLaws DL WNL WS UL IL.
    Module WithCollections (S : SET V) (M : MAP V) (Features : Base.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module Internal := Laws.WithCollections S M Features SL ML.
      Module R := Internal.R.
      Module Sem := Internal.Sem.
      Module N := Internal.N.

      Module Spec := Internal.Spec.
      Include Spec.
      Definition narrowing_fixed := narrowing_fixed_with WN.narrow
        (fun final owner direct => D.join direct (R.aggregate final owner)).

      Theorem successful_run_fixed : forall fuel tf roots final,
        monotonic_system tf -> N.solve_fuel fuel tf roots = Some final ->
        narrowing_fixed tf final.
      Proof.
        intros fuel tf roots final Hmono Hrun.
        exact (@Internal.successful_run_fixedpoint fuel tf roots final Hrun Hmono).
      Qed.

    End WithCollections.
  End WithLaws.
End Make.

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

(** Share one concrete OneBox instance between correctness and fixedness audits.
    Runtime examples are separate and do not instantiate this proof graph again. *)
Module Instances.
  Module E := IdempotentChain.
  Module Fixed := FixedPoint.Make E.V E.D E.WN.
  Module FixedUL := E.UpdateLaws Fixed.U.
  Module FixedIL := E.Idempotency Fixed.U.
  Module FixedLaws := Fixed.WithLaws E.DL E.WNL E.WS FixedUL FixedIL.
  Module FixedCells := FixedLaws.WithCollections E.S E.M
    Base.AllEnabledFeatures E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolution.Make E.V E.D U E.S E.M
    Base.AllEnabledFeatures E.DL UL UBL E.SL E.ML.
End Instances.

Goal True. idtac "SLR-TC_N total correctness proven with assumptions:". Abort.
Print Assumptions Instances.FixedCells.total_correct.

Goal True. idtac "SLR-TC_N leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.

Goal True. idtac "SLR-TC_N narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.FixedCells.successful_run_fixedpoint.
