From Stdlib Require Import List.
From TcSolvers Require Export common.Assumptions common.BoxUpdate common.FiniteHeight
  common.instances.Chain
  solvers.slr.narrowing_fixed_point.Proofs
  solvers.slr.narrowing_fixed_point.Precision.
Set Implicit Arguments.

(** Public correctness, leastness, fallback avoidance, and narrowing fixedness. *)
Module Correctness (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Proofs.Make V D U S M Features DL UL SL ML.
  Module Sem.
    Include Internal.Sem.
    Arguments support _ _ _ : clear implicits.
    Module R := Internal.R.
    Module ConstraintSyntax := Internal.B.Syntax.
    Definition step := Internal.B.step.
    Definition steps := Internal.B.steps.
    Definition StepsRefl := Internal.B.steps_refl.
    Definition StepsStep := Internal.B.steps_cons.
    Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
    Definition terminal_config := Internal.B.terminal.
    Definition terminates_to tf roots final :=
      steps tf (R.initial_config roots) (terminal_config final) /\ quiescent final.
    Definition solved := Internal.Spec.solved.
    Definition state_valuation (st : R.state) : valuation := R.sigma_value st.
    Definition rhs_eval := Internal.Spec.replay.
    Definition side_effects_below (st : R.state) (effects : list (V.t * D.t)) :=
      forall target value, In (target,value) effects -> D.leq value (R.sigma_value st target) = true.
    Definition rhs_post_solution (st : R.state) owner (body : R.ConstraintSystem.rhs) :=
      forall direct reads effects, rhs_eval st body direct reads effects ->
        D.leq direct (R.sigma_value st owner) = true /\ side_effects_below st effects.
    Definition correct_final_state tf roots final := forall owner, In owner roots ->
      solved final owner /\ rhs_post_solution final owner (tf owner).
    Definition totally_correct_on tf roots := exists fuel final,
      R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
    Definition rhs_observes_spawns_supported := Internal.B.supported_spawns.
    Definition observes_at_deterministic := Internal.B.observation_unique.
  End Sem.
  Module R := Internal.R.
  Module N := Internal.N.
  Module Spec := Internal.Spec.
  Include Spec.
  Definition terminates_to := Internal.terminates_to.
  Theorem semantic_termination : forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Proof. exact Internal.semantic_termination. Qed.
  Theorem sufficient_fuel : forall tf roots, Sem.finite_system tf roots ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final.
  Proof. exact Internal.sufficient_fuel. Qed.
  Theorem successful_run_correct : forall fuel tf roots final,
    N.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Proof. exact Internal.successful_run_correct. Qed.
  Corollary total_correct : forall tf roots, Sem.finite_system tf roots ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
  Proof. exact Internal.total_correct. Qed.
End Correctness.

(** Expose precision results directly to share their machine instance. *)
Module Make := Precision.Make.

Module LeastSolutionMake (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Proofs.Make V D U S M Features DL UL SL ML.
  Module R := Internal.R.
  Module N := Internal.N.
  Module Sem.
    Include Internal.Sem.
    Arguments support _ _ _ : clear implicits.
    Module R := Internal.R.
    Module ConstraintSyntax := Internal.B.Syntax.
    Definition step := Internal.B.step.
    Definition steps := Internal.B.steps.
    Definition StepsRefl := Internal.B.steps_refl.
    Definition StepsStep := Internal.B.steps_cons.
    Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
    Definition terminal_config := Internal.B.terminal.
    Definition terminates_to tf roots final :=
      steps tf (R.initial_config roots) (terminal_config final) /\ quiescent final.
    Definition solved := Internal.Spec.solved.
    Definition state_valuation (st : R.state) : valuation := R.sigma_value st.
    Definition rhs_eval := Internal.Spec.replay.
    Definition side_effects_below (st : R.state) (effects : list (V.t * D.t)) :=
      forall target value, In (target,value) effects -> D.leq value (R.sigma_value st target) = true.
    Definition rhs_post_solution (st : R.state) owner (body : R.ConstraintSystem.rhs) :=
      forall direct reads effects, rhs_eval st body direct reads effects ->
        D.leq direct (R.sigma_value st owner) = true /\ side_effects_below st effects.
    Definition correct_final_state tf roots final := forall owner, In owner roots ->
      solved final owner /\ rhs_post_solution final owner (tf owner).
    Definition totally_correct_on tf roots := exists fuel final,
      R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
    Definition rhs_observes_spawns_supported := Internal.B.supported_spawns.
    Definition observes_at_deterministic := Internal.B.observation_unique.
  End Sem.
  Module Strict := Internal.B.Strict.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.
  Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (@Sem.support tf roots finite) roots -> Sem.system_monotone_on tf (@Sem.support tf roots finite) ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (@Sem.support tf roots finite) (R.sigma_value final).
  Proof.
    intros tf roots finite; exact (@Internal.total_least_solution tf roots finite UBL.update_preserves_upper_bound).
  Qed.
End LeastSolutionMake.

(** Concrete public instances, retained for existing clients. *)
Module Instances.
  Module E := Chain.
  Module Fixed := Make E.V E.D E.WN.
  Module FixedUL := E.UpdateLaws Fixed.U.
  Module FixedLaws := Fixed.WithLaws E.DL E.WNL E.WS FixedUL.
  Module FixedCells := FixedLaws.WithCollections E.S E.M Base.AllEnabledFeatures E.SL E.ML.
  Definition fixed_run := FixedCells.successful_run_fixedpoint eq_refl.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M Base.AllEnabledFeatures E.DL UL UBL E.SL E.ML.
End Instances.
