From Stdlib Require Import List.
From TcSolvers Require Export common.Assumptions common.BoxUpdate common.FiniteHeight
  common.instances.Chain
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting.Proofs.
Set Implicit Arguments.

(** Public correctness, leastness, and ordinary-system precision results.
    The OneBox instance discharges the optional discovery and phase laws. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : Restarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Proofs.Make V D U S M Rk Features RankLaws RankFinite DL UL SL ML.
  Module Sem.
    Include Internal.Sem.
    Module R := Internal.R.
    Module ConstraintSyntax := Internal.Syntax.
    Definition step := Internal.step.
    Definition steps := Internal.steps.
    Definition StepsRefl := Internal.steps_refl.
    Definition StepsStep := Internal.steps_cons.
    Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
    Definition terminal_config := Internal.terminal.
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
    Definition rhs_observes_spawns_supported := Internal.supported_spawns.
    Definition observes_at_deterministic := Internal.observation_unique.
  End Sem.
  Module R := Internal.R.
  Module Spec := Internal.Spec.
  Include Spec.
  Definition terminates_to := Sem.terminates_to.
  Theorem semantic_termination : forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Proof.
    intros tf roots finite; destruct (Internal.semantic_termination finite) as [final [Hpath Hquiet]].
    exists final; split; [exact Hpath |unfold Sem.quiescent; rewrite Hquiet; reflexivity].
  Qed.
  Theorem sufficient_fuel : forall tf roots, Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final.
  Proof. exact Internal.sufficient_fuel. Qed.
  Theorem successful_run_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Proof. exact Internal.successful_run_correct. Qed.
  Corollary total_correct : forall tf roots, Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
  Proof. exact Internal.total_correct. Qed.
End Make.

Module LeastSolutionMake (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : Restarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Proofs.Make V D U S M Rk Features RankLaws RankFinite DL UL SL ML.
  Module Sem.
    Include Internal.Sem.
    Module R := Internal.R.
    Module ConstraintSyntax := Internal.Syntax.
    Definition step := Internal.step.
    Definition steps := Internal.steps.
    Definition StepsRefl := Internal.steps_refl.
    Definition StepsStep := Internal.steps_cons.
    Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
    Definition terminal_config := Internal.terminal.
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
    Definition rhs_observes_spawns_supported := Internal.supported_spawns.
    Definition observes_at_deterministic := Internal.observation_unique.
  End Sem.
  Module R := Internal.R.
  Module Strict := Internal.Strict.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.
  Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (Sem.support finite) roots ->
    Sem.system_monotone_on tf (Sem.support finite) ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros tf roots finite; exact (@Internal.total_least_solution tf roots finite UBL.update_preserves_upper_bound).
  Qed.
End LeastSolutionMake.

Module OrdinaryFixedPointMake (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module U := OneBoxUpdate V D WN.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (UL : UPDATE_LAWS V D U).
    Module WithCollections (S : SET V) (M : MAP V) (Features : Restarting.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module Ranks := ListDiscoveryOrder V.
      Module RL := ListDiscoveryOrderLaws V.
      Module RF := ListFiniteDiscoveryOrderLaws V.
      Module Internal := Proofs.Make V D U S M Ranks Features RL RF DL UL SL ML.
      Module Sem.
        Include Internal.Sem.
        Module R := Internal.R.
        Module ConstraintSyntax := Internal.Syntax.
        Definition step := Internal.step.
        Definition steps := Internal.steps.
        Definition StepsRefl := Internal.steps_refl.
        Definition StepsStep := Internal.steps_cons.
        Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
        Definition terminal_config := Internal.terminal.
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
        Definition rhs_observes_spawns_supported := Internal.supported_spawns.
        Definition observes_at_deterministic := Internal.observation_unique.
      End Sem.
      Module R := Internal.R.
      Module Spec := Internal.Spec.
      Include Spec.
      Definition discovery : Internal.first_discovery_laws.
      Proof.
        constructor.
        - intros order target next rank variable Hobserve [variable_rank Hlookup].
          unfold Ranks.observe in Hobserve; destruct (Ranks.lookup order target) eqn:Htarget; inversion Hobserve; subst next rank.
          + right; exists variable_rank; exact Hlookup.
          + cbn in Hlookup; destruct (V.eq_dec variable target) as [Heq|Hneq].
            * left; exact Heq.
            * right; exists variable_rank; exact Hlookup.
        - intros order target next rank owner old_rank Hvalid Hfresh Howner Hobserve.
          destruct (@RL.observe_fresh order target next rank Hfresh Hobserve) as [-> _].
          exact (@RL.lookup_bound order owner old_rank Hvalid Howner).
      Qed.
      Definition phases : Internal.ordinary_phase_laws.
      Proof.
        refine {| Internal.phase_safe := U.avoids_fallback;
          Internal.phase_narrowing := fun phase => phase = U.BoxN |}.
        - apply U.initial_avoids_fallback.
        - intros owner Hnarrow; discriminate.
        - intros owner phase old input Hsafe Hinput;
            exact (@U.admissible_update_avoids_fallback false owner phase old input Hsafe Hinput).
        - intros owner phase old input Hsafe Hnarrow; destruct phase;
            cbn [U.update] in Hnarrow; destruct (D.leq input old) eqn:Hle; try discriminate; reflexivity.
        - intros owner phase old input Hsafe Hinput; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
            cbn [U.update]; rewrite Hinput; apply WNL.narrow_upper; exact Hinput.
      Defined.
      Lemma update_narrow owner phase old input : Internal.phase_safe phases phase ->
        D.leq input old = true -> snd (U.update false owner phase old input) = WN.narrow old input.
      Proof.
        intros Hsafe Hinput; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
          cbn [U.update]; rewrite Hinput; reflexivity.
      Qed.
      Definition narrowing_fixed := narrowing_fixed_with WN.narrow (fun _ _ direct => direct).
      Definition control_avoids_fallback := Internal.control_avoids_fallback phases.
      Definition avoids_fallback (tf : R.ConstraintSystem.system) (roots : list V.t) :=
        forall c, Sem.steps tf (R.initial_config roots) c -> control_avoids_fallback (R.cfg_control c).
      (** Fallback avoidance and narrowing fixedness for finite ordinary systems. *)
      Theorem ordinary_avoids_fallback : forall tf roots,
        Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf -> avoids_fallback tf roots.
      Proof. intros tf roots _; exact (@Internal.ordinary_avoids_fallback discovery phases tf roots). Qed.
      Theorem successful_run_fixed : Features.recompute_controlled = true ->
        forall fuel tf roots final, Sem.finite_system tf roots -> monotonic_system tf -> no_side_effects tf ->
        R.solve_fuel fuel tf roots = Some final -> narrowing_fixed tf final.
      Proof.
        intros Hon fuel tf roots final _; exact (@Internal.successful_run_fixed discovery phases WN.narrow
          WNL.narrow_lower WNL.narrow_upper update_narrow fuel tf roots final Hon).
      Qed.
      (** Fallback avoidance and successful-run fixedness also hold without
          a finite-system premise. *)
      Definition ordinary_avoids_fallback_unbounded := @Internal.ordinary_avoids_fallback discovery phases.
      Definition successful_run_fixed_unbounded := @Internal.successful_run_fixed discovery phases WN.narrow
        WNL.narrow_lower WNL.narrow_upper update_narrow.
      Definition total_fixed := @Internal.total_fixed discovery phases WN.narrow
        WNL.narrow_lower WNL.narrow_upper update_narrow.
    End WithCollections.
  End WithLaws.
End OrdinaryFixedPointMake.

(** Concrete public instances, retained for existing clients. *)
Module Instances.
  Module E := Chain.
  Module Rk := ListDiscoveryOrder E.V.
  Module RankLaws := ListDiscoveryOrderLaws E.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws E.V.
  Module Correct := Make E.V E.D E.U E.S E.M Rk Restarting.AllEnabledFeatures
    RankLaws RankFinite E.DL E.UL E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M Rk Restarting.AllEnabledFeatures
    RankLaws RankFinite E.DL UL UBL E.SL E.ML.
  Module IE := Chain.
  Module Fixed := OrdinaryFixedPointMake IE.V IE.D IE.WN.
  Module FixedUL := IE.UpdateLaws Fixed.U.
  Module FixedLaws := Fixed.WithLaws IE.DL IE.WNL FixedUL.
  Module Ordinary := FixedLaws.WithCollections IE.S IE.M Restarting.AllEnabledFeatures
    IE.SL IE.ML.
  Module OrdinaryReaderWakeups := FixedLaws.WithCollections IE.S IE.M
    Restarting.ReaderWakeupsOnlyFeatures IE.SL IE.ML.
  Definition ordinary_fixed := Ordinary.successful_run_fixed eq_refl.
End Instances.

Goal True. idtac "SLR-TC_R total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_R leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.

Goal True. idtac "SLR-TC_R ordinary fallback avoidance proven with assumptions:". Abort.
Print Assumptions Instances.Ordinary.ordinary_avoids_fallback.

Goal True. idtac "SLR-TC_R total ordinary narrowing fixedness proven with assumptions:". Abort.
Print Assumptions Instances.Ordinary.total_fixed.
