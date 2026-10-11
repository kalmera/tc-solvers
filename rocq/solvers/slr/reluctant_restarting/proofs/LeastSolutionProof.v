From Stdlib Require Import List Sorting.Permutation.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  common.SourceStrictness
  common.Observations
  common.SideUpdate
  common.ReluctantUpdate
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces
  solvers.slr.reluctant_restarting.proofs.Termination.

Import ListNotations.
Set Implicit Arguments.

(** Internal least-solution proof for updates that preserve every common upper bound. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : ReluctantRestarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U)
  (SUL : RESTARTING_SIDE_UPDATE_TERMINATION_LAWS V D SU)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Total := Termination.Make
    V D U SU S M Rk Features RankLaws RankFinite DL OUL SUL SL ML.
  Module Sem := Total.Sem.
  Module R := Total.R.
  Module Least := Sem.Observation.
  Import Least.
  Notation rhs_observes := Sem.rhs_observes.
  Notation ObserveRet := Sem.ObserveRet.
  Notation ObserveGet := Sem.ObserveGet.
  Notation ObserveSide := Sem.ObserveSide.
  Notation ObserveSpawn := Sem.ObserveSpawn.
  Notation observes_at := Sem.observes_at.
  Notation rhs_dependencies_monotone := Sem.rhs_dependencies_monotone.
  Notation rhs_effects_monotone := Sem.rhs_effects_monotone.
  Notation system_monotone_on := Sem.system_monotone_on.
  Notation system_dependencies_monotone := Sem.system_dependencies_monotone.
  Notation system_effects_monotone := Sem.system_effects_monotone.
  Notation post_solution_on := Sem.post_solution_on.
  Notation least_solution_on := Sem.least_solution_on.
  Notation closed_finite_system := Sem.closed_finite_system.
  Notation closed_variables_nodup := Sem.closed_variables_nodup.
  Notation closed_system_supported := Sem.closed_system_supported.

  Lemma dependency_order_gives_read_order :
    forall body lower upper,
      rhs_dependencies_monotone body ->
      rhs_observes body lower ->
      rhs_observes body upper ->
      common_read_values_le lower upper ->
      valued_events_le
        (observed_reads lower) (observed_reads upper).
  Proof.
    intros body lower upper Hdependencies Hlower Hupper Hvalues
      target lower_value Hin.
    pose proof (Hdependencies lower upper Hlower Hupper Hvalues)
      as Hincluded.
    assert (Htarget :
      List.In target (List.map fst (observed_reads lower))).
    { apply in_map_iff. exists (target, lower_value). now split. }
    specialize (Hincluded target Htarget).
    apply in_map_iff in Hincluded.
    destruct Hincluded as [[upper_target upper_value] [Hequal Hinupper]].
    cbn in Hequal. subst upper_target.
    exists upper_value. split; [exact Hinupper |].
    eapply Hvalues; eassumption.
  Qed.

  Lemma monotone_observations :
    forall body lower upper,
      rhs_dependencies_monotone body ->
      rhs_effects_monotone body ->
      rhs_observes body lower ->
      rhs_observes body upper ->
      common_read_values_le lower upper ->
      effects_le lower upper.
  Proof.
    intros body lower upper Hdependencies Heffects
      Hlower Hupper Hvalues.
    eapply Heffects; [exact Hlower |exact Hupper |].
    eapply dependency_order_gives_read_order; eassumption.
  Qed.

  Lemma supported_observes_at :
    forall supported body values,
      Sem.rhs_supported supported body ->
      exists result, observes_at values body result.
  Proof.
    intros supported body values Hsupported. induction Hsupported.
    - exists {| observed_direct := value;
                observed_reads := [];
                observed_sides := [];
                observed_spawns := [] |}.
      split; [apply ObserveRet |intros target observed Hin; inversion Hin].
    - destruct (H1 (values target)) as [result [Hresult Hreads]].
      exists {| observed_direct := observed_direct result;
                observed_reads := (target, values target) ::
                  observed_reads result;
                observed_sides := observed_sides result;
                observed_spawns := observed_spawns result |}.
      split; [now apply ObserveGet |].
      intros observed value Hin. cbn in Hin.
      destruct Hin as [Hequal | Hin].
      + inversion Hequal. reflexivity.
      + now apply Hreads with (target := observed).
    - destruct IHHsupported as [result [Hresult Hreads]].
      exists {| observed_direct := observed_direct result;
                observed_reads := observed_reads result;
                observed_sides := (target, value) :: observed_sides result;
                observed_spawns := observed_spawns result |}.
      split; [now apply ObserveSide |exact Hreads].
    - destruct IHHsupported as [result [Hresult Hreads]].
      exists {| observed_direct := observed_direct result;
                observed_reads := observed_reads result;
                observed_sides := observed_sides result;
                observed_spawns := target :: observed_spawns result |}.
      split; [now apply ObserveSpawn |exact Hreads].
  Qed.

  Definition full_rhs_context
    (root current : R.ConstraintSystem.rhs)
    (prefix_reads prefix_sides : list (V.t * D.t))
    (prefix_spawns : list V.t) : Prop :=
    forall suffix,
      rhs_observes current suffix ->
      exists result,
        rhs_observes root result /\
        observed_direct result = observed_direct suffix /\
        observed_reads result = prefix_reads ++ observed_reads suffix /\
        observed_sides result = prefix_sides ++ observed_sides suffix /\
        observed_spawns result = prefix_spawns ++ observed_spawns suffix.

  Lemma initial_full_rhs_context :
    forall body, full_rhs_context body body [] [] [].
  Proof.
    intros body suffix Hsuffix. exists suffix.
    repeat split; try exact Hsuffix; reflexivity.
  Qed.

  Lemma full_rhs_context_get :
    forall root target next prefix_reads prefix_sides prefix_spawns value,
      full_rhs_context root (R.ConstraintSystem.Get target next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root (next value)
        (prefix_reads ++ [(target, value)]) prefix_sides prefix_spawns.
  Proof.
    intros root target next prefix_reads prefix_sides prefix_spawns
      value Hcontext suffix Hsuffix.
    pose (current :=
      {| observed_direct := observed_direct suffix;
         observed_reads := (target, value) :: observed_reads suffix;
         observed_sides := observed_sides suffix;
         observed_spawns := observed_spawns suffix |}).
    assert (Hcurrent :
      rhs_observes (R.ConstraintSystem.Get target next) current).
    { unfold current. now apply ObserveGet. }
    destruct (Hcontext current Hcurrent) as
      [result [Hresult [Hdirect [Hreads [Hsides Hspawns]]]]].
    exists result. repeat split; try assumption.
    rewrite Hreads. unfold current. cbn.
    change (prefix_reads ++ ([(target, value)] ++ observed_reads suffix) =
      (prefix_reads ++ [(target, value)]) ++ observed_reads suffix).
    apply app_assoc.
  Qed.

  Lemma full_rhs_context_side :
    forall root target payload next
      prefix_reads prefix_sides prefix_spawns,
      full_rhs_context root (R.ConstraintSystem.Side target payload next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root next prefix_reads
        (prefix_sides ++ [(target, payload)]) prefix_spawns.
  Proof.
    intros root target payload next prefix_reads prefix_sides prefix_spawns
      Hcontext suffix Hsuffix.
    pose (current :=
      {| observed_direct := observed_direct suffix;
         observed_reads := observed_reads suffix;
         observed_sides := (target, payload) :: observed_sides suffix;
         observed_spawns := observed_spawns suffix |}).
    assert (Hcurrent :
      rhs_observes (R.ConstraintSystem.Side target payload next) current).
    { unfold current. now apply ObserveSide. }
    destruct (Hcontext current Hcurrent) as
      [result [Hresult [Hdirect [Hreads [Hsides Hspawns]]]]].
    exists result. repeat split; try assumption.
    rewrite Hsides. unfold current. cbn.
    change (prefix_sides ++
      ([(target, payload)] ++ observed_sides suffix) =
      (prefix_sides ++ [(target, payload)]) ++ observed_sides suffix).
    apply app_assoc.
  Qed.

  Lemma full_rhs_context_spawn :
    forall root target next prefix_reads prefix_sides prefix_spawns,
      full_rhs_context root (R.ConstraintSystem.Spawn target next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root next prefix_reads prefix_sides
        (prefix_spawns ++ [target]).
  Proof.
    intros root target next prefix_reads prefix_sides prefix_spawns
      Hcontext suffix Hsuffix.
    pose (current :=
      {| observed_direct := observed_direct suffix;
         observed_reads := observed_reads suffix;
         observed_sides := observed_sides suffix;
         observed_spawns := target :: observed_spawns suffix |}).
    assert (Hcurrent :
      rhs_observes (R.ConstraintSystem.Spawn target next) current).
    { unfold current. now apply ObserveSpawn. }
    destruct (Hcontext current Hcurrent) as
      [result [Hresult [Hdirect [Hreads [Hsides Hspawns]]]]].
    exists result. repeat split; try assumption.
    rewrite Hspawns. unfold current. cbn.
    change (prefix_spawns ++ ([target] ++ observed_spawns suffix) =
      (prefix_spawns ++ [target]) ++ observed_spawns suffix).
    apply app_assoc.
  Qed.

  Lemma full_rhs_context_bottom_completion :
    forall root current prefix_reads prefix_sides prefix_spawns supported,
      full_rhs_context root current
        prefix_reads prefix_sides prefix_spawns ->
      Sem.rhs_supported supported current ->
      exists suffix result,
        observes_at (fun _ => D.bottom) current suffix /\
        rhs_observes root result /\
        observed_direct result = observed_direct suffix /\
        observed_reads result = prefix_reads ++ observed_reads suffix /\
        observed_sides result = prefix_sides ++ observed_sides suffix /\
        observed_spawns result = prefix_spawns ++ observed_spawns suffix.
  Proof.
    intros root current prefix_reads prefix_sides prefix_spawns
      supported Hcontext Hsupported.
    destruct (@supported_observes_at supported current
      (fun _ => D.bottom) Hsupported) as [suffix [Hsuffix Hbottom]].
    destruct (Hcontext suffix Hsuffix) as
      [result [Hresult [Hdirect [Hreads [Hsides Hspawns]]]]].
    exists suffix, result. repeat split; assumption.
  Qed.

  Definition sigma_below
    (upper : Least.valuation) (st : R.state) : Prop :=
    forall variable,
      D.leq (R.sigma_value st variable) (upper variable) = true.

  Definition aggregates_below
    (upper : Least.valuation) (st : R.state) : Prop :=
    forall target,
      D.leq (R.aggregate st target) (upper target) = true.

  Record state_below (upper : Least.valuation) (st : R.state) : Prop := {
    state_sigma_below : sigma_below upper st;
    state_aggregates_below : aggregates_below upper st;
  }.

  Definition frame_local_below
    (upper : Least.valuation) (fr : R.frame) : Prop :=
    forall target value,
      M.lookup (R.frame_local_side fr) target = Some value ->
      D.leq value (upper target) = true.

  Record frame_data_below
    (support : list V.t) (upper : Least.valuation) (fr : R.frame) : Prop := {
    frame_owner_below_supported :
      List.In (R.frame_owner fr) support;
    frame_local_side_below :
      frame_local_below upper fr;
  }.

  Inductive rhs_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (owner : V.t)
    (current : R.ConstraintSystem.rhs) : Prop :=
  | RhsBelow :
      forall
        (owner_supported : List.In owner support)
        (root_supported :
          Sem.rhs_supported (fun target => List.In target support) (tf owner))
        (current_supported :
          Sem.rhs_supported (fun target => List.In target support) current)
        (prefix_reads prefix_sides : list (V.t * D.t))
        (prefix_spawns : list V.t),
        full_rhs_context (tf owner) current
          prefix_reads prefix_sides prefix_spawns ->
        prefix_reads_below upper prefix_reads ->
        rhs_below support tf upper owner current.

  Record active_rhs_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (fr : R.frame)
    (body : R.ConstraintSystem.rhs) : Prop := {
    active_frame_data_below : frame_data_below support upper fr;
    active_body_below :
      rhs_below support tf upper (R.frame_owner fr) body;
  }.

  Record completed_frame_below
    (support : list V.t) (upper : Least.valuation)
    (fr : R.frame) (direct : D.t) : Prop := {
    completed_frame_data_below : frame_data_below support upper fr;
    completed_direct_below :
      D.leq direct (upper (R.frame_owner fr)) = true;
  }.

  Fixpoint continuation_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr target next rest =>
        active_rhs_below support tf upper fr
          (R.ConstraintSystem.Get target next) /\
        continuation_below support tf upper rest
    | R.KAfterSide fr next rest
    | R.KAfterSpawn fr next rest =>
        active_rhs_below support tf upper fr next /\
        continuation_below support tf upper rest
    | R.KDead fr direct _ rest =>
        completed_frame_below support upper fr direct /\
        continuation_below support tf upper rest
    | R.KDrain fr rest =>
        frame_data_below support upper fr /\
        continuation_below support tf upper rest
    end.

  Definition control_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode owner rest =>
        List.In owner support /\
        continuation_below support tf upper rest
    | R.RunRhs fr body rest =>
        active_rhs_below support tf upper fr body /\
        continuation_below support tf upper rest
    | R.RunDead fr direct _ rest | R.RunCommit fr direct rest =>
        completed_frame_below support upper fr direct /\
        continuation_below support tf upper rest
    | R.RunDrain fr rest =>
        frame_data_below support upper fr /\
        continuation_below support tf upper rest
    | R.Return rest => continuation_below support tf upper rest
    end.

  Record config_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (c : R.config) : Prop := {
    config_state_below : state_below upper (R.cfg_state c);
    config_control_below : control_below support tf upper (R.cfg_control c);
  }.

  Lemma state_below_core_view :
    forall upper before after,
      R.sigma before = R.sigma after ->
      R.contributions before = R.contributions after ->
      state_below upper before ->
      state_below upper after.
  Proof.
    intros upper before after Hsigma Hcontributions [Hvalues Haggregates].
    constructor.
    - intros variable. unfold R.sigma_value in *.
      rewrite <- Hsigma. apply Hvalues.
    - intros target. unfold R.aggregate in *.
      rewrite <- Hcontributions. apply Haggregates.
  Qed.

  Lemma empty_state_below :
    forall upper, state_below upper R.empty_state.
  Proof.
    intros upper. constructor.
    - intros variable. unfold R.sigma_value. cbn.
      rewrite ML.lookup_empty. apply DL.bottom_least.
    - intros target. unfold R.aggregate, R.lookup_map. cbn.
      rewrite ML.lookup_empty, ML.values_empty. cbn.
      apply DL.bottom_least.
  Qed.

  Lemma join_values_le :
    forall lower upper,
      (forall value,
        List.In value lower ->
        exists bound,
          List.In bound upper /\ D.leq value bound = true) ->
      D.leq (R.join_values lower) (R.join_values upper) = true.
  Proof.
    induction lower as [|value rest IH]; intros upper Hvalues; cbn.
    - apply DL.bottom_least.
    - apply DL.join_least.
      + destruct (Hvalues value (or_introl eq_refl))
          as [bound [Hbound Hle]].
        eapply DL.leq_trans; [exact Hle |].
        eapply Total.value_below_join_values. exact Hbound.
      + apply IH. intros observed Hin. apply Hvalues. now right.
  Qed.

  Lemma join_values_permutation_le :
    forall lower upper,
      Permutation lower upper ->
      D.leq (R.join_values lower) (R.join_values upper) = true.
  Proof.
    intros lower upper Hpermutation. apply join_values_le.
    intros value Hin. exists value. split.
    - eapply Permutation_in; eassumption.
    - apply DL.leq_refl.
  Qed.

  Lemma stored_contribution_below :
    forall upper st source target,
      aggregates_below upper st ->
      D.leq (R.stored_contribution st source target) (upper target) = true.
  Proof.
    intros upper st source target Haggregate.
    unfold R.stored_contribution.
    destruct (M.lookup (R.lookup_map (R.contributions st) target) source)
      as [value |] eqn:Hlookup.
    - eapply DL.leq_trans.
      + eapply Total.stored_contribution_below_aggregate. exact Hlookup.
      + apply Haggregate.
    - apply DL.bottom_least.
  Qed.

  Lemma aggregate_update_below :
    forall upper st source target next,
      aggregates_below upper st ->
      D.leq next (upper target) = true ->
      aggregates_below upper
        (R.with_contributions st
          (R.update_map (R.contributions st) target source next)).
  Proof.
    intros upper st source target next Haggregate Hnext observed.
    destruct (V.eq_dec observed target) as [-> | Hneq].
    - unfold R.aggregate, R.update_map, R.lookup_map. cbn.
      rewrite ML.lookup_update_same.
      destruct (ML.values_update
        (R.lookup_map (R.contributions st) target) source next)
        as [rest [Hnew Hold]].
      eapply DL.leq_trans.
      + apply join_values_permutation_le. exact Hnew.
      + cbn. apply DL.join_least; [exact Hnext |].
        eapply DL.leq_trans; [|apply Haggregate].
        destruct (M.lookup
          (R.lookup_map (R.contributions st) target) source)
          as [old |] eqn:Hlookup.
        * eapply DL.leq_trans with
            (y := R.join_values (old :: rest)).
          -- cbn. apply DL.join_upper_right.
          -- unfold R.aggregate.
             apply join_values_permutation_le.
             now apply Permutation_sym.
        * unfold R.aggregate. apply join_values_permutation_le.
          now apply Permutation_sym.
    - unfold R.aggregate, R.update_map, R.lookup_map. cbn.
      rewrite ML.lookup_update_other by exact Hneq.
      apply Haggregate.
  Qed.

  Lemma state_below_observe :
    forall upper st target,
      state_below upper st ->
      state_below upper (R.observe st target).
  Proof.
    intros upper st target Hbelow. unfold R.observe.
    destruct (R.Ranking.observe (R.ranking st) target).
    eapply state_below_core_view; cbn; try reflexivity; exact Hbelow.
  Qed.

  Lemma state_below_with_queue :
    forall upper st queue,
      state_below upper st -> state_below upper (R.with_queue st queue).
  Proof.
    intros upper st queue Hstate.
    eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma state_below_enqueue :
    forall upper st target,
      state_below upper st -> state_below upper (R.enqueue st target).
  Proof.
    intros upper st target Hstate. unfold R.enqueue.
    repeat match goal with
    | |- context [if ?condition then _ else _] => destruct condition eqn:?
    | |- context [match ?subject with _ => _ end] => destruct subject eqn:?
    end;
    try exact Hstate;
    eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma state_below_publish_targets :
    forall upper st fr,
      state_below upper st -> state_below upper (R.publish_targets st fr).
  Proof.
    intros upper st fr Hstate. unfold R.publish_targets.
    eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma state_below_reset_registered_cells :
    forall upper st owner,
      state_below upper st ->
      state_below upper (R.reset_registered_cells st owner).
  Proof.
    intros upper st owner Hstate. unfold R.reset_registered_cells.
    destruct Features.restart_side_phases;
      [eapply state_below_core_view; cbn; try reflexivity; exact Hstate
      |exact Hstate].
  Qed.

  Lemma state_below_materialize :
    forall upper st target,
      state_below upper st ->
      state_below upper (R.materialize st target).
  Proof.
    intros upper st target Hbelow. unfold R.materialize.
    destruct (M.lookup (R.sigma st) target) eqn:Hlookup; [exact Hbelow |].
    constructor.
    - intros observed. unfold R.sigma_value. cbn.
      destruct (V.eq_dec observed target) as [-> |Hneq].
      + rewrite ML.lookup_update_same. apply DL.bottom_least.
      + rewrite ML.lookup_update_other by exact Hneq.
        apply (state_sigma_below Hbelow).
    - exact (state_aggregates_below Hbelow).
  Qed.

  Lemma state_below_sigma_update :
    forall upper st variable value,
      state_below upper st ->
      D.leq value (upper variable) = true ->
      state_below upper
        (R.with_sigma st (M.update (R.sigma st) variable value)).
  Proof.
    intros upper st variable value Hbelow Hvalue. constructor.
    - intros observed. unfold R.sigma_value. cbn.
      destruct (V.eq_dec observed variable) as [-> |Hneq].
      + now rewrite ML.lookup_update_same.
      + rewrite ML.lookup_update_other by exact Hneq.
        apply (state_sigma_below Hbelow).
    - exact (state_aggregates_below Hbelow).
  Qed.

  Lemma state_below_with_contribution :
    forall upper st source target value,
      state_below upper st ->
      D.leq value (upper target) = true ->
      state_below upper
        (R.with_contributions st
          (R.update_map (R.contributions st) target source value)).
  Proof.
    intros upper st source target value Hbelow Hvalue. constructor.
    - exact (state_sigma_below Hbelow).
    - apply aggregate_update_below.
      + exact (state_aggregates_below Hbelow).
      + exact Hvalue.
  Qed.

  Lemma state_below_promote_side_target :
    forall upper st fr target,
      state_below upper st ->
      state_below upper (R.promote_side_target st fr target).
  Proof.
    intros upper st fr target Hstate. unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr)); [exact Hstate |].
    unfold R.promote_controlled.
    eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma state_below_register_reset :
    forall upper st source target scope phase,
      state_below upper st ->
      state_below upper (R.register_reset st source target scope phase).
  Proof.
    intros upper st source target scope phase Hstate.
    unfold R.register_reset.
    repeat match goal with
    | |- context [if ?condition then _ else _] => destruct condition eqn:?
    | |- context [match ?subject with _ => _ end] => destruct subject eqn:?
    end;
    eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma frame_data_fresh :
    forall support upper st owner phase,
      List.In owner support ->
      frame_data_below support upper (R.fresh_frame st owner phase).
  Proof.
    intros support upper st owner phase Howner. constructor; [exact Howner |].
    intros target value Hlookup. cbn in Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma frame_data_with_phase :
    forall support upper fr phase,
      frame_data_below support upper fr ->
      frame_data_below support upper (R.with_frame_phase fr phase).
  Proof. intros support upper fr phase [Howner Hlocal]; now constructor. Qed.

  Lemma frame_data_with_read :
    forall support upper fr minimum maximum,
      frame_data_below support upper fr ->
      frame_data_below support upper (R.with_frame_read fr minimum maximum).
  Proof. intros support upper fr minimum maximum [Howner Hlocal]; now constructor. Qed.

  Lemma frame_local_with_side :
    forall upper fr target input,
      frame_local_below upper fr ->
      D.leq input (upper target) = true ->
      frame_local_below upper (R.with_frame_side fr target input).
  Proof.
    intros upper fr target input Hlocal Hinput observed value Hlookup.
    unfold R.with_frame_side in Hlookup. cbn in Hlookup.
    destruct (V.eq_dec observed target) as [Heq |Hneq].
    - subst observed. rewrite ML.lookup_update_same in Hlookup.
      inversion Hlookup; subst. exact Hinput.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      eapply Hlocal; exact Hlookup.
  Qed.

  Lemma accumulated_side_input_below :
    forall upper fr target raw,
      frame_local_below upper fr ->
      D.leq raw (upper target) = true ->
      D.leq (R.accumulated_side_input fr target raw) (upper target) = true.
  Proof.
    intros upper fr target raw Hlocal Hraw.
    unfold R.accumulated_side_input.
    destruct (M.lookup (R.frame_local_side fr) target)
      as [previous |] eqn:Hlookup.
    - apply DL.join_least; [eapply Hlocal; exact Hlookup |exact Hraw].
    - exact Hraw.
  Qed.

  Lemma record_side_input_below :
    forall support upper fr target raw next input,
      frame_data_below support upper fr ->
      D.leq raw (upper target) = true ->
      R.record_side_input fr target raw = (next, input) ->
      frame_data_below support upper next /\
      D.leq input (upper target) = true.
  Proof.
    intros support upper fr target raw next input
      [Howner Hlocal] Hraw Hrecord.
    unfold R.record_side_input in Hrecord. inversion Hrecord; subst.
    pose proof (@accumulated_side_input_below upper fr target raw
      Hlocal Hraw) as Hinput.
    split.
    - constructor; [exact Howner |].
      apply frame_local_with_side; assumption.
    - exact Hinput.
  Qed.

  Lemma frame_owner_record_side_input :
    forall fr target raw next input,
      R.record_side_input fr target raw = (next, input) ->
      R.frame_owner next = R.frame_owner fr.
  Proof.
    intros fr target raw next input Hrecord.
    unfold R.record_side_input in Hrecord. inversion Hrecord. reflexivity.
  Qed.

  Lemma state_below_complete_get :
    forall support upper st fr target next next_fr value,
      state_below upper st ->
      frame_data_below support upper fr ->
      R.complete_get st fr target = (next, next_fr, value) ->
      state_below upper next /\
      frame_data_below support upper next_fr /\
      D.leq value (upper target) = true.
  Proof.
    intros support upper st fr target next next_fr value
      Hstate Hframe Hcomplete.
    unfold R.complete_get in Hcomplete.
    repeat match type of Hcomplete with
    | context [if ?condition then _ else _] => destruct condition eqn:?
    | context [match ?subject with _ => _ end] => destruct subject eqn:?
    end;
    inversion Hcomplete; subst; clear Hcomplete; cbn.
    all: split.
    all: try (apply state_below_materialize;
      eapply state_below_core_view; cbn; try reflexivity; exact Hstate).
    all: split.
    all: try (apply frame_data_with_read; exact Hframe).
    all: apply state_sigma_below.
    all: apply state_below_materialize.
    all: eapply state_below_core_view; cbn; try reflexivity; exact Hstate.
  Qed.

  Lemma frame_owner_complete_get :
    forall st fr target next next_fr value,
      R.complete_get st fr target = (next, next_fr, value) ->
      R.frame_owner next_fr = R.frame_owner fr.
  Proof.
    intros st fr target next next_fr value Hcomplete.
    unfold R.complete_get in Hcomplete.
    repeat match type of Hcomplete with
    | context [if ?condition then _ else _] => destruct condition eqn:?
    | context [match ?subject with _ => _ end] => destruct subject eqn:?
    end;
    inversion Hcomplete; reflexivity.
  Qed.

  Lemma state_below_write_side :
    forall upper st fr target input next changed,
      state_below upper st ->
      D.leq input (upper target) = true ->
      R.write_side_contribution st fr target input = (next, changed) ->
      state_below upper next.
  Proof.
    intros upper st fr target input next changed Hstate Hinput Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted.
    destruct (R.side_update promoted (R.frame_owner fr) target input)
      as [phase value] eqn:Hupdate.
    inversion Hwrite; subst; clear Hwrite.
    apply state_below_register_reset, state_below_with_contribution.
    - now apply state_below_promote_side_target.
    - assert (Hold : D.leq
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) (upper target) = true).
      { eapply stored_contribution_below.
        exact (state_aggregates_below
          (state_below_promote_side_target fr target Hstate)). }
      pose proof (@SUBL.update_preserves_upper_bound
        (R.frame_owner fr) target
        (R.side_phase (R.stored_side_cell
          (R.promote_side_target st fr target)
          (R.frame_owner fr) target))
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) input
        (R.aggregate (R.promote_side_target st fr target) target)
        (upper target) Hold Hinput)
        as Hbound.
      unfold R.side_update in Hupdate. rewrite Hupdate in Hbound.
      exact Hbound.
  Qed.

  Lemma state_below_set_value :
    forall support upper st fr direct next next_fr,
      state_below upper st ->
      completed_frame_below support upper fr direct ->
      R.set_value st fr direct = (next, next_fr) ->
      state_below upper next /\
      frame_data_below support upper next_fr.
  Proof.
    intros support upper st fr direct next next_fr
      Hstate [Hframe Hdirect] Hset.
    unfold R.set_value in Hset.
    assert (Hcandidate : D.leq
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (upper (R.frame_owner fr)) = true).
    { apply DL.join_least; [exact Hdirect |].
      apply state_aggregates_below. exact Hstate. }
    assert (Hold : D.leq (R.sigma_value st (R.frame_owner fr))
      (upper (R.frame_owner fr)) = true).
    { apply state_sigma_below. exact Hstate. }
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))) eqn:Hequivalent.
    - inversion Hset; subst. split; [exact Hstate |exact Hframe].
    - destruct (S.mem (R.frame_owner fr) (R.controlled st))
        eqn:Hcontrolled.
      + destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
          (R.sigma_value st (R.frame_owner fr))
          (D.join direct (R.aggregate st (R.frame_owner fr))))
          as [phase value] eqn:Hupdate.
        assert (Hvalue :
          D.leq value (upper (R.frame_owner fr)) = true).
        { pose proof (@UBL.update_preserves_upper_bound false
            (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr)))
            (upper (R.frame_owner fr)) Hold Hcandidate) as Hbound.
          rewrite Hupdate in Hbound. exact Hbound. }
        destruct (R.equivalent value
          (R.sigma_value st (R.frame_owner fr))) eqn:Hsame.
        * cbn in Hset. rewrite Hsame in Hset.
          inversion Hset; subst; clear Hset. split.
          -- exact Hstate.
          -- now apply frame_data_with_phase.
        * cbn in Hset. rewrite Hsame in Hset.
          inversion Hset; subst; clear Hset. split.
          -- eapply state_below_core_view with
               (before := R.with_sigma st
                 (M.update (R.sigma st) (R.frame_owner fr) value));
               cbn; try reflexivity.
             apply state_below_sigma_update; assumption.
          -- now apply frame_data_with_phase.
      + cbn in Hset. rewrite Hequivalent in Hset.
        inversion Hset; subst; clear Hset. split.
        * eapply state_below_core_view with
            (before := R.with_sigma st
              (M.update (R.sigma st) (R.frame_owner fr)
                (D.join direct (R.aggregate st (R.frame_owner fr)))));
            cbn; try reflexivity.
          apply state_below_sigma_update; assumption.
        * now apply frame_data_with_phase.
  Qed.

  Lemma initial_rhs_below :
    forall support tf upper owner,
      List.In owner support ->
      Sem.rhs_supported
        (fun target => List.In target support) (tf owner) ->
      rhs_below support tf upper owner (tf owner).
  Proof.
    intros support tf upper owner Howner Hsupported.
    eapply RhsBelow with
      (prefix_reads := []) (prefix_sides := []) (prefix_spawns := []).
    - exact Howner.
    - exact Hsupported.
    - exact Hsupported.
    - apply initial_full_rhs_context.
    - intros target value Hin. contradiction.
  Qed.

  Lemma rhs_below_get :
    forall support tf upper owner target next value,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Get target next) ->
      D.leq value (upper target) = true ->
      rhs_below support tf upper owner (next value).
  Proof.
    intros support tf upper owner target next value Hbelow Hvalue.
    destruct Hbelow as
      [Howner Hroot Hcurrent reads sides spawns Hcontext Hreads].
    inversion Hcurrent; subst.
    eapply RhsBelow; eauto using full_rhs_context_get,
      prefix_reads_below_snoc.
  Qed.

  Lemma rhs_below_side :
    forall support tf upper owner target payload next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Side target payload next) ->
      rhs_below support tf upper owner next.
  Proof.
    intros support tf upper owner target payload next Hbelow.
    destruct Hbelow as
      [Howner Hroot Hcurrent reads sides spawns Hcontext Hreads].
    inversion Hcurrent; subst.
    eapply RhsBelow; eauto using full_rhs_context_side.
  Qed.

  Lemma rhs_below_spawn :
    forall support tf upper owner target next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Spawn target next) ->
      rhs_below support tf upper owner next.
  Proof.
    intros support tf upper owner target next Hbelow.
    destruct Hbelow as
      [Howner Hroot Hcurrent reads sides spawns Hcontext Hreads].
    inversion Hcurrent; subst.
    eapply RhsBelow; eauto using full_rhs_context_spawn.
  Qed.

  Lemma current_completion_below_upper :
    forall support tf upper owner current,
      system_monotone_on tf support ->
      rhs_below support tf upper owner current ->
      exists prefix_sides suffix lower upper_result,
        observes_at (fun _ => D.bottom) current suffix /\
        rhs_observes (tf owner) lower /\
        observes_at upper (tf owner) upper_result /\
        effects_le lower upper_result /\
        observed_direct lower = observed_direct suffix /\
        observed_sides lower = prefix_sides ++ observed_sides suffix.
  Proof.
    intros support tf upper owner current Hmonotone Hbelow.
    destruct Hbelow as
      [Howner Hroot Hcurrent reads sides spawns Hcontext Hreads].
    destruct (@supported_observes_at
      (fun target => List.In target support) (tf owner) upper Hroot)
      as [upper_result [Hupper Hupper_reads]].
    destruct (@full_rhs_context_bottom_completion
      (tf owner) current reads sides spawns
      (fun target => List.In target support) Hcontext Hcurrent)
      as [suffix [lower
        [[Hsuffix Hbottom]
          [Hlower [Hdirect [Hlower_reads [Hlower_sides Hlower_spawns]]]]]]].
    assert (Hcommon : common_read_values_le lower upper_result).
    { intros target lower_value upper_value Hinlower Hinupper.
      rewrite Hlower_reads in Hinlower.
      apply in_app_or in Hinlower. destruct Hinlower as [Hin | Hin].
      - rewrite (Hupper_reads target upper_value Hinupper).
        now apply Hreads with (target := target).
      - rewrite (Hbottom target lower_value Hin).
        apply DL.bottom_least. }
    pose proof (monotone_observations
      (system_dependencies_monotone Hmonotone owner Howner)
      (system_effects_monotone Hmonotone owner Howner)
      Hlower Hupper Hcommon) as Heffects.
    exists sides, suffix, lower, upper_result.
    split; [now split |].
    split; [exact Hlower |].
    split; [now split |].
    split; [exact Heffects |].
    split; assumption.
  Qed.

  Lemma current_direct_below :
    forall support tf upper owner direct,
      system_monotone_on tf support ->
      post_solution_on tf support upper ->
      rhs_below support tf upper owner (R.ConstraintSystem.Ret direct) ->
      D.leq direct (upper owner) = true.
  Proof.
    intros support tf upper owner direct Hmonotone Hpost Hbelow.
    pose proof (Hbelow) as Howner.
    destruct Howner as [Howner _ _ _ _ _ _ _].
    destruct (current_completion_below_upper Hmonotone Hbelow)
      as [sides [suffix [lower [upper_result
        [[Hsuffix _]
          [Hlower [[Hupper Hupper_reads]
            [Heffects [Hdirect Hsides]]]]]]]]].
    inversion Hsuffix; subst. cbn in Hdirect.
    pose proof (Hpost owner Howner upper_result
      (conj Hupper Hupper_reads)) as [Hpost_direct _].
    eapply DL.leq_trans.
    - rewrite <- Hdirect. exact (direct_effect_le Heffects).
    - exact Hpost_direct.
  Qed.

  Lemma current_side_below :
    forall support tf upper owner target payload next,
      system_monotone_on tf support ->
      post_solution_on tf support upper ->
      rhs_below support tf upper owner
        (R.ConstraintSystem.Side target payload next) ->
      D.leq payload (upper target) = true.
  Proof.
    intros support tf upper owner target payload next
      Hmonotone Hpost Hbelow.
    pose proof (Hbelow) as Howner.
    destruct Howner as [Howner _ _ _ _ _ _ _].
    destruct (current_completion_below_upper Hmonotone Hbelow)
      as [sides [suffix [lower [upper_result
        [[Hsuffix _]
          [Hlower [[Hupper Hupper_reads]
            [Heffects [Hdirect Hsides]]]]]]]]].
    inversion Hsuffix; subst. cbn in Hsides.
    assert (Hinlower :
      List.In (target, payload) (observed_sides lower)).
    { rewrite Hsides. apply in_or_app. right. now left. }
    destruct (side_effects_le Heffects target payload Hinlower)
      as [upper_payload [Hinupper Hpayload]].
    pose proof (Hpost owner Howner upper_result
      (conj Hupper Hupper_reads)) as [_ [Hpost_sides _]].
    eapply DL.leq_trans; [exact Hpayload |].
    now apply Hpost_sides with (target := target).
  Qed.

  Lemma rhs_below_owner_in_support :
    forall support tf upper owner current,
      rhs_below support tf upper owner current ->
      List.In owner support.
  Proof. intros support tf upper owner current H; now destruct H. Qed.

  Lemma rhs_below_get_target_in_support :
    forall support tf upper owner target next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Get target next) ->
      List.In target support.
  Proof.
    intros support tf upper owner target next Hbelow.
    destruct Hbelow as [_ _ Hsupported]. inversion Hsupported; assumption.
  Qed.

  Lemma rhs_below_side_target_in_support :
    forall support tf upper owner target payload next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Side target payload next) ->
      List.In target support.
  Proof.
    intros support tf upper owner target payload next Hbelow.
    destruct Hbelow as [_ _ Hsupported]. inversion Hsupported; assumption.
  Qed.

  Lemma rhs_below_spawn_target_in_support :
    forall support tf upper owner target next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Spawn target next) ->
      List.In target support.
  Proof.
    intros support tf upper owner target next Hbelow.
    destruct Hbelow as [_ _ Hsupported]. inversion Hsupported; assumption.
  Qed.

  Theorem config_below_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper before after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.config_supported (Sem.support finite) before ->
      config_below (Sem.support finite) tf upper before ->
      Sem.step tf before after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper [st control] after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported]
      [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step, R.next_config in Hstep.
    destruct control;
      cbn in Hstate_supported, Hstate_below,
        Hcontrol_supported, Hcontrol_below;
      cbn [R.cfg_state R.cfg_control] in Hstep.
    - destruct (R.queue_pop (R.queue st)) as [[owner rest] |]
        eqn:Hpop; try discriminate.
      inversion Hstep; subst; clear Hstep. constructor.
      + now apply state_below_with_queue.
      + cbn. split; [|exact I].
        destruct (@Total.queue_supported_pop
          (Sem.support finite) (R.queue st) owner rest
          (Total.state_queue_supported Hstate_supported) Hpop)
          as [Howner _]. exact Howner.
    - destruct l as [|root remaining].
      + inversion Hstep; subst. now constructor.
      + destruct (R.is_materialized (R.observe st root) root) eqn:Hstarted.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- exact I.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- cbn. inversion Hcontrol_supported; subst. now split.
    - destruct (R.queue_pop (R.queue st)) as [[owner rest] |]
        eqn:Hpop; inversion Hstep; subst; clear Hstep; constructor.
      + now apply state_below_with_queue.
      + cbn. split; [|exact Hcontrol_below].
        destruct (@Total.queue_supported_pop
          (Sem.support finite) (R.queue st) owner rest
          (Total.state_queue_supported Hstate_supported) Hpop)
          as [Howner _]. exact Howner.
      + exact Hstate_below.
      + exact I.
    - inversion Hstep; subst; clear Hstep. constructor.
      + now apply state_below_materialize.
      + cbn. destruct Hcontrol_below as [Howner Hk]. split; [|exact Hk].
        constructor.
        * now apply frame_data_fresh.
        * apply initial_rhs_below; [exact Howner |].
          apply Sem.system_supported. exact Howner.
    - destruct r.
      + destruct Features.eliminate_dead_sides;
          inversion Hstep; subst; clear Hstep.
        * constructor; [exact Hstate_below |]. cbn.
          destruct Hcontrol_below as [[Hframe Hrhs] Hk]. split.
          -- constructor; [exact Hframe |eapply current_direct_below; eauto].
          -- exact Hk.
        * constructor; [exact Hstate_below |]. cbn.
          destruct Hcontrol_below as [[Hframe Hrhs] Hk]. split.
          -- constructor; [exact Hframe |eapply current_direct_below; eauto].
          -- exact Hk.
      + remember (R.observe st t) as st0 eqn:Hobserve.
        destruct (andb (negb (R.is_materialized st0 t))
          (R.rank_lt st0 (R.frame_owner f) t)) eqn:Hrecursive.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- cbn. destruct Hcontrol_below as [Hactive Hk]. split.
             ++ destruct Hactive as [_ Hrhs].
                now apply rhs_below_get_target_in_support in Hrhs.
             ++ now split.
        * remember (if R.is_materialized st0 t then st0 else R.enqueue st0 t)
            as ready eqn:Hready.
          assert (Hst0 : state_below upper st0).
          { subst st0. now apply state_below_observe. }
          assert (Hready_below : state_below upper ready).
          { subst ready. destruct (R.is_materialized st0 t);
              [exact Hst0 |now apply state_below_enqueue]. }
          destruct (R.complete_get ready f t) as [[next next_fr] value]
            eqn:Hget.
          inversion Hstep; subst; clear Hstep.
          destruct Hcontrol_below as [[Hframe Hrhs] Hk].
          destruct (@state_below_complete_get
            (Sem.support finite) upper _ f t next next_fr value
            Hready_below Hframe Hget) as [Hnext [Hnext_fr Hvalue]].
          constructor; [exact Hnext |]. cbn. split; [|exact Hk].
          constructor; [exact Hnext_fr |].
          rewrite (frame_owner_complete_get Hget).
          now apply rhs_below_get with (target := t).
      + remember (R.observe st t) as st0 eqn:Hobserve.
        destruct (R.record_side_input f t t0) as [next_fr input]
          eqn:Hrecord.
        destruct (R.write_side_contribution st0 next_fr t input)
          as [next changed] eqn:Hwrite.
        unfold R.continue_side in Hstep.
        destruct changed;
          try destruct (andb (R.rank_lt next (R.frame_owner next_fr) t)
            (negb (R.is_materialized next t)));
          inversion Hstep; subst; clear Hstep.
        all: destruct Hcontrol_below as [[Hframe Hrhs] Hk].
        all: assert (Hraw : D.leq t0 (upper t) = true)
          by (eapply current_side_below; eauto).
        all: destruct (@record_side_input_below
          (Sem.support finite) upper f t t0 next_fr input Hframe Hraw Hrecord)
          as [Hnext_fr Hinput].
        all: assert (Hnext : state_below upper next) by
          (eapply state_below_write_side with
            (st := R.observe st t) (fr := next_fr)
            (target := t) (input := input);
           [now apply state_below_observe |exact Hinput |exact Hwrite]).
        all: assert (Hactive : active_rhs_below
          (Sem.support finite) tf upper next_fr r) by
          (constructor; [exact Hnext_fr |];
           rewrite (frame_owner_record_side_input Hrecord);
           now apply rhs_below_side with (target := t) (payload := t0)).
        * constructor; [exact Hnext |]. cbn. split.
          -- now apply rhs_below_side_target_in_support in Hrhs.
          -- now split.
        * constructor; [now apply state_below_enqueue |]. cbn. now split.
        * constructor; [exact Hnext |]. cbn. now split.
        * constructor; [exact Hnext |]. cbn. now split.
      + remember (R.observe st t) as st0 eqn:Hobserve.
        destruct (R.is_materialized st0 t) eqn:Hmaterialized.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- cbn. destruct Hcontrol_below as [[Hframe Hrhs] Hk].
             split; [constructor; [exact Hframe |now apply rhs_below_spawn
               with (target := t)] |exact Hk].
        * destruct (R.rank_lt st0 (R.frame_owner f) t) eqn:Hrank.
          -- inversion Hstep; subst; clear Hstep. constructor.
             ++ now apply state_below_observe.
             ++ cbn. destruct Hcontrol_below as [[Hframe Hrhs] Hk]. split.
                ** now apply rhs_below_spawn_target_in_support in Hrhs.
                ** split; [constructor; [exact Hframe |] |exact Hk].
                   now apply rhs_below_spawn with (target := t).
          -- inversion Hstep; subst; clear Hstep. constructor.
             ++ apply state_below_materialize, state_below_enqueue.
                now apply state_below_observe.
             ++ cbn. destruct Hcontrol_below as [[Hframe Hrhs] Hk].
                split; [constructor; [exact Hframe |now apply rhs_below_spawn
                  with (target := t)] |exact Hk].
    - destruct l as [|target remaining].
      + inversion Hstep; subst; clear Hstep. constructor.
        * now apply state_below_publish_targets.
        * exact Hcontrol_below.
      + destruct (S.mem target (R.frame_current_targets f)) eqn:Hcurrent.
        * inversion Hstep; subst; clear Hstep. now constructor.
        * destruct (R.write_side_contribution st f target D.bottom)
            as [next changed] eqn:Hwrite.
          unfold R.continue_dead in Hstep.
          destruct changed;
            try destruct (andb (R.rank_lt next (R.frame_owner f) target)
              (negb (R.is_materialized next target)));
            inversion Hstep; subst; clear Hstep.
          all: destruct Hcontrol_below as [Hcompleted Hk].
          all: assert (Hnext : state_below upper next)
            by (eapply state_below_write_side;
              [exact Hstate_below |apply DL.bottom_least |exact Hwrite]).
          { constructor; [exact Hnext |]. cbn. split.
            - inversion Hcontrol_supported as [Hfr [Hpending Hks]].
              inversion Hpending; subst. assumption.
            - now split. }
          { constructor; [now apply state_below_enqueue |]. cbn. now split. }
          { constructor; [exact Hnext |]. cbn. now split. }
          { constructor; [exact Hnext |]. cbn. now split. }
    - destruct (R.set_value st f t) as [next next_fr] eqn:Hset.
      inversion Hstep; subst; clear Hstep.
      destruct Hcontrol_below as [Hcompleted Hk].
      destruct (@state_below_set_value
        (Sem.support finite) upper st f t next next_fr
        Hstate_below Hcompleted Hset) as [Hnext Hnext_fr].
      constructor; [exact Hnext |]. cbn. now split.
    - destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
      + destruct (V.eq_dec next (R.frame_owner f)) as [Hequal |Hneq].
        * destruct (R.queue_pop (R.queue st)) as [[ignored rest] |]
            eqn:Hpop; try discriminate.
          inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_with_queue.
          -- cbn. destruct Hcontrol_below as [Hframe Hk]. split; [|exact Hk].
             constructor.
             ++ apply frame_data_fresh. exact (frame_owner_below_supported Hframe).
             ++ apply initial_rhs_below.
                ** exact (frame_owner_below_supported Hframe).
                ** apply Sem.system_supported.
                   exact (frame_owner_below_supported Hframe).
        * destruct (R.rank_lt st (R.frame_owner f) next) eqn:Hrank.
          -- destruct (R.queue_pop (R.queue st)) as [[ignored rest] |]
               eqn:Hpop; try discriminate.
             inversion Hstep; subst; clear Hstep. constructor.
             ++ now apply state_below_with_queue.
             ++ cbn. destruct Hcontrol_below as [Hframe Hk]. split.
                ** destruct (@Total.queue_supported_pop
                     (Sem.support finite) (R.queue st) ignored rest
                     (Total.state_queue_supported Hstate_supported) Hpop)
                     as [Hnext _].
                   rewrite (@Total.queue_peek_pop_same
                     (R.queue st) next ignored rest Hpeek Hpop).
                   exact Hnext.
                ** now split.
          -- inversion Hstep; subst; clear Hstep. constructor.
             ++ now apply state_below_reset_registered_cells.
             ++ exact (proj2 Hcontrol_below).
      + inversion Hstep; subst; clear Hstep. constructor.
        * now apply state_below_reset_registered_cells.
        * exact (proj2 Hcontrol_below).
    - destruct c.
      + inversion Hstep; subst; clear Hstep. now constructor.
      + inversion Hstep; subst; clear Hstep. now constructor.
      + destruct (R.complete_get st f t) as [[next next_fr] value]
          eqn:Hget.
        inversion Hstep; subst; clear Hstep.
        destruct Hcontrol_below as [[Hframe Hrhs] Hk].
        destruct (@state_below_complete_get
          (Sem.support finite) upper st f t next next_fr value
          Hstate_below Hframe Hget) as [Hnext [Hnext_fr Hvalue]].
        constructor; [exact Hnext |]. cbn. split; [|exact Hk].
        constructor; [exact Hnext_fr |].
        rewrite (frame_owner_complete_get Hget).
        now apply rhs_below_get with (target := t).
      + inversion Hstep; subst; clear Hstep.
        constructor; [exact Hstate_below |exact Hcontrol_below].
      + inversion Hstep; subst; clear Hstep.
        constructor; [exact Hstate_below |exact Hcontrol_below].
      + inversion Hstep; subst; clear Hstep.
        constructor; [exact Hstate_below |exact Hcontrol_below].
      + inversion Hstep; subst; clear Hstep.
        constructor; [exact Hstate_below |exact Hcontrol_below].
  Qed.

  Lemma initial_config_below :
    forall support tf roots upper,
      config_below support tf upper (R.initial_config roots).
  Proof.
    intros support tf roots upper. constructor.
    - apply empty_state_below.
    - exact I.
  Qed.

  Lemma config_below_steps :
    forall tf roots (finite : Sem.finite_system tf roots)
      upper before after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.config_supported (Sem.support finite) before ->
      config_below (Sem.support finite) tf upper before ->
      Sem.steps tf before after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper before after Hmonotone Hpost
      Hsupported Hbelow Hsteps.
    induction Hsteps.
    - exact Hbelow.
    - apply IHHsteps.
      + eapply Total.next_config_supported.
        * exact (Sem.system_supported finite).
        * exact Hsupported.
        * exact H.
      + eapply config_below_step; eassumption.
  Qed.

  Theorem reachable_config_below :
    forall tf roots (finite : Sem.finite_system tf roots) upper after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Sem.steps tf (R.initial_config roots) after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper after Hmonotone Hpost Hsteps.
    eapply config_below_steps; eauto.
    - apply Total.initial_config_supported.
    - apply initial_config_below.
  Qed.

  Theorem successful_run_below :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final upper,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      R.solve_fuel fuel tf roots = Some final ->
      sigma_below upper final.
  Proof.
    intros fuel tf roots finite final upper Hmonotone Hpost Hsolve.
    pose proof (@Total.successful_run_terminates_to
      fuel tf roots final Hsolve) as [Hsteps Hquiet].
    pose proof (@reachable_config_below tf roots finite upper
      (Sem.terminal_config final) Hmonotone Hpost Hsteps) as Hbelow.
    exact (state_sigma_below (config_state_below Hbelow)).
  Qed.

  (** A successful run is pointwise below every supported post-solution on
      each requested root. *)
  Theorem solve_fuel_least_on_roots :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      system_monotone_on tf (Sem.support finite) ->
      R.solve_fuel fuel tf roots = Some final ->
      forall upper,
        post_solution_on tf (Sem.support finite) upper ->
        forall root,
          List.In root roots ->
          D.leq (R.sigma_value final root) (upper root) = true.
  Proof.
    intros fuel tf roots finite final Hmonotone Hsolve
      upper Hpost root Hroot.
    eapply successful_run_below; eauto.
  Qed.

  (** Public total-correctness theorem for finite-height clients: the solver
      returns a correct result whose requested values are below those of
      every post-solution on the finite support. *)
  (** Legacy root-only compatibility result; intentionally not a public facade export. *)
  Theorem total_least_on_roots :
    forall tf roots (finite : Sem.finite_system tf roots),
      system_monotone_on tf (Sem.support finite) ->
      exists fuel final,
        R.solve_fuel fuel tf roots = Some final /\
        Sem.correct_final_state tf roots final /\
        forall upper,
          post_solution_on tf (Sem.support finite) upper ->
          forall root,
            List.In root roots ->
            D.leq (R.sigma_value final root) (upper root) = true.
  Proof.
    intros tf roots finite Hmonotone.
    destruct (@Total.sufficient_fuel tf roots finite)
      as [fuel [final Hsolve]].
    exists fuel, final. split; [exact Hsolve |]. split.
    - now apply Total.solve_fuel_correct with (fuel := fuel).
    - intros upper Hpost root Hroot.
      eapply solve_fuel_least_on_roots; eauto.
  Qed.

  Module Strict := SourceStrictness.Make V D DL.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at
      Sem.observed_direct Sem.observed_sides.

  Lemma lookup_value_agrees : forall st target value,
    M.lookup (R.sigma st) target = Some value ->
    value = R.sigma_value st target.
  Proof.
    intros st target value Hlookup. unfold R.sigma_value.
    now rewrite Hlookup.
  Qed.

  (** The existing replay fixes the observation under the completed store;
      only reads on this path need to be solved. *)
  Lemma rhs_eval_observation_agrees :
    forall st body direct reads effects result,
      Sem.rhs_eval st body direct reads effects ->
      observes_at (R.sigma_value st) body result ->
      direct = observed_direct result /\
      reads = observed_reads result /\ effects = observed_sides result.
  Proof.
    intros st body direct reads effects result Heval.
    revert result. induction Heval; intros result [Hobs Hreads];
      inversion Hobs; subst; cbn.
    - repeat split.
    - assert (Hvalue : value = value0).
      { rewrite (@lookup_value_agrees st target value H).
        symmetry. apply Hreads. now left. }
      subst value0.
      assert (Htail : observes_at (R.sigma_value st) (next value) result0).
      { split; [assumption |].
        intros target' value' Hin. apply Hreads. now right. }
      destruct (IHHeval result0 Htail) as [-> [-> ->]]. repeat split.
    - assert (Htail : observes_at (R.sigma_value st) next result0).
      { split; [assumption |]. exact Hreads. }
      destruct (IHHeval result0 Htail) as [-> [-> ->]]. repeat split.
    - assert (Htail : observes_at (R.sigma_value st) next result0).
      { split; [assumption |]. exact Hreads. }
      exact (IHHeval result0 Htail).
  Qed.

  Lemma solved_dec : forall st x, {Sem.solved st x} + {~ Sem.solved st x}.
  Proof.
    intros st x. unfold Sem.solved, Sem.StateSpec.solved.
    destruct (M.lookup (R.sigma st) x) eqn:Hlookup.
    - left. now exists t.
    - right. intros [value Hvalue]. discriminate.
  Defined.

  Lemma unsolved_value_bottom : forall st x,
    ~ Sem.solved st x -> D.leq (R.sigma_value st x) D.bottom = true.
  Proof.
    intros st x Hunsolved. unfold R.sigma_value.
    destruct (M.lookup (R.sigma st) x) eqn:Hlookup.
    - exfalso. apply Hunsolved. exists t. exact Hlookup.
    - apply DL.leq_refl.
  Qed.

  Lemma terminal_solved_observation_post :
    forall tf roots final owner result,
      Sem.terminates_to tf roots final ->
      Sem.solved final owner ->
      observes_at (R.sigma_value final) (tf owner) result ->
      D.leq (observed_direct result) (R.sigma_value final owner) = true /\
      Sem.valuation_side_effects_below
        (R.sigma_value final) (observed_sides result).
  Proof.
    intros tf roots final owner result Hterm Hsolved Hobs.
    pose proof (@Total.terminal_invariant tf roots final Hterm) as Hinv.
    destruct Hterm as [_ Hquiet].
    assert (Hnotqueued : forall x, ~ Total.queued final x).
    { intros x. eapply Total.quiescent_not_queued; exact Hquiet. }
    assert (Haggregate : forall target,
      D.leq (R.aggregate final target) (R.sigma_value final target) = true).
    { intros target. destruct (Total.invariant_aggregate Hinv target)
        as [Hqueued | [Hactive | Hbounded]].
      - contradiction (Hnotqueued target Hqueued).
      - contradiction.
      - exact Hbounded. }
    destruct (Total.invariant_summaries Hinv Hsolved)
      as [Hqueued | [Hactive | Hsummary]].
    - contradiction (Hnotqueued owner Hqueued).
    - contradiction.
    - pose proof (Total.summary_post_solution Hquiet Haggregate Hsummary) as Hpost.
      destruct Hsummary as [_ [direct [reads [effects
        [Htrace [Hreads [Heffects Hdirect]]]]]]].
      assert (Heval : Sem.rhs_eval final (tf owner) direct reads effects).
      { eapply Total.rhs_trace_replay; [exact Htrace |].
        eapply Total.guarded_reads_agree; eauto. }
      destruct (rhs_eval_observation_agrees Heval Hobs) as [<- [_ <-]].
      exact (Hpost direct reads effects Heval).
  Qed.

  (** Source strictness closes the unsolved part of the finite system. *)
  (** Finite support covers spawns as well as reads and side targets. *)
  Lemma supported_observed_spawns : forall supported body result,
    Sem.rhs_supported supported body -> Sem.rhs_observes body result ->
    forall target, In target (Sem.observed_spawns result) -> supported target.
  Proof.
    intros supported body result Hsupported Hobs. revert Hsupported.
    induction Hobs; intros Hsupported target' Hin; inversion Hsupported; subst; cbn in Hin.
    - contradiction.
    - eapply IHHobs; eauto.
    - eapply IHHobs; eauto.
    - destruct Hin as [<-|Hin]; [assumption|eapply IHHobs; eauto].
  Qed.

  Lemma finite_spawn_closed : forall tf roots (finite : Sem.finite_system tf roots) values,
    Sem.spawn_closed_on tf (Sem.support finite) values.
  Proof.
    intros tf roots finite values owner Hin result [Hobs Hreads] target Hspawn.
    exact (@supported_observed_spawns (fun y => In y (Sem.support finite))
      (tf owner) result (Sem.system_supported finite owner Hin) Hobs target Hspawn).
  Qed.

  Theorem successful_source_strict_solution :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      source_strict_on tf (Sem.support finite) roots ->
      R.solve_fuel fuel tf roots = Some final ->
      post_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros fuel tf roots finite final Hstrict Hrun.
    pose proof (@Total.successful_run_terminates_to
      fuel tf roots final Hrun) as Hterm.
    apply Sem.post_solution_on_intro; [apply finite_spawn_closed|].
    eapply (@Strict.bottom_completion_is_value_post_solution _ _ Sem.observes_at
      Sem.observed_direct Sem.observed_sides tf (Sem.support finite) roots
      (R.sigma_value final) (Sem.solved final)).
    - apply solved_dec.
    - exact Hstrict.
    - intros x Hin. exact (proj1 (@Total.solve_fuel_correct
        fuel tf roots final Hrun x Hin)).
    - apply unsolved_value_bottom.
    - intros owner Hin Hsolved result Hobs.
      eapply terminal_solved_observation_post; eauto.
  Qed.

  Theorem solve_fuel_least_solution :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      source_strict_on tf (Sem.support finite) roots ->
      system_monotone_on tf (Sem.support finite) ->
      R.solve_fuel fuel tf roots = Some final ->
      least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros fuel tf roots finite final Hstrict Hmono Hrun. split.
    - eapply successful_source_strict_solution; eauto.
    - intros upper Hpost x Hin.
      exact (@successful_run_below fuel tf roots finite final upper
        Hmono Hpost Hrun x).
  Qed.

  (** Arbitrary requested roots suffice; every semantically solved unknown
      is minimal, and the bottom-completed store solves the whole support. *)
  Theorem total_least_on_solved :
    forall tf roots (finite : Sem.finite_system tf roots),
      source_strict_on tf (Sem.support finite) roots ->
      system_monotone_on tf (Sem.support finite) ->
      exists fuel final,
        R.solve_fuel fuel tf roots = Some final /\
        Sem.correct_final_state tf roots final /\
        post_solution_on tf (Sem.support finite) (R.sigma_value final) /\
        forall upper, post_solution_on tf (Sem.support finite) upper ->
          forall x, Sem.solved final x ->
            D.leq (R.sigma_value final x) (upper x) = true.
  Proof.
    intros tf roots finite Hstrict Hmono.
    destruct (@Total.sufficient_fuel tf roots finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |]. split.
    - exact (@Total.solve_fuel_correct fuel tf roots final Hrun).
    - split.
      + eapply successful_source_strict_solution; eauto.
      + intros upper Hpost x Hsolved.
        exact (@successful_run_below fuel tf roots finite final upper
          Hmono Hpost Hrun x).
  Qed.

  Lemma observes_at_rhs_eval :
    forall support st body result,
      Sem.rhs_supported (fun target => List.In target support) body ->
      (forall target,
        List.In target support ->
        Sem.solved st target) ->
      observes_at (R.sigma_value st) body result ->
      Sem.rhs_eval st body
        (observed_direct result)
        (observed_reads result)
        (observed_sides result).
  Proof.
    intros support st body result Hsupported Hsolved Hobserves.
    revert result Hobserves. induction Hsupported;
      intros result [Hobserve Hreads]; inversion Hobserve; subst; cbn.
    - constructor.
    - assert (Hread : value = R.sigma_value st target).
      { apply Hreads. now left. }
      destruct (Hsolved target H) as [stored Hlookup].
      assert (Hsigma : R.sigma_value st target = stored).
      { unfold R.sigma_value. now rewrite Hlookup. }
      rewrite Hsigma in Hread. subst value.
      econstructor; [exact Hlookup |].
      apply H1. split; [exact H5 |].
      intros observed observed_value Hin.
      apply Hreads. now right.
    - constructor. apply IHHsupported. split; [exact H4 |].
      intros observed observed_value Hin. apply Hreads. exact Hin.
    - constructor. apply IHHsupported. split; [exact H3 |].
      intros observed observed_value Hin. apply Hreads. exact Hin.
  Qed.

  Lemma closed_finite_system_is_finite :
    forall tf variables,
      closed_finite_system tf variables ->
      Sem.finite_system tf variables.
  Proof.
    intros tf variables Hclosed.
    refine {| Sem.support := variables;
              Sem.support_nodup := closed_variables_nodup Hclosed |}.
    - intros variable Hin. exact Hin.
    - exact (closed_system_supported Hclosed).
  Defined.

  Lemma correct_all_is_post_solution :
    forall tf variables final,
      closed_finite_system tf variables ->
      Sem.correct_final_state tf variables final ->
      post_solution_on tf variables (R.sigma_value final).
  Proof.
    intros tf variables final Hclosed Hcorrect.
    apply Sem.post_solution_on_intro.
    - intros owner Hin result [Hobs Hreads] target Hspawn.
      exact (@supported_observed_spawns (fun y => In y variables) (tf owner)
        result (closed_system_supported Hclosed owner Hin) Hobs target Hspawn).
    - intros owner Howner result Hobserves.
      pose proof (Hcorrect owner Howner) as [Howner_solved Howner_post].
      assert (Hall_solved : forall target,
        List.In target variables -> Sem.solved final target).
      { intros target Htarget. exact (proj1 (Hcorrect target Htarget)). }
      pose proof (@observes_at_rhs_eval variables final (tf owner) result
        (closed_system_supported Hclosed owner Howner)
        Hall_solved Hobserves) as Heval.
      exact (Howner_post
        (observed_direct result)
        (observed_reads result)
        (observed_sides result) Heval).
  Qed.

  (** If every variable in a finite closed system is requested, the returned
      valuation is itself a post-solution and is below every other one. *)
  Theorem total_least_solution :
    forall tf variables,
      closed_finite_system tf variables ->
      system_monotone_on tf variables ->
      exists fuel final,
        R.solve_fuel fuel tf variables = Some final /\
        post_solution_on tf variables (R.sigma_value final) /\
        forall upper,
          post_solution_on tf variables upper ->
          valuation_le_on variables (R.sigma_value final) upper.
  Proof.
    intros tf variables Hclosed Hmonotone.
    pose (finite := closed_finite_system_is_finite Hclosed).
    destruct (@total_least_on_roots tf variables finite Hmonotone)
      as [fuel [final [Hsolve [Hcorrect Hleast]]]].
    exists fuel, final. split; [exact Hsolve |]. split.
    - now apply correct_all_is_post_solution.
    - intros upper Hpost variable Hvariable.
      exact (Hleast upper Hpost variable Hvariable).
  Qed.


End Make.

(** Finite-height specialization using the canonical join update. *)
Module FiniteHeight
  (V : VAR)
  (D : DOMAIN)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : ReluctantRestarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module U := JoinUpdate V D.
  Module UL := JoinUpdateLaws V D DL FH.
  Module UBL := JoinUpdateUpperBoundLaws V D DL.
  Module OUL := OrdinaryUpdateTerminationAdapter V D U UL.
  Module SU := ReluctantSideUpdate V D U.
  Module Covered.
    Lemma covered_join_nonincreasing :
      forall target phase old input aggregate,
        D.leq old aggregate = true ->
        D.leq input old = false ->
        D.leq input aggregate = true ->
        UL.remaining_changes
          (fst (U.update true target phase old input))
          (D.join old input) <=
        UL.remaining_changes phase old.
    Proof.
      intros. exact (UL.remaining_changes_nonincreasing
        true target phase old input).
    Qed.
  End Covered.
  Module SUL := ReluctantRestartingSideUpdateTerminationLaws
    V D U DL UL Covered.
  Module SUBL := ReluctantSideUpdateUpperBoundLaws V D U DL UBL.
  Include Make
    V D U SU S M Rk Features RankLaws RankFinite
    DL OUL SUL UBL SUBL SL ML.
End FiniteHeight.

Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (S : SET V)
  (M : MAP V)
  (Features : ReluctantRestarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Rk := ListDiscoveryOrder V.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module RankFinite <: FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws :=
    ListFiniteDiscoveryOrderLaws V.
  Include FiniteHeight
    V D S M Rk Features RankLaws RankFinite DL FH SL ML.
End FirstDiscovery.

Module FixedRank
  (V : VAR)
  (D : DOMAIN)
  (S : SET V)
  (M : MAP V)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed)
  (Features : ReluctantRestarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module RankFinite <: FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws :=
    FixedRankFiniteDiscoveryOrderLaws V Fixed FixedLaws.
  Include FiniteHeight
    V D S M Rk Features RankLaws RankFinite DL FH SL ML.
End FixedRank.
