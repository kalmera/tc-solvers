From Stdlib Require Import List Sorting.Permutation.
From TcSolvers Require Import common.Assumptions common.FiniteHeight
 common.SourceStrictness common.Observations
 solvers.slr.narrowing_fixed_point.proofs.Replay.
Import ListNotations.
Set Implicit Arguments.

(** Upper-bound preservation for the batched-drain machine.
    Local algebra is adapted from the parent least-solution proof;
    all reachability and termination below use N, the batched machine.
    C is used only for one-step algebra inherited by N. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
 (S : SET V) (M : MAP V) (Features : Base.FEATURES)
 (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
 (UBL : UPPER_BOUND_UPDATE_LAWS V D U) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
Module Replay := Replay.Make V D U S M Features DL UL SL ML.
Import Replay.Front.
Module C := Replay.C.
Module P := C.P.
Module Total := Replay.B.
  Module Sem := Total.Sem.
  Module R := Total.R.
  Arguments Sem.support {tf initial} _.
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
    destruct (U.update true target
      (R.side_phase
        (R.stored_side_cell promoted (R.frame_owner fr) target))
      (R.stored_contribution promoted (R.frame_owner fr) target) input)
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
      pose proof (@UBL.update_preserves_upper_bound true target
        (R.side_phase (R.stored_side_cell
          (R.promote_side_target st fr target)
          (R.frame_owner fr) target))
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) input (upper target) Hold Hinput)
        as Hbound.
      rewrite Hupdate in Hbound. exact Hbound.
  Qed.

  Lemma update_result_below is_side owner phase old input bound next_phase value :
    D.leq old bound=true -> D.leq input bound=true ->
    U.update is_side owner phase old input=(next_phase,value) -> D.leq value bound=true.
  Proof.
    intros Hold Hinput Hupdate.
    pose proof (@UBL.update_preserves_upper_bound is_side owner phase old input bound Hold Hinput) as Hbound.
    rewrite Hupdate in Hbound. exact Hbound.
  Qed.

  Lemma candidate_below upper st owner direct :
    state_below upper st -> D.leq direct (upper owner)=true ->
    D.leq (D.join direct (R.aggregate st owner)) (upper owner)=true.
  Proof.
    intros Hstate Hdirect. apply DL.join_least;[exact Hdirect |].
    apply state_aggregates_below,Hstate.
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
      (upper (R.frame_owner fr)) = true)
      by (apply candidate_below;assumption).
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
        { exact (@update_result_below false (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr)))
            (upper (R.frame_owner fr)) phase value Hold Hcandidate Hupdate). }
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
      (@system_dependencies_monotone tf support Hmonotone owner Howner)
      (@system_effects_monotone tf support Hmonotone owner Howner)
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
      (conj Hupper Hupper_reads)) as [_ Hpost_sides].
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

Lemma base_loop_below tf roots (finite : Sem.finite_system tf roots) upper st  after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunLoop|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunLoop|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunLoop|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct (R.queue_pop (R.queue st)) as [[owner rest] |]
        eqn:Hpop; try discriminate.
      inversion Hstep; subst; clear Hstep. constructor.
      + now apply state_below_with_queue.
      + cbn. split; [|exact I].
        destruct (@Total.queue_supported_pop
          (Sem.support finite) (R.queue st) owner rest
          (Total.state_queue_supported Hstate_supported) Hpop)
          as [Howner _]. exact Howner.
Qed.
Lemma base_seeds_below tf roots (finite : Sem.finite_system tf roots) upper st l after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds l|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds l|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds l|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct l as [|root remaining].
      + inversion Hstep; subst. now constructor.
      + destruct (R.is_materialized (R.observe st root) root) eqn:Hstarted.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- exact I.
        * inversion Hstep; subst; clear Hstep. constructor.
          -- now apply state_below_observe.
          -- cbn. inversion Hcontrol_supported; subst. now split.
Qed.
Lemma base_seed_loop_below tf roots (finite : Sem.finite_system tf roots) upper st l after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunSeedLoop l|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunSeedLoop l|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeedLoop l|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct (R.queue_pop (R.queue st)) as [[owner rest] |]
        eqn:Hpop; inversion Hstep; subst; clear Hstep; constructor.
      + now apply state_below_with_queue.
      + cbn. split; [|exact Hcontrol_below].
        destruct (@Total.queue_supported_pop
          (Sem.support finite) (R.queue st) owner rest
          (Total.state_queue_supported Hstate_supported) Hpop)
          as [Howner _]. exact Howner.
      + exact Hstate_below.
      + exact I.
Qed.
Lemma base_start_below tf roots (finite : Sem.finite_system tf roots) upper st t c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode t c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode t c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode t c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 inversion Hstep; subst; clear Hstep. constructor.
      + now apply state_below_materialize.
      + cbn. destruct Hcontrol_below as [Howner Hk]. split; [|exact Hk].
        constructor.
        * now apply frame_data_fresh.
        * apply initial_rhs_below; [exact Howner |].
          apply Sem.system_supported. exact Howner.
Qed.
Lemma base_ret_below tf roots (finite : Sem.finite_system tf roots) upper st f t c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Ret t) c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Ret t) c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Ret t) c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct Features.eliminate_dead_sides;
          inversion Hstep; subst; clear Hstep.
        * constructor; [exact Hstate_below |]. cbn.
          destruct Hcontrol_below as [[Hframe Hrhs] Hk]. split.
          -- constructor; [exact Hframe |eapply current_direct_below; eauto].
          -- exact Hk.
        * constructor; [exact Hstate_below |]. cbn.
          destruct Hcontrol_below as [[Hframe Hrhs] Hk]. split.
          -- constructor; [exact Hframe |eapply current_direct_below; eauto].
          -- exact Hk.
Qed.
Lemma base_get_below tf roots (finite : Sem.finite_system tf roots) upper st f t r c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Get t r) c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Get t r) c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Get t r) c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 remember (R.observe st t) as st0 eqn:Hobserve.
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
Qed.
Lemma base_side_below tf roots (finite : Sem.finite_system tf roots) upper st f t t0 r c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Side t t0 r) c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Side t t0 r) c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Side t t0 r) c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 remember (R.observe st t) as st0 eqn:Hobserve.
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
Qed.
Lemma base_spawn_below tf roots (finite : Sem.finite_system tf roots) upper st f t r c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Spawn t r) c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Spawn t r) c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs f (R.ConstraintSystem.Spawn t r) c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 remember (R.observe st t) as st0 eqn:Hobserve.
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
Qed.
Lemma base_dead_below tf roots (finite : Sem.finite_system tf roots) upper st f t l c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunDead f t l c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunDead f t l c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead f t l c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct l as [|target remaining].
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
Qed.
Lemma base_commit_below tf roots (finite : Sem.finite_system tf roots) upper st f t c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit f t c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunCommit f t c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit f t c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct (R.set_value st f t) as [next next_fr] eqn:Hset.
      inversion Hstep; subst; clear Hstep.
      destruct Hcontrol_below as [Hcompleted Hk].
      destruct (@state_below_set_value
        (Sem.support finite) upper st f t next next_fr
        Hstate_below Hcompleted Hset) as [Hnext Hnext_fr].
      constructor; [now apply state_below_with_queue |]. cbn. now split.
Qed.
Lemma base_drain_below tf roots (finite : Sem.finite_system tf roots) upper st f c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain f c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunDrain f c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain f c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
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
Qed.
Lemma base_return_below tf roots (finite : Sem.finite_system tf roots) upper st c after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.Return c|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.Return c|} ->
 Sem.step tf {|R.cfg_state:=st;R.cfg_control:=R.Return c|} after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmonotone Hpost [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
 unfold Sem.step,R.next_config in Hstep.
 cbn in Hstate_supported,Hstate_below,Hcontrol_supported,Hcontrol_below.
 cbn [R.cfg_state R.cfg_control] in Hstep.
 destruct c.
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
  Theorem base_config_below_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper before after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.config_supported (Sem.support finite) before ->
      config_below (Sem.support finite) tf upper before ->
      Sem.step tf before after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper [st control] after Hmono Hpost Hsupported Hbelow Hstep.
    destruct control;
      try solve [eapply base_loop_below;eassumption];
      try solve [eapply base_seeds_below;eassumption];
      try solve [eapply base_seed_loop_below;eassumption];
      try solve [eapply base_start_below;eassumption];
      try solve [eapply base_dead_below;eassumption];
      try solve [eapply base_commit_below;eassumption];
      try solve [eapply base_drain_below;eassumption];
      try solve [eapply base_return_below;eassumption].
    destruct r;[eapply base_ret_below |eapply base_get_below |eapply base_side_below |eapply base_spawn_below];eassumption.
  Qed.

  Lemma initial_config_below :
    forall support tf roots upper,
      config_below support tf upper (R.initial_config roots).
  Proof.
    intros support tf roots upper. constructor.
    - apply empty_state_below.
    - exact I.
  Qed.


Lemma fresh_active tf roots (finite : Sem.finite_system tf roots) upper st owner phase :
 In owner (Sem.support finite) ->
 active_rhs_below (Sem.support finite) tf upper (R.fresh_frame st owner phase) (tf owner).
Proof.
 intro Howner. constructor;[apply frame_data_fresh,Howner |].
 apply initial_rhs_below;[exact Howner |apply Sem.system_supported,Howner].
Qed.
Lemma clear_below support tf upper st ctrl owner :
 config_below support tf upper {|R.cfg_state:=st;R.cfg_control:=ctrl|} ->
 config_below support tf upper {|R.cfg_state:=P.clear_owner st owner;R.cfg_control:=ctrl|}.
Proof. intros [Hs Hc]. constructor;[apply state_below_with_queue,Hs |exact Hc]. Qed.
Lemma suspend_below tf roots (finite : Sem.finite_system tf roots) upper st fr direct k target rest :
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 config_below (Sem.support finite) tf upper (P.suspend_commit tf st fr k target rest).
Proof.
 intros [Hsupport _] [Hs [[Hfr Hd] Hk]] Hp.
 destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop _]].
 destruct (@Total.queue_supported_pop (Sem.support finite) (R.queue st) target rest
 (Total.state_queue_supported Hsupport) Hpop) as [Ht _].
 constructor;[apply state_below_with_queue,Hs |]. split;[exact Ht |].
 split;[apply fresh_active, (frame_owner_below_supported Hfr) |exact Hk].
Qed.
Lemma precommit_below tf roots (finite : Sem.finite_system tf roots) upper before after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) before -> config_below (Sem.support finite) tf upper before ->
 P.next_config tf before=Some after -> config_below (Sem.support finite) tf upper after.
Proof.
 destruct before as [st ctrl]. intros Hmono Hpost Hsupport Hbelow Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_config_below_step;eassumption].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply suspend_below;eassumption.
 - eapply base_config_below_step;eassumption.
Qed.
Lemma old_publish_below upper targets st fr :
 state_below upper st -> frame_local_below upper fr ->
 state_below upper (P.publish_accumulated targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hs Hfr;
 cbn -[R.write_side_contribution];[exact Hs |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH;[|exact Hfr]. assert (Hnext : state_below upper next).
 { eapply state_below_write_side;[exact Hs | |exact Hw].
   destruct (M.lookup (R.frame_local_side fr) target) eqn:Hlookup;
   [eapply Hfr;exact Hlookup |apply DL.bottom_least]. }
 destruct changed;[apply state_below_enqueue,Hnext |exact Hnext].
Qed.
Lemma batched_below tf roots (finite : Sem.finite_system tf roots) upper before after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) before -> config_below (Sem.support finite) tf upper before ->
 P.next_batched tf before=Some after -> config_below (Sem.support finite) tf upper after.
Proof.
 destruct before as [st ctrl]. intros Hmono Hpost Hsupport Hbelow Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_below;eassumption].
 - destruct r;try solve [eapply precommit_below;eassumption].
   destruct Hbelow as [Hs [[Hfr Hrhs] Hk]].
   destruct (R.record_side_input f t t0) as [next_fr input] eqn:Hr.
   inversion Hstep;subst. constructor;[apply state_below_observe,Hs |]. split;[|exact Hk].
   destruct (@record_side_input_below (Sem.support finite) upper f t t0 next_fr input
   Hfr (@current_side_below (Sem.support finite) tf upper (R.frame_owner f) t t0 r Hmono Hpost Hrhs) Hr)
   as [Hnext _]. constructor;[exact Hnext |].
   rewrite (frame_owner_record_side_input Hr). eapply rhs_below_side;exact Hrhs.
 - destruct l;[|eapply precommit_below;eassumption].
   inversion Hstep;subst. destruct Hbelow as [Hs [[Hfr Hd] Hk]]. constructor.
   + apply state_below_publish_targets,old_publish_below;[exact Hs |exact (frame_local_side_below Hfr)].
   + split;[constructor;assumption |exact Hk].
Qed.
Lemma retry_below tf roots (finite : Sem.finite_system tf roots) upper st fr direct k :
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 config_below (Sem.support finite) tf upper (P.retry_current tf st fr k).
Proof.
 intros [Hs [[Hfr Hd] Hk]]. constructor;[apply state_below_with_queue,Hs |].
 split;[apply fresh_active, (frame_owner_below_supported Hfr) |exact Hk].
Qed.
Lemma fresh_below tf roots (finite : Sem.finite_system tf roots) upper before after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) before -> config_below (Sem.support finite) tf upper before ->
 P.next_fresh tf before=Some after -> config_below (Sem.support finite) tf upper after.
Proof.
 destruct before as [st ctrl]. intros Hmono Hpost Hsupport Hbelow Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_below;eassumption].
 - eapply batched_below;[exact Hmono |exact Hpost | | |exact Hstep].
   + apply Replay.Support.clear_config,Hsupport.
   + apply clear_below,Hbelow.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply suspend_below;eassumption.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. eapply retry_below;exact Hbelow.
     * eapply batched_below;eassumption.
 - destruct c;try solve [eapply batched_below;eassumption].
   eapply batched_below;[exact Hmono |exact Hpost | | |exact Hstep].
   + apply Replay.Support.clear_config,Hsupport.
   + apply clear_below,Hbelow.
Qed.
Lemma requeue_below upper before after source target :
 state_below upper after -> state_below upper (C.requeue_source before after source target).
Proof. unfold C.requeue_source. destruct C.cell_changed;[apply state_below_enqueue |trivial]. Qed.
Lemma finish_below upper before after fr target changed :
 state_below upper after -> state_below upper (C.finish_write before after fr target changed).
Proof. unfold C.finish_write. destruct changed;[intro H;apply state_below_enqueue,requeue_below,H |apply requeue_below]. Qed.
Lemma publish_below upper targets st fr :
 state_below upper st -> frame_local_below upper fr -> state_below upper (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hs Hfr;
 cbn -[R.write_side_contribution C.finish_write];[exact Hs |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw. apply IH;[apply finish_below |exact Hfr].
 eapply state_below_write_side;[exact Hs | |exact Hw].
 destruct (M.lookup (R.frame_local_side fr) target) eqn:Hlookup;
 [eapply Hfr;exact Hlookup |apply DL.bottom_least].
Qed.
Lemma continue_dead_below support tf upper st fr direct target rest k changed :
 In target support ->
 config_below support tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct rest k|} ->
 config_below support tf upper (R.continue_dead st fr direct target rest k changed).
Proof.
 intros Htarget [Hs [Hfr Hk]]. unfold R.continue_dead.
 destruct changed;[destruct (_ && _)%bool |];constructor;
 try exact Hs;try solve [apply state_below_enqueue,Hs];cbn;auto.
Qed.
Lemma dead_below tf roots (finite : Sem.finite_system tf roots) upper st fr direct pending k after :
 Total.config_supported (Sem.support finite) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 config_below (Sem.support finite) tf upper {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 C.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros [Hsupport [Hfs [Hpending Hks]]] [Hs [Hfr Hk]] Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst. constructor.
   + apply state_below_publish_targets,publish_below;[exact Hs |].
     exact (frame_local_side_below (completed_frame_data_below Hfr)).
   + now split.
 - inversion Hpending;subst.
   cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));
   [inversion Hstep;subst;constructor;[exact Hs |now split] |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. apply continue_dead_below;[assumption |]. constructor.
   + apply requeue_below. eapply state_below_write_side;[exact Hs |apply DL.bottom_least |exact Hw].
   + now split.
Qed.
Theorem original_config_below_step tf roots (finite : Sem.finite_system tf roots) upper before after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) before -> config_below (Sem.support finite) tf upper before ->
 C.next_config tf before=Some after -> config_below (Sem.support finite) tf upper after.
Proof.
 destruct before as [st ctrl]. intros Hmono Hpost Hsupport Hbelow Hstep. destruct ctrl;
 try solve [eapply fresh_below;eassumption]. eapply dead_below;eassumption.
Qed.
(** The extra return-to-child transition changes only the pending queue
    and the suspended frame; both remain below the same post-solution. *)
Lemma resume_below tf roots (finite : Sem.finite_system tf roots)
 upper st fr body k target rest :
 Total.config_supported (Sem.support finite)
   {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterSide fr body k)|} ->
 config_below (Sem.support finite) tf upper
   {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterSide fr body k)|} ->
 P.pending_above st (R.frame_owner fr)=Some(target,rest) ->
 config_below (Sem.support finite) tf upper
   (P.suspend_commit tf st fr k target rest).
Proof.
 intros [Hs [Hfr [Hbody Hk]]] [Hbelow [[Hdata Hrhs] Hrest]] Hp.
 eapply (@suspend_below tf roots finite upper st fr D.bottom k target rest).
 - split;[exact Hs |]. now split.
 - constructor;[exact Hbelow |]. split;[|exact Hrest].
   constructor;[exact Hdata |apply DL.bottom_least].
 - exact Hp.
Qed.

Theorem config_below_step tf roots (finite : Sem.finite_system tf roots)
 upper before after :
 system_monotone_on tf (Sem.support finite) ->
 post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) before ->
 config_below (Sem.support finite) tf upper before ->
 N.next_config tf before=Some after ->
 config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmono Hpost Hsupport Hbelow Hstep.
 destruct (@Replay.Front.step_cases tf before after Hstep)
 as [Hold|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - eapply original_config_below_step;eassumption.
 - eapply resume_below;eassumption.
Qed.

Lemma config_below_steps tf roots (finite : Sem.finite_system tf roots) upper first last :
 N.steps tf first last -> system_monotone_on tf (Sem.support finite) ->
 post_solution_on tf (Sem.support finite) upper ->
 Total.config_supported (Sem.support finite) first -> config_below (Sem.support finite) tf upper first ->
 config_below (Sem.support finite) tf upper last.
Proof.
 intro Hsteps. induction Hsteps;intros Hmono Hpost Hsupported Hbelow;[exact Hbelow |].
 apply IHHsteps;[exact Hmono |exact Hpost | |].
 - eapply Replay.Support.next;[ |exact Hsupported |exact H].
   intros owner Hin. pose proof (@Sem.system_supported tf roots finite owner Hin) as Hbody.
   induction Hbody;constructor;assumption.
 - eapply config_below_step;eassumption.
Qed.
Theorem reachable_config_below tf roots (finite : Sem.finite_system tf roots) upper after :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 N.steps tf (R.initial_config roots) after -> config_below (Sem.support finite) tf upper after.
Proof.
 intros Hmono Hpost Hsteps. eapply config_below_steps;[exact Hsteps |exact Hmono |exact Hpost | |].
 - unfold Total.config_supported. split;[apply Total.empty_state_supported |].
   cbn. apply Forall_forall. intros x Hin. exact (@Sem.initial_supported tf roots finite x Hin).
 - apply initial_config_below.
Qed.
Theorem successful_run_below fuel tf roots (finite : Sem.finite_system tf roots) final upper :
 system_monotone_on tf (Sem.support finite) -> post_solution_on tf (Sem.support finite) upper ->
 N.solve_fuel fuel tf roots=Some final -> sigma_below upper final.
Proof.
 intros Hmono Hpost Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@Total.terminal_state_shape _ final Hsolve) as [Hshape Hquiet].
 pose proof (@reachable_config_below tf roots finite upper _ Hmono Hpost
 (N.fuel_steps fuel tf (R.initial_config roots))) as Hbelow.
 rewrite Hshape in Hbelow. exact (state_sigma_below (config_state_below Hbelow)).
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
    intros st x. unfold Sem.solved.
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


Lemma eval_replay st body direct reads effects :
 Sem.rhs_eval st body direct reads effects -> Replay.Sem.rhs_eval st body direct reads effects.
Proof. intro Heval. induction Heval;constructor;assumption. Qed.
Lemma replay_eval st body direct reads effects :
 Replay.Sem.rhs_eval st body direct reads effects -> Sem.rhs_eval st body direct reads effects.
Proof. intro Heval. induction Heval;constructor;assumption. Qed.
Theorem successful_run_correct fuel tf roots final :
 N.solve_fuel fuel tf roots=Some final -> Sem.correct_final_state tf roots final.
Proof.
 intros Hrun owner Hin. destruct (@Replay.successful_run_correct fuel tf roots final Hrun owner Hin)
 as [Hsolved Hpost]. split;[exact Hsolved |].
 intros direct reads effects Heval. exact (Hpost direct reads effects (eval_replay Heval)).
Qed.
Lemma successful_solved_observation_post fuel tf roots final owner result :
 N.solve_fuel fuel tf roots=Some final -> Sem.solved final owner ->
 observes_at (R.sigma_value final) (tf owner) result ->
 D.leq (observed_direct result) (R.sigma_value final owner)=true /\
 Sem.valuation_side_effects_below (R.sigma_value final) (observed_sides result).
Proof.
 intros Hrun Hsolved Hobs.
 destruct (@Replay.successful_run_replay_post_solution fuel tf roots final Hrun owner Hsolved)
 as [[direct [reads [effects Heval]]] Hpost].
 pose proof (@replay_eval final (tf owner) direct reads effects Heval) as Hlocal.
 destruct (rhs_eval_observation_agrees Hlocal Hobs) as [<- [_ <-]].
 exact (Hpost direct reads effects Heval).
Qed.
Theorem successful_source_strict_solution fuel tf roots (finite : Sem.finite_system tf roots) final :
 source_strict_on tf (Sem.support finite) roots -> N.solve_fuel fuel tf roots=Some final ->
 post_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
 intros Hstrict Hrun.
 eapply (@Strict.bottom_completion_is_post_solution _ _ Sem.observes_at
 Sem.observed_direct Sem.observed_sides tf (Sem.support finite) roots
 (R.sigma_value final) (Sem.solved final)).
 - apply solved_dec.
 - exact Hstrict.
 - intros x Hin. exact (proj1 (@successful_run_correct fuel tf roots final Hrun x Hin)).
 - apply unsolved_value_bottom.
 - intros owner Hin Hsolved result Hobs. eapply successful_solved_observation_post;eassumption.
Qed.
Definition finite_replay tf roots (finite : Sem.finite_system tf roots) : Replay.Sem.finite_system tf roots.
Proof.
 refine (@Replay.Sem.Build_finite_system tf roots (Sem.support finite)
 (@Sem.support_nodup tf roots finite) (@Sem.initial_supported tf roots finite) _).
 intros owner Hin. pose proof (@Sem.system_supported tf roots finite owner Hin) as Hbody.
 induction Hbody;constructor;assumption.
Defined.
Theorem sufficient_fuel tf roots (finite : Sem.finite_system tf roots) :
 exists fuel final,N.solve_fuel fuel tf roots=Some final.
Proof. exact (@Replay.Termination.sufficient_fuel tf roots (finite_replay finite)). Qed.
(** Minimality at every solved owner needs no condition on unrequested owners. *)
Theorem total_minimal_on_solved tf roots (finite : Sem.finite_system tf roots) :
 system_monotone_on tf (Sem.support finite) ->
 exists fuel final,N.solve_fuel fuel tf roots=Some final /\
 Sem.correct_final_state tf roots final /\
 forall upper,post_solution_on tf (Sem.support finite) upper ->
 forall owner,Sem.solved final owner -> D.leq (R.sigma_value final owner) (upper owner)=true.
Proof.
 intro Hmono. destruct (sufficient_fuel finite) as [fuel [final Hrun]].
 exists fuel,final. split;[exact Hrun |].
 split;[exact (@successful_run_correct fuel tf roots final Hrun) |].
 intros upper Hpost owner Hsolved. eapply successful_run_below;eassumption.
Qed.
Theorem total_least_on_solved tf roots (finite : Sem.finite_system tf roots) :
 source_strict_on tf (Sem.support finite) roots -> system_monotone_on tf (Sem.support finite) ->
 exists fuel final,N.solve_fuel fuel tf roots=Some final /\
 Sem.correct_final_state tf roots final /\
 post_solution_on tf (Sem.support finite) (R.sigma_value final) /\
 forall upper,post_solution_on tf (Sem.support finite) upper ->
 forall owner,Sem.solved final owner -> D.leq (R.sigma_value final owner) (upper owner)=true.
Proof.
 intros Hstrict Hmono. destruct (sufficient_fuel finite) as [fuel [final Hrun]].
 exists fuel,final. split;[exact Hrun |]. split;[exact (@successful_run_correct fuel tf roots final Hrun) |].
 split;[eapply successful_source_strict_solution;eassumption |].
 intros upper Hpost owner Hsolved. eapply successful_run_below;eassumption.
Qed.
Theorem total_least_solution tf roots (finite : Sem.finite_system tf roots) :
 source_strict_on tf (Sem.support finite) roots -> system_monotone_on tf (Sem.support finite) ->
 exists fuel final,N.solve_fuel fuel tf roots=Some final /\
 least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
 intros Hstrict Hmono. destruct (sufficient_fuel finite) as [fuel [final Hrun]].
 exists fuel,final. split;[exact Hrun |]. split.
 - eapply successful_source_strict_solution;eassumption.
 - intros upper Hpost owner Hin. eapply successful_run_below;eassumption.
Qed.

End Make.
