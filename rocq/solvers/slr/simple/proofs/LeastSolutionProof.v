From Stdlib Require Import List Sorting.Permutation.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  common.SourceStrictness
  common.Observations
  solvers.slr.simple.proofs.Correctness.

Import ListNotations.
Set Implicit Arguments.

(** Internal least-solution proof for updates that preserve every common upper bound. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Total := Correctness.Make
    V D U S M Rk RankLaws RankFinite DL UL SL ML.
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

  Definition local_sides_below
    (upper : Least.valuation) (st : R.state) : Prop :=
    forall source target value,
      M.lookup (R.lookup_map (R.local_sides st) source) target = Some value ->
      D.leq value (upper target) = true.

  Record state_below (upper : Least.valuation) (st : R.state) : Prop := {
    state_sigma_below : sigma_below upper st;
    state_aggregates_below : aggregates_below upper st;
    state_local_sides_below : local_sides_below upper st;
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

  Fixpoint continuation_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest =>
        List.In (R.handle_variable owner) support /\
        continuation_below support tf upper rest
    | R.KAfterGet owner target next rest =>
        rhs_below support tf upper (R.handle_variable owner)
          (R.ConstraintSystem.Get (R.handle_variable target) next) /\
        continuation_below support tf upper rest
    | R.KAfterSide owner next rest
    | R.KAfterSpawn owner next rest =>
        rhs_below support tf upper (R.handle_variable owner) next /\
        continuation_below support tf upper rest
    end.

  Definition control_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne owner rest | R.RunSolveOneLoop owner rest =>
        List.In (R.handle_variable owner) support /\
        continuation_below support tf upper rest
    | R.RunRhs owner body rest =>
        rhs_below support tf upper (R.handle_variable owner) body /\
        continuation_below support tf upper rest
    | R.AfterGet owner target next rest =>
        rhs_below support tf upper (R.handle_variable owner)
          (R.ConstraintSystem.Get (R.handle_variable target) next) /\
        continuation_below support tf upper rest
    | R.AfterSide owner next rest | R.AfterSpawn owner next rest =>
        rhs_below support tf upper (R.handle_variable owner) next /\
        continuation_below support tf upper rest
    end.

  Record config_below
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (upper : Least.valuation) (c : R.config) : Prop := {
    config_state_below : state_below upper (R.cfg_state c);
    config_control_below : control_below support tf upper (R.cfg_control c);
  }.

  Lemma empty_state_below :
    forall upper, state_below upper R.empty_state.
  Proof.
    intros upper. constructor.
    - intros variable. unfold R.sigma_value. cbn.
      rewrite ML.lookup_empty. apply DL.bottom_least.
    - intros target. unfold R.aggregate, R.lookup_map. cbn.
      rewrite ML.lookup_empty, ML.values_empty. cbn.
      apply DL.bottom_least.
    - intros source target value Hlookup.
      unfold R.lookup_map in Hlookup. cbn in Hlookup.
      rewrite ML.lookup_empty, ML.lookup_empty in Hlookup. discriminate.
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
        eapply Total.Total.value_below_join_values. exact Hbound.
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
      + eapply Total.Total.stored_value_below_aggregate. exact Hlookup.
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

  Lemma local_sides_update_below :
    forall upper st source target next,
      local_sides_below upper st ->
      D.leq next (upper target) = true ->
      local_sides_below upper
        (R.with_local_sides st
          (R.update_map (R.local_sides st) source target next)).
  Proof.
    intros upper st source target next Hlocal Hnext
      observed_source observed_target value Hlookup.
    cbn in Hlookup.
    destruct (V.eq_dec observed_source source) as [-> | Hsource].
    - destruct (V.eq_dec observed_target target) as [-> | Htarget].
      + rewrite Total.Total.lookup_update_map_same in Hlookup.
        inversion Hlookup; subst. exact Hnext.
      + rewrite Total.Accounting.lookup_update_map_other_inner in Hlookup
          by exact Htarget.
        eapply Hlocal; exact Hlookup.
    - rewrite Total.Accounting.lookup_update_map_other_outer in Hlookup
        by exact Hsource.
      eapply Hlocal; exact Hlookup.
  Qed.

  Lemma accumulated_side_input_below :
    forall upper st source target raw,
      local_sides_below upper st ->
      D.leq raw (upper target) = true ->
      D.leq (R.accumulated_side_input st source target raw)
        (upper target) = true.
  Proof.
    intros upper st source target raw Hlocal Hraw.
    unfold R.accumulated_side_input.
    destruct (M.lookup (R.lookup_map (R.local_sides st) source) target)
      as [previous |] eqn:Hlookup.
    - apply DL.join_least; [eapply Hlocal; exact Hlookup |exact Hraw].
    - exact Hraw.
  Qed.

  Lemma state_below_observe :
    forall upper st target next entry,
      state_below upper st ->
      R.observe st target = (next, entry) ->
      state_below upper next.
  Proof.
    intros upper st target next entry Hbelow Hobserve.
    destruct Hbelow as [Hsigma Haggregate Hlocal]. constructor.
    - intros observed. rewrite (@Total.Payment.sigma_value_observe
        st target next entry observed Hobserve). apply Hsigma.
    - intros observed. rewrite (@Total.ExitReady.aggregate_observe
        st target next entry observed Hobserve). apply Haggregate.
    - intros source observed value Hlookup.
      unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) target);
        inversion Hobserve; subst. exact (Hlocal source observed value Hlookup).
  Qed.

  Lemma state_below_enqueue_handle :
    forall upper st entry,
      state_below upper st ->
      state_below upper (R.enqueue_handle st entry).
  Proof.
    intros upper st entry [Hsigma Haggregate Hlocal].
    constructor; assumption.
  Qed.

  Lemma state_below_with_queue :
    forall upper st queue,
      state_below upper st ->
      state_below upper (R.with_queue st queue).
  Proof.
    intros upper st queue [Hsigma Haggregate Hlocal].
    constructor; assumption.
  Qed.

  Lemma state_below_with_started :
    forall upper st started,
      state_below upper st ->
      state_below upper (R.with_started st started).
  Proof.
    intros upper st started [Hsigma Haggregate Hlocal].
    constructor; assumption.
  Qed.

  Lemma state_below_materialize :
    forall upper st target,
      state_below upper st ->
      state_below upper (R.materialize st target).
  Proof.
    intros upper st target [Hsigma Haggregate Hlocal]. constructor.
    - intros observed. rewrite Total.Payment.sigma_value_materialize.
      apply Hsigma.
    - intros observed. rewrite Total.ExitReady.aggregate_materialize.
      apply Haggregate.
    - intros source observed value Hlookup.
      unfold R.materialize in Hlookup.
      destruct (R.is_materialized st target); cbn in Hlookup;
        eapply Hlocal; exact Hlookup.
  Qed.

  Lemma state_below_start_evaluation :
    forall upper st owner,
      state_below upper st ->
      state_below upper (R.start_evaluation st owner).
  Proof.
    intros upper st owner [Hsigma Haggregate Hlocal]. constructor.
    - intros observed. rewrite Total.Payment.sigma_value_start_evaluation.
      apply Hsigma.
    - intros observed. rewrite Total.ExitReady.aggregate_start_evaluation.
      apply Haggregate.
    - intros source target value Hlookup.
      unfold R.start_evaluation, R.reset_local_sides in Hlookup. cbn in Hlookup.
      destruct (V.eq_dec source owner) as [-> | Hneq].
      + unfold R.lookup_map in Hlookup. cbn in Hlookup.
        rewrite ML.lookup_update_same, ML.lookup_empty in Hlookup.
        discriminate.
      + unfold R.lookup_map in Hlookup. cbn in Hlookup.
        rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        unfold R.materialize in Hlookup.
        destruct (R.is_materialized st owner); cbn in Hlookup;
          eapply Hlocal; exact Hlookup.
  Qed.

  Lemma state_below_get_ready :
    forall upper st owner target,
      state_below upper st ->
      state_below upper (R.get_ready_state st owner target).
  Proof.
    intros upper st owner target [Hsigma Haggregate Hlocal]. constructor.
    - intros observed. rewrite Total.Payment.sigma_value_get_ready.
      apply Hsigma.
    - intros observed. rewrite Total.ExitReady.aggregate_get_ready.
      apply Haggregate.
    - intros source observed value Hlookup.
      unfold R.get_ready_state, R.add_reader, R.promote_controlled in Hlookup.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        unfold R.materialize in Hlookup;
        destruct (R.is_materialized _ _); cbn in Hlookup;
        eapply Hlocal; exact Hlookup.
  Qed.

  Lemma state_below_side_ready :
    forall upper st source target raw,
      state_below upper st ->
      D.leq raw (upper (R.handle_variable target)) = true ->
      state_below upper (R.side_ready_state st source target raw).
  Proof.
    intros upper st source target raw [Hsigma Haggregate Hlocal] Hraw.
    pose proof (@accumulated_side_input_below upper st
      (R.handle_variable source) (R.handle_variable target) raw
      Hlocal Hraw) as Hinput.
    pose proof (@stored_contribution_below upper st
      (R.handle_variable source) (R.handle_variable target) Haggregate)
      as Hold.
    pose proof (@UBL.update_preserves_upper_bound true
      (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw)
      (upper (R.handle_variable target)) Hold Hinput) as Hupdated.
    unfold R.side_ready_state, R.record_side_payload.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw)) as [phase next] eqn:Hupdate.
    cbn in Hupdated.
    assert (Haggregate_next : aggregates_below upper
      (R.with_contributions st
        (R.update_map (R.contributions st) (R.handle_variable target)
          (R.handle_variable source) next))).
    { eapply aggregate_update_below; [exact Haggregate |exact Hupdated]. }
    assert (Hlocal_next : local_sides_below upper
      (R.with_local_sides st
        (R.update_map (R.local_sides st) (R.handle_variable source)
          (R.handle_variable target)
          (R.accumulated_side_input st (R.handle_variable source)
            (R.handle_variable target) raw)))).
    { eapply local_sides_update_below; [exact Hlocal |exact Hinput]. }
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      constructor; cbn; assumption.
  Qed.

  Lemma local_sides_set_value :
    forall st owner direct,
      R.local_sides (R.set_value st owner direct) = R.local_sides st.
  Proof.
    intros st owner direct. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [reflexivity |].
    destruct (S.mem owner (R.controlled st));
      [|unfold R.write_changed_value; cbn;
         now rewrite Total.Total.local_sides_enqueue_all].
    destruct (U.update false owner (R.stored_phase st owner)
      (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
      as [phase value]. cbn.
    destruct (R.equivalent value (R.sigma_value st owner));
      [reflexivity |unfold R.write_changed_value; cbn;
         now rewrite Total.Total.local_sides_enqueue_all].
  Qed.

  Lemma state_below_set_value :
    forall upper st owner direct,
      state_below upper st ->
      D.leq direct (upper owner) = true ->
      state_below upper (R.set_value st owner direct).
  Proof.
    intros upper st owner direct [Hsigma Haggregate Hlocal] Hdirect.
    assert (Hcandidate :
      D.leq (D.join direct (R.aggregate st owner)) (upper owner) = true).
    { apply DL.join_least; [exact Hdirect |apply Haggregate]. }
    constructor.
    - intros observed. destruct (V.eq_dec observed owner) as [-> | Hneq].
      + unfold R.set_value.
        destruct (R.equivalent
          (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
          [apply Hsigma |].
        destruct (S.mem owner (R.controlled st)).
        * destruct (U.update false owner (R.stored_phase st owner)
            (R.sigma_value st owner)
            (D.join direct (R.aggregate st owner)))
            as [phase value] eqn:Hupdate. cbn.
          pose proof (@UBL.update_preserves_upper_bound false owner
            (R.stored_phase st owner) (R.sigma_value st owner)
            (D.join direct (R.aggregate st owner)) (upper owner)
            (Hsigma owner) Hcandidate) as Hvalue.
          rewrite Hupdate in Hvalue. cbn in Hvalue.
          destruct (R.equivalent value (R.sigma_value st owner));
            [apply Hsigma |].
          rewrite Total.Accounting.sigma_value_write_changed_same.
          exact Hvalue.
        * rewrite Total.Accounting.sigma_value_write_changed_same.
          exact Hcandidate.
      + rewrite Total.Payment.sigma_value_set_value_other by exact Hneq.
        apply Hsigma.
    - intros target. rewrite Total.ExitReady.aggregate_set_value.
      apply Haggregate.
    - intros source target value Hlookup.
      rewrite local_sides_set_value in Hlookup.
      eapply Hlocal; exact Hlookup.
  Qed.

  Lemma initial_rhs_below :
    forall support tf upper owner,
      List.In owner support ->
      Sem.rhs_supported (fun target => List.In target support) (tf owner) ->
      rhs_below support tf upper owner (tf owner).
  Proof.
    intros support tf upper owner Howner Hbody.
    refine (@RhsBelow support tf upper owner (tf owner)
      Howner Hbody Hbody [] [] [] _ _).
    - apply initial_full_rhs_context.
    - intros target value Hin. contradiction.
  Qed.

  Lemma rhs_below_get :
    forall support tf upper owner target next value,
      rhs_below support tf upper owner (R.ConstraintSystem.Get target next) ->
      D.leq value (upper target) = true ->
      rhs_below support tf upper owner (next value).
  Proof.
    intros support tf upper owner target next value Hbelow Hvalue.
    destruct Hbelow as
      [Howner Hroot Hsupported reads sides spawns Hcontext Hreads].
    assert (Hnext : forall observed,
      Sem.rhs_supported (fun variable => List.In variable support)
        (next observed)).
    { inversion Hsupported; subst. assumption. }
    refine (@RhsBelow support tf upper owner (next value)
      Howner Hroot (Hnext value)
      (reads ++ [(target, value)]) sides spawns _ _).
    - now apply full_rhs_context_get.
    - now apply prefix_reads_below_snoc.
  Qed.

  Lemma rhs_below_side :
    forall support tf upper owner target payload next,
      rhs_below support tf upper owner
        (R.ConstraintSystem.Side target payload next) ->
      rhs_below support tf upper owner next.
  Proof.
    intros support tf upper owner target payload next Hbelow.
    destruct Hbelow as
      [Howner Hroot Hsupported reads sides spawns Hcontext Hreads].
    assert (Hnext :
      Sem.rhs_supported (fun variable => List.In variable support) next).
    { inversion Hsupported; subst. assumption. }
    refine (@RhsBelow support tf upper owner next
      Howner Hroot Hnext reads
      (sides ++ [(target, payload)]) spawns _ _).
    - now apply full_rhs_context_side.
    - exact Hreads.
  Qed.

  Lemma rhs_below_spawn :
    forall support tf upper owner target next,
      rhs_below support tf upper owner (R.ConstraintSystem.Spawn target next) ->
      rhs_below support tf upper owner next.
  Proof.
    intros support tf upper owner target next Hbelow.
    destruct Hbelow as
      [Howner Hroot Hsupported reads sides spawns Hcontext Hreads].
    assert (Hnext :
      Sem.rhs_supported (fun variable => List.In variable support) next).
    { inversion Hsupported; subst. assumption. }
    refine (@RhsBelow support tf upper owner next
      Howner Hroot Hnext reads sides
      (spawns ++ [target]) _ _).
    - now apply full_rhs_context_spawn.
    - exact Hreads.
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

  Lemma continuation_below_continue :
    forall support tf upper k,
      continuation_below support tf upper k ->
      control_below support tf upper (R.continue k).
  Proof. intros support tf upper k Hbelow. destruct k; exact Hbelow. Qed.

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
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - destruct (@Total.queue_supported_pop
        (Sem.support finite) (R.queue st) h w
        (Total.queue_is_supported Hstate_supported) Hcase)
        as [Howner _].
      constructor; [now apply state_below_with_queue |].
      cbn. now split.
    - constructor; [exact Hstate_below |exact I].
    - constructor; [eapply state_below_observe; eauto |exact I].
    - inversion Hcontrol_supported as [|? ? Hroot Hrest]; subst.
      pose proof (@Total.observed_handle_variable st t s h Hcase0)
        as Hvariable.
      constructor; [eapply state_below_observe; eauto |].
      cbn. rewrite Hvariable. now split.
    - destruct (@Total.queue_supported_pop
        (Sem.support finite) (R.queue st) h w
        (Total.queue_is_supported Hstate_supported) Hcase)
        as [Howner _].
      constructor; [now apply state_below_with_queue |].
      cbn. now split.
    - constructor; [exact Hstate_below |exact I].
    - destruct Hcontrol_below as [Howner Hk]. constructor.
      + apply state_below_with_started, state_below_start_evaluation.
        exact Hstate_below.
      + cbn. split.
        * apply initial_rhs_below; [exact Howner |].
          apply Sem.system_supported. exact Howner.
        * exact Hk.
    - constructor; [now apply state_below_with_queue |exact Hcontrol_below].
    - destruct (@Total.queue_supported_pop
        (Sem.support finite) (R.queue st) h0 w
        (Total.queue_is_supported Hstate_supported) Hcase0)
        as [Hnext _].
      destruct Hcontrol_below as [Howner Hk].
      constructor; [now apply state_below_with_queue |].
      cbn. split; [exact Hnext |]. now split.
    - constructor; [exact Hstate_below |].
      apply continuation_below_continue. exact (proj2 Hcontrol_below).
    - destruct Hcontrol_below as [Hrhs Hk]. constructor.
      + apply state_below_set_value; [exact Hstate_below |].
        eapply current_direct_below; eauto.
      + cbn. split.
        * eapply rhs_below_owner_in_support; exact Hrhs.
        * exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      assert (Hready : state_below upper (R.get_ready_state s h h0))
        by (now apply state_below_get_ready).
      constructor; [exact Hready |]. cbn. split.
      + eapply rhs_below_get with (target := t); [exact Hrhs |].
        exact (state_sigma_below Hready t).
      + exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      pose proof (@Total.observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      constructor; [eapply state_below_observe; eauto |].
      cbn. split.
      + rewrite Hvariable.
        eapply rhs_below_get_target_in_support; exact Hrhs.
      + rewrite Hvariable. split; assumption.
    - destruct Hcontrol_below as [Hrhs Hk].
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      assert (Henqueued : state_below upper (R.enqueue_handle s h0))
        by (now apply state_below_enqueue_handle).
      assert (Hready : state_below upper
        (R.get_ready_state (R.enqueue_handle s h0) h h0))
        by (now apply state_below_get_ready).
      constructor; [exact Hready |]. cbn. split.
      + eapply rhs_below_get with (target := t); [exact Hrhs |].
        exact (state_sigma_below Hready t).
      + exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      pose proof (@Total.observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      assert (Hraw : D.leq t0 (upper t) = true)
        by (eapply current_side_below; eauto).
      assert (Hready : state_below upper (R.side_ready_state s h h0 t0)).
      { apply state_below_side_ready; [exact Hobserved |].
        now rewrite Hvariable. }
      assert (Hnext : rhs_below (Sem.support finite) tf upper
        (R.handle_variable h) r0)
        by (now apply rhs_below_side with (target := t) (payload := t0)).
      constructor; [exact Hready |]. cbn. split.
      + rewrite Hvariable.
        eapply rhs_below_side_target_in_support; exact Hrhs.
      + now split.
    - destruct Hcontrol_below as [Hrhs Hk].
      pose proof (@Total.observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      assert (Hraw : D.leq t0 (upper t) = true)
        by (eapply current_side_below; eauto).
      assert (Hready : state_below upper (R.side_ready_state s h h0 t0)).
      { apply state_below_side_ready; [exact Hobserved |].
        now rewrite Hvariable. }
      constructor; [now apply state_below_enqueue_handle |].
      cbn. split.
      + now apply rhs_below_side with (target := t) (payload := t0).
      + exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      pose proof (@Total.observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      assert (Hraw : D.leq t0 (upper t) = true)
        by (eapply current_side_below; eauto).
      assert (Hready : state_below upper (R.side_ready_state s h h0 t0)).
      { apply state_below_side_ready; [exact Hobserved |].
        now rewrite Hvariable. }
      constructor; [exact Hready |]. cbn. split.
      + now apply rhs_below_side with (target := t) (payload := t0).
      + exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk]. constructor.
      + eapply state_below_observe; eauto.
      + cbn. split.
        * now apply rhs_below_spawn with (target := t).
        * exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      pose proof (@Total.observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      assert (Hnext : rhs_below (Sem.support finite) tf upper
        (R.handle_variable h) r0)
        by (now apply rhs_below_spawn with (target := t)).
      constructor; [eapply state_below_observe; eauto |].
      cbn. split.
      + rewrite Hvariable.
        eapply rhs_below_spawn_target_in_support; exact Hrhs.
      + now split.
    - destruct Hcontrol_below as [Hrhs Hk].
      assert (Hobserved : state_below upper s)
        by (eapply state_below_observe; eauto).
      constructor.
      + apply state_below_materialize, state_below_enqueue_handle.
        exact Hobserved.
      + cbn. split.
        * now apply rhs_below_spawn with (target := t).
        * exact Hk.
    - destruct Hcontrol_below as [Hrhs Hk].
      assert (Hready : state_below upper (R.get_ready_state st h h0))
        by (now apply state_below_get_ready).
      constructor; [exact Hready |]. cbn. split.
      + eapply rhs_below_get with (target := R.handle_variable h0);
          [exact Hrhs |].
        exact (state_sigma_below Hready (R.handle_variable h0)).
      + exact Hk.
    - constructor; [exact Hstate_below |exact Hcontrol_below].
    - constructor; [exact Hstate_below |exact Hcontrol_below].
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
      + eapply Total.next_config_supported; eauto.
      + eapply config_below_step; eauto.
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
    pose proof (@Total.Total.terminal_invariant tf roots final Hterm) as Hinv.
    destruct Hterm as [_ Hquiet].
    assert (Hnotqueued : forall x, ~ Total.Total.queued final x).
    { intros x. eapply Total.Total.quiescent_not_queued; exact Hquiet. }
    assert (Haggregate : forall target,
      D.leq (R.aggregate final target) (R.sigma_value final target) = true).
    { intros target. destruct (Total.Total.invariant_aggregate Hinv target)
        as [Hqueued | [Hactive | Hbounded]].
      - contradiction (Hnotqueued target Hqueued).
      - contradiction.
      - exact Hbounded. }
    destruct (Total.Total.invariant_summaries Hinv Hsolved)
      as [Hqueued | [Hactive | Hsummary]].
    - contradiction (Hnotqueued owner Hqueued).
    - contradiction.
    - pose proof (Total.Total.summary_valid_replay (Hnotqueued owner) Haggregate Hsummary) as Hpost.
      destruct Hsummary as [direct [reads [effects
        [Htrace [Hreads [Heffects Hdirect]]]]]].
      assert (Heval : Sem.rhs_eval final (tf owner) direct reads effects).
      { eapply Total.Total.guarded_trace_evaluates; eauto. }
      destruct (rhs_eval_observation_agrees Heval Hobs) as [<- [_ <-]].
      exact (Hpost direct reads effects Heval).
  Qed.

  (** Source strictness closes the unsolved part of the finite system. *)
  Theorem successful_source_strict_solution :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      source_strict_on tf (Sem.support finite) roots ->
      R.solve_fuel fuel tf roots = Some final ->
      post_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros fuel tf roots finite final Hstrict Hrun.
    pose proof (@Total.successful_run_terminates_to
      fuel tf roots final Hrun) as Hterm.
    eapply (@Strict.bottom_completion_is_post_solution _ _ Sem.observes_at
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
    intros tf variables final Hclosed Hcorrect owner Howner result Hobserves.
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
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module U := JoinUpdate V D.
  Module UL := JoinUpdateLaws V D DL FH.
  Module UBL := JoinUpdateUpperBoundLaws V D DL.
  Include Make V D U S M Rk RankLaws RankFinite DL UL UBL SL ML.
End FiniteHeight.

Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (S : SET V)
  (M : MAP V)
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
    V D S M Rk RankLaws RankFinite DL FH SL ML.
End FirstDiscovery.

Module FixedRank
  (V : VAR)
  (D : DOMAIN)
  (S : SET V)
  (M : MAP V)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed)
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
    V D S M Rk RankLaws RankFinite DL FH SL ML.
End FixedRank.
