From Stdlib Require Import List Sorting.Permutation.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  common.SourceStrictness
  common.Observations
  common.SideUpdate
  common.ReluctantUpdate
  solvers.slr.deferred_simple.DeferredSimple
  solvers.slr.deferred_simple.proofs.Termination.

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
  (Features : DeferredSimple.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DormantRankLaws : DORMANT_DISCOVERY_ORDER_LAWS V Rk)
  (DL : DOMAIN_LAWS D)
  (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U)
  (SUL : SIDE_UPDATE_TERMINATION_LAWS V D SU)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Total := Termination.Make
    V D U SU S M Rk Features SL ML DL OUL SUL RankLaws DormantRankLaws RankFinite.
  Module Sem := Total.Sem.
  Module R := Total.R.
  Module LeastSolution
    (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
    (SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU).
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

  Lemma aggregate_observe : forall st target next entry observed,
    R.observe st target = (next, entry) -> R.aggregate next observed = R.aggregate st observed.
  Proof.
    intros st target next entry observed Ho. unfold R.observe in Ho.
    destruct (R.Ranking.observe (R.ranking st) target); inversion Ho; reflexivity.
  Qed.

  Lemma aggregate_start_evaluation : forall st owner observed,
    R.aggregate (R.start_evaluation st owner) observed = R.aggregate st observed.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides. apply Total.C.materialize_aggregate.
  Qed.

  Lemma aggregate_try_dirty_read : forall tf st owner target next observed,
    R.try_dirty_read tf st owner target = Some next ->
    R.aggregate next observed = R.aggregate st observed.
  Proof.
    intros tf st owner target next observed Hread. unfold R.aggregate.
    now rewrite (@Total.C.try_dirty_read_contributions tf st owner target next Hread).
  Qed.

  Lemma aggregate_set_value : forall st owner direct target,
    R.aggregate (R.set_value st owner direct) target = R.aggregate st target.
  Proof. intros. unfold R.aggregate. now rewrite Total.C.set_value_contributions. Qed.

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
        eapply Total.C.join_values_upper. exact Hbound.
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
      + eapply Total.C.stored_value_below_aggregate. exact Hlookup.
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
      + rewrite Total.C.lookup_update_map_same in Hlookup.
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
    - intros observed. rewrite (@aggregate_observe
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

  Lemma state_below_mark_side_dirty :
    forall upper st target,
      state_below upper st ->
      state_below upper (R.mark_side_dirty st target).
  Proof.
    intros upper st target [Hsigma Haggregate Hlocal].
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
    - intros observed. rewrite Total.C.materialize_aggregate.
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
    - intros observed. rewrite aggregate_start_evaluation.
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
    - intros observed. rewrite Total.C.get_ready_state_aggregate.
      apply Haggregate.
    - intros source observed value Hlookup.
      unfold R.get_ready_state, R.add_reader, R.promote_controlled in Hlookup.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        unfold R.materialize in Hlookup;
        destruct (R.is_materialized _ _); cbn in Hlookup;
        eapply Hlocal; exact Hlookup.
  Qed.

  Lemma local_sides_try_dirty_read :
    forall tf st owner target next,
      R.try_dirty_read tf st owner target = Some next ->
      R.local_sides next = R.local_sides st.
  Proof.
    intros tf st owner target next Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      try rewrite Total.C.local_sides_enqueue_all; reflexivity.
  Qed.

  Lemma state_below_try_dirty_read :
    forall upper tf st owner target next,
      state_below upper st ->
      R.try_dirty_read tf st owner target = Some next ->
      state_below upper next.
  Proof.
    intros upper tf st owner target next [Hsigma Haggregate Hlocal] Hread.
    constructor.
    - intros observed.
      destruct (V.eq_dec observed (R.handle_variable target))
        as [-> | Hneq].
      + pose proof Hread as Hread_original.
        unfold R.try_dirty_read in Hread.
        repeat
          match type of Hread with
          | context [if ?condition then _ else _] => destruct condition eqn:?
          | context [match ?subject with _ => _ end] => destruct subject eqn:?
          | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
          end;
          try discriminate; inversion Hread; subst; cbn in *.
        all: try apply Hsigma.
        all: try rewrite Total.Accounting.sigma_value_write_changed_same.
        all: apply Bool.andb_true_iff in Heqb1 as [Hdirect _].
        all: assert (Hcandidate : D.leq
          (D.join t (R.aggregate st (R.handle_variable target)))
          (upper (R.handle_variable target)) = true).
        all: try (apply DL.join_least;
          [eapply DL.leq_trans; [exact Hdirect |apply DL.bottom_least]
          |apply Haggregate]).
        * pose proof (@UBL.update_preserves_upper_bound false
            (R.handle_variable target)
            (R.stored_phase
              (R.promote_controlled
                (R.with_started st
                  (S.add (R.handle_variable target) (R.started st)))
                (R.handle_variable target))
              (R.handle_variable target))
            (R.sigma_value st (R.handle_variable target))
            (D.join t (R.aggregate st (R.handle_variable target)))
            (upper (R.handle_variable target))
            (Hsigma (R.handle_variable target)) Hcandidate) as Hupdated.
          exact Hupdated.
      + rewrite (@Total.Payment.sigma_value_try_dirty_read_other_payment
          tf st owner target next observed Hread Hneq).
        apply Hsigma.
    - intros observed. rewrite (@aggregate_try_dirty_read
        tf st owner target next observed Hread). apply Haggregate.
    - intros source observed value Hlookup.
      rewrite (@local_sides_try_dirty_read tf st owner target next Hread)
        in Hlookup.
      eapply Hlocal; exact Hlookup.
  Qed.

  Lemma state_below_dirty_get_ready :
    forall upper tf st owner target,
      state_below upper st ->
      state_below upper (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros upper tf st owner target Hbelow.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : state_below upper prepared).
    { subst prepared. unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        apply state_below_materialize;
        destruct Hbelow; constructor; assumption. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - pose proof (@state_below_try_dirty_read upper tf prepared owner target
        next Hprepared Hread) as Hnext.
      destruct Hnext. constructor; assumption.
    - destruct Hprepared. constructor; assumption.
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
    pose proof (@SUBL.update_preserves_upper_bound
      (R.handle_variable source) (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw)
      (R.aggregate st (R.handle_variable target))
      (upper (R.handle_variable target)) Hold Hinput) as Hupdated.
    unfold R.side_ready_state, R.record_side_payload.
    destruct (SU.update (R.handle_variable source)
      (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw)
      (R.aggregate st (R.handle_variable target)))
      as [phase next] eqn:Hupdate.
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
         now rewrite Total.C.local_sides_enqueue_all].
    destruct (U.update false owner (R.stored_phase st owner)
      (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
      as [phase value]. cbn.
    destruct (R.equivalent value (R.sigma_value st owner));
      [reflexivity |unfold R.write_changed_value; cbn;
         now rewrite Total.C.local_sides_enqueue_all].
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
    - intros target. rewrite aggregate_set_value.
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

  Lemma continuation_below_continue :
    forall support tf upper k,
      continuation_below support tf upper k ->
      control_below support tf upper (R.continue k).
  Proof. intros support tf upper k Hbelow. destruct k; exact Hbelow. Qed.

  Lemma state_below_request_spawn : forall upper st target,
    state_below upper st -> state_below upper (R.request_spawn st target).
  Proof.
    intros upper st target Hbelow. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); destruct Hbelow; constructor; assumption.
  Qed.

  Lemma config_below_request_spawn : forall support tf upper st owner target next k,
    state_below upper st ->
    rhs_below support tf upper (R.handle_variable owner) (R.ConstraintSystem.Spawn target next) ->
    continuation_below support tf upper k ->
    config_below support tf upper
      {| R.cfg_state := R.request_spawn st target; R.cfg_control := R.RunRhs owner next k |}.
  Proof.
    intros support tf upper st owner target next k Hstate Hrhs Hk. constructor.
    - now apply state_below_request_spawn.
    - split; [now apply rhs_below_spawn with (target := target)|exact Hk].
  Qed.

  Lemma config_below_loop_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st  after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunLoop |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunLoop |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunLoop |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st  after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    all: try match goal with
    | |- config_below _ _ _ {| R.cfg_state := R.with_spawns _ _ _; R.cfg_control := R.RunSeeds _ |} =>
      constructor; [destruct Hstate_below; constructor; assumption|exact I]
    end.
    - destruct (@Total.C.E.queue_pop_in
        (Sem.support finite) (R.queue st) h w
        (Total.C.E.state_queue_in Hstate_supported) Hcase)
        as [Howner _].
      constructor; [now apply state_below_with_queue |].
      cbn. now split.
  Qed.

  Lemma config_below_seeds_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st l after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds l |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds l |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunSeeds l |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st l after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - constructor; [exact Hstate_below |exact I].
    - assert (Hroot : In t (Sem.support finite)) by (apply Hcontrol_supported; now left).
      constructor.
      + destruct Hstate_below. constructor; assumption.
      + exact I.
    - assert (Hroot : In t (Sem.support finite)) by (apply Hcontrol_supported; now left).
      pose proof (@Total.C.observed_handle_variable st t s h Hcase2)
        as Hvariable.
      constructor.
      + exact (@state_below_observe upper st t s h
          Hstate_below Hcase2).
      + cbn. rewrite Hvariable. now split.
    - assert (Hroot : In t (Sem.support finite)) by (apply Hcontrol_supported; now left).
      constructor.
      + destruct Hstate_below. constructor; assumption.
      + exact I.
    - assert (Hroot : In t (Sem.support finite)) by (apply Hcontrol_supported; now left).
      pose proof (@Total.C.observed_handle_variable st t s h Hcase3)
        as Hvariable.
      constructor.
      + exact (@state_below_observe upper st t s h
          Hstate_below Hcase3).
      + cbn. rewrite Hvariable. now split.
  Qed.

  Lemma config_below_seed_loop_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st l after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop l |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop l |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop l |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st l after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - destruct (@Total.C.E.queue_pop_in
        (Sem.support finite) (R.queue st) h w
        (Total.C.E.state_queue_in Hstate_supported) Hcase)
        as [Howner _].
      constructor; [now apply state_below_with_queue |].
      cbn. now split.
    - constructor; [exact Hstate_below |exact I].
  Qed.

  Lemma config_below_solve_one_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOne h c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOne h c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunSolveOne h c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - destruct Hcontrol_below as [Howner Hk]. constructor.
      + apply state_below_with_started, state_below_start_evaluation.
        exact Hstate_below.
      + cbn. split.
        * apply initial_rhs_below; [exact Howner |].
          apply Sem.system_supported. exact Howner.
        * exact Hk.
  Qed.

  Lemma config_below_solve_loop_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop h c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop h c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop h c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - constructor; [now apply state_below_with_queue |exact Hcontrol_below].
    - destruct (@Total.C.E.queue_pop_in
        (Sem.support finite) (R.queue st) h0 w
        (Total.C.E.state_queue_in Hstate_supported) Hcase0)
        as [Hnext _].
      destruct Hcontrol_below as [Howner Hk].
      constructor; [now apply state_below_with_queue |].
      cbn. split; [exact Hnext |]. now split.
    - constructor; [exact Hstate_below |].
      apply continuation_below_continue. exact (proj2 Hcontrol_below).
  Qed.

  Lemma config_below_ret_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h t c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Ret t) c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Ret t) c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Ret t) c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h t c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - destruct Hcontrol_below as [Hrhs Hk]. constructor.
      + apply state_below_set_value; [exact Hstate_below |].
        eapply current_direct_below; eauto.
      + cbn. split.
        * eapply rhs_below_owner_in_support; exact Hrhs.
        * exact Hk.
  Qed.

  Lemma config_below_after_get_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h h0 r c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.AfterGet h h0 r c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.AfterGet h h0 r c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.AfterGet h h0 r c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h h0 r c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - destruct Hcontrol_below as [Hrhs Hk].
      assert (Hready : state_below upper (R.get_ready_state st h h0))
        by (now apply state_below_get_ready).
      constructor; [exact Hready |]. cbn. split.
      + eapply rhs_below_get with (target := R.handle_variable h0);
          [exact Hrhs |].
        exact (state_sigma_below Hready (R.handle_variable h0)).
      + exact Hk.
  Qed.

  Lemma config_below_after_side_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h r c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.AfterSide h r c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.AfterSide h r c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.AfterSide h r c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h r c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - constructor; [exact Hstate_below |exact Hcontrol_below].
  Qed.

  Lemma config_below_after_spawn_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h r c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.AfterSpawn h r c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.AfterSpawn h r c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.AfterSpawn h r c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h r c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol_supported, Hcontrol_below |- *.
    - constructor; [exact Hstate_below |exact Hcontrol_below].
  Qed.

  Lemma config_below_get_value : forall support tf upper st owner target next k value,
    state_below upper st ->
    rhs_below support tf upper (R.handle_variable owner) (R.ConstraintSystem.Get target next) ->
    continuation_below support tf upper k ->
    D.leq value (upper target) = true ->
    config_below support tf upper
      {| R.cfg_state := st; R.cfg_control := R.RunRhs owner (next value) k |}.
  Proof.
    intros support tf upper st owner target next k value Hstate Hrhs Hk Hvalue.
    constructor; [exact Hstate|]. cbn. split; [eapply rhs_below_get; eauto|exact Hk].
  Qed.

  Lemma config_below_get_child : forall support tf upper st observed owner target handle next k,
    state_below upper st -> R.observe st target = (observed, handle) ->
    rhs_below support tf upper (R.handle_variable owner) (R.ConstraintSystem.Get target next) ->
    continuation_below support tf upper k ->
    config_below support tf upper
      {| R.cfg_state := observed;
         R.cfg_control := R.RunSolveOne handle (R.KAfterGet owner handle next k) |}.
  Proof.
    intros support tf upper st observed owner target handle next k Hstate Hobserve Hrhs Hk.
    pose proof (@Total.C.observed_handle_variable st target observed handle Hobserve) as Hvariable.
    constructor; [eapply state_below_observe; eauto|]. cbn. rewrite Hvariable.
    split; [eapply rhs_below_get_target_in_support; eauto|now split].
  Qed.

  Lemma config_below_get_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h t r c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Get t r) c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Get t r) c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Get t r) c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h t r c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    cbn in Hcontrol_below. destruct Hcontrol_below as [Hrhs Hk].
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end; try discriminate; inversion Hstep; subst; clear Hstep.
    all: try solve [eapply config_below_get_child; eauto].
    - eapply config_below_get_value; [|exact Hrhs|exact Hk|apply DL.bottom_least].
      destruct Hstate_below. constructor; assumption.
    - assert (Hready : state_below upper (R.dirty_get_ready_state tf s h h0)).
      { apply state_below_dirty_get_ready. eapply state_below_observe; eauto. }
      eapply config_below_get_value;
        [exact Hready|exact Hrhs|exact Hk|exact (state_sigma_below Hready t)].
    - assert (Hready : state_below upper (R.get_ready_state (R.enqueue_handle s h0) h h0)).
      { apply state_below_get_ready, state_below_enqueue_handle.
        eapply state_below_observe; eauto. }
      eapply config_below_get_value;
        [exact Hready|exact Hrhs|exact Hk|exact (state_sigma_below Hready t)].
    - eapply config_below_get_value; [|exact Hrhs|exact Hk|apply DL.bottom_least].
      destruct Hstate_below. constructor; assumption.
    - assert (Hready : state_below upper (R.get_ready_state (R.enqueue_handle s h0) h h0)).
      { apply state_below_get_ready, state_below_enqueue_handle.
        eapply state_below_observe; eauto. }
      eapply config_below_get_value;
        [exact Hready|exact Hrhs|exact Hk|exact (state_sigma_below Hready t)].
  Qed.

  Lemma config_below_side_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h t t0 r0 c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Side t t0 r0) c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Side t t0 r0) c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Side t t0 r0) c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h t t0 r0 c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    cbn in Hcontrol_below. destruct Hcontrol_below as [Hrhs Hk].
    assert (Hraw : D.leq t0 (upper t) = true)
      by (eapply current_side_below; eauto).
    pose proof (rhs_below_side Hrhs) as Hnext.
    pose proof (rhs_below_side_target_in_support Hrhs) as Htarget.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end; try discriminate; inversion Hstep; subst; clear Hstep.
    all: pose proof (@Total.C.observed_handle_variable st t s h0 ltac:(assumption))
      as Hvariable.
    all: assert (Hobserved : state_below upper s)
      by (eapply state_below_observe; eauto).
    all: assert (Hready : state_below upper (R.side_ready_state s h h0 t0))
      by (apply state_below_side_ready; [exact Hobserved|now rewrite Hvariable]).
    - constructor; [exact Hready|]. cbn. rewrite Hvariable. repeat split; assumption.
    - constructor; [now apply state_below_enqueue_handle|]. cbn. now split.
    - constructor; [now apply state_below_mark_side_dirty|].
      cbn. rewrite Hvariable. repeat split; assumption.
    - constructor.
      + now apply state_below_enqueue_handle, state_below_mark_side_dirty.
      + cbn. now split.
    - constructor; [exact Hready|]. cbn. now split.
  Qed.

  Lemma config_below_spawn_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper st h t r0 c after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Spawn t r0) c |} ->
      config_below (Sem.support finite) tf upper
        {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Spawn t r0) c |} ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Spawn t r0) c |} after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper st h t r0 c after Hmonotone Hpost
      [Hstate_supported Hcontrol_supported] [Hstate_below Hcontrol_below] Hstep.
    cbn in Hcontrol_below. destruct Hcontrol_below as [Hrhs Hk].
    pose proof (rhs_below_spawn Hrhs) as Hnext.
    pose proof (rhs_below_spawn_target_in_support Hrhs) as Htarget.
    unfold Sem.step in Hstep. cbn in Hstep.
    repeat match type of Hstep with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
    | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
    end; try discriminate; inversion Hstep; subst; clear Hstep.
    all: try solve [eapply config_below_request_spawn; eauto].
    - constructor; [exact Hstate_below|]. cbn. now split.
    - constructor; [eapply state_below_observe; eauto|]. cbn. now split.
    - pose proof (@Total.C.observed_handle_variable st t s h0 ltac:(assumption))
        as Hvariable.
      constructor; [eapply state_below_observe; eauto|].
      cbn. rewrite Hvariable. repeat split; assumption.
    - constructor.
      + apply state_below_materialize, state_below_enqueue_handle.
        eapply state_below_observe; eauto.
      + cbn. now split.
    - constructor; [destruct Hstate_below; constructor; assumption|]. cbn. now split.
    - pose proof (@Total.C.observed_handle_variable st t s h0 ltac:(assumption))
        as Hvariable.
      constructor; [eapply state_below_observe; eauto|].
      cbn. rewrite Hvariable. repeat split; assumption.
    - constructor.
      + apply state_below_materialize, state_below_enqueue_handle.
        eapply state_below_observe; eauto.
      + cbn. now split.
  Qed.

  Theorem config_below_step :
    forall tf roots (finite : Sem.finite_system tf roots) upper before after,
      system_monotone_on tf (Sem.support finite) ->
      post_solution_on tf (Sem.support finite) upper ->
      Total.C.E.config_in (Sem.support finite) before ->
      config_below (Sem.support finite) tf upper before ->
      Sem.step tf before after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper [st control] after Hmonotone Hpost
      Hsupported Hbelow Hstep.
    destruct control.
    - eapply config_below_loop_step; eauto.
    - eapply config_below_seeds_step; eauto.
    - eapply config_below_seed_loop_step; eauto.
    - eapply config_below_solve_one_step; eauto.
    - eapply config_below_solve_loop_step; eauto.
    - destruct r.
      + eapply config_below_ret_step; eauto.
      + eapply config_below_get_step; eauto.
      + eapply config_below_side_step; eauto.
      + eapply config_below_spawn_step; eauto.
    - eapply config_below_after_get_step; eauto.
    - eapply config_below_after_side_step; eauto.
    - eapply config_below_after_spawn_step; eauto.
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
      Total.C.E.config_in (Sem.support finite) before ->
      config_below (Sem.support finite) tf upper before ->
      Sem.steps tf before after ->
      config_below (Sem.support finite) tf upper after.
  Proof.
    intros tf roots finite upper before after Hmonotone Hpost
      Hsupported Hbelow Hsteps.
    induction Hsteps.
    - exact Hbelow.
    - apply IHHsteps.
      + eapply Total.C.E.next_config_in; [apply Sem.system_supported|exact Hsupported|exact H].
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
    - split; [apply Total.C.E.empty_state_in|exact (Sem.initial_supported finite)].
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
    pose proof (@Total.C.E.successful_run_terminates_to
      fuel tf roots final Hsolve) as [Hsteps Hquiet].
    pose proof (@reachable_config_below tf roots finite upper
      (Sem.terminal_config final) Hmonotone Hpost Hsteps) as Hbelow.
    exact (state_sigma_below (config_state_below Hbelow)).
  Qed.

  Module Strict := SourceStrictness.Make V D DL.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at
      Sem.observed_direct Sem.observed_sides.

  Lemma lookup_value_agrees : forall st target value,
    R.semantic_lookup st target = Some value ->
    value = R.sigma_value st target.
  Proof.
    intros st target value Hlookup.
    unfold R.semantic_lookup, R.sigma_value in *.
    destruct (M.lookup (R.sigma st) target); [now inversion Hlookup |].
    destruct (S.mem target (R.dormant_bottom st)); now inversion Hlookup.
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
    destruct (R.semantic_lookup st x) eqn:Hlookup.
    - left. now exists t.
    - right. intros [value Hvalue]. discriminate.
  Defined.

  Lemma unsolved_value_bottom : forall st x,
    ~ Sem.solved st x -> D.leq (R.sigma_value st x) D.bottom = true.
  Proof.
    intros st x Hunsolved. unfold R.sigma_value.
    destruct (M.lookup (R.sigma st) x) eqn:Hlookup.
    - exfalso. apply Hunsolved. exists t. unfold R.semantic_lookup. now rewrite Hlookup.
    - apply DL.leq_refl.
  Qed.

  Lemma terminal_materialized_eval : forall tf roots final owner,
    Sem.terminates_to tf roots final -> Total.C.Progress.solved final owner ->
    exists direct reads effects, Sem.rhs_eval final (tf owner) direct reads effects.
  Proof.
    intros tf roots final owner [Hsteps Hquiet] Hsolved.
    pose proof (@Total.C.history_invariant_steps (fun _ => True) tf (R.initial_config roots)
      (Sem.terminal_config final) (Total.C.initial_history_invariant (fun _ => True) tf roots) Hsteps
      (@Total.C.numerical_spawned_path tf (R.initial_config roots) (Sem.terminal_config final))) as Hi.
    destruct (Total.C.history_summaries Hi Hsolved) as [Hqueued|[Hactive|Hsummary]].
    - exfalso. eapply Total.C.quiescent_not_queued; eauto.
    - contradiction.
    - destruct Hsummary as [direct [reads [effects [Htrace [Hreads _]]]]].
      exists direct, reads, effects. eapply Total.C.guarded_trace_evaluates;
        [exact Htrace|exact Hreads|]. now apply Total.C.quiescent_not_queued.
  Qed.

  Lemma terminal_dormant_sound : forall tf roots final,
    Sem.terminates_to tf roots final -> Total.C.dormant_sound tf final.
  Proof.
    intros tf roots final [Hsteps Hquiet].
    destruct (Total.C.E.steps_have_exact_fuel Hsteps) as [fuel Hfuel].
    pose proof (@Total.C.reachable_dormant_sound fuel tf roots) as Hsound.
    now rewrite Hfuel in Hsound.
  Qed.

  Lemma terminal_solved_observation_post :
    forall tf roots final owner result,
      Sem.terminates_to tf roots final -> Sem.solved final owner ->
      observes_at (R.sigma_value final) (tf owner) result ->
      D.leq (observed_direct result) (R.sigma_value final owner) = true /\
      Sem.valuation_side_effects_below (R.sigma_value final) (observed_sides result).
  Proof.
    intros tf roots final owner result Hterm Hsolved Hobs.
    destruct (M.lookup (R.sigma final) owner) as [stored|] eqn:Hsigma.
    - assert (Hmaterialized : Total.C.Progress.solved final owner) by (now exists stored).
      destruct (@terminal_materialized_eval tf roots final owner Hterm Hmaterialized)
        as [direct [reads [effects Heval]]].
      destruct (rhs_eval_observation_agrees Heval Hobs) as [<- [_ <-]].
      exact (@Total.C.terminal_materialized_post_solution tf roots final owner
        Hterm Hmaterialized direct reads effects Heval).
    - destruct Hsolved as [value Hlookup].
      unfold R.semantic_lookup in Hlookup. rewrite Hsigma in Hlookup.
      destruct (S.mem owner (R.dormant_bottom final)) eqn:Hmem; try discriminate.
      pose proof (@terminal_dormant_sound tf roots final Hterm owner Hmem) as Hbottom.
      unfold R.pure_bottom_rhs in Hbottom.
      destruct (tf owner); try discriminate.
      unfold R.equivalent in Hbottom. apply Bool.andb_true_iff in Hbottom as [Hbelow _].
      destruct Hobs as [Hobs Hreads]. inversion Hobs; subst; cbn. split.
      + unfold R.sigma_value. now rewrite Hsigma.
      + intros target raw Hin. contradiction.
  Qed.

  (** Source strictness closes the unsolved part of the finite system. *)
  Theorem successful_source_strict_solution :
    forall fuel tf roots (finite : Sem.finite_system tf roots) final,
      source_strict_on tf (Sem.support finite) roots ->
      R.solve_fuel fuel tf roots = Some final ->
      post_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros fuel tf roots finite final Hstrict Hrun.
    pose proof (@Total.C.E.successful_run_terminates_to
      fuel tf roots final Hrun) as Hterm.
    apply Sem.post_solution_on_intro; [apply Sem.finite_spawn_closed|].
    eapply (@Strict.bottom_completion_is_value_post_solution _ _ Sem.observes_at
      Sem.observed_direct Sem.observed_sides tf (Sem.support finite) roots
      (R.sigma_value final) (Sem.solved final)).
    - apply solved_dec.
    - exact Hstrict.
    - intros x Hin. eapply Total.C.E.successful_run_roots_solved; eauto.
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
    destruct (@Total.total_correct tf roots finite) as [fuel [final [Hrun [Hcorrect Hquiet]]]].
    exists fuel, final. split; [exact Hrun |]. split.
    - exact Hcorrect.
    - split.
      + eapply successful_source_strict_solution; eauto.
      + intros upper Hpost x Hsolved.
        exact (@successful_run_below fuel tf roots finite final upper
          Hmono Hpost Hrun x).
  Qed.

  End LeastSolution.
End Make.
