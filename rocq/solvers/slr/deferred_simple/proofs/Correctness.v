From TcSolvers Require Export common.SolverContracts solvers.slr.deferred_simple.proofs.Execution.
Import ListNotations.
Set Implicit Arguments.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : DeferredSimple.FEATURES) (SL : SET_LAWS V S) (ML : MAP_LAWS V M)
  (DL : DOMAIN_LAWS D) (OUL : ORDINARY_UPDATE_SOUND_LAWS V D U)
  (SUL : SIDE_UPDATE_SOUND_LAWS V D SU)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk).
  Module E := Execution.Make V D U SU S M Rk Features SL ML.
  Module Sem := E.Sem.
  Module R := E.R.
  Module Solver := Sem.Solver.
  Module Spec := SolverContracts.ForSolver V D Solver.

  (** Scheduling may change ranks and reader obligations, but not values. *)
  Definition value_view (before after : R.state) : Prop :=
    R.sigma after = R.sigma before /\ R.contributions after = R.contributions before.

  Lemma enqueue_view : forall st target, value_view st (R.enqueue st target).
  Proof.
    intros. unfold R.enqueue, R.observe. destruct (R.Ranking.observe _ _).
    split; reflexivity.
  Qed.

  Lemma enqueue_all_view : forall xs st, value_view st (R.enqueue_all st xs).
  Proof.
    induction xs; intros st; cbn; [split; reflexivity|].
    destruct (IHxs (R.enqueue st a)) as [Hs Hc].
    destruct (enqueue_view st a) as [Hs' Hc']. split; congruence.
  Qed.

  Lemma write_changed_value_sigma : forall st owner value,
    R.sigma (R.write_changed_value st owner value) = M.update (R.sigma st) owner value.
  Proof.
    intros. unfold R.write_changed_value. cbn [R.with_readers].
    exact (proj1 (enqueue_all_view _ _)).
  Qed.

  Lemma write_changed_value_contributions : forall st owner value,
    R.contributions (R.write_changed_value st owner value) = R.contributions st.
  Proof.
    intros. unfold R.write_changed_value. cbn [R.with_readers].
    exact (proj2 (enqueue_all_view _ _)).
  Qed.

  Lemma write_changed_value_same : forall st owner value,
    R.sigma_value (R.write_changed_value st owner value) owner = value.
  Proof.
    intros. unfold R.sigma_value. rewrite write_changed_value_sigma, ML.lookup_update_same.
    reflexivity.
  Qed.

  Lemma write_changed_value_other : forall st owner value x,
    x <> owner -> R.sigma_value (R.write_changed_value st owner value) x = R.sigma_value st x.
  Proof.
    intros. unfold R.sigma_value. rewrite write_changed_value_sigma, ML.lookup_update_other by assumption.
    reflexivity.
  Qed.

  Lemma set_value_contributions : forall st owner direct,
    R.contributions (R.set_value st owner direct) = R.contributions st.
  Proof.
    intros. unfold R.set_value.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      try rewrite write_changed_value_contributions; reflexivity.
  Qed.

  Lemma set_value_other : forall st owner direct x,
    x <> owner -> R.sigma_value (R.set_value st owner direct) x = R.sigma_value st x.
  Proof.
    intros. unfold R.set_value.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      try rewrite write_changed_value_other by assumption; reflexivity.
  Qed.

  Lemma set_value_covers_candidate : forall st owner direct,
    D.leq (D.join direct (R.aggregate st owner))
      (R.sigma_value (R.set_value st owner direct) owner) = true.
  Proof.
    intros st owner direct. unfold R.set_value.
    destruct (R.equivalent (D.join direct (R.aggregate st owner)) (R.sigma_value st owner)) eqn:Hsame.
    - now apply Bool.andb_true_iff in Hsame as [Hsame _].
    - destruct (S.mem owner (R.controlled st)).
      + destruct (R.equivalent
          (snd (U.update false owner (R.stored_phase st owner) (R.sigma_value st owner)
            (D.join direct (R.aggregate st owner)))) (R.sigma_value st owner)) eqn:Hupdated.
        * apply Bool.andb_true_iff in Hupdated as [Hupdated _].
          eapply DL.leq_trans; [apply OUL.update_sound|exact Hupdated].
        * rewrite write_changed_value_same. apply OUL.update_sound.
      + rewrite write_changed_value_same. apply DL.leq_refl.
  Qed.

  Definition aggregate_bounded st owner :=
    D.leq (R.aggregate st owner) (R.sigma_value st owner) = true.

  Lemma set_value_covers_direct : forall st owner direct,
    D.leq direct (R.sigma_value (R.set_value st owner direct) owner) = true.
  Proof.
    intros. eapply DL.leq_trans; [apply DL.join_upper_left|apply set_value_covers_candidate].
  Qed.

  Lemma set_value_aggregate_bounded : forall st owner direct,
    aggregate_bounded (R.set_value st owner direct) owner.
  Proof.
    intros. unfold aggregate_bounded, R.aggregate. rewrite set_value_contributions.
    eapply DL.leq_trans; [apply DL.join_upper_right|apply set_value_covers_candidate].
  Qed.

  Lemma set_value_preserves_aggregate_bound : forall st owner direct x,
    aggregate_bounded st x -> aggregate_bounded (R.set_value st owner direct) x.
  Proof.
    intros st owner direct x Hbound. destruct (V.eq_dec x owner) as [->|Hneq].
    - apply set_value_aggregate_bounded.
    - unfold aggregate_bounded, R.aggregate in *. rewrite set_value_contributions.
      now rewrite set_value_other.
  Qed.

  Lemma join_values_upper : forall values value,
    In value values -> D.leq value (R.join_values values) = true.
  Proof.
    induction values as [|head rest IH]; intros value Hin; [contradiction|].
    destruct Hin as [<-|Hin]; cbn; [apply DL.join_upper_left|].
    eapply DL.leq_trans; [now apply IH|apply DL.join_upper_right].
  Qed.

  Lemma stored_contribution_below_aggregate : forall st source target,
    D.leq (R.stored_contribution st source target) (R.aggregate st target) = true.
  Proof.
    intros. unfold R.stored_contribution, R.aggregate.
    destruct (M.lookup _ source) eqn:Hlookup; [|apply DL.bottom_least].
    apply join_values_upper. eapply ML.lookup_values; exact Hlookup.
  Qed.

  Lemma accumulated_side_covers_raw : forall st source target raw,
    D.leq raw (R.accumulated_side_input st source target raw) = true.
  Proof.
    intros. unfold R.accumulated_side_input. destruct (M.lookup _ _);
      [apply DL.join_upper_right|apply DL.leq_refl].
  Qed.

  Lemma record_side_payload_cell : forall st source target raw,
    R.stored_contribution (R.record_side_payload st source target raw) source target =
    snd (SU.update source target (R.stored_side_phase st source target)
      (R.stored_contribution st source target)
      (R.accumulated_side_input st source target raw) (R.aggregate st target)).
  Proof.
    intros. unfold R.record_side_payload, R.stored_contribution, R.update_map; cbn.
    unfold R.lookup_map. rewrite !ML.lookup_update_same. reflexivity.
  Qed.

  Lemma record_side_payload_covers_raw : forall st source target raw,
    D.leq raw (R.aggregate (R.record_side_payload st source target raw) target) = true.
  Proof.
    intros. eapply DL.leq_trans; [apply accumulated_side_covers_raw|].
    eapply DL.leq_trans; [apply SUL.update_sound|].
    rewrite <- record_side_payload_cell. apply stored_contribution_below_aggregate.
  Qed.

  Lemma materialize_value : forall st target x,
    R.sigma_value (R.materialize st target) x = R.sigma_value st x.
  Proof.
    intros st target x. unfold R.materialize, R.is_materialized.
    destruct (M.lookup (R.sigma st) target) eqn:Hlookup; [reflexivity|].
    unfold R.sigma_value; cbn. destruct (V.eq_dec x target) as [->|Hneq].
    - now rewrite ML.lookup_update_same, Hlookup.
    - now rewrite ML.lookup_update_other.
  Qed.

  Lemma materialize_aggregate : forall st target x,
    R.aggregate (R.materialize st target) x = R.aggregate st x.
  Proof.
    intros. unfold R.materialize. destruct (R.is_materialized st target); reflexivity.
  Qed.

  Lemma get_ready_state_value : forall st owner target x,
    R.sigma_value (R.get_ready_state st owner target) x = R.sigma_value st x.
  Proof.
    intros. unfold R.get_ready_state. rewrite materialize_value.
    destruct (Nat.ltb _ _); reflexivity.
  Qed.

  Lemma get_ready_state_aggregate : forall st owner target x,
    R.aggregate (R.get_ready_state st owner target) x = R.aggregate st x.
  Proof.
    intros. unfold R.get_ready_state. rewrite materialize_aggregate.
    destruct (Nat.ltb _ _); reflexivity.
  Qed.

  Lemma try_dirty_read_contributions : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next -> R.contributions next = R.contributions st.
  Proof.
    intros tf st owner target next H. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?b with _ => _ end] => destruct b eqn:?
    end; try discriminate; inversion H; subst;
      try rewrite write_changed_value_contributions; reflexivity.
  Qed.

  Lemma try_dirty_read_other : forall tf st owner target next x,
    R.try_dirty_read tf st owner target = Some next -> x <> R.handle_variable target ->
    R.sigma_value next x = R.sigma_value st x.
  Proof.
    intros tf st owner target next x H Hneq. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?b with _ => _ end] => destruct b eqn:?
    end; try discriminate; inversion H; subst;
      try rewrite write_changed_value_other by exact Hneq; reflexivity.
  Qed.

  Lemma try_dirty_read_candidate : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next ->
    exists direct, tf (R.handle_variable target) = R.ConstraintSystem.Ret direct /\
      D.leq (D.join direct (R.aggregate st (R.handle_variable target)))
        (R.sigma_value next (R.handle_variable target)) = true.
  Proof.
    intros tf st owner target next H. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?b with _ => _ end] => destruct b eqn:?
    end; try discriminate; inversion H; subst.
    all: eexists; split; [reflexivity|].
    all: try rewrite write_changed_value_same; cbn [R.sigma_value R.with_phases R.with_started
      R.promote_controlled R.with_controlled R.cancel_dirty_target R.clear_side_dirty
      R.with_queue R.with_dirty_side_targets].
    all: try apply OUL.update_sound; try apply DL.leq_refl.
    all: repeat match goal with
    | Heq : R.equivalent ?left ?right = true |- _ =>
      apply Bool.andb_true_iff in Heq as [Heq _]
    end.
    all: eauto using DL.leq_trans, OUL.update_sound.
  Qed.

  Lemma try_dirty_read_aggregate_bounded : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next -> aggregate_bounded next (R.handle_variable target).
  Proof.
    intros tf st owner target next H.
    destruct (@try_dirty_read_candidate tf st owner target next H) as [direct [Htf Hbound]].
    unfold aggregate_bounded, R.aggregate. rewrite (@try_dirty_read_contributions tf st owner target next H).
    eapply DL.leq_trans; [apply DL.join_upper_right|exact Hbound].
  Qed.

  Lemma try_dirty_read_preserves_aggregate_bound : forall tf st owner target next x,
    R.try_dirty_read tf st owner target = Some next ->
    aggregate_bounded st x -> aggregate_bounded next x.
  Proof.
    intros tf st owner target next x H Hbound.
    destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
    - now apply try_dirty_read_aggregate_bounded in H.
    - unfold aggregate_bounded, R.aggregate in *. rewrite (@try_dirty_read_contributions tf st owner target next H).
      now rewrite (@try_dirty_read_other tf st owner target next x H Hneq).
  Qed.

  Lemma dirty_get_ready_state_preserves_aggregate_bound : forall tf st owner target x,
    aggregate_bounded st x -> aggregate_bounded (R.dirty_get_ready_state tf st owner target) x.
  Proof.
    intros tf st owner target x Hbound. unfold R.dirty_get_ready_state.
    assert (Hprepared : aggregate_bounded
      (R.materialize (R.get_control_state st owner target) (R.handle_variable target)) x).
    { unfold aggregate_bounded. rewrite materialize_value, materialize_aggregate.
      unfold R.get_control_state. destruct (Nat.ltb _ _); exact Hbound. }
    destruct (R.try_dirty_read _ _ _ _) as [next|] eqn:Hread.
    - change (aggregate_bounded next x).
      eapply try_dirty_read_preserves_aggregate_bound; eauto.
    - exact Hprepared.
  Qed.

  Lemma record_side_payload_sigma : forall st source target raw,
    R.sigma (R.record_side_payload st source target raw) = R.sigma st.
  Proof. reflexivity. Qed.

  Lemma record_side_payload_other : forall st source target raw x,
    x <> target -> R.aggregate (R.record_side_payload st source target raw) x = R.aggregate st x.
  Proof.
    intros st source target raw x Hneq. unfold R.record_side_payload, R.aggregate; cbn.
    unfold R.update_map, R.lookup_map. now rewrite ML.lookup_update_other.
  Qed.

  Lemma record_side_payload_covers_accumulated : forall st source target raw,
    D.leq (R.accumulated_side_input st source target raw)
      (R.aggregate (R.record_side_payload st source target raw) target) = true.
  Proof.
    intros. eapply DL.leq_trans; [apply SUL.update_sound|].
    rewrite <- record_side_payload_cell. apply stored_contribution_below_aggregate.
  Qed.

  Lemma side_ready_state_covers_raw : forall st source target raw,
    D.leq raw (R.aggregate (R.side_ready_state st source target raw) (R.handle_variable target)) = true.
  Proof.
    intros. unfold R.side_ready_state. destruct (Nat.ltb _ _); apply record_side_payload_covers_raw.
  Qed.

  Lemma side_ready_state_other : forall st source target raw x,
    x <> R.handle_variable target ->
    aggregate_bounded st x -> aggregate_bounded (R.side_ready_state st source target raw) x.
  Proof.
    intros st source target raw x Hneq Hbound. unfold R.side_ready_state.
    destruct (Nat.ltb _ _); unfold aggregate_bounded;
      change (D.leq (R.aggregate (R.record_side_payload st (R.handle_variable source)
        (R.handle_variable target) raw) x) (R.sigma_value st x) = true);
      now rewrite record_side_payload_other.
  Qed.

  Lemma side_ready_state_not_grown : forall st source target raw,
    R.aggregate_grew st (R.side_ready_state st source target raw) (R.handle_variable target) = false ->
    aggregate_bounded st (R.handle_variable target) ->
    aggregate_bounded (R.side_ready_state st source target raw) (R.handle_variable target).
  Proof.
    intros st source target raw Hgrow Hbound.
    unfold R.aggregate_grew in Hgrow. apply Bool.negb_false_iff in Hgrow.
    unfold aggregate_bounded in *. eapply DL.leq_trans; [exact Hgrow|].
    unfold R.side_ready_state. destruct (Nat.ltb _ _); exact Hbound.
  Qed.
  Create HintDb dormant.
  Lemma with_sigma_dormant : forall st next,
    R.dormant_bottom (R.with_sigma st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_sigma_dormant : dormant.

  Lemma with_ranking_dormant : forall st next,
    R.dormant_bottom (R.with_ranking st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_ranking_dormant : dormant.

  Lemma with_queue_dormant : forall st next,
    R.dormant_bottom (R.with_queue st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_queue_dormant : dormant.

  Lemma with_started_dormant : forall st next,
    R.dormant_bottom (R.with_started st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_started_dormant : dormant.

  Lemma with_readers_dormant : forall st next,
    R.dormant_bottom (R.with_readers st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_readers_dormant : dormant.

  Lemma with_contributions_dormant : forall st next,
    R.dormant_bottom (R.with_contributions st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_contributions_dormant : dormant.

  Lemma with_phases_dormant : forall st next,
    R.dormant_bottom (R.with_phases st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_phases_dormant : dormant.

  Lemma with_side_phases_dormant : forall st next,
    R.dormant_bottom (R.with_side_phases st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_side_phases_dormant : dormant.

  Lemma with_local_sides_dormant : forall st next,
    R.dormant_bottom (R.with_local_sides st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_local_sides_dormant : dormant.


  Lemma with_controlled_dormant : forall st next,
    R.dormant_bottom (R.with_controlled st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_controlled_dormant : dormant.

  Lemma with_dirty_side_targets_dormant : forall st next,
    R.dormant_bottom (R.with_dirty_side_targets st next) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_dirty_side_targets_dormant : dormant.


  Lemma enqueue_handle_dormant : forall st entry,
    R.dormant_bottom (R.enqueue_handle st entry) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite enqueue_handle_dormant : dormant.

  Lemma mark_side_dirty_dormant : forall st target,
    R.dormant_bottom (R.mark_side_dirty st target) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite mark_side_dirty_dormant : dormant.

  Lemma clear_side_dirty_dormant : forall st target,
    R.dormant_bottom (R.clear_side_dirty st target) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite clear_side_dirty_dormant : dormant.

  Lemma cancel_dirty_target_dormant : forall st target,
    R.dormant_bottom (R.cancel_dirty_target st target) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite cancel_dirty_target_dormant : dormant.

  Lemma promote_controlled_dormant : forall st x,
    R.dormant_bottom (R.promote_controlled st x) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite promote_controlled_dormant : dormant.

  Lemma add_reader_dormant : forall st target owner,
    R.dormant_bottom (R.add_reader st target owner) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite add_reader_dormant : dormant.

  Lemma reset_local_sides_dormant : forall st owner,
    R.dormant_bottom (R.reset_local_sides st owner) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite reset_local_sides_dormant : dormant.

  Lemma observe_dormant : forall st target next entry,
    R.observe st target = (next, entry) -> R.dormant_bottom next = R.dormant_bottom st.
  Proof.
    intros st target next entry H. unfold R.observe in H.
    destruct (R.Ranking.observe (R.ranking st) target).
    inversion H; reflexivity.
  Qed.

  Lemma enqueue_dormant : forall st target,
    R.dormant_bottom (R.enqueue st target) = R.dormant_bottom st.
  Proof.
    intros. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) target); reflexivity.
  Qed.
  #[local] Hint Rewrite enqueue_dormant : dormant.

  Lemma enqueue_all_dormant : forall xs st,
    R.dormant_bottom (R.enqueue_all st xs) = R.dormant_bottom st.
  Proof.
    induction xs; intros st; cbn; [reflexivity|].
    rewrite IHxs. apply enqueue_dormant.
  Qed.
  #[local] Hint Rewrite enqueue_all_dormant : dormant.

  Lemma materialize_dormant : forall st x,
    R.dormant_bottom (R.materialize st x) = R.dormant_bottom st.
  Proof.
    intros. unfold R.materialize.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite materialize_dormant : dormant.

  Lemma get_control_state_dormant : forall st owner target,
    R.dormant_bottom (R.get_control_state st owner target) = R.dormant_bottom st.
  Proof.
    intros. unfold R.get_control_state.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite get_control_state_dormant : dormant.

  Lemma get_ready_state_dormant : forall st owner target,
    R.dormant_bottom (R.get_ready_state st owner target) = R.dormant_bottom st.
  Proof.
    intros. unfold R.get_ready_state.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite get_ready_state_dormant : dormant.

  Lemma start_evaluation_dormant : forall st owner,
    R.dormant_bottom (R.start_evaluation st owner) = R.dormant_bottom st.
  Proof.
    intros. unfold R.start_evaluation.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite start_evaluation_dormant : dormant.

  Lemma record_side_payload_dormant : forall st owner target raw,
    R.dormant_bottom (R.record_side_payload st owner target raw) = R.dormant_bottom st.
  Proof.
    intros. unfold R.record_side_payload.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite record_side_payload_dormant : dormant.

  Lemma side_ready_state_dormant : forall st owner target raw,
    R.dormant_bottom (R.side_ready_state st owner target raw) = R.dormant_bottom st.
  Proof.
    intros. unfold R.side_ready_state.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite side_ready_state_dormant : dormant.

  Lemma write_changed_value_dormant : forall st owner value,
    R.dormant_bottom (R.write_changed_value st owner value) = R.dormant_bottom st.
  Proof.
    intros. unfold R.write_changed_value.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite write_changed_value_dormant : dormant.

  Lemma set_value_dormant : forall st owner direct,
    R.dormant_bottom (R.set_value st owner direct) = R.dormant_bottom st.
  Proof.
    intros. unfold R.set_value.
    autorewrite with dormant.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with dormant; reflexivity.
  Qed.
  #[local] Hint Rewrite set_value_dormant : dormant.

  Lemma try_dirty_read_dormant : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next -> R.dormant_bottom next = R.dormant_bottom st.
  Proof.
    intros tf st owner target next H. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end; try discriminate; inversion H; subst;
      autorewrite with dormant; reflexivity.
  Qed.

  Lemma dirty_get_ready_state_dormant : forall tf st owner target,
    R.dormant_bottom (R.dirty_get_ready_state tf st owner target) = R.dormant_bottom st.
  Proof.
    intros. unfold R.dirty_get_ready_state. autorewrite with dormant.
    destruct (R.try_dirty_read tf _ _ _) eqn:H.
    - rewrite (@try_dirty_read_dormant _ _ _ _ _ H). now autorewrite with dormant.
    - now autorewrite with dormant.
  Qed.
  #[local] Hint Rewrite dirty_get_ready_state_dormant : dormant.

  Lemma with_spawns_dormant : forall st pending requested,
    R.dormant_bottom (R.with_spawns st pending requested) = R.dormant_bottom st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_spawns_dormant : dormant.

  Lemma request_spawn_dormant : forall st target,
    R.dormant_bottom (R.request_spawn st target) = R.dormant_bottom st.
  Proof.
    intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); reflexivity.
  Qed.
  #[local] Hint Rewrite request_spawn_dormant : dormant.

  Lemma next_config_dormant_cases : forall tf before after,
    R.next_config tf before = Some after ->
    R.dormant_bottom (R.cfg_state after) = R.dormant_bottom (R.cfg_state before) \/
    exists target, R.pure_bottom_rhs tf target = true /\
      R.dormant_bottom (R.cfg_state after) = S.add target (R.dormant_bottom (R.cfg_state before)).
  Proof.
    intros tf [st control] after H.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control] in H |- *;
      repeat match type of H with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion H; subst; cbn [R.cfg_state];
      try (left; autorewrite with dormant; reflexivity).
    all: try match goal with
    | Hp : (R.pure_bottom_rhs ?system ?target && _)%bool = true |- _ =>
      right; exists target; split; [now apply Bool.andb_true_iff in Hp as [Hp _]|reflexivity]
    end.
    all: left; autorewrite with dormant.
    all: match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      now rewrite (@observe_dormant base target next entry Hobs)
    end.
  Qed.

  Definition dormant_sound tf st := forall owner,
    S.mem owner (R.dormant_bottom st) = true -> R.pure_bottom_rhs tf owner = true.

  Lemma next_config_dormant_sound : forall tf before after,
    R.next_config tf before = Some after ->
    dormant_sound tf (R.cfg_state before) -> dormant_sound tf (R.cfg_state after).
  Proof.
    intros tf before after Hnext Hsound owner Hmem.
    destruct (@next_config_dormant_cases tf before after Hnext) as [Heq|[target [Hp Heq]]];
      rewrite Heq in Hmem; [now apply Hsound|].
    apply SL.add_spec in Hmem as [->|Hmem]; [exact Hp|now apply Hsound].
  Qed.

  Lemma run_fuel_dormant_sound : forall fuel tf start,
    dormant_sound tf (R.cfg_state start) -> dormant_sound tf (R.cfg_state (R.run_fuel fuel tf start)).
  Proof.
    induction fuel as [|fuel IH]; intros tf start Hsound; cbn; [exact Hsound|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|exact Hsound].
    apply IH. eapply next_config_dormant_sound; eauto.
  Qed.

  Theorem reachable_dormant_sound : forall fuel tf roots,
    dormant_sound tf (R.cfg_state (R.run_fuel fuel tf (R.initial_config roots))).
  Proof.
    intros. apply run_fuel_dormant_sound. intros owner Hmem.
    cbn in Hmem. rewrite SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma pure_bottom_post_solution : forall tf st owner,
    R.pure_bottom_rhs tf owner = true -> Sem.rhs_post_solution st owner (tf owner).
  Proof.
    intros tf st owner Hp. unfold R.pure_bottom_rhs in Hp.
    destruct (tf owner) eqn:Hrhs; try discriminate.
    apply Bool.andb_true_iff in Hp as [Hp _].
    intros direct reads effects Heval. inversion Heval; subst.
    split; [eapply DL.leq_trans; [exact Hp|apply DL.bottom_least]|].
    intros target value Hin. contradiction.
  Qed.

  Theorem successful_run_dormant_post_solution : forall fuel tf roots final owner,
    R.solve_fuel fuel tf roots = Some final ->
    S.mem owner (R.dormant_bottom final) = true -> Sem.rhs_post_solution final owner (tf owner).
  Proof.
    intros fuel tf roots final owner Hrun Hmem. apply pure_bottom_post_solution.
    unfold R.solve_fuel in Hrun. apply E.terminal_state_shape in Hrun as [Hshape _].
    pose proof (@reachable_dormant_sound fuel tf roots) as Hsound.
    rewrite Hshape in Hsound. now apply Hsound.
  Qed.

  Definition queued (st : R.state) (owner : V.t) :=
    exists entry, In entry (R.queue st) /\ R.handle_variable entry = owner.

  Definition read_event := (V.t * D.t)%type.
  Definition side_effect := (V.t * D.t)%type.

  Section SpawnTraces.
  Variable spawned : V.t -> Prop.

  Inductive rhs_trace :
    R.ConstraintSystem.rhs ->
    D.t -> list read_event -> list side_effect -> Prop :=
  | TraceRet :
      forall direct,
        rhs_trace (R.ConstraintSystem.Ret direct) direct [] []
  | TraceGet :
      forall target value next direct reads effects,
        rhs_trace (next value) direct reads effects ->
        rhs_trace (R.ConstraintSystem.Get target next)
          direct ((target, value) :: reads) effects
  | TraceSide :
      forall target raw next direct reads effects,
        rhs_trace next direct reads effects ->
        rhs_trace (R.ConstraintSystem.Side target raw next)
          direct reads ((target, raw) :: effects)
  | TraceSpawn :
      forall target next direct reads effects,
        spawned target -> rhs_trace next direct reads effects ->
        rhs_trace (R.ConstraintSystem.Spawn target next)
          direct reads effects.

  Inductive rhs_prefix :
    R.ConstraintSystem.rhs -> R.ConstraintSystem.rhs ->
    list read_event -> list side_effect -> Prop :=
  | PrefixHere :
      forall body, rhs_prefix body body [] []
  | PrefixGet :
      forall target value next current reads effects,
        rhs_prefix (next value) current reads effects ->
        rhs_prefix (R.ConstraintSystem.Get target next) current
          ((target, value) :: reads) effects
  | PrefixSide :
      forall target raw next current reads effects,
        rhs_prefix next current reads effects ->
        rhs_prefix (R.ConstraintSystem.Side target raw next) current
          reads ((target, raw) :: effects)
  | PrefixSpawn :
      forall target next current reads effects,
        spawned target -> rhs_prefix next current reads effects ->
        rhs_prefix (R.ConstraintSystem.Spawn target next) current
          reads effects.

  Lemma rhs_prefix_snoc_get :
    forall original target next reads effects value,
      rhs_prefix original (R.ConstraintSystem.Get target next)
        reads effects ->
      rhs_prefix original (next value)
        (reads ++ [(target, value)]) effects.
  Proof.
    intros original target next reads effects value Hprefix.
    remember (R.ConstraintSystem.Get target next) as current eqn:Hcurrent.
    revert target next value Hcurrent.
    induction Hprefix; intros target0 next0 value0 Hcurrent.
    - inversion Hcurrent; subst. cbn. constructor. constructor.
    - cbn. econstructor; eauto.
    - cbn. econstructor; eauto.
    - cbn. econstructor; eauto.
  Qed.

  Lemma rhs_prefix_snoc_side :
    forall original target raw next reads effects,
      rhs_prefix original (R.ConstraintSystem.Side target raw next)
        reads effects ->
      rhs_prefix original next reads (effects ++ [(target, raw)]).
  Proof.
    intros original target raw next reads effects Hprefix.
    remember (R.ConstraintSystem.Side target raw next)
      as current eqn:Hcurrent.
    revert target raw next Hcurrent.
    induction Hprefix; intros target0 raw0 next0 Hcurrent.
    - inversion Hcurrent; subst. cbn. constructor. constructor.
    - cbn. econstructor; eauto.
    - cbn. econstructor; eauto.
    - cbn. econstructor; eauto.
  Qed.

  Lemma rhs_prefix_snoc_spawn :
    forall original target next reads effects,
      spawned target ->
      rhs_prefix original (R.ConstraintSystem.Spawn target next)
        reads effects ->
      rhs_prefix original next reads effects.
  Proof.
    intros original target next reads effects Hspawn Hprefix.
    remember (R.ConstraintSystem.Spawn target next) as current eqn:Hcurrent.
    revert target next Hspawn Hcurrent.
    induction Hprefix; intros target0 next0 Hspawn Hcurrent.
    - inversion Hcurrent; subst. econstructor; [exact Hspawn |constructor].
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Lemma rhs_prefix_complete :
    forall original direct reads effects,
      rhs_prefix original (R.ConstraintSystem.Ret direct) reads effects ->
      rhs_trace original direct reads effects.
  Proof.
    intros original direct reads effects Hprefix.
    remember (R.ConstraintSystem.Ret direct) as current eqn:Hcurrent.
    revert direct Hcurrent.
    induction Hprefix; intros direct0 Hcurrent.
    - inversion Hcurrent; subst. constructor.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
  Qed.

  Definition reader_registered
    (st : R.state) (reader target : V.t) : Prop :=
    S.mem reader (R.lookup_set (R.readers st) target) = true.

  Definition read_guarded
    (st : R.state) (owner : V.t) (event : read_event) : Prop :=
    Sem.solved st (fst event) /\
    (reader_registered st owner (fst event) \/ queued st owner) /\
    (R.semantic_lookup st (fst event) = Some (snd event) \/
      queued st owner).

  Definition reads_guarded
    (st : R.state) (owner : V.t) (reads : list read_event) : Prop :=
    Forall (read_guarded st owner) reads.

  Definition effect_recorded
    (st : R.state) (source : V.t) (effect : side_effect) : Prop :=
    exists contribution,
      M.lookup (R.lookup_map (R.contributions st) (fst effect)) source =
        Some contribution /\
      D.leq (snd effect) contribution = true.

  Definition effects_recorded
    (st : R.state) (source : V.t) (effects : list side_effect) : Prop :=
    Forall (effect_recorded st source) effects.

  Definition effect_accumulated
    (st : R.state) (source : V.t) (effect : side_effect) : Prop :=
    exists accumulated,
      M.lookup (R.lookup_map (R.local_sides st) source) (fst effect) =
        Some accumulated /\
      D.leq (snd effect) accumulated = true.

  Definition effects_accumulated
    (st : R.state) (source : V.t) (effects : list side_effect) : Prop :=
    Forall (effect_accumulated st source) effects.

  Definition rhs_progress
    (tf : R.ConstraintSystem.system) (st : R.state)
    (owner : V.t) (current : R.ConstraintSystem.rhs) : Prop :=
    exists reads effects,
      rhs_prefix (tf owner) current reads effects /\
      reads_guarded st owner reads /\
      effects_recorded st owner effects /\
      effects_accumulated st owner effects.

  Definition summary_valid
    (tf : R.ConstraintSystem.system) (st : R.state) (owner : V.t) : Prop :=
    exists direct reads effects,
      rhs_trace (tf owner) direct reads effects /\
      reads_guarded st owner reads /\
      effects_recorded st owner effects /\
      D.leq direct (R.sigma_value st owner) = true.

  Lemma initial_rhs_progress :
    forall tf st owner,
      rhs_progress tf (R.start_evaluation st owner) owner (tf owner).
  Proof. intros. exists [], []. repeat split; constructor. Qed.

  Lemma stored_value_below_aggregate : forall st source target value,
    M.lookup (R.lookup_map (R.contributions st) target) source = Some value ->
    D.leq value (R.aggregate st target) = true.
  Proof.
    intros st source target value H. unfold R.aggregate.
    apply join_values_upper. eapply ML.lookup_values; exact H.
  Qed.

  Lemma guarded_trace_evaluates :
    forall st owner body direct reads effects,
      rhs_trace body direct reads effects ->
      reads_guarded st owner reads ->
      ~ queued st owner ->
      Sem.rhs_eval st body direct reads effects.
  Proof.
    intros st owner body direct reads effects Htrace.
    induction Htrace; intros Hreads Hnotqueued.
    - constructor.
    - inversion Hreads as [|event rest Hguarded Hrest]; subst.
      destruct Hguarded as [Hsolved [_ Hvalue]].
      destruct Hvalue as [Heq | Hqueued]; [|contradiction].
      cbn in Heq.
      eapply Sem.EvalGet.
      + exact Heq.
      +
      apply IHHtrace; assumption.
    - constructor. apply IHHtrace; assumption.
    - constructor. apply IHHtrace; assumption.
  Qed.

  Lemma recorded_effects_below :
    forall st source effects,
      effects_recorded st source effects ->
      (forall target,
        D.leq (R.aggregate st target) (R.sigma_value st target) = true) ->
      Sem.side_effects_below st effects.
  Proof.
    intros st source effects Hrecorded Haggregate target raw Hin.
    apply Forall_forall with (x := (target, raw)) in Hrecorded;
      [|exact Hin].
    destruct Hrecorded as [contribution [Hlookup Hraw]].
    eapply DL.leq_trans; [exact Hraw |]. eapply DL.leq_trans.
    - eapply stored_value_below_aggregate. exact Hlookup.
    - apply Haggregate.
  Qed.

  Lemma rhs_eval_deterministic :
    forall st body direct reads effects
      replay_direct replay_reads replay_effects,
      Sem.rhs_eval st body direct reads effects ->
      Sem.rhs_eval st body replay_direct replay_reads replay_effects ->
      replay_direct = direct /\
      replay_reads = reads /\ replay_effects = effects.
  Proof.
    intros st body direct reads effects replay_direct replay_reads
      replay_effects Hcanonical Hreplay.
    revert direct reads effects Hcanonical.
    induction Hreplay; intros direct0 reads0 effects0 Hcanonical;
      inversion Hcanonical; subst.
    - repeat split.
    - match goal with
      | Hleft : R.semantic_lookup st ?target = Some ?left,
        Hright : R.semantic_lookup st ?target = Some ?right |- _ =>
          first
            [ constr_eq Hleft Hright; fail 1
            | assert (left = right) by congruence; subst right ]
      end.
      match goal with
      | |- _ = ?tail_direct /\
          _ = (_ :: ?tail_reads) /\ _ = ?tail_effects =>
          specialize (IHHreplay tail_direct tail_reads tail_effects
            ltac:(assumption))
      end.
      destruct IHHreplay as [-> [-> ->]]. repeat split.
    - match goal with
      | |- _ = ?tail_direct /\
          _ = ?tail_reads /\ _ = (_ :: ?tail_effects) =>
          specialize (IHHreplay tail_direct tail_reads tail_effects
            ltac:(assumption))
      end.
      destruct IHHreplay as [-> [-> ->]]. repeat split.
    - match goal with
      | |- _ = ?tail_direct /\
          _ = ?tail_reads /\ _ = ?tail_effects =>
          specialize (IHHreplay tail_direct tail_reads tail_effects
            ltac:(assumption))
      end.
      destruct IHHreplay as [-> [-> ->]]. repeat split.
  Qed.

  Lemma summary_valid_replay :
    forall tf st owner,
      ~ queued st owner ->
      (forall target,
        D.leq (R.aggregate st target) (R.sigma_value st target) = true) ->
      summary_valid tf st owner ->
      Sem.rhs_post_solution st owner (tf owner).
  Proof.
    intros tf st owner Hnotqueued Haggregate
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    intros replay_direct replay_reads replay_effects Heval.
    assert (Hcanonical : Sem.rhs_eval st (tf owner) direct reads effects).
    { eapply guarded_trace_evaluates; eauto. }
    destruct (@rhs_eval_deterministic st (tf owner) direct reads effects
      replay_direct replay_reads replay_effects Hcanonical Heval)
      as [-> [-> ->]]. split.
    - exact Hdirect.
    - apply recorded_effects_below with (source := owner); assumption.
  Qed.

  Lemma quiescent_not_queued : forall st owner,
    Sem.quiescent st -> ~ queued st owner.
  Proof.
    intros st owner [Hqueue _] [entry [Hin _]]. unfold R.queue_peek in Hqueue.
    destruct (R.queue st); [contradiction|discriminate].
  Qed.

  Lemma terminal_summary_post_solution : forall tf st owner,
    Sem.quiescent st -> (forall target, aggregate_bounded st target) ->
    summary_valid tf st owner -> Sem.rhs_post_solution st owner (tf owner).
  Proof.
    intros. apply summary_valid_replay; auto. now apply quiescent_not_queued.
  Qed.

  Lemma request_spawn_progress : forall tf st owner body target,
    rhs_progress tf st owner body -> rhs_progress tf (R.request_spawn st target) owner body.
  Proof.
    intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); exact H.
  Qed.

  Lemma request_spawn_summary : forall tf st owner target,
    summary_valid tf st owner -> summary_valid tf (R.request_spawn st target) owner.
  Proof.
    intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); exact H.
  Qed.

  Lemma rhs_progress_deferred_spawn : forall tf st owner target body,
    spawned target ->
    rhs_progress tf st owner (R.ConstraintSystem.Spawn target body) ->
    rhs_progress tf (R.request_spawn st target) owner body.
  Proof.
    intros tf st owner target body Hspawn [reads [effects [Hp [Hr [Hs Hl]]]]].
    apply request_spawn_progress. exists reads, effects. repeat split; auto.
    eapply rhs_prefix_snoc_spawn; eassumption.
  Qed.

  Lemma dispatch_progress : forall tf st owner body pending requested,
    rhs_progress tf st owner body -> rhs_progress tf (R.with_spawns st pending requested) owner body.
  Proof. intros; exact H. Qed.

  Lemma dispatch_summary : forall tf st owner pending requested,
    summary_valid tf st owner -> summary_valid tf (R.with_spawns st pending requested) owner.
  Proof. intros; exact H. Qed.

  Lemma pure_bottom_summary : forall tf st owner,
    R.pure_bottom_rhs tf owner = true -> summary_valid tf st owner.
  Proof.
    intros tf st owner Hp. unfold R.pure_bottom_rhs in Hp.
    destruct (tf owner) eqn:Htf; try discriminate.
    apply Bool.andb_true_iff in Hp as [Hp _].
    exists t, [], []. repeat split; try constructor.
    - rewrite Htf. constructor.
    - eapply DL.leq_trans; [exact Hp|apply DL.bottom_least].
  Qed.

  Lemma lookup_update_map_same : forall A (table : M.t (M.t A)) outer inner value,
    M.lookup (R.lookup_map (R.update_map table outer inner value) outer) inner = Some value.
  Proof.
    intros. unfold R.update_map, R.lookup_map. rewrite ML.lookup_update_same.
    apply ML.lookup_update_same.
  Qed.

  Lemma lookup_update_map_other_inner : forall A (table : M.t (M.t A)) outer inner value observed,
    observed <> inner ->
    M.lookup (R.lookup_map (R.update_map table outer inner value) outer) observed =
    M.lookup (R.lookup_map table outer) observed.
  Proof.
    intros. unfold R.update_map, R.lookup_map. rewrite ML.lookup_update_same.
    now rewrite ML.lookup_update_other.
  Qed.

  Lemma accumulated_side_input_upper_previous : forall st source target raw previous,
    M.lookup (R.lookup_map (R.local_sides st) source) target = Some previous ->
    D.leq previous (R.accumulated_side_input st source target raw) = true.
  Proof.
    intros st source target raw previous H. unfold R.accumulated_side_input. rewrite H.
    apply DL.join_upper_left.
  Qed.

  Lemma lookup_update_map_other_outer : forall A (table : M.t (M.t A)) outer inner value observed,
    observed <> outer ->
    R.lookup_map (R.update_map table outer inner value) observed = R.lookup_map table observed.
  Proof. intros. unfold R.lookup_map, R.update_map. now rewrite ML.lookup_update_other. Qed.

  Lemma record_side_input_below_contribution : forall st source target raw,
    D.leq (R.accumulated_side_input st source target raw)
      (R.stored_contribution (R.record_side_payload st source target raw) source target) = true.
  Proof. intros. rewrite record_side_payload_cell. apply SUL.update_sound. Qed.

  Lemma record_side_raw_below_contribution : forall st source target raw,
    D.leq raw (R.stored_contribution (R.record_side_payload st source target raw) source target) = true.
  Proof.
    intros. eapply DL.leq_trans; [apply accumulated_side_covers_raw|apply record_side_input_below_contribution].
  Qed.
  Lemma local_side_record_same :
    forall st source target raw,
      M.lookup
        (R.lookup_map
          (R.local_sides (R.record_side_payload st source target raw))
          source) target =
      Some (R.accumulated_side_input st source target raw).
  Proof.
    intros. unfold R.record_side_payload. apply lookup_update_map_same.
  Qed.

  Lemma local_side_record_other_target :
    forall st source target raw observed,
      observed <> target ->
      M.lookup
        (R.lookup_map
          (R.local_sides (R.record_side_payload st source target raw))
          source) observed =
      M.lookup (R.lookup_map (R.local_sides st) source) observed.
  Proof.
    intros. unfold R.record_side_payload.
    apply lookup_update_map_other_inner. exact H.
  Qed.

  Lemma effect_accumulated_record_new :
    forall st source target raw,
      effect_accumulated
        (R.record_side_payload st source target raw)
        source (target, raw).
  Proof.
    intros. exists (R.accumulated_side_input st source target raw). split.
    - apply local_side_record_same.
    - apply accumulated_side_covers_raw.
  Qed.

  Lemma effect_accumulated_record_old :
    forall st source target raw effect,
      effect_accumulated st source effect ->
      effect_accumulated
        (R.record_side_payload st source target raw) source effect.
  Proof.
    intros st source target raw [observed old]
      [accumulated [Hlookup Hbelow]].
    destruct (V.eq_dec observed target) as [-> | Hneq].
    - exists (R.accumulated_side_input st source target raw). split.
      + apply local_side_record_same.
      + eapply DL.leq_trans; [exact Hbelow |].
        eapply accumulated_side_input_upper_previous. exact Hlookup.
    - exists accumulated. split; [|exact Hbelow].
      rewrite local_side_record_other_target by exact Hneq. exact Hlookup.
  Qed.

  Lemma effects_accumulated_record :
    forall st source target raw effects,
      effects_accumulated st source effects ->
      effects_accumulated
        (R.record_side_payload st source target raw)
        source (effects ++ [(target, raw)]).
  Proof.
    intros. apply Forall_app. split.
    - eapply Forall_impl; [|exact H].
      intros effect Hold. now apply effect_accumulated_record_old.
    - constructor; [apply effect_accumulated_record_new |constructor].
  Qed.

  Lemma effect_recorded_from_accumulated :
    forall st source target raw effect,
      effect_recorded st source effect ->
      effect_accumulated st source effect ->
      effect_recorded
        (R.record_side_payload st source target raw) source effect.
  Proof.
    intros st source target raw [observed old]
      [old_contribution [Hold_lookup Hold_below]]
      [accumulated [Hlookup Hbelow]].
    destruct (V.eq_dec observed target) as [-> | Hneq].
    - exists (R.stored_contribution
        (R.record_side_payload st source target raw) source target).
      split.
      + unfold R.stored_contribution, R.record_side_payload. cbn.
        rewrite !lookup_update_map_same. reflexivity.
      + eapply DL.leq_trans; [exact Hbelow |].
        eapply DL.leq_trans.
        * eapply accumulated_side_input_upper_previous. exact Hlookup.
        * apply record_side_input_below_contribution.
    - exists old_contribution. split; [|exact Hold_below].
      unfold R.record_side_payload. cbn.
      rewrite lookup_update_map_other_outer by exact Hneq.
      exact Hold_lookup.
  Qed.

  Lemma effects_recorded_record :
    forall st source target raw effects,
      effects_recorded st source effects ->
      effects_accumulated st source effects ->
      effects_recorded
        (R.record_side_payload st source target raw)
        source (effects ++ [(target, raw)]).
  Proof.
    intros st source target raw effects Hrecorded Haccumulated.
    apply Forall_app. split.
    - revert Haccumulated.
      induction Hrecorded as [|effect effects Heffect Heffects IH];
        intros Haccumulated; [constructor |].
      inversion Haccumulated as [|effect0 effects0 Hlocal Hlocals]; subst.
      constructor; [eapply effect_recorded_from_accumulated; eauto |].
      apply IH. exact Hlocals.
    - constructor; [|constructor]. unfold effect_recorded. cbn.
      exists (R.stored_contribution
        (R.record_side_payload st source target raw) source target).
      split.
      + unfold R.stored_contribution, R.record_side_payload. cbn.
        rewrite !lookup_update_map_same. reflexivity.
      + apply record_side_raw_below_contribution.
  Qed.

  Lemma effects_recorded_side_ready :
    forall st source target raw effects,
      effects_recorded st (R.handle_variable source) effects ->
      effects_accumulated st (R.handle_variable source) effects ->
      effects_recorded (R.side_ready_state st source target raw)
        (R.handle_variable source)
        (effects ++ [(R.handle_variable target, raw)]).
  Proof.
    intros. unfold R.side_ready_state, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      eapply effects_recorded_record; eauto.
  Qed.

  Lemma effects_accumulated_side_ready :
    forall st source target raw effects,
      effects_accumulated st (R.handle_variable source) effects ->
      effects_accumulated (R.side_ready_state st source target raw)
        (R.handle_variable source)
        (effects ++ [(R.handle_variable target, raw)]).
  Proof.
    intros. unfold R.side_ready_state, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      apply effects_accumulated_record; exact H.
  Qed.

  Lemma read_guarded_side_ready :
    forall st source target raw owner event,
      read_guarded st owner event ->
      read_guarded (R.side_ready_state st source target raw) owner event.
  Proof.
    intros st source target raw owner [read value]
      [Hsolved [Hregistered Hvalue]].
    assert (Hbase : read_guarded
      (R.record_side_payload st (R.handle_variable source)
        (R.handle_variable target) raw) owner (read, value)).
    { repeat split.
      - destruct Hsolved as [old Hlookup]. exists old.
        unfold R.record_side_payload. cbn. exact Hlookup.
      - destruct Hregistered as [Hregistered | Hqueued].
        + left. unfold reader_registered in *.
          unfold R.record_side_payload. exact Hregistered.
        + right. unfold queued in *. unfold R.record_side_payload.
          exact Hqueued.
      - destruct Hvalue as [Hvalue | Hqueued].
        + left. unfold R.record_side_payload. exact Hvalue.
        + right. unfold queued in *. unfold R.record_side_payload.
          exact Hqueued. }
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      [exact Hbase |].
    unfold R.promote_controlled. exact Hbase.
  Qed.

  Lemma reads_guarded_side_ready :
    forall st source target raw owner reads,
      reads_guarded st owner reads ->
      reads_guarded (R.side_ready_state st source target raw) owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H].
    intros. now apply read_guarded_side_ready.
  Qed.

  Lemma rhs_progress_side :
    forall tf st owner target raw next,
      rhs_progress tf st (R.handle_variable owner)
        (R.ConstraintSystem.Side (R.handle_variable target) raw next) ->
      rhs_progress tf (R.side_ready_state st owner target raw)
        (R.handle_variable owner) next.
  Proof.
    intros tf st owner target raw next
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, (effects ++ [(R.handle_variable target, raw)]).
    repeat split.
    - eapply rhs_prefix_snoc_side. exact Hprefix.
    - apply reads_guarded_side_ready. exact Hreads.
    - eapply effects_recorded_side_ready; eauto.
    - apply effects_accumulated_side_ready. exact Haccumulated.
  Qed.

  Lemma semantic_lookup_dormant :
    forall st x,
      R.is_dormant st x = true ->
      R.semantic_lookup st x = Some D.bottom.
  Proof.
    intros st x Hdormant.
    unfold R.is_dormant in Hdormant.
    destruct (S.mem x (R.dormant_bottom st)) eqn:Hmember;
      cbn in Hdormant; try discriminate.
    destruct (M.lookup (R.sigma st) x) eqn:Hsigma;
      cbn in Hdormant; try discriminate.
    unfold R.semantic_lookup. now rewrite Hsigma, Hmember.
  Qed.

  Lemma remember_dormant_active :
    forall st x,
      R.Ranking.lookup (R.ranking st) x = None ->
      R.is_materialized st x = false ->
      R.is_dormant (R.remember_dormant st x) x = true.
  Proof.
    intros st x Hrank Hmaterialized.
    unfold R.is_materialized in Hmaterialized.
    destruct (M.lookup (R.sigma st) x) eqn:Hsigma; try discriminate.
    unfold R.is_dormant, R.remember_dormant, R.with_dormant_bottom; cbn.
    rewrite Hsigma, Hrank. cbn.
    assert (Hmember : S.mem x (S.add x (R.dormant_bottom st)) = true).
    { apply SL.add_spec. now left. }
    now rewrite Hmember.
  Qed.

  Lemma semantic_lookup_add_reader :
    forall st target reader x,
      R.semantic_lookup (R.add_reader st target reader) x =
      R.semantic_lookup st x.
  Proof.
    intros. unfold R.semantic_lookup, R.add_reader, R.promote_controlled.
    reflexivity.
  Qed.

  Lemma semantic_lookup_remember_dormant :
    forall st target x value,
      R.semantic_lookup st x = Some value ->
      R.semantic_lookup (R.remember_dormant st target) x = Some value.
  Proof.
    intros st target x value Hlookup.
    unfold R.semantic_lookup, R.remember_dormant,
      R.with_dormant_bottom in *; cbn.
    destruct (M.lookup (R.sigma st) x) eqn:Hsigma.
    - exact Hlookup.
    - destruct (S.mem x (R.dormant_bottom st)) eqn:Hmember;
        inversion Hlookup; subst.
      assert (Hadded :
        S.mem x (S.add target (R.dormant_bottom st)) = true).
      { apply SL.add_spec. now right. }
      now rewrite Hadded.
  Qed.

  Lemma semantic_lookup_materialize_solved :
    forall st target x value,
      R.semantic_lookup st x = Some value ->
      R.semantic_lookup (R.materialize st target) x = Some value.
  Proof.
    intros st target x value Hlookup.
    unfold R.materialize, R.is_materialized.
    destruct (M.lookup (R.sigma st) target) eqn:Htarget;
      [exact Hlookup |].
    unfold R.semantic_lookup in *; cbn.
    destruct (V.eq_dec x target) as [-> | Hneq].
    - rewrite ML.lookup_update_same.
      rewrite Htarget in Hlookup.
      destruct (S.mem target (R.dormant_bottom st));
        inversion Hlookup. reflexivity.
    - rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
  Qed.

  Lemma semantic_lookup_get_ready_solved :
    forall st owner target x value,
      R.semantic_lookup st x = Some value ->
      R.semantic_lookup (R.get_ready_state st owner target) x = Some value.
  Proof.
    intros. unfold R.get_ready_state.
    apply semantic_lookup_materialize_solved.
    rewrite semantic_lookup_add_reader.
    unfold R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      exact H.
  Qed.

  Lemma semantic_lookup_solved :
    forall st x,
      Sem.solved st x ->
      R.semantic_lookup st x = Some (R.sigma_value st x).
  Proof.
    intros st x [value Hlookup].
    unfold R.semantic_lookup, R.sigma_value in *.
    destruct (M.lookup (R.sigma st) x); [reflexivity |].
    destruct (S.mem x (R.dormant_bottom st));
      inversion Hlookup; reflexivity.
  Qed.

  Lemma semantic_solved_get_ready_self : forall st owner target,
    Sem.solved (R.get_ready_state st owner target) (R.handle_variable target).
  Proof. intros. unfold R.get_ready_state. apply E.materialize_solves. Qed.

  Lemma queued_get_ready : forall st reader target owner,
    queued st owner -> queued (R.get_ready_state st reader target) owner.
  Proof.
    intros. unfold R.get_ready_state, R.materialize, R.is_materialized.
    destruct (M.lookup _ _); destruct (Nat.ltb _ _); exact H.
  Qed.

  Lemma reader_registered_add :
    forall st target owner,
      reader_registered (R.add_reader st target owner) owner target.
  Proof.
    intros. unfold reader_registered, R.add_reader, R.lookup_set. cbn.
    rewrite ML.lookup_update_same. apply SL.add_spec. left. reflexivity.
  Qed.

  Lemma reader_registered_add_preserved :
    forall st target owner reader observed,
      reader_registered st reader observed ->
      reader_registered (R.add_reader st target owner) reader observed.
  Proof.
    intros st target owner reader observed Hregistered.
    unfold reader_registered, R.add_reader, R.lookup_set in *; cbn.
    destruct (V.eq_dec observed target) as [-> | Hneq].
    - rewrite ML.lookup_update_same. apply SL.add_spec. right.
      exact Hregistered.
    - rewrite ML.lookup_update_other by exact Hneq. exact Hregistered.
  Qed.

  Lemma reader_registered_materialize :
    forall st x reader observed,
      reader_registered st reader observed ->
      reader_registered (R.materialize st x) reader observed.
  Proof.
    intros st x reader observed Hregistered.
    unfold reader_registered, R.materialize, R.is_materialized in *.
    destruct (M.lookup (R.sigma st) x); exact Hregistered.
  Qed.

  Lemma read_guarded_add_reader :
    forall st target added owner event,
      read_guarded st owner event ->
      read_guarded (R.add_reader st target added) owner event.
  Proof.
    intros st target added owner [observed value]
      [Hsolved [Hregistered Hvalue]]. repeat split.
    - now apply E.add_reader_solved.
    - destruct Hregistered as [Hregistered | Hqueued].
      + left. now apply reader_registered_add_preserved.
      + right. unfold queued, R.add_reader, R.promote_controlled in *.
        exact Hqueued.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. now rewrite semantic_lookup_add_reader.
      + right. unfold queued, R.add_reader, R.promote_controlled in *.
        exact Hqueued.
  Qed.

  Lemma read_guarded_remember_dormant :
    forall st target owner event,
      read_guarded st owner event ->
      read_guarded (R.remember_dormant st target) owner event.
  Proof.
    intros st target owner [observed value]
      [Hsolved [Hregistered Hvalue]]. repeat split.
    - now apply E.remember_dormant_solved.
    - unfold reader_registered, queued, R.remember_dormant,
        R.with_dormant_bottom in *; exact Hregistered.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. now apply semantic_lookup_remember_dormant.
      + right. unfold queued, R.remember_dormant,
          R.with_dormant_bottom in *; exact Hqueued.
  Qed.

  Lemma reads_guarded_add_reader :
    forall st target added owner reads,
      reads_guarded st owner reads ->
      reads_guarded (R.add_reader st target added) owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H].
    intros. now apply read_guarded_add_reader.
  Qed.

  Lemma reads_guarded_remember_dormant :
    forall st target owner reads,
      reads_guarded st owner reads ->
      reads_guarded (R.remember_dormant st target) owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H].
    intros. now apply read_guarded_remember_dormant.
  Qed.

  Lemma read_guarded_get_ready_old :
    forall st owner target event,
      read_guarded st (R.handle_variable owner) event ->
      read_guarded (R.get_ready_state st owner target)
        (R.handle_variable owner) event.
  Proof.
    intros st owner target [read value]
      [Hsolved [Hregistered Hvalue]].
    unfold R.get_ready_state.
    set (st1 := if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
      then st else R.promote_controlled st (R.handle_variable target)).
    repeat split.
    - apply E.materialize_solved, E.add_reader_solved.
      unfold st1, R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued].
      + left. apply reader_registered_materialize,
          reader_registered_add_preserved.
        unfold st1, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Hregistered.
      + right. unfold queued in *.
        now apply queued_get_ready.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. apply semantic_lookup_materialize_solved.
        rewrite semantic_lookup_add_reader.
        unfold st1, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Hvalue.
      + right. unfold queued in *.
        now apply queued_get_ready.
  Qed.

  Lemma read_guarded_get_ready_new :
    forall st owner target,
      read_guarded (R.get_ready_state st owner target)
        (R.handle_variable owner)
        (R.handle_variable target,
          R.sigma_value (R.get_ready_state st owner target)
            (R.handle_variable target)).
  Proof.
    intros. repeat split.
    - apply semantic_solved_get_ready_self.
    - left. unfold R.get_ready_state.
      apply reader_registered_materialize, reader_registered_add.
    - left. apply semantic_lookup_solved.
      apply semantic_solved_get_ready_self.
  Qed.

  Lemma reads_guarded_get_ready :
    forall st owner target reads,
      reads_guarded st (R.handle_variable owner) reads ->
      reads_guarded (R.get_ready_state st owner target)
        (R.handle_variable owner)
        (reads ++ [(R.handle_variable target,
          R.sigma_value (R.get_ready_state st owner target)
            (R.handle_variable target))]).
  Proof.
    intros. apply Forall_app. split.
    - eapply Forall_impl; [|exact H].
      intros. now apply read_guarded_get_ready_old.
    - constructor; [apply read_guarded_get_ready_new |constructor].
  Qed.

  Lemma effects_recorded_get_ready :
    forall st owner target effects,
      effects_recorded st (R.handle_variable owner) effects ->
      effects_recorded (R.get_ready_state st owner target)
        (R.handle_variable owner) effects.
  Proof.
    intros st owner target effects Hrecorded.
    unfold effects_recorded, effect_recorded in *.
    unfold R.get_ready_state, R.materialize, R.is_materialized.
    destruct (M.lookup
      (R.sigma (R.add_reader
        (if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
         then st else R.promote_controlled st (R.handle_variable target))
        (R.handle_variable target) (R.handle_variable owner)))
      (R.handle_variable target));
      unfold R.add_reader, R.promote_controlled;
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      exact Hrecorded.
  Qed.

  Lemma effects_accumulated_get_ready :
    forall st owner target effects,
      effects_accumulated st (R.handle_variable owner) effects ->
      effects_accumulated (R.get_ready_state st owner target)
        (R.handle_variable owner) effects.
  Proof.
    intros st owner target effects Haccumulated.
    unfold effects_accumulated, effect_accumulated in *.
    unfold R.get_ready_state, R.materialize, R.is_materialized.
    destruct (M.lookup
      (R.sigma (R.add_reader
        (if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
         then st else R.promote_controlled st (R.handle_variable target))
        (R.handle_variable target) (R.handle_variable owner)))
      (R.handle_variable target));
      unfold R.add_reader, R.promote_controlled;
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      exact Haccumulated.
  Qed.

  Lemma rhs_progress_get :
    forall tf st owner target next,
      rhs_progress tf st (R.handle_variable owner)
        (R.ConstraintSystem.Get (R.handle_variable target) next) ->
      let ready := R.get_ready_state st owner target in
      rhs_progress tf ready (R.handle_variable owner)
        (next (R.sigma_value ready (R.handle_variable target))).
  Proof.
    intros tf st owner target next
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    cbn. exists (reads ++ [(R.handle_variable target,
      R.sigma_value (R.get_ready_state st owner target)
        (R.handle_variable target))]), effects. repeat split.
    - eapply rhs_prefix_snoc_get. exact Hprefix.
    - apply reads_guarded_get_ready. exact Hreads.
    - apply effects_recorded_get_ready. exact Hrecorded.
    - apply effects_accumulated_get_ready. exact Haccumulated.
  Qed.

  Lemma queue_insert_fresh_preserves :
    forall inserted queue observed,
      List.In observed queue ->
      List.In observed (R.queue_insert_fresh inserted queue).
  Proof.
    intros inserted queue. induction queue as [|head rest IH];
      intros observed Hin; [contradiction |].
    change (List.In observed
      (if Nat.ltb (R.handle_rank head) (R.handle_rank inserted)
       then inserted :: head :: rest
       else head :: R.queue_insert_fresh inserted rest)).
    destruct (Nat.ltb (R.handle_rank head) (R.handle_rank inserted)).
    - cbn. destruct Hin as [-> | Hin]; auto.
    - cbn. destruct Hin as [-> | Hin]; [now left |].
      right. now apply IH.
  Qed.

  Lemma queue_insert_preserves :
    forall inserted queue observed,
      List.In observed queue -> List.In observed (R.queue_insert inserted queue).
  Proof.
    intros. unfold R.queue_insert.
    destruct (R.queue_contains_rank (R.handle_rank inserted) queue);
      eauto using queue_insert_fresh_preserves.
  Qed.

  Lemma queued_enqueue_handle :
    forall st inserted tracked,
      queued st tracked ->
      queued (R.enqueue_handle st inserted) tracked.
  Proof.
    intros st inserted tracked [entry [Hin Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.enqueue_handle. cbn. now apply queue_insert_preserves.
  Qed.

  Lemma queued_observe :
    forall st target next entry tracked,
      R.observe st target = (next, entry) ->
      queued st tracked ->
      queued next tracked.
  Proof.
    intros st target next entry tracked Hobserve Hqueued.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; subst; exact Hqueued.
  Qed.

  Lemma queued_enqueue :
    forall st inserted tracked,
      queued st tracked ->
      queued (R.enqueue st inserted) tracked.
  Proof.
    intros st inserted tracked Hqueued. unfold R.enqueue.
    destruct (R.observe st inserted) as [next entry] eqn:Hobserve.
    apply queued_enqueue_handle. eapply queued_observe; eauto.
  Qed.

  Lemma queued_enqueue_all :
    forall xs st tracked,
      queued st tracked ->
      queued (R.enqueue_all st xs) tracked.
  Proof.
    induction xs as [|x xs IH]; intros st tracked Hqueued; cbn;
      eauto using queued_enqueue.
  Qed.

  Lemma queued_write_changed_value :
    forall st owner value tracked,
      queued st tracked ->
      queued (R.write_changed_value st owner value) tracked.
  Proof.
    intros st owner value tracked Hqueued.
    unfold R.write_changed_value. apply queued_enqueue_all. exact Hqueued.
  Qed.
  Lemma read_guarded_observe :
    forall st observed next entry owner event,
      R.observe st observed = (next, entry) ->
      read_guarded st owner event -> read_guarded next owner event.
  Proof.
    intros st observed next entry owner event Hobserve Hguarded.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) observed);
      inversion Hobserve; subst; exact Hguarded.
  Qed.

  Lemma reads_guarded_observe :
    forall st observed next entry owner reads,
      R.observe st observed = (next, entry) ->
      reads_guarded st owner reads -> reads_guarded next owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H0].
    intros. eapply read_guarded_observe; eauto.
  Qed.

  Lemma read_guarded_enqueue_handle :
    forall st inserted owner event,
      read_guarded st owner event ->
      read_guarded (R.enqueue_handle st inserted) owner event.
  Proof.
    intros st inserted owner event [Hsolved [Hregistered Hvalue]].
    repeat split; try exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued]; [now left |].
      right. unfold queued in *. now apply queued_enqueue_handle.
    - destruct Hvalue as [Hvalue | Hqueued]; [now left |].
      right. unfold queued in *. now apply queued_enqueue_handle.
  Qed.

  Lemma reads_guarded_enqueue_handle :
    forall st inserted owner reads,
      reads_guarded st owner reads ->
      reads_guarded (R.enqueue_handle st inserted) owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H].
    intros. now apply read_guarded_enqueue_handle.
  Qed.


  Lemma semantic_lookup_write_changed_other : forall st owner value x,
    x <> owner -> R.semantic_lookup (R.write_changed_value st owner value) x = R.semantic_lookup st x.
  Proof.
    intros. unfold R.semantic_lookup. rewrite write_changed_value_sigma.
    rewrite ML.lookup_update_other by assumption. rewrite write_changed_value_dormant. reflexivity.
  Qed.

  Lemma read_guarded_enqueue : forall st target owner event,
    read_guarded st owner event -> read_guarded (R.enqueue st target) owner event.
  Proof.
    intros st target owner event H. unfold R.enqueue. destruct (R.observe st target) eqn:Hobs.
    apply read_guarded_enqueue_handle. eapply read_guarded_observe; eauto.
  Qed.

  Lemma reads_guarded_enqueue_all : forall xs st owner reads,
    reads_guarded st owner reads -> reads_guarded (R.enqueue_all st xs) owner reads.
  Proof.
    induction xs; intros; cbn; [assumption|]. apply IHxs.
    eapply Forall_impl; [|exact H]. intros. now apply read_guarded_enqueue.
  Qed.

  Lemma rhs_progress_observe : forall tf st target next entry owner body,
    R.observe st target = (next, entry) -> rhs_progress tf st owner body ->
    rhs_progress tf next owner body.
  Proof.
    intros tf st target next entry owner body Hobs Hprogress.
    unfold R.observe in Hobs. destruct (R.Ranking.observe _ _); inversion Hobs; subst.
    exact Hprogress.
  Qed.

  Lemma rhs_progress_enqueue_handle : forall tf st entry owner body,
    rhs_progress tf st owner body -> rhs_progress tf (R.enqueue_handle st entry) owner body.
  Proof.
    intros tf st entry owner body [reads [effects [Hp [Hr [Hs Hl]]]]].
    exists reads, effects. repeat split; auto. now apply reads_guarded_enqueue_handle.
  Qed.

  Lemma rhs_progress_enqueue : forall tf st target owner body,
    rhs_progress tf st owner body -> rhs_progress tf (R.enqueue st target) owner body.
  Proof.
    intros tf st target owner body H. unfold R.enqueue. destruct (R.observe st target) eqn:Hobs.
    apply rhs_progress_enqueue_handle. eapply rhs_progress_observe; eauto.
  Qed.

  Lemma summary_valid_enqueue_handle : forall tf st entry owner,
    summary_valid tf st owner -> summary_valid tf (R.enqueue_handle st entry) owner.
  Proof.
    intros tf st entry owner [direct [reads [effects [Ht [Hr [Hs Hd]]]]]].
    exists direct, reads, effects. repeat split; auto. now apply reads_guarded_enqueue_handle.
  Qed.
  Definition side_update_result
    (st : R.state) (source target : V.t) (raw : D.t) : SU.phase * D.t :=
    SU.update source target
      (R.stored_side_phase st source target)
      (R.stored_contribution st source target)
      (R.accumulated_side_input st source target raw)
      (R.aggregate st target).

  Definition rank_valid (st : R.state) : Prop :=
    RankLaws.valid (R.ranking st).

  Definition rank_extends (before after : R.state) : Prop :=
    forall x rank,
      R.Ranking.lookup (R.ranking before) x = Some rank ->
      R.Ranking.lookup (R.ranking after) x = Some rank.

  Definition handle_valid (st : R.state) (entry : R.handle) : Prop :=
    R.Ranking.lookup (R.ranking st) (R.handle_variable entry) =
      Some (R.handle_rank entry).

  Lemma rank_extends_refl : forall st, rank_extends st st.
  Proof. intros st x rank Hlookup. exact Hlookup. Qed.

  Lemma rank_extends_trans :
    forall first second third,
      rank_extends first second ->
      rank_extends second third ->
      rank_extends first third.
  Proof. intros first second third H12 H23 x rank Hx. auto. Qed.

  Lemma rank_extends_same_ranking :
    forall before after,
      R.ranking before = R.ranking after ->
      rank_extends before after.
  Proof. intros before after Heq x rank Hlookup. now rewrite <- Heq. Qed.

  Lemma empty_rank_valid : rank_valid R.empty_state.
  Proof. apply RankLaws.empty_valid. Qed.

  Lemma rank_valid_observe :
    forall st x next entry,
      rank_valid st ->
      R.observe st x = (next, entry) ->
      rank_valid next.
  Proof.
    intros st x next entry Hvalid Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking rank] eqn:Hrank.
    inversion Hobserve; subst. unfold rank_valid in *. cbn.
    eapply RankLaws.observe_valid; eauto.
  Qed.

  Lemma rank_extends_observe :
    forall st x next entry,
      R.observe st x = (next, entry) ->
      rank_extends st next.
  Proof.
    intros st x next entry Hobserve variable rank Hlookup.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking observed_rank] eqn:Hrank.
    inversion Hobserve; subst. cbn.
    exact
      (@RankLaws.observe_preserves
        (R.ranking st) x ranking observed_rank variable rank
        Hrank Hlookup).
  Qed.

  Lemma observed_handle_valid :
    forall st x next entry,
      R.observe st x = (next, entry) ->
      handle_valid next entry.
  Proof.
    intros st x next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking rank] eqn:Hrank.
    inversion Hobserve; subst. unfold handle_valid. cbn.
    exact (@RankLaws.observe_lookup
      (R.ranking st) x ranking rank Hrank).
  Qed.

  Lemma observed_handle_variable :
    forall st x next entry,
      R.observe st x = (next, entry) ->
      R.handle_variable entry = x.
  Proof.
    intros st x next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma handle_valid_extended :
    forall before after entry,
      rank_extends before after ->
      handle_valid before entry ->
      handle_valid after entry.
  Proof. intros before after entry Hextends Hvalid. now apply Hextends. Qed.

  Lemma rank_extends_after_observe :
    forall st x next entry after,
      R.observe st x = (next, entry) ->
      rank_extends next after ->
      rank_extends st after.
  Proof.
    intros st x next entry after Hobserve Hnext.
    eapply (@rank_extends_trans st next after).
    - exact (@rank_extends_observe st x next entry Hobserve).
    - exact Hnext.
  Qed.

  Lemma rank_extends_with_queue :
    forall st queue,
      rank_extends st (R.with_queue st queue).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_started :
    forall st started,
      rank_extends st (R.with_started st started).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_remember_dormant :
    forall st variable,
      rank_extends st (R.remember_dormant st variable).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_enqueue_handle :
    forall st entry,
      rank_extends st (R.enqueue_handle st entry).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_mark_side_dirty :
    forall st target,
      rank_extends st (R.mark_side_dirty st target).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_start_evaluation :
    forall st owner,
      rank_extends st (R.start_evaluation st owner).
  Proof.
    intros st owner. apply rank_extends_same_ranking.
    unfold R.start_evaluation, R.reset_local_sides, R.materialize.
    destruct (R.is_materialized st owner); reflexivity.
  Qed.

  Lemma rank_extends_materialize :
    forall st variable,
      rank_extends st (R.materialize st variable).
  Proof.
    intros st variable. apply rank_extends_same_ranking.
    unfold R.materialize. destruct (R.is_materialized st variable);
      reflexivity.
  Qed.

  Lemma rank_extends_get_ready :
    forall st owner target,
      rank_extends st (R.get_ready_state st owner target).
  Proof.
    intros st owner target. apply rank_extends_same_ranking.
    unfold R.get_ready_state, R.promote_controlled, R.add_reader,
      R.materialize.
    repeat
      match goal with
      | |- context [if ?condition then _ else _] => destruct condition
      end;
      reflexivity.
  Qed.

  Lemma rank_extends_add_reader :
    forall st target reader,
      rank_extends st (R.add_reader st target reader).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_side_ready :
    forall st source target raw,
      rank_extends st (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw. apply rank_extends_same_ranking.
    unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled.
    repeat
      match goal with
      | |- context [if ?condition then _ else _] => destruct condition
      | |- context [let '(_, _) := ?pair in _] => destruct pair
      end;
      reflexivity.
  Qed.

  Lemma rank_extends_started_evaluation :
    forall st owner started,
      rank_extends st
        (R.with_started (R.start_evaluation st owner) started).
  Proof.
    intros. eapply rank_extends_trans.
    - apply rank_extends_start_evaluation.
    - apply rank_extends_with_started.
  Qed.

  Lemma rank_extends_remember_add_reader :
    forall st target reader,
      rank_extends st
        (R.add_reader (R.remember_dormant st target) target reader).
  Proof.
    intros. eapply rank_extends_trans.
    - apply rank_extends_remember_dormant.
    - apply rank_extends_add_reader.
  Qed.

  Lemma rank_extends_after_observe_enqueue_get_ready :
    forall st target observed target_handle owner,
      R.observe st target = (observed, target_handle) ->
      rank_extends st
        (R.get_ready_state
           (R.enqueue_handle observed target_handle) owner target_handle).
  Proof.
    intros. eapply rank_extends_after_observe; [eassumption |].
    eapply rank_extends_trans.
    - apply rank_extends_enqueue_handle.
    - apply rank_extends_get_ready.
  Qed.

  Lemma rank_extends_after_observe_side_enqueue :
    forall st target observed target_handle owner raw,
      R.observe st target = (observed, target_handle) ->
      rank_extends st
        (R.enqueue_handle
           (R.side_ready_state observed owner target_handle raw)
           target_handle).
  Proof.
    intros. eapply rank_extends_after_observe; [eassumption |].
    eapply rank_extends_trans.
    - apply rank_extends_side_ready.
    - apply rank_extends_enqueue_handle.
  Qed.

  Lemma rank_extends_after_observe_side_mark :
    forall st target observed target_handle owner raw,
      R.observe st target = (observed, target_handle) ->
      rank_extends st
        (R.mark_side_dirty
          (R.side_ready_state observed owner target_handle raw) target).
  Proof.
    intros. eapply rank_extends_after_observe; [eassumption |].
    eapply rank_extends_trans.
    - apply rank_extends_side_ready.
    - apply rank_extends_mark_side_dirty.
  Qed.

  Lemma rank_extends_after_observe_side_mark_enqueue :
    forall st target observed target_handle owner raw,
      R.observe st target = (observed, target_handle) ->
      rank_extends st
        (R.enqueue_handle
          (R.mark_side_dirty
            (R.side_ready_state observed owner target_handle raw) target)
          target_handle).
  Proof.
    intros. eapply rank_extends_after_observe; [eassumption |].
    eapply rank_extends_trans.
    - apply rank_extends_side_ready.
    - eapply rank_extends_trans.
      + apply rank_extends_mark_side_dirty.
      + apply rank_extends_enqueue_handle.
  Qed.

  Lemma rank_extends_after_observe_enqueue_materialize :
    forall st target observed target_handle,
      R.observe st target = (observed, target_handle) ->
      rank_extends st
        (R.materialize (R.enqueue_handle observed target_handle) target).
  Proof.
    intros. eapply rank_extends_after_observe; [eassumption |].
    eapply rank_extends_trans.
    - apply rank_extends_enqueue_handle.
    - apply rank_extends_materialize.
  Qed.

  Lemma rank_valid_enqueue_handle :
    forall st entry,
      rank_valid st -> rank_valid (R.enqueue_handle st entry).
  Proof. intros. exact H. Qed.

  Lemma rank_valid_mark_side_dirty :
    forall st target,
      rank_valid st -> rank_valid (R.mark_side_dirty st target).
  Proof. intros. exact H. Qed.

  Lemma rank_valid_remember_dormant :
    forall st variable,
      rank_valid st -> rank_valid (R.remember_dormant st variable).
  Proof. intros. exact H. Qed.

  Lemma rank_valid_enqueue :
    forall st x,
      rank_valid st -> rank_valid (R.enqueue st x).
  Proof.
    intros st x Hvalid. unfold R.enqueue.
    destruct (R.observe st x) as [next entry] eqn:Hobserve.
    apply rank_valid_enqueue_handle.
    exact (@rank_valid_observe st x next entry Hvalid Hobserve).
  Qed.

  Lemma rank_valid_enqueue_all :
    forall xs st,
      rank_valid st -> rank_valid (R.enqueue_all st xs).
  Proof.
    induction xs as [|x xs IH]; intros st Hvalid; cbn; auto.
    apply IH. now apply rank_valid_enqueue.
  Qed.

  Lemma rank_valid_materialize :
    forall st x,
      rank_valid st -> rank_valid (R.materialize st x).
  Proof.
    intros st x Hvalid. unfold R.materialize.
    destruct (R.is_materialized st x); exact Hvalid.
  Qed.

  Lemma rank_valid_get_ready :
    forall st owner target,
      rank_valid st -> rank_valid (R.get_ready_state st owner target).
  Proof.
    intros st owner target Hvalid.
    unfold R.get_ready_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      apply rank_valid_materialize; exact Hvalid.
  Qed.

  Lemma rank_valid_side_ready :
    forall st source target raw,
      rank_valid st -> rank_valid (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw Hvalid.
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hvalid.
  Qed.

  Lemma rank_valid_start_evaluation :
    forall st owner,
      rank_valid st -> rank_valid (R.start_evaluation st owner).
  Proof.
    intros st owner Hvalid. unfold R.start_evaluation.
    apply rank_valid_materialize. exact Hvalid.
  Qed.

  Lemma rank_valid_write_changed :
    forall st owner value,
      rank_valid st -> rank_valid (R.write_changed_value st owner value).
  Proof.
    intros st owner value Hvalid. unfold R.write_changed_value.
    apply rank_valid_enqueue_all. exact Hvalid.
  Qed.

  Lemma rank_valid_set_value :
    forall st owner direct,
      rank_valid st -> rank_valid (R.set_value st owner direct).
  Proof.
    intros st owner direct Hvalid. unfold R.set_value.
    repeat
      match goal with
      | |- context [if ?condition then _ else _] => destruct condition
      | |- context [let '(_, _) := ?pair in _] => destruct pair
      end;
      try exact Hvalid;
      now apply rank_valid_write_changed.
  Qed.

  Lemma rank_valid_cancel_dirty_target :
    forall st target,
      rank_valid st -> rank_valid (R.cancel_dirty_target st target).
  Proof. intros st target Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_try_dirty_read :
    forall tf st owner target next,
      rank_valid st ->
      R.try_dirty_read tf st owner target = Some next ->
      rank_valid next.
  Proof.
    intros tf st owner target next Hvalid Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using rank_valid_write_changed, rank_valid_cancel_dirty_target.
  Qed.

  Lemma rank_valid_dirty_get_ready :
    forall tf st owner target,
      rank_valid st ->
      rank_valid (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target Hvalid.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hvalid. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - apply rank_valid_try_dirty_read in Hread; auto.
    - exact Hprepared.
  Qed.

  Lemma rank_extends_enqueue :
    forall st x,
      rank_extends st (R.enqueue st x).
  Proof.
    intros st x. unfold R.enqueue.
    destruct (R.observe st x) as [next entry] eqn:Hobserve.
    exact (@rank_extends_observe st x next entry Hobserve).
  Qed.

  Lemma rank_extends_enqueue_all :
    forall xs st,
      rank_extends st (R.enqueue_all st xs).
  Proof.
    induction xs as [|x xs IH]; intros st; cbn.
    - apply rank_extends_refl.
    - eapply rank_extends_trans.
      + apply rank_extends_enqueue.
      + apply IH.
  Qed.

  Lemma rank_extends_write_changed :
    forall st owner value,
      rank_extends st (R.write_changed_value st owner value).
  Proof.
    intros st owner value. unfold R.write_changed_value.
    set (st1 := R.with_sigma st (M.update (R.sigma st) owner value)).
    set (st2 := R.enqueue_all st1
      (S.elements (R.lookup_set (R.readers st) owner))).
    change (rank_extends st
      (R.with_readers st2 (M.update (R.readers st2) owner S.empty))).
    eapply (@rank_extends_trans st st1).
    - apply rank_extends_same_ranking. reflexivity.
    - eapply (@rank_extends_trans st1 st2).
      + apply rank_extends_enqueue_all.
      + apply rank_extends_same_ranking. reflexivity.
  Qed.

  Lemma rank_extends_set_value :
    forall st owner direct,
      rank_extends st (R.set_value st owner direct).
  Proof.
    intros st owner direct. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner)).
    - apply rank_extends_refl.
    - destruct (S.mem owner (R.controlled st)).
      + destruct (U.update false owner (R.stored_phase st owner)
          (R.sigma_value st owner)
          (D.join direct (R.aggregate st owner))) as [phase value].
        cbn. destruct (R.equivalent value (R.sigma_value st owner)).
        * apply rank_extends_same_ranking. reflexivity.
        * eapply (@rank_extends_trans st
            (R.with_phases st (M.update (R.phases st) owner phase))).
          -- apply rank_extends_same_ranking. reflexivity.
          -- apply rank_extends_write_changed.
      + apply rank_extends_write_changed.
  Qed.

  Lemma rank_extends_cancel_dirty_target :
    forall st target,
      rank_extends st (R.cancel_dirty_target st target).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_same_cancel_dirty_target :
    forall before st target,
      R.ranking before = R.ranking st ->
      rank_extends before (R.cancel_dirty_target st target).
  Proof.
    intros before st target Hranking.
    eapply (@rank_extends_trans before st (R.cancel_dirty_target st target)).
    - now apply rank_extends_same_ranking.
    - apply rank_extends_cancel_dirty_target.
  Qed.

  Lemma rank_extends_same_write_cancel_dirty_target :
    forall before st owner value target,
      R.ranking before = R.ranking st ->
      rank_extends before
        (R.cancel_dirty_target
          (R.write_changed_value st owner value) target).
  Proof.
    intros before st owner value target Hranking.
    eapply (@rank_extends_trans before st
      (R.cancel_dirty_target
        (R.write_changed_value st owner value) target)).
    - now apply rank_extends_same_ranking.
    - eapply (@rank_extends_trans st
        (R.write_changed_value st owner value)
        (R.cancel_dirty_target
          (R.write_changed_value st owner value) target)).
      + apply rank_extends_write_changed.
      + apply rank_extends_cancel_dirty_target.
  Qed.

  Lemma rank_extends_same_cancel_write_dirty_target :
    forall before st owner value target,
      R.ranking before = R.ranking st ->
      rank_extends before
        (R.write_changed_value (R.cancel_dirty_target st target) owner value).
  Proof.
    intros before st owner value target Hranking.
    eapply (@rank_extends_trans before st
      (R.write_changed_value (R.cancel_dirty_target st target) owner value)).
    - now apply rank_extends_same_ranking.
    - eapply (@rank_extends_trans st (R.cancel_dirty_target st target)).
      + apply rank_extends_cancel_dirty_target.
      + apply rank_extends_write_changed.
  Qed.

  Lemma rank_extends_try_dirty_read :
    forall tf st owner target next,
      R.try_dirty_read tf st owner target = Some next ->
      rank_extends st next.
  Proof.
    intros tf st owner target next Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using rank_extends_same_cancel_dirty_target,
        rank_extends_same_write_cancel_dirty_target,
        rank_extends_same_cancel_write_dirty_target.
  Qed.

  Lemma rank_extends_dirty_get_ready :
    forall tf st owner target,
      rank_extends st (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target. unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : rank_extends st prepared).
    { subst prepared. eapply (@rank_extends_trans st
        (R.get_control_state st owner target)
        (R.materialize (R.get_control_state st owner target)
          (R.handle_variable target))).
      - unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          [apply rank_extends_refl |apply rank_extends_same_ranking];
          reflexivity.
      - apply rank_extends_materialize. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - eapply (@rank_extends_trans st prepared
        (R.add_reader next (R.handle_variable target)
          (R.handle_variable owner))); [exact Hprepared |].
      eapply (@rank_extends_trans prepared next
        (R.add_reader next (R.handle_variable target)
          (R.handle_variable owner))).
      + eapply rank_extends_try_dirty_read; eauto.
      + apply rank_extends_add_reader.
    - eapply (@rank_extends_trans st prepared
        (R.add_reader prepared (R.handle_variable target)
          (R.handle_variable owner))); [exact Hprepared |].
      apply rank_extends_add_reader.
  Qed.

  Lemma rank_valid_request_spawn : forall st target,
    rank_valid st -> rank_valid (R.request_spawn st target).
  Proof. intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); exact H. Qed.

  Lemma rank_extends_request_spawn : forall st target,
    rank_extends st (R.request_spawn st target).
  Proof.
    intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st));
      apply rank_extends_same_ranking; reflexivity.
  Qed.

  Lemma next_config_rank_valid :
    forall tf before after,
      rank_valid (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      rank_valid (R.cfg_state after).
  Proof.
    intros tf [st control] after Hvalid Hstep.
    cbn in Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn;
      eauto using rank_valid_request_spawn, rank_valid_observe, rank_valid_enqueue_handle,
        rank_valid_get_ready, rank_valid_dirty_get_ready, rank_valid_side_ready,
        rank_valid_mark_side_dirty,
        rank_valid_start_evaluation, rank_valid_materialize,
        rank_valid_set_value, rank_valid_remember_dormant.
    change (rank_valid (R.start_evaluation st (R.handle_variable h))).
    apply rank_valid_start_evaluation. cbn in Hvalid. exact Hvalid.
  Qed.

  Lemma steps_rank_valid :
    forall tf before after,
      rank_valid (R.cfg_state before) ->
      Sem.steps tf before after ->
      rank_valid (R.cfg_state after).
  Proof.
    intros tf before after Hvalid Hsteps. induction Hsteps.
    - exact Hvalid.
    - apply IHHsteps. eapply next_config_rank_valid; eauto.
  Qed.

  Lemma next_config_rank_extends :
    forall tf before after,
      R.next_config tf before = Some after ->
      rank_extends (R.cfg_state before) (R.cfg_state after).
  Proof.
    intros tf [st control] after Hstep.
    cbn in Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn;
      eauto using rank_extends_request_spawn, rank_extends_refl, rank_extends_observe,
        rank_extends_after_observe, rank_extends_with_queue,
        rank_extends_with_started, rank_extends_enqueue_handle,
        rank_extends_start_evaluation, rank_extends_materialize,
        rank_extends_get_ready, rank_extends_side_ready,
        rank_extends_dirty_get_ready,
        rank_extends_set_value, rank_extends_remember_dormant,
        rank_extends_add_reader, rank_extends_started_evaluation,
        rank_extends_remember_add_reader,
        rank_extends_after_observe_enqueue_get_ready,
        rank_extends_after_observe_side_enqueue,
        rank_extends_after_observe_side_mark,
        rank_extends_after_observe_side_mark_enqueue,
        rank_extends_after_observe_enqueue_materialize.
    all: apply rank_extends_same_ranking; reflexivity.
  Qed.

  Lemma steps_rank_extend :
    forall tf before after,
      Sem.steps tf before after ->
      rank_extends (R.cfg_state before) (R.cfg_state after).
  Proof.
    intros tf before after Hsteps. induction Hsteps.
    - apply rank_extends_refl.
    - eapply (@rank_extends_trans
        (R.cfg_state first) (R.cfg_state next) (R.cfg_state final)).
      + exact (@next_config_rank_extends tf first next H).
      + exact IHHsteps.
  Qed.
  Theorem reachable_rank_valid :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      rank_valid (R.cfg_state after).
  Proof.
    intros tf roots after Hsteps.
    eapply (@steps_rank_valid tf (R.initial_config roots) after).
    - cbn. apply empty_rank_valid.
    - exact Hsteps.
  Qed.

  Lemma handle_rank_equal_variable_equal :
    forall st left right,
      rank_valid st ->
      handle_valid st left ->
      handle_valid st right ->
      R.handle_rank left = R.handle_rank right ->
      R.handle_variable left = R.handle_variable right.
  Proof.
    intros st left right Hvalid Hleft Hright Hequal.
    eapply RankLaws.lookup_injective with (rank := R.handle_rank left).
    - exact Hvalid.
    - exact Hleft.
    - rewrite Hequal. exact Hright.
  Qed.

  Fixpoint continuation_valid (st : R.state) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        handle_valid st owner /\ continuation_valid st rest
    | R.KAfterGet owner target _ rest =>
        handle_valid st owner /\ handle_valid st target /\
        continuation_valid st rest
    end.

  Definition control_valid (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne owner rest
    | R.RunSolveOneLoop owner rest
    | R.RunRhs owner _ rest
    | R.AfterSide owner _ rest
    | R.AfterSpawn owner _ rest =>
        handle_valid st owner /\ continuation_valid st rest
    | R.AfterGet owner target _ rest =>
        handle_valid st owner /\ handle_valid st target /\
        continuation_valid st rest
    end.

  Definition queue_valid (st : R.state) : Prop :=
    Forall (handle_valid st) (R.queue st).

  Record handles_valid (c : R.config) : Prop := {
    handles_rank_valid : rank_valid (R.cfg_state c);
    handles_queue_valid : queue_valid (R.cfg_state c);
    handles_control_valid :
      control_valid (R.cfg_state c) (R.cfg_control c);
  }.

  Lemma continuation_valid_extended :
    forall before after k,
      rank_extends before after ->
      continuation_valid before k ->
      continuation_valid after k.
  Proof.
    intros before after k Hextends. induction k; cbn; intuition;
      eauto using handle_valid_extended.
  Qed.

  Lemma control_valid_extended :
    forall before after control,
      rank_extends before after ->
      control_valid before control ->
      control_valid after control.
  Proof.
    intros before after control Hextends. destruct control; cbn; intuition;
      eauto using handle_valid_extended, continuation_valid_extended.
  Qed.

  Lemma queue_list_valid_extended :
    forall before after queue,
      rank_extends before after ->
      Forall (handle_valid before) queue ->
      Forall (handle_valid after) queue.
  Proof.
    intros before after queue Hextends Hqueue. induction Hqueue; constructor;
      eauto using handle_valid_extended.
  Qed.

  Lemma queue_insert_fresh_valid :
    forall st entry queue,
      handle_valid st entry ->
      Forall (handle_valid st) queue ->
      Forall (handle_valid st) (R.queue_insert_fresh entry queue).
  Proof.
    intros st entry queue Hentry Hqueue.
    induction Hqueue as [|head rest Hhead Hrest IH].
    - cbn. constructor; [exact Hentry | constructor].
    - change (Forall (handle_valid st)
        (if Nat.ltb (R.handle_rank head) (R.handle_rank entry)
         then entry :: head :: rest
         else head :: R.queue_insert_fresh entry rest)).
      destruct (Nat.ltb (R.handle_rank head) (R.handle_rank entry)).
      + repeat constructor; assumption.
      + constructor; assumption.
  Qed.

  Lemma queue_insert_valid :
    forall st entry queue,
      handle_valid st entry ->
      Forall (handle_valid st) queue ->
      Forall (handle_valid st) (R.queue_insert entry queue).
  Proof.
    intros st entry queue Hentry Hqueue. unfold R.queue_insert.
    destruct (R.queue_contains_rank (R.handle_rank entry) queue);
      auto using queue_insert_fresh_valid.
  Qed.

  Lemma queue_pop_valid :
    forall st entry rest,
      queue_valid st ->
      R.queue_pop (R.queue st) = Some (entry, rest) ->
      handle_valid st entry /\
      Forall (handle_valid st) rest.
  Proof.
    intros st entry rest Hvalid Hpop. unfold queue_valid in Hvalid.
    destruct (R.queue st) as [|head tail]; cbn in Hpop; try discriminate.
    inversion Hpop; subst. now inversion Hvalid.
  Qed.

  Lemma continuation_valid_continue :
    forall st k,
      continuation_valid st k ->
      control_valid st (R.continue k).
  Proof. intros st k. destruct k; cbn; intuition. Qed.

  Lemma queue_valid_preserved :
    forall before after,
      rank_extends before after ->
      R.queue after = R.queue before ->
      queue_valid before ->
      queue_valid after.
  Proof.
    intros before after Hextends Hqueue Hvalid. unfold queue_valid in *.
    rewrite Hqueue. now apply queue_list_valid_extended with before.
  Qed.

  Lemma queue_valid_with_queue :
    forall st queue,
      Forall (handle_valid st) queue ->
      queue_valid (R.with_queue st queue).
  Proof. intros. exact H. Qed.

  Lemma queue_valid_observe :
    forall st x next entry,
      queue_valid st ->
      R.observe st x = (next, entry) ->
      queue_valid next.
  Proof.
    intros st x next entry Hvalid Hobserve.
    eapply queue_valid_preserved.
    - exact (@rank_extends_observe st x next entry Hobserve).
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) x); inversion Hobserve.
      reflexivity.
    - exact Hvalid.
  Qed.

  Lemma queue_valid_enqueue_handle :
    forall st entry,
      handle_valid st entry ->
      queue_valid st ->
      queue_valid (R.enqueue_handle st entry).
  Proof.
    intros st entry Hentry Hqueue. unfold queue_valid in *.
    apply queue_insert_valid; assumption.
  Qed.

  Lemma queue_valid_enqueue :
    forall st x,
      queue_valid st ->
      queue_valid (R.enqueue st x).
  Proof.
    intros st x Hqueue. unfold R.enqueue.
    destruct (R.observe st x) as [next entry] eqn:Hobserve.
    apply queue_valid_enqueue_handle.
    - exact (@observed_handle_valid st x next entry Hobserve).
    - exact (@queue_valid_observe st x next entry Hqueue Hobserve).
  Qed.

  Lemma queue_valid_enqueue_all :
    forall xs st,
      queue_valid st ->
      queue_valid (R.enqueue_all st xs).
  Proof.
    induction xs as [|x xs IH]; intros st Hvalid; cbn; auto.
    apply IH. now apply queue_valid_enqueue.
  Qed.
  Lemma queue_contains_rank_true :
    forall rank queue,
      R.queue_contains_rank rank queue = true ->
      exists entry, List.In entry queue /\ R.handle_rank entry = rank.
  Proof.
    intros rank queue. induction queue as [|head rest IH]; intros Hcontains;
      cbn in Hcontains; try discriminate.
    destruct (PeanoNat.Nat.eq_dec rank (R.handle_rank head)) as [Heq | Hneq].
    - exists head. split; [now left |lia].
    - destruct (IH Hcontains) as [entry [Hin Hrank]].
      exists entry. split; [now right |exact Hrank].
  Qed.

  Lemma queue_insert_fresh_inserted :
    forall inserted queue,
      List.In inserted (R.queue_insert_fresh inserted queue).
  Proof.
    intros inserted queue. induction queue as [|head rest IH]; [now left |].
    change (List.In inserted
      (if Nat.ltb (R.handle_rank head) (R.handle_rank inserted)
       then inserted :: head :: rest
       else head :: R.queue_insert_fresh inserted rest)).
    destruct (Nat.ltb (R.handle_rank head) (R.handle_rank inserted));
      [now left |now right].
  Qed.

  Lemma enqueue_handle_queues_variable :
    forall st inserted,
      rank_valid st -> queue_valid st -> handle_valid st inserted ->
      queued (R.enqueue_handle st inserted)
        (R.handle_variable inserted).
  Proof.
    intros st inserted Hrank Hqueue Hinserted.
    unfold R.enqueue_handle, queued. cbn.
    unfold R.queue_insert.
    destruct (R.queue_contains_rank (R.handle_rank inserted) (R.queue st))
      eqn:Hcontains.
    - destruct (@queue_contains_rank_true (R.handle_rank inserted)
        (R.queue st) Hcontains) as [entry [Hin Hranks]].
      exists entry. split; [exact Hin |].
      symmetry. eapply handle_rank_equal_variable_equal; eauto.
      unfold queue_valid in Hqueue.
      now apply Forall_forall with (x := entry) in Hqueue.
    - exists inserted. split; [apply queue_insert_fresh_inserted |reflexivity].
  Qed.

  Lemma enqueue_queues_variable :
    forall st inserted,
      rank_valid st -> queue_valid st ->
      queued (R.enqueue st inserted) inserted.
  Proof.
    intros st inserted Hrank Hqueue. unfold R.enqueue.
    destruct (R.observe st inserted) as [next entry] eqn:Hobserve.
    unfold queued. rewrite <- (@observed_handle_variable
      st inserted next entry Hobserve).
    apply enqueue_handle_queues_variable.
    - eapply rank_valid_observe; eauto.
    - eapply queue_valid_observe; eauto.
    - eapply observed_handle_valid; eauto.
  Qed.

  Lemma enqueue_all_contains :
    forall xs st inserted,
      List.In inserted xs ->
      rank_valid st -> queue_valid st ->
      queued (R.enqueue_all st xs) inserted.
  Proof.
    induction xs as [|head rest IH]; intros st inserted Hin Hrank Hqueue;
      cbn in *; [contradiction |].
    destruct Hin as [-> | Hin].
    - unfold queued. apply queued_enqueue_all.
      unfold queued in *. now apply enqueue_queues_variable.
    - apply IH; [exact Hin |now apply rank_valid_enqueue |].
      now apply queue_valid_enqueue.
  Qed.


  Lemma readers_enqueue_all : forall xs st,
    R.readers (R.enqueue_all st xs) = R.readers st.
  Proof.
    induction xs; intros; cbn; [reflexivity|]. rewrite IHxs.
    unfold R.enqueue, R.observe. destruct (R.Ranking.observe _ _); reflexivity.
  Qed.

  Lemma read_obligation_write_changed_value :
    forall st owner value reader target,
      rank_valid st -> queue_valid st ->
      reader_registered st reader target \/ queued st reader ->
      reader_registered (R.write_changed_value st owner value) reader target \/
      queued (R.write_changed_value st owner value) reader.
  Proof.
    intros st owner value reader target Hrank Hqueue
      [Hregistered | Hqueued].
    - destruct (V.eq_dec target owner) as [-> | Hneq].
      + right. unfold R.write_changed_value. cbn.
        apply enqueue_all_contains.
        * apply SL.mem_spec. exact Hregistered.
        * exact Hrank.
        * exact Hqueue.
      + left. unfold reader_registered, R.write_changed_value,
          R.lookup_set in *. cbn.
        rewrite readers_enqueue_all.
        rewrite ML.lookup_update_other by exact Hneq. exact Hregistered.
    - right. unfold queued in *.
      unfold R.write_changed_value. cbn.
      now apply queued_enqueue_all.
  Qed.

  Lemma read_guarded_write_changed_value :
    forall st reader event owner value,
      rank_valid st -> queue_valid st ->
      read_guarded st reader event ->
      read_guarded (R.write_changed_value st owner value) reader event.
  Proof.
    intros st reader [target observed] owner value Hrank Hqueue
      [Hsolved [Hread Hvalue]]. repeat split.
    - apply E.write_changed_value_solved. exact Hsolved.
    - eapply read_obligation_write_changed_value; eauto.
    - destruct Hvalue as [Heq | Hqueued].
      + destruct (V.eq_dec target owner) as [-> | Hneq].
        * right. destruct Hread as [Hregistered | Hqueued].
          -- unfold R.write_changed_value. cbn. apply enqueue_all_contains.
             ++ apply SL.mem_spec. exact Hregistered.
             ++ exact Hrank.
             ++ exact Hqueue.
          -- unfold queued in *. unfold R.write_changed_value. cbn.
             now apply queued_enqueue_all.
        * left. rewrite semantic_lookup_write_changed_other by exact Hneq.
          exact Heq.
      + right. unfold queued in *. unfold R.write_changed_value. cbn.
        now apply queued_enqueue_all.
  Qed.

  Lemma read_guarded_set_value :
    forall st reader event owner direct,
      rank_valid st -> queue_valid st ->
      read_guarded st reader event ->
      read_guarded (R.set_value st owner direct) reader event.
  Proof.
    intros st reader event owner direct Hrank Hqueue Hguarded.
    unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hguarded |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner)).
      + unfold read_guarded, reader_registered, queued in *. exact Hguarded.
      + apply read_guarded_write_changed_value; assumption.
    - apply read_guarded_write_changed_value; assumption.
  Qed.

  Lemma reads_guarded_set_value :
    forall st reader reads owner direct,
      rank_valid st -> queue_valid st ->
      reads_guarded st reader reads ->
      reads_guarded (R.set_value st owner direct) reader reads.
  Proof.
    intros. eapply Forall_impl; [|exact H1].
    intros. eapply read_guarded_set_value; eauto.
  Qed.

  Lemma effects_recorded_write_changed_value :
    forall st source effects owner value,
      effects_recorded st source effects ->
      effects_recorded (R.write_changed_value st owner value) source effects.
  Proof.
    intros st source effects owner value Hrecorded.
    unfold effects_recorded, effect_recorded in *.
    rewrite write_changed_value_contributions. exact Hrecorded.
  Qed.

  Lemma effects_recorded_set_value :
    forall st source effects owner direct,
      effects_recorded st source effects ->
      effects_recorded (R.set_value st owner direct) source effects.
  Proof.
    intros st source effects owner direct Hrecorded.
    unfold effects_recorded, effect_recorded in *.
    unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hrecorded |].
    destruct (S.mem owner (R.controlled st));
      [|now apply effects_recorded_write_changed_value].
    destruct (U.update false owner (R.stored_phase st owner)
      (R.sigma_value st owner)
      (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
    destruct (R.equivalent value (R.sigma_value st owner));
      [exact Hrecorded |now apply effects_recorded_write_changed_value].
  Qed.

  Lemma rhs_progress_ret_summary :
    forall tf st owner direct,
      rank_valid st -> queue_valid st ->
      rhs_progress tf st owner (R.ConstraintSystem.Ret direct) ->
      summary_valid tf (R.set_value st owner direct) owner.
  Proof.
    intros tf st owner direct Hrank Hqueue
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists direct, reads, effects. repeat split.
    - apply rhs_prefix_complete. exact Hprefix.
    - eapply reads_guarded_set_value; eauto.
    - apply effects_recorded_set_value. exact Hrecorded.
    - apply set_value_covers_direct.
  Qed.

  Lemma queue_valid_materialize :
    forall st x,
      queue_valid st -> queue_valid (R.materialize st x).
  Proof.
    intros st x. apply queue_valid_preserved.
    - apply rank_extends_materialize.
    - unfold R.materialize. destruct (R.is_materialized st x); reflexivity.
  Qed.

  Lemma queue_valid_start_evaluation :
    forall st owner,
      queue_valid st -> queue_valid (R.start_evaluation st owner).
  Proof.
    intros st owner. apply queue_valid_preserved.
    - apply rank_extends_start_evaluation.
    - unfold R.start_evaluation, R.reset_local_sides, R.materialize.
      destruct (R.is_materialized st owner); reflexivity.
  Qed.

  Lemma queue_valid_get_ready :
    forall st owner target,
      queue_valid st -> queue_valid (R.get_ready_state st owner target).
  Proof.
    intros st owner target. apply queue_valid_preserved.
    - apply rank_extends_get_ready.
    - unfold R.get_ready_state, R.promote_controlled, R.add_reader,
        R.materialize.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ (R.handle_variable target));
        reflexivity.
  Qed.

  Lemma queue_valid_side_ready :
    forall st source target raw,
      queue_valid st -> queue_valid (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw. apply queue_valid_preserved.
    - apply rank_extends_side_ready.
    - unfold R.side_ready_state, R.record_side_payload,
        R.promote_controlled.
      destruct (side_update_result st (R.handle_variable source)
        (R.handle_variable target) raw);
        destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
        reflexivity.
  Qed.

  Lemma queue_valid_write_changed :
    forall st owner value,
      queue_valid st -> queue_valid (R.write_changed_value st owner value).
  Proof.
    intros st owner value Hvalid. unfold R.write_changed_value.
    apply queue_valid_preserved with
      (before := R.enqueue_all
        (R.with_sigma st (M.update (R.sigma st) owner value))
        (S.elements (R.lookup_set (R.readers st) owner))).
    - apply rank_extends_same_ranking. reflexivity.
    - reflexivity.
    - apply queue_valid_enqueue_all. exact Hvalid.
  Qed.

  Lemma queue_remove_rank_valid :
    forall st rank queue,
      Forall (handle_valid st) queue ->
      Forall (handle_valid st) (R.queue_remove_rank rank queue).
  Proof.
    intros st rank queue Hvalid. induction Hvalid as [|head rest Hhead Hrest IH].
    - constructor.
    - cbn. destruct (Nat.eqb rank (R.handle_rank head)).
      + exact Hrest.
      + constructor; assumption.
  Qed.

  Lemma queue_valid_cancel_dirty_target :
    forall st target,
      queue_valid st -> queue_valid (R.cancel_dirty_target st target).
  Proof.
    intros st target Hvalid. unfold queue_valid in *.
    unfold R.cancel_dirty_target. cbn.
    now apply queue_remove_rank_valid.
  Qed.

  Lemma queue_valid_try_dirty_read :
    forall tf st owner target next,
      queue_valid st ->
      R.try_dirty_read tf st owner target = Some next ->
      queue_valid next.
  Proof.
    intros tf st owner target next Hvalid Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using queue_valid_write_changed,
        queue_valid_cancel_dirty_target.
  Qed.

  Lemma queue_valid_dirty_get_ready :
    forall tf st owner target,
      queue_valid st ->
      queue_valid (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target Hvalid. unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hvalid. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - apply queue_valid_try_dirty_read in Hread; auto.
    - exact Hprepared.
  Qed.

  Lemma queue_valid_set_value :
    forall st owner direct,
      queue_valid st -> queue_valid (R.set_value st owner direct).
  Proof.
    intros st owner direct Hvalid. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner)).
    - exact Hvalid.
    - destruct (S.mem owner (R.controlled st)).
      + destruct (U.update false owner (R.stored_phase st owner)
          (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
          as [phase output]; cbn.
        destruct (R.equivalent output (R.sigma_value st owner)).
        * exact Hvalid.
        * apply queue_valid_write_changed. exact Hvalid.
      + apply queue_valid_write_changed. exact Hvalid.
  Qed.

  Lemma initial_handles_valid :
    forall roots, handles_valid (R.initial_config roots).
  Proof.
    intros roots. constructor; cbn.
    - apply empty_rank_valid.
    - constructor.
    - exact I.
  Qed.


  Lemma queue_valid_request_spawn : forall st target,
    queue_valid st -> queue_valid (R.request_spawn st target).
  Proof. intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); exact H. Qed.

  Lemma queue_valid_with_started : forall st next,
    queue_valid st -> queue_valid (R.with_started st next).
  Proof. intros; exact H. Qed.
  Lemma queue_valid_mark_side_dirty : forall st target,
    queue_valid st -> queue_valid (R.mark_side_dirty st target).
  Proof. intros; exact H. Qed.
  Lemma handle_valid_mark_side_dirty : forall st target entry,
    handle_valid st entry -> handle_valid (R.mark_side_dirty st target) entry.
  Proof. intros; exact H. Qed.
  Lemma handle_valid_side_ready : forall st owner target raw entry,
    handle_valid st entry -> handle_valid (R.side_ready_state st owner target raw) entry.
  Proof. intros. eapply handle_valid_extended; [apply rank_extends_side_ready|exact H]. Qed.
  Lemma handle_valid_materialize : forall st target entry,
    handle_valid st entry -> handle_valid (R.materialize st target) entry.
  Proof. intros. eapply handle_valid_extended; [apply rank_extends_materialize|exact H]. Qed.
  Lemma handle_valid_enqueue_handle : forall st added entry,
    handle_valid st entry -> handle_valid (R.enqueue_handle st added) entry.
  Proof. intros; exact H. Qed.
  Lemma handle_valid_get_ready : forall st owner target entry,
    handle_valid st entry -> handle_valid (R.get_ready_state st owner target) entry.
  Proof. intros. eapply handle_valid_extended; [apply rank_extends_get_ready|exact H]. Qed.

  Create HintDb valid_handles.
  #[local] Hint Resolve queue_valid_materialize queue_valid_start_evaluation queue_valid_get_ready
    queue_valid_side_ready queue_valid_dirty_get_ready queue_valid_set_value queue_valid_request_spawn
    queue_valid_observe queue_valid_enqueue_handle observed_handle_valid
    rank_extends_materialize rank_extends_side_ready rank_extends_get_ready rank_extends_enqueue_handle
    handle_valid_mark_side_dirty handle_valid_side_ready handle_valid_materialize
    handle_valid_enqueue_handle handle_valid_get_ready
    queue_valid_with_started queue_valid_mark_side_dirty : valid_handles.

  Lemma next_config_queue_valid : forall tf before after,
    queue_valid (R.cfg_state before) -> R.next_config tf before = Some after ->
    queue_valid (R.cfg_state after).
  Proof.
    intros tf [st control] after Hqueue Hstep.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control] in Hstep, Hqueue |- *;
      repeat match type of Hstep with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion Hstep; subst; cbn [R.cfg_state].
    all: try match goal with
    | Hpop : R.queue_pop (R.queue ?base) = Some (?entry, ?rest) |- _ =>
      destruct (@queue_pop_valid base entry rest Hqueue Hpop)
    end.
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      pose proof (@queue_valid_observe base target next entry Hqueue Hobs);
      pose proof (@observed_handle_valid base target next entry Hobs)
    end.
    all: try solve [eauto 6 with valid_handles].
  Qed.

  Lemma next_config_control_valid : forall tf before after,
    queue_valid (R.cfg_state before) -> control_valid (R.cfg_state before) (R.cfg_control before) ->
    R.next_config tf before = Some after -> control_valid (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hqueue Hcontrol Hstep.
    pose proof (@next_config_rank_extends tf
      {| R.cfg_state := st; R.cfg_control := control |} after Hstep) as Hextends.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control control_valid] in Hstep, Hqueue, Hcontrol;
      repeat match type of Hstep with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion Hstep; subst; cbn [R.cfg_state R.cfg_control] in *.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try match goal with
    | Hpop : R.queue_pop (R.queue ?base) = Some (?entry, ?rest) |- _ =>
      destruct (@queue_pop_valid base entry rest Hqueue Hpop)
    end.
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      pose proof (@observed_handle_valid base target next entry Hobs)
    end.
    all: cbn [control_valid continuation_valid]; repeat split;
      eauto 4 using handle_valid_extended, continuation_valid_extended, continuation_valid_continue with valid_handles.
  Qed.

  Lemma next_config_handles_valid : forall tf before after,
    handles_valid before -> R.next_config tf before = Some after -> handles_valid after.
  Proof.
    intros tf before after [Hr Hq Hc] Hstep. constructor.
    - eapply next_config_rank_valid; eauto.
    - eapply next_config_queue_valid; eauto.
    - eapply next_config_control_valid; eauto.
  Qed.
  Lemma steps_handles_valid :
    forall tf before after,
      handles_valid before ->
      Sem.steps tf before after ->
      handles_valid after.
  Proof.
    intros tf before after Hvalid Hsteps. induction Hsteps; auto.
    apply IHHsteps. eapply next_config_handles_valid; eauto.
  Qed.

  Theorem reachable_handles_valid :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      handles_valid after.
  Proof.
    intros tf roots after Hsteps. eapply steps_handles_valid; eauto.
    apply initial_handles_valid.
  Qed.
  Definition rank_above (higher lower : R.handle) : Prop :=
    R.handle_rank lower < R.handle_rank higher.

  Definition queue_ordered (queue : R.work_queue) : Prop :=
    StronglySorted rank_above queue.

  Lemma queue_contains_false_rank_neq :
    forall rank queue,
      R.queue_contains_rank rank queue = false ->
      forall entry,
        List.In entry queue -> R.handle_rank entry <> rank.
  Proof.
    intros rank queue. induction queue as [|head rest IH];
      intros Hcontains entry Hin; cbn in *; [contradiction |].
    destruct (PeanoNat.Nat.eq_dec rank (R.handle_rank head))
      as [Heq | Hneq]; try discriminate.
    destruct Hin as [-> | Hin]; [lia |].
    now apply (IH Hcontains entry Hin).
  Qed.

  Lemma queue_insert_fresh_members :
    forall entry queue observed,
      List.In observed (R.queue_insert_fresh entry queue) ->
      observed = entry \/ List.In observed queue.
  Proof.
    intros entry queue. induction queue as [|head rest IH]; intros observed Hin.
    - cbn in Hin. destruct Hin as [-> | []]. now left.
    - change (List.In observed
        (if Nat.ltb (R.handle_rank head) (R.handle_rank entry)
         then entry :: head :: rest
         else head :: R.queue_insert_fresh entry rest)) in Hin.
      destruct (Nat.ltb (R.handle_rank head) (R.handle_rank entry)).
      + cbn in Hin. destruct Hin as [-> | Hin]; [now left | now right].
      + cbn in Hin. destruct Hin as [-> | Hin].
        * right. now left.
        * destruct (IH observed Hin); [now left | right; now right].
  Qed.

  Lemma queue_insert_fresh_ordered :
    forall entry queue,
      queue_ordered queue ->
      (forall old, List.In old queue ->
        R.handle_rank old <> R.handle_rank entry) ->
      queue_ordered (R.queue_insert_fresh entry queue).
  Proof.
    intros entry queue Hordered. induction Hordered as
      [|head rest Hrest IH Hall]; intros Hfresh.
    - cbn. constructor; [constructor |constructor].
    - change (queue_ordered
        (if Nat.ltb (R.handle_rank head) (R.handle_rank entry)
         then entry :: head :: rest
         else head :: R.queue_insert_fresh entry rest)).
      destruct (Nat.ltb (R.handle_rank head) (R.handle_rank entry))
        eqn:Hcompare.
      + constructor.
        * constructor; assumption.
        * apply Forall_forall. intros old [-> | Hin].
          -- unfold rank_above. now apply Nat.ltb_lt.
          -- unfold rank_above. apply Nat.ltb_lt in Hcompare.
             apply Forall_forall with (x := old) in Hall; auto.
             unfold rank_above in Hall. lia.
      + constructor.
        * apply IH. intros old Hin. apply Hfresh. now right.
        * apply Forall_forall. intros old Hin.
          apply queue_insert_fresh_members in Hin.
          destruct Hin as [-> | Hin].
          -- unfold rank_above. apply Nat.ltb_ge in Hcompare.
             assert (R.handle_rank head <> R.handle_rank entry).
             { apply Hfresh. now left. }
             lia.
          -- apply Forall_forall with (x := old) in Hall; assumption.
  Qed.

  Lemma queue_insert_ordered :
    forall entry queue,
      queue_ordered queue -> queue_ordered (R.queue_insert entry queue).
  Proof.
    intros entry queue Hordered. unfold R.queue_insert.
    destruct (R.queue_contains_rank (R.handle_rank entry) queue)
      eqn:Hcontains; [exact Hordered |].
    apply queue_insert_fresh_ordered; [exact Hordered |].
    intros old Hin. now apply queue_contains_false_rank_neq with queue.
  Qed.

  Lemma queue_pop_ordered :
    forall queue head rest,
      queue_ordered queue ->
      R.queue_pop queue = Some (head, rest) ->
      queue_ordered rest /\
      forall entry, List.In entry rest ->
        R.handle_rank entry < R.handle_rank head.
  Proof.
    intros queue head rest Hordered Hpop.
    destruct queue as [|first tail]; cbn in Hpop; try discriminate.
    inversion Hpop; subst. inversion Hordered; subst. split; [assumption |].
    intros entry Hin. apply Forall_forall with (x := entry) in H2; auto.
  Qed.

  Lemma queue_remove_rank_members :
    forall rank queue entry,
      List.In entry (R.queue_remove_rank rank queue) ->
      List.In entry queue.
  Proof.
    intros rank queue. induction queue as [|head rest IH]; intros entry Hin.
    - contradiction.
    - cbn in Hin. destruct (Nat.eqb rank (R.handle_rank head)).
      + now right.
      + destruct Hin as [-> | Hin]; [now left | right; now apply IH].
  Qed.

  Lemma queue_remove_rank_preserves_neq :
    forall rank queue entry,
      R.handle_rank entry <> rank ->
      List.In entry queue ->
      List.In entry (R.queue_remove_rank rank queue).
  Proof.
    intros rank queue. induction queue as [|head rest IH];
      intros entry Hneq Hin; [contradiction |].
    cbn. destruct (Nat.eqb rank (R.handle_rank head)) eqn:Heq.
    - apply Nat.eqb_eq in Heq. destruct Hin as [-> | Hin].
      + exfalso. apply Hneq. symmetry. exact Heq.
      + exact Hin.
    - destruct Hin as [-> | Hin]; [now left |right; now apply IH].
  Qed.

  Lemma queue_remove_rank_ordered :
    forall rank queue,
      queue_ordered queue ->
      queue_ordered (R.queue_remove_rank rank queue).
  Proof.
    intros rank queue Hordered. induction Hordered as
      [|head rest Hrest IH Hall].
    - constructor.
    - cbn. destruct (Nat.eqb rank (R.handle_rank head)).
      + exact Hrest.
      + constructor; [exact IH |].
        apply Forall_forall. intros entry Hin.
        apply Forall_forall with (x := entry) in Hall.
        * exact Hall.
        * now apply queue_remove_rank_members in Hin.
  Qed.

  Definition state_queue_ordered (st : R.state) : Prop :=
    queue_ordered (R.queue st).

  Lemma enqueue_handle_ordered :
    forall st entry,
      state_queue_ordered st ->
      state_queue_ordered (R.enqueue_handle st entry).
  Proof. intros. now apply queue_insert_ordered. Qed.

  Lemma enqueue_ordered :
    forall st x,
      state_queue_ordered st -> state_queue_ordered (R.enqueue st x).
  Proof.
    intros st x Hordered. unfold R.enqueue.
    destruct (R.observe st x) as [next entry] eqn:Hobserve.
    apply enqueue_handle_ordered. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x); inversion Hobserve; subst.
    exact Hordered.
  Qed.

  Lemma enqueue_all_ordered :
    forall xs st,
      state_queue_ordered st -> state_queue_ordered (R.enqueue_all st xs).
  Proof.
    induction xs as [|x xs IH]; intros st Hordered; cbn; auto.
    apply IH. now apply enqueue_ordered.
  Qed.

  Lemma observe_ordered :
    forall st x next entry,
      state_queue_ordered st ->
      R.observe st x = (next, entry) ->
      state_queue_ordered next.
  Proof.
    intros st x next entry Hordered Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x);
      inversion Hobserve; subst. exact Hordered.
  Qed.

  Lemma start_evaluation_ordered :
    forall st owner,
      state_queue_ordered st ->
      state_queue_ordered (R.start_evaluation st owner).
  Proof.
    intros st owner Hordered.
    unfold R.start_evaluation, R.reset_local_sides, R.materialize.
    destruct (R.is_materialized st owner); exact Hordered.
  Qed.

  Lemma get_ready_ordered :
    forall st owner target,
      state_queue_ordered st ->
      state_queue_ordered (R.get_ready_state st owner target).
  Proof.
    intros st owner target Hordered.
    unfold R.get_ready_state, R.promote_controlled, R.add_reader,
      R.materialize.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      destruct (R.is_materialized _ (R.handle_variable target));
      exact Hordered.
  Qed.

  Lemma side_ready_ordered :
    forall st source target raw,
      state_queue_ordered st ->
      state_queue_ordered (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw Hordered.
    unfold R.side_ready_state, R.record_side_payload, R.promote_controlled.
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hordered.
  Qed.

  Lemma mark_side_dirty_ordered :
    forall st target,
      state_queue_ordered st ->
      state_queue_ordered (R.mark_side_dirty st target).
  Proof. intros st target Hordered. exact Hordered. Qed.

  Lemma materialize_ordered :
    forall st target,
      state_queue_ordered st ->
      state_queue_ordered (R.materialize st target).
  Proof.
    intros st target Hordered. unfold R.materialize.
    destruct (R.is_materialized st target); exact Hordered.
  Qed.

  Lemma write_changed_value_ordered :
    forall st owner value,
      state_queue_ordered st ->
      state_queue_ordered (R.write_changed_value st owner value).
  Proof.
    intros st owner value Hordered. unfold R.write_changed_value.
    apply enqueue_all_ordered. exact Hordered.
  Qed.

  Lemma cancel_dirty_target_ordered :
    forall st target,
      state_queue_ordered st ->
      state_queue_ordered (R.cancel_dirty_target st target).
  Proof.
    intros st target Hordered. unfold state_queue_ordered in *.
    unfold R.cancel_dirty_target. cbn.
    now apply queue_remove_rank_ordered.
  Qed.

  Lemma try_dirty_read_ordered :
    forall tf st owner target next,
      state_queue_ordered st ->
      R.try_dirty_read tf st owner target = Some next ->
      state_queue_ordered next.
  Proof.
    intros tf st owner target next Hordered Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using write_changed_value_ordered,
        cancel_dirty_target_ordered.
  Qed.

  Lemma dirty_get_ready_ordered :
    forall tf st owner target,
      state_queue_ordered st ->
      state_queue_ordered (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target Hordered. unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : state_queue_ordered prepared).
    { subst prepared. apply materialize_ordered.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hordered. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - change (state_queue_ordered next).
      eapply try_dirty_read_ordered; eauto.
    - change (state_queue_ordered prepared). exact Hprepared.
  Qed.

  Lemma set_value_ordered :
    forall st owner direct,
      state_queue_ordered st ->
      state_queue_ordered (R.set_value st owner direct).
  Proof.
    intros st owner direct Hordered. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner)).
    - exact Hordered.
    - destruct (S.mem owner (R.controlled st)).
      + destruct (U.update false owner (R.stored_phase st owner)
          (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
          as [phase value]; cbn.
        destruct (R.equivalent value (R.sigma_value st owner)); auto.
        now apply write_changed_value_ordered.
      + now apply write_changed_value_ordered.
  Qed.

  Lemma request_spawn_ordered : forall st target,
    state_queue_ordered st -> state_queue_ordered (R.request_spawn st target).
  Proof. intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); exact H. Qed.

  Lemma next_config_queue_ordered :
    forall tf before after,
      state_queue_ordered (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      state_queue_ordered (R.cfg_state after).
  Proof.
    intros tf [st control] after Hordered Hstep.
    cbn in Hordered, Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; clear Hstep; cbn;
      eauto 5 using request_spawn_ordered, queue_pop_ordered, observe_ordered,
        start_evaluation_ordered, get_ready_ordered, dirty_get_ready_ordered,
        side_ready_ordered, mark_side_dirty_ordered,
        materialize_ordered, enqueue_handle_ordered, set_value_ordered.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest),
        Hord : state_queue_ordered ?before
        |- state_queue_ordered (R.with_queue ?before ?rest) =>
          exact (proj1 (@queue_pop_ordered
            (R.queue before) head rest Hord Hpop))
      end.
    apply start_evaluation_ordered. exact Hordered.
  Qed.

  Lemma steps_queue_ordered :
    forall tf before after,
      state_queue_ordered (R.cfg_state before) ->
      Sem.steps tf before after ->
      state_queue_ordered (R.cfg_state after).
  Proof.
    intros tf before after Hordered Hsteps. induction Hsteps; auto.
    apply IHHsteps. eapply next_config_queue_ordered; eauto.
  Qed.

  Theorem reachable_queue_ordered :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      state_queue_ordered (R.cfg_state after).
  Proof.
    intros tf roots after Hsteps. eapply steps_queue_ordered; [|exact Hsteps].
    constructor.
  Qed.

  Definition queue_strictly_below (owner : R.handle) (st : R.state) : Prop :=
    forall queued,
      List.In queued (R.queue st) ->
      R.handle_rank queued < R.handle_rank owner.

  Theorem owner_may_false_queue_below :
    forall st owner,
      rank_valid st ->
      handle_valid st owner ->
      queue_valid st ->
      state_queue_ordered st ->
      R.owner_may_still_be_queued st owner = false ->
      queue_strictly_below owner st.
  Proof.
    intros st owner Hrank Howner Hhandles Hordered Hmay queued Hqueued.
    unfold state_queue_ordered in Hordered.
    unfold R.owner_may_still_be_queued in Hmay.
    destruct (R.queue st) as [|head rest] eqn:Hqueue; [contradiction |].
    cbn in Hmay. destruct (V.eq_dec (R.handle_variable head)
      (R.handle_variable owner)) as [Heq | Hneq]; try discriminate.
    apply Nat.ltb_ge in Hmay.
    assert (Hhead : handle_valid st head).
    {
      unfold queue_valid in Hhandles. rewrite Hqueue in Hhandles.
      inversion Hhandles. assumption.
    }
    assert (Hranks_neq : R.handle_rank head <> R.handle_rank owner).
    {
      intro Hranks. apply Hneq.
      exact (@handle_rank_equal_variable_equal
        st head owner Hrank Hhead Howner Hranks).
    }
    assert (Hhead_below : R.handle_rank head < R.handle_rank owner) by lia.
    inversion Hordered; subst. destruct Hqueued as [-> | Hqueued].
    - exact Hhead_below.
    - apply Forall_forall with (x := queued) in H2; auto.
      unfold rank_above in H2. lia.
  Qed.

  Corollary reachable_owner_may_false_queue_below :
    forall tf roots before owner,
      Sem.steps tf (R.initial_config roots) before ->
      handle_valid (R.cfg_state before) owner ->
      R.owner_may_still_be_queued (R.cfg_state before) owner = false ->
      queue_strictly_below owner (R.cfg_state before).
  Proof.
    intros tf roots before owner Hsteps Howner Hmay.
    pose proof (reachable_handles_valid Hsteps) as Hhandles.
    apply owner_may_false_queue_below.
    - exact (handles_rank_valid Hhandles).
    - exact Howner.
    - exact (handles_queue_valid Hhandles).
    - exact (reachable_queue_ordered Hsteps).
    - exact Hmay.
  Qed.
  Lemma rhs_trace_spawn_closed : forall st body direct reads effects,
    rhs_trace body direct reads effects ->
    (forall target value, In (target, value) reads -> R.semantic_lookup st target = Some value) ->
    forall result, Sem.observes_at (R.sigma_value st) body result ->
    forall target, In target (Sem.observed_spawns result) -> spawned target.
  Proof.
    intros st body direct reads effects Htrace. induction Htrace;
      intros Hagree result [Hobs Hreads] target' Hin;
      inversion Hobs; subst; cbn in *.
    - contradiction.
    - assert (Hvalue : value = value0).
      { pose proof (Hreads target value0 (or_introl eq_refl)) as Hvalue0.
        pose proof (Hagree target value (or_introl eq_refl)) as Hlookup.
        pose proof (@semantic_lookup_solved st target (ex_intro _ value Hlookup)) as Hsigma.
        rewrite Hlookup in Hsigma. inversion Hsigma. congruence. }
      subst value0. eapply IHHtrace.
      + intros read v Hread. apply Hagree. right. exact Hread.
      + split; [eassumption |]. intros read v Hread. apply Hreads. right. exact Hread.
      + exact Hin.
    - eapply IHHtrace; [exact Hagree |split; eassumption |exact Hin].
    - destruct Hin as [<- | Hin]; [assumption |].
      eapply IHHtrace; [exact Hagree |split; eassumption |exact Hin].
  Qed.

  End SpawnTraces.

  Module ControlStack.
  Fixpoint continuation_ordered
    (current : R.handle) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterGet owner _ _ rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        Nat.ltb (R.handle_rank owner) (R.handle_rank current) = true /\
        continuation_ordered owner rest
    end.

  Definition control_ordered (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne owner rest
    | R.RunSolveOneLoop owner rest
    | R.RunRhs owner _ rest
    | R.AfterGet owner _ _ rest
    | R.AfterSide owner _ rest
    | R.AfterSpawn owner _ rest => continuation_ordered owner rest
    end.

  Lemma continuation_ordered_continue :
    forall owner k,
      continuation_ordered owner k -> control_ordered (R.continue k).
  Proof. intros owner k Hordered. destruct k; cbn in *; tauto. Qed.

  Lemma owner_may_pop_higher :
    forall st owner next rest,
      R.owner_may_still_be_queued st owner = true ->
      R.queue_pop (R.queue st) = Some (next, rest) ->
      R.handle_variable next <> R.handle_variable owner ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank next) = true.
  Proof.
    intros st owner next rest Hmay Hpop Hneq.
    unfold R.owner_may_still_be_queued in Hmay.
    destruct (R.queue st) as [|head tail] eqn:Hqueue; cbn in Hpop;
      try discriminate.
    inversion Hpop; subst. cbn in Hmay.
    destruct (V.eq_dec (R.handle_variable next)
      (R.handle_variable owner)); contradiction || assumption.
  Qed.

  Theorem next_config_control_ordered :
    forall tf before after,
      control_ordered (R.cfg_control before) ->
      R.next_config tf before = Some after ->
      control_ordered (R.cfg_control after).
  Proof.
    intros tf [st control] after Hordered Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hordered; try exact I.
    1: (split;
      [eapply ControlStack.owner_may_pop_higher; eauto | exact Hordered]).
    1: exact (ControlStack.continuation_ordered_continue h c Hordered).
    all: try (split; [assumption | exact Hordered]).
    all: repeat match goal with
      | H : andb _ _ = true |- _ =>
          apply Bool.andb_true_iff in H; destruct H
      end.
    all: (repeat split; assumption).
  Qed.

  Lemma steps_control_ordered :
    forall tf before after,
      control_ordered (R.cfg_control before) ->
      Sem.steps tf before after ->
      control_ordered (R.cfg_control after).
  Proof.
    intros tf before after Hordered Hsteps. induction Hsteps; auto.
    apply IHHsteps. eapply next_config_control_ordered; eauto.
  Qed.

  Theorem reachable_control_ordered :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      control_ordered (R.cfg_control after).
  Proof.
    intros tf roots after Hsteps. eapply steps_control_ordered; eauto.
    exact I.
  Qed.
  End ControlStack.

  Module Progress.
  Definition solved (st : R.state) (x : V.t) : Prop :=
    exists value, M.lookup (R.sigma st) x = Some value.

  Lemma solved_is_materialized :
    forall st x, solved st x <-> R.is_materialized st x = true.
  Proof.
    intros st x. unfold solved, R.is_materialized.
    destruct (M.lookup (R.sigma st) x); cbn; split; intros H; eauto;
      try discriminate; destruct H as [? H]; discriminate.
  Qed.

  Lemma solved_same_sigma :
    forall before after x,
      R.sigma after = R.sigma before ->
      solved before x -> solved after x.
  Proof.
    intros before after x Hsigma [value Hlookup].
    exists value. cbn in *. now rewrite Hsigma.
  Qed.

  Lemma solved_update :
    forall st owner value x,
      solved st x ->
      solved (R.with_sigma st (M.update (R.sigma st) owner value)) x.
  Proof.
    intros st owner value x [old Hold]. unfold solved. cbn.
    destruct (V.eq_dec x owner) as [-> | Hneq].
    - exists value. apply ML.lookup_update_same.
    - exists old. rewrite ML.lookup_update_other; assumption.
  Qed.

  Lemma solved_materialize :
    forall st target x,
      solved st x -> solved (R.materialize st target) x.
  Proof.
    intros st target x Hsolved. unfold R.materialize.
    destruct (R.is_materialized st target); [exact Hsolved |].
    now apply solved_update.
  Qed.

  Lemma solved_materialize_self :
    forall st target, solved (R.materialize st target) target.
  Proof.
    intros st target. unfold R.materialize, R.is_materialized, solved.
    destruct (M.lookup (R.sigma st) target) as [value |] eqn:Hlookup.
    - now exists value.
    - exists D.bottom. cbn. apply ML.lookup_update_same.
  Qed.

  Lemma solved_start_evaluation :
    forall st owner x,
      solved st x -> solved (R.start_evaluation st owner) x.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides.
    now apply solved_materialize.
  Qed.

  Lemma solved_start_evaluation_self :
    forall st owner, solved (R.start_evaluation st owner) owner.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides.
    apply solved_materialize_self.
  Qed.

  Lemma solved_get_ready :
    forall st owner target x,
      solved st x -> solved (R.get_ready_state st owner target) x.
  Proof.
    intros. unfold R.get_ready_state, R.add_reader, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      now apply solved_materialize.
  Qed.

  Lemma solved_side_ready :
    forall st source target raw x,
      solved st x -> solved (R.side_ready_state st source target raw) x.
  Proof.
    intros. unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled.
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact H.
  Qed.

  Lemma solved_mark_side_dirty :
    forall st target x,
      solved st x -> solved (R.mark_side_dirty st target) x.
  Proof. intros st target x Hsolved. exact Hsolved. Qed.

  Lemma solved_observe :
    forall st target next entry x,
      R.observe st target = (next, entry) ->
      solved st x -> solved next x.
  Proof.
    intros st target next entry x Hobserve Hsolved.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; subst; exact Hsolved.
  Qed.

  Lemma solved_enqueue_handle :
    forall st entry x,
      solved st x -> solved (R.enqueue_handle st entry) x.
  Proof. intros. exact H. Qed.

  Lemma solved_enqueue :
    forall st target x,
      solved st x -> solved (R.enqueue st target) x.
  Proof.
    intros st target x Hsolved. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    apply solved_enqueue_handle.
    eapply solved_observe; eassumption.
  Qed.

  Lemma solved_enqueue_all :
    forall xs st x,
      solved st x -> solved (R.enqueue_all st xs) x.
  Proof.
    induction xs; intros; cbn; auto using solved_enqueue.
  Qed.

  Lemma solved_write_changed_value :
    forall st owner value x,
      solved st x -> solved (R.write_changed_value st owner value) x.
  Proof.
    intros. unfold R.write_changed_value.
    apply solved_same_sigma with
      (before := R.enqueue_all
        (R.with_sigma st (M.update (R.sigma st) owner value))
        (S.elements (R.lookup_set (R.readers st) owner)));
      [reflexivity |].
    apply solved_enqueue_all. now apply solved_update.
  Qed.

  Lemma solved_cancel_dirty_target :
    forall st target x,
      solved st x -> solved (R.cancel_dirty_target st target) x.
  Proof. intros st target x Hsolved. exact Hsolved. Qed.

  Lemma solved_try_dirty_read :
    forall tf st owner target next x,
      R.try_dirty_read tf st owner target = Some next ->
      solved st x -> solved next x.
  Proof.
    intros tf st owner target next x Hread Hsolved.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using solved_write_changed_value, solved_cancel_dirty_target.
  Qed.

  Lemma solved_dirty_get_ready :
    forall tf st owner target x,
      solved st x ->
      solved (R.dirty_get_ready_state tf st owner target) x.
  Proof.
    intros tf st owner target x Hsolved. unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : solved prepared x).
    { subst prepared. apply solved_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hsolved. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - change (solved next x). eapply solved_try_dirty_read; eauto.
    - change (solved prepared x). exact Hprepared.
  Qed.

  Lemma solved_set_value :
    forall st owner direct x,
      solved st x -> solved (R.set_value st owner direct) x.
  Proof.
    intros st owner direct x Hsolved. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hsolved |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase output].
      cbn. destruct (R.equivalent output (R.sigma_value st owner));
        auto using solved_write_changed_value.
    - now apply solved_write_changed_value.
  Qed.

  Theorem next_config_solved_preserved :
    forall tf before after x,
      R.next_config tf before = Some after ->
      solved (R.cfg_state before) x ->
      solved (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x Hstep Hsolved. cbn in Hstep, Hsolved.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn;
      eauto 8 using solved_same_sigma, solved_observe,
        solved_start_evaluation, solved_get_ready, solved_side_ready,
        solved_dirty_get_ready, solved_mark_side_dirty,
        solved_materialize, solved_enqueue_handle, solved_set_value.
    eapply solved_same_sigma; [reflexivity |].
    now apply solved_start_evaluation.
    unfold R.request_spawn.
    destruct (S.mem t (R.requested_spawns st)); exact Hsolved.
  Qed.

  Fixpoint continuation_solved
    (st : R.state) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterGet owner _ _ rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        solved st (R.handle_variable owner) /\
        continuation_solved st rest
    end.

  Fixpoint continuation_solved_except
    (st : R.state) (current : R.handle)
    (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterGet owner _ _ rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        (owner = current \/ solved st (R.handle_variable owner)) /\
        continuation_solved_except st current rest
    end.

  Definition control_solved (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne owner rest =>
        continuation_solved_except st owner rest
    | R.RunSolveOneLoop owner rest
    | R.RunRhs owner _ rest
    | R.AfterGet owner _ _ rest
    | R.AfterSide owner _ rest
    | R.AfterSpawn owner _ rest =>
        solved st (R.handle_variable owner) /\
        continuation_solved st rest
    end.

  Lemma continuation_solved_preserve :
    forall before after k,
      (forall x, solved before x -> solved after x) ->
      continuation_solved before k ->
      continuation_solved after k.
  Proof.
    intros before after k Hpreserve. induction k; cbn; intros Hsolved;
      try exact I; destruct Hsolved; split; eauto.
  Qed.

  Lemma continuation_except_preserve :
    forall before after current k,
      (forall x, solved before x -> solved after x) ->
      continuation_solved_except before current k ->
      continuation_solved_except after current k.
  Proof.
    intros before after current k Hpreserve. induction k; cbn;
      intros Hsolved; try exact I; destruct Hsolved as [Howner Hrest].
    all: split; [destruct Howner; eauto | eauto].
  Qed.

  Lemma continuation_solved_to_except :
    forall st current k,
      continuation_solved st k ->
      continuation_solved_except st current k.
  Proof.
    intros st current k. induction k; cbn; intros Hsolved; try exact I;
      destruct Hsolved as [Howner Hrest]; split; eauto.
  Qed.

  Lemma continuation_except_started :
    forall st after current k,
      solved after (R.handle_variable current) ->
      (forall x, solved st x -> solved after x) ->
      continuation_solved_except st current k ->
      continuation_solved after k.
  Proof.
    intros st after current k Hcurrent Hpreserve.
    induction k; cbn; intros Hsolved; try exact I;
      destruct Hsolved as [[-> | Howner] Hrest]; split; eauto.
  Qed.

  Lemma continuation_solved_continue :
    forall st k,
      continuation_solved st k -> control_solved st (R.continue k).
  Proof. intros st k Hsolved. destruct k; exact Hsolved. Qed.

  Theorem next_config_control_solved :
    forall tf before after,
      control_solved (R.cfg_state before) (R.cfg_control before) ->
      R.next_config tf before = Some after ->
      control_solved (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf before after Howners Hstep.
    assert (Hpreserve : forall x,
      solved (R.cfg_state before) x -> solved (R.cfg_state after) x).
    { intros. eapply next_config_solved_preserved; eauto. }
    destruct before as [st control]. cbn in Howners, Hstep, Hpreserve.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact I; try exact Howners.
    all: try match goal with
      | Hexcept : continuation_solved_except ?before ?current ?k
        |- solved ?after (R.handle_variable ?current) /\
           continuation_solved ?after ?k =>
          assert (Hcurrent : solved after (R.handle_variable current));
          [ eapply solved_same_sigma;
            [ reflexivity | apply solved_start_evaluation_self ]
          | split; [exact Hcurrent |];
            eapply continuation_except_started; eauto ]
      end.
    all: try (destruct Howners as [Howner Hrest]).
    all: try split; try (eapply Hpreserve; eassumption).
    all: try (eapply continuation_solved_preserve; eauto).
    all: try (eapply continuation_except_preserve; eauto).
    all: try (apply continuation_solved_to_except;
      eapply continuation_solved_preserve; eauto).
    all: try (apply continuation_solved_continue;
      eapply continuation_solved_preserve; eauto).
    all: right; apply Hpreserve; exact Howner.
  Qed.

  Lemma steps_control_solved :
    forall tf before after,
      control_solved (R.cfg_state before) (R.cfg_control before) ->
      Sem.steps tf before after ->
      control_solved (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf before after Hsolved Hsteps. induction Hsteps; auto.
    apply IHHsteps. eapply next_config_control_solved; eauto.
  Qed.

  Theorem reachable_control_solved :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      control_solved (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros. eapply steps_control_solved with
      (before := R.initial_config roots); [exact I | eassumption].
  Qed.

  Fixpoint continuation_ready
    (current : R.handle) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest => continuation_ready owner rest
    | R.KAfterGet owner target _ rest =>
        current = target /\ continuation_ready owner rest
    end.

  Definition control_ready (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne owner rest
    | R.RunSolveOneLoop owner rest
    | R.RunRhs owner _ rest => continuation_ready owner rest
    | R.AfterGet owner target _ rest =>
        solved st (R.handle_variable target) /\
        continuation_ready owner rest
    | R.AfterSide owner _ rest
    | R.AfterSpawn owner _ rest => continuation_ready owner rest
    end.

  Lemma continuation_ready_continue :
    forall st current k,
      solved st (R.handle_variable current) ->
      continuation_ready current k ->
      control_ready st (R.continue k).
  Proof.
    intros st current k Hsolved Hready. destruct k; cbn in *;
      try exact Hready. destruct Hready as [-> Hready]. auto.
  Qed.

  Theorem next_config_control_ready :
    forall tf before after,
      control_solved (R.cfg_state before) (R.cfg_control before) ->
      control_ready (R.cfg_state before) (R.cfg_control before) ->
      R.next_config tf before = Some after ->
      control_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hsolved Hready Hstep.
    cbn in Hsolved, Hready, Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact I; try exact Hready.
    1: (destruct Hsolved as [Howner _];
      eapply continuation_ready_continue; eassumption).
    all: try (split; [reflexivity | exact Hready]).
    all: try exact Hready.
    all: destruct Hready as [_ Hrest]; exact Hrest.
  Qed.

  Lemma steps_control_ready :
    forall tf before after,
      control_solved (R.cfg_state before) (R.cfg_control before) ->
      control_ready (R.cfg_state before) (R.cfg_control before) ->
      Sem.steps tf before after ->
      control_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf before after Hsolved Hready Hsteps. induction Hsteps; auto.
    apply IHHsteps.
    - eapply next_config_control_solved; eauto.
    - eapply next_config_control_ready; eauto.
  Qed.

  Theorem reachable_control_ready :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      control_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros. eapply steps_control_ready with
      (before := R.initial_config roots);
      [exact I | exact I | eassumption].
  Qed.

  Corollary reachable_after_get_materialized :
    forall tf roots st owner target next k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.AfterGet owner target next k |} ->
      R.is_materialized st (R.handle_variable target) = true.
  Proof.
    intros. pose proof (reachable_control_ready H) as Hready.
    cbn in Hready. now apply solved_is_materialized.
  Qed.

  End Progress.

  Section SpawnTracesFinal.
  Variable spawned : V.t -> Prop.
  Local Notation rhs_trace := (@rhs_trace spawned).
  Local Notation rhs_prefix := (@rhs_prefix spawned).
  Local Notation rhs_progress := (@rhs_progress spawned).
  Local Notation summary_valid := (@summary_valid spawned).

  Lemma aggregate_bounded_start : forall st owner tracked,
    aggregate_bounded st tracked ->
    aggregate_bounded (R.start_evaluation st owner) tracked.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides, aggregate_bounded in *.
    change (D.leq (R.aggregate (R.materialize st owner) tracked)
      (R.sigma_value (R.materialize st owner) tracked) = true).
    rewrite materialize_aggregate, materialize_value. exact H.
  Qed.

  Lemma aggregate_bounded_get_ready : forall st owner target tracked,
    aggregate_bounded st tracked ->
    aggregate_bounded (R.get_ready_state st owner target) tracked.
  Proof.
    intros. unfold aggregate_bounded in *.
    rewrite get_ready_state_aggregate, get_ready_state_value. exact H.
  Qed.

  Lemma aggregate_bounded_side_covered : forall st source target raw,
    D.leq (R.aggregate (R.side_ready_state st source target raw)
      (R.handle_variable target)) (R.aggregate st (R.handle_variable target)) = true ->
    aggregate_bounded st (R.handle_variable target) ->
    aggregate_bounded (R.side_ready_state st source target raw) (R.handle_variable target).
  Proof.
    intros. apply side_ready_state_not_grown; [|assumption].
    unfold R.aggregate_grew. now rewrite H.
  Qed.

  Definition owner_exit_ready (st : R.state) (owner : R.handle) : Prop :=
    aggregate_bounded st (R.handle_variable owner) \/
    queued st (R.handle_variable owner).

  Fixpoint continuation_exit_ready
    (st : R.state) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest =>
        owner_exit_ready st owner /\ continuation_exit_ready st rest
    | R.KAfterGet _ _ _ rest
    | R.KAfterSide _ _ rest
    | R.KAfterSpawn _ _ rest => continuation_exit_ready st rest
    end.

  Definition control_exit_ready (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOneLoop owner rest =>
        owner_exit_ready st owner /\ continuation_exit_ready st rest
    | R.RunSolveOne _ rest
    | R.RunRhs _ _ rest
    | R.AfterGet _ _ _ rest
    | R.AfterSide _ _ rest
    | R.AfterSpawn _ _ rest => continuation_exit_ready st rest
    end.

  Lemma queued_cancel_dirty_target_other :
    forall st target tracked,
      rank_valid st ->
      queue_valid st ->
      handle_valid st target ->
      tracked <> R.handle_variable target ->
      queued st tracked ->
      queued (R.cancel_dirty_target st target) tracked.
  Proof.
    intros st target tracked Hrank Hqueue Htarget Hneq
      [entry [Hin Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.cancel_dirty_target. cbn.
    apply queue_remove_rank_preserves_neq; [|exact Hin].
    intro Hranks.
    assert (Hentry : handle_valid st entry).
    { unfold queue_valid in Hqueue.
      eapply Forall_forall; eauto. }
    pose proof (@handle_rank_equal_variable_equal st entry target
      Hrank Hentry Htarget Hranks) as Hvariables.
    apply Hneq. rewrite <- Hvariable. exact Hvariables.
  Qed.

  Lemma queued_try_dirty_read_other :
    forall tf st owner target next tracked,
      rank_valid st ->
      queue_valid st ->
      handle_valid st target ->
      tracked <> R.handle_variable target ->
      queued st tracked ->
      R.try_dirty_read tf st owner target = Some next ->
      queued next tracked.
  Proof.
    intros tf st owner target next tracked Hrank Hqueue Htarget Hneq
      Hqueued Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using queued_write_changed_value,
        queued_cancel_dirty_target_other.
  Qed.

  Lemma queued_set_value :
    forall st owner direct tracked,
      queued st tracked ->
      queued (R.set_value st owner direct) tracked.
  Proof.
    intros st owner direct tracked Hqueued. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hqueued |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
        as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner));
        [exact Hqueued |].
      unfold R.write_changed_value. apply queued_enqueue_all. exact Hqueued.
    - unfold R.write_changed_value. apply queued_enqueue_all. exact Hqueued.
  Qed.

  Lemma owner_exit_map :
    forall before after,
      (forall owner,
        aggregate_bounded before (R.handle_variable owner) ->
        aggregate_bounded after (R.handle_variable owner)) ->
      (forall owner,
        queued before (R.handle_variable owner) ->
        queued after (R.handle_variable owner)) ->
      forall owner, owner_exit_ready before owner -> owner_exit_ready after owner.
  Proof.
    intros before after Hsound Hqueue owner [H | H].
    - left. now apply Hsound.
    - right. now apply Hqueue.
  Qed.

  Lemma continuation_exit_map :
    forall before after,
      (forall owner, owner_exit_ready before owner -> owner_exit_ready after owner) ->
      forall k,
        continuation_exit_ready before k -> continuation_exit_ready after k.
  Proof.
    intros before after Hmap k. induction k; cbn; intros Hready; try exact I.
    - destruct Hready. split; eauto.
    - eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma queued_start :
    forall st active tracked,
      queued st tracked ->
      queued (R.start_evaluation st active) tracked.
  Proof.
    intros st active tracked Hqueued.
    unfold R.start_evaluation, R.reset_local_sides, R.materialize.
    destruct (R.is_materialized st active); exact Hqueued.
  Qed.

  Lemma queued_side_ready :
    forall st source target raw tracked,
      queued st tracked ->
      queued (R.side_ready_state st source target raw) tracked.
  Proof.
    intros st source target raw tracked Hqueued.
    unfold R.side_ready_state, R.record_side_payload, R.promote_controlled.
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hqueued.
  Qed.

  Lemma owner_exit_start :
    forall st active owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.start_evaluation st active) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply aggregate_bounded_start.
    - intros. now apply queued_start.
  Qed.

  Lemma owner_exit_get_ready :
    forall st active target owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.get_ready_state st active target) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply aggregate_bounded_get_ready.
    - intros. now apply queued_get_ready.
  Qed.

  Lemma owner_exit_set_value :
    forall st variable direct owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.set_value st variable direct) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply set_value_preserves_aggregate_bound.
    - intros. now apply queued_set_value.
  Qed.

  Lemma owner_exit_side_other :
    forall st source target raw owner,
      R.handle_variable owner <> R.handle_variable target ->
      owner_exit_ready st owner ->
      owner_exit_ready (R.side_ready_state st source target raw) owner.
  Proof.
    intros st source target raw owner Hneq [Hsound | Hqueued].
    - left. now apply side_ready_state_other.
    - right. now apply queued_side_ready.
  Qed.

  Lemma owner_exit_side_covered :
    forall st source target raw owner,
      D.leq
        (R.aggregate (R.side_ready_state st source target raw)
          (R.handle_variable target))
        (R.aggregate st (R.handle_variable target)) = true ->
      owner_exit_ready st owner ->
      owner_exit_ready (R.side_ready_state st source target raw) owner.
  Proof.
    intros st source target raw owner Hcovered [Hsound | Hqueued].
    - left. destruct (V.eq_dec (R.handle_variable owner)
        (R.handle_variable target)) as [Heq | Hneq].
      + rewrite Heq in *. now apply aggregate_bounded_side_covered.
      + now apply side_ready_state_other.
    - right. now apply queued_side_ready.
  Qed.

  Lemma continuation_exit_start :
    forall st active k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.start_evaluation st active) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros. now apply owner_exit_start.
  Qed.

  Lemma continuation_exit_get_ready :
    forall st owner target k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.get_ready_state st owner target) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros. now apply owner_exit_get_ready.
  Qed.

  Lemma continuation_exit_get_control_state :
    forall st owner target k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.get_control_state st owner target) k.
  Proof.
    intros st owner target k Hready. unfold R.get_control_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      [exact Hready |].
    unfold R.promote_controlled.
    eapply continuation_exit_map; [|exact Hready].
    intros tracked [Hsound | Hqueued]; [left |right]; assumption.
  Qed.

  Lemma owner_exit_try_dirty_read :
    forall tf st owner target next tracked,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      R.try_dirty_read tf st owner target = Some next ->
      owner_exit_ready st tracked -> owner_exit_ready next tracked.
  Proof.
    intros tf st owner target next tracked Hrank Hqueue Htarget Hread
      [Hsound | Hqueued].
    - left. eapply try_dirty_read_preserves_aggregate_bound; eauto.
    - destruct (V.eq_dec (R.handle_variable tracked)
        (R.handle_variable target)) as [Heq | Hneq].
      + left. rewrite Heq. eapply try_dirty_read_aggregate_bounded; eauto.
      + right. eapply queued_try_dirty_read_other; eauto.
  Qed.

  Lemma continuation_exit_try_dirty_read :
    forall tf st owner target next k,
      rank_valid st ->
      queue_valid st ->
      handle_valid st target ->
      R.try_dirty_read tf st owner target = Some next ->
      continuation_exit_ready st k ->
      continuation_exit_ready next k.
  Proof.
    intros tf st owner target next k Hrank Hqueue Htarget Hread Hready.
    eapply continuation_exit_map; [|exact Hready].
    intros tracked Hexit. eapply owner_exit_try_dirty_read; eauto.
  Qed.

  Lemma same_variable_valid_rank :
    forall st left right,
      handle_valid st left ->
      handle_valid st right ->
      R.handle_variable left = R.handle_variable right ->
      R.handle_rank left = R.handle_rank right.
  Proof.
    intros st left right Hleft Hright Hvariable.
    unfold handle_valid in Hleft, Hright.
    rewrite Hvariable, Hright in Hleft. now inversion Hleft.
  Qed.
  Lemma continuation_exit_add_reader_early :
    forall st target reader k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.add_reader st target reader) k.
  Proof.
    intros st target reader k Hready.
    eapply continuation_exit_map; [|exact Hready].
    intros tracked [Hsound | Hqueued]; [left |right]; assumption.
  Qed.

  Lemma continuation_exit_dirty_get_ready : forall tf st owner target k,
    rank_valid st -> queue_valid st -> handle_valid st target ->
    continuation_valid st k -> continuation_exit_ready st k ->
    continuation_exit_ready (R.dirty_get_ready_state tf st owner target) k.
  Proof.
    intros tf st owner target k Hrank Hqueue Htarget Hvalid Hready.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize (R.get_control_state st owner target)
      (R.handle_variable target)).
    assert (Hr : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state. destruct (Nat.ltb _ _); exact Hrank. }
    assert (Hq : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state. destruct (Nat.ltb _ _); exact Hqueue. }
    assert (Ht : handle_valid prepared target).
    { subst prepared. apply handle_valid_materialize.
      unfold R.get_control_state. destruct (Nat.ltb _ _); exact Htarget. }
    assert (He : continuation_exit_ready prepared k).
    { subst prepared. eapply continuation_exit_map; [|exact Hready].
      intros tracked [Hb | Hqueued].
      - left. unfold aggregate_bounded in *.
        rewrite materialize_aggregate, materialize_value.
        unfold R.get_control_state. destruct (Nat.ltb _ _); exact Hb.
      - right. unfold R.materialize, R.get_control_state.
        destruct (Nat.ltb _ _); destruct (R.is_materialized _ _); exact Hqueued. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread;
      apply continuation_exit_add_reader_early; [|exact He].
    eapply continuation_exit_try_dirty_read; eauto.
  Qed.

  Lemma continuation_exit_set_value :
    forall st variable direct k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.set_value st variable direct) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros. now apply owner_exit_set_value.
  Qed.

  Lemma continuation_exit_side_covered :
    forall st source target raw k,
      D.leq
        (R.aggregate (R.side_ready_state st source target raw)
          (R.handle_variable target))
        (R.aggregate st (R.handle_variable target)) = true ->
      continuation_exit_ready st k ->
      continuation_exit_ready (R.side_ready_state st source target raw) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H0].
    intros. now eapply owner_exit_side_covered.
  Qed.

  Lemma owner_exit_pop_other :
    forall st popped tail owner,
      R.queue_pop (R.queue st) = Some (popped, tail) ->
      R.handle_variable owner <> R.handle_variable popped ->
      owner_exit_ready st owner ->
      owner_exit_ready (R.with_queue st tail) owner.
  Proof.
    intros st popped tail owner Hpop Hneq [Hsound | Hqueued].
    - now left.
    - right. destruct Hqueued as [entry [Hin Hvariable]].
      exists entry. split; [|exact Hvariable].
      unfold R.queue_pop in Hpop.
      destruct (R.queue st) as [|head rest] eqn:Hqueue;
        cbn in Hpop; try discriminate.
      inversion Hpop; subst. cbn in Hin. destruct Hin as [-> | Hin].
      + exfalso. apply Hneq. now rewrite Hvariable.
      + exact Hin.
  Qed.

  Lemma valid_ranked_variables_differ :
    forall st left right,
      handle_valid st left -> handle_valid st right ->
      R.handle_rank left < R.handle_rank right ->
      R.handle_variable left <> R.handle_variable right.
  Proof.
    intros st left right Hleft Hright Hlt Heq.
    assert (R.handle_rank left = R.handle_rank right).
    { eapply same_variable_valid_rank; eauto. }
    lia.
  Qed.

  Lemma continuation_exit_pop :
    forall st popped tail upper k,
      queue_valid st -> continuation_valid st k ->
      R.queue_pop (R.queue st) = Some (popped, tail) ->
      ControlStack.continuation_ordered upper k ->
      (upper = popped \/ R.handle_rank upper < R.handle_rank popped) ->
      continuation_exit_ready st k ->
      continuation_exit_ready (R.with_queue st tail) k.
  Proof.
    intros st popped tail upper k Hqueue Hvalid Hpop.
    revert upper Hvalid. induction k as
      [| roots
       | owner rest IH
       | owner target next rest IH
       | owner next rest IH
       | owner next rest IH];
      intros upper Hvalid Hordered Hbound Hready; cbn in *; try exact I.
    all: destruct Hvalid as [Howner Hvalid].
    all: destruct Hordered as [Howner_order Hordered].
    all: apply Nat.ltb_lt in Howner_order.
    all: assert (Howner_popped : R.handle_rank owner < R.handle_rank popped)
      by (destruct Hbound as [-> | Hbound]; lia).
    - destruct Hready as [Hhead Htail]. split.
      + eapply owner_exit_pop_other; [exact Hpop | |exact Hhead].
        eapply valid_ranked_variables_differ;
          [exact Howner | |exact Howner_popped].
        exact (proj1 (@queue_pop_valid st popped tail Hqueue Hpop)).
      + eapply IH; eauto.
    - eapply IH; eauto. exact (proj2 Hvalid).
    - eapply IH; eauto.
    - eapply IH; eauto.
  Qed.

  Lemma continuation_exit_side_above :
    forall st source target raw upper k,
      continuation_valid st k -> handle_valid st target ->
      R.handle_rank upper < R.handle_rank target ->
      ControlStack.continuation_ordered upper k ->
      continuation_exit_ready st k ->
      continuation_exit_ready (R.side_ready_state st source target raw) k.
  Proof.
    intros st source target raw upper k Hvalid Htarget.
    revert upper Hvalid. induction k as
      [| roots
       | owner rest IH
       | owner read next rest IH
       | owner next rest IH
       | owner next rest IH];
      intros upper Hvalid Hhigher Hordered Hready; cbn in *; try exact I.
    all: destruct Hvalid as [Howner Hvalid].
    all: destruct Hordered as [Howner_order Hordered].
    all: apply Nat.ltb_lt in Howner_order.
    all: assert (Howner_target : R.handle_rank owner < R.handle_rank target)
      by lia.
    - destruct Hready as [Hhead Htail]. split.
      + eapply owner_exit_side_other; [|exact Hhead].
        eapply valid_ranked_variables_differ; eauto.
      + eapply IH; eauto.
    - eapply IH; eauto. exact (proj2 Hvalid).
    - eapply IH; eauto.
    - eapply IH; eauto.
  Qed.

  Lemma aggregate_bounded_observe : forall st target next entry tracked,
    R.observe st target = (next, entry) ->
    aggregate_bounded st tracked -> aggregate_bounded next tracked.
  Proof.
    intros st target next entry tracked Hobserve Hbound.
    unfold R.observe in Hobserve. destruct (R.Ranking.observe _ _);
      inversion Hobserve; subst; exact Hbound.
  Qed.

  Lemma owner_exit_observe :
    forall st target next entry owner,
      R.observe st target = (next, entry) ->
      owner_exit_ready st owner -> owner_exit_ready next owner.
  Proof.
    intros st target next entry owner Hobserve [Hsound | Hqueued].
    - left. eapply aggregate_bounded_observe; eauto.
    - right. eapply queued_observe; eauto.
  Qed.

  Lemma owner_exit_enqueue_handle :
    forall st inserted owner,
      owner_exit_ready st owner -> owner_exit_ready (R.enqueue_handle st inserted) owner.
  Proof.
    intros st inserted owner [Hsound | Hqueued].
    - now left.
    - right. now apply queued_enqueue_handle.
  Qed.

  Lemma owner_exit_materialize :
    forall st target owner,
      owner_exit_ready st owner -> owner_exit_ready (R.materialize st target) owner.
  Proof.
    intros st target owner [Hsound | Hqueued].
    - left. unfold aggregate_bounded in *. rewrite materialize_aggregate,
        materialize_value. exact Hsound.
    - right. unfold R.materialize.
      destruct (R.is_materialized st target); exact Hqueued.
  Qed.

  Lemma continuation_exit_observe :
    forall st target next entry k,
      R.observe st target = (next, entry) ->
      continuation_exit_ready st k -> continuation_exit_ready next k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H0].
    intros. eapply owner_exit_observe; eauto.
  Qed.

  Lemma continuation_exit_enqueue_handle :
    forall st inserted k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.enqueue_handle st inserted) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros. now apply owner_exit_enqueue_handle.
  Qed.

  Lemma continuation_exit_materialize :
    forall st target k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.materialize st target) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros. now apply owner_exit_materialize.
  Qed.

  Lemma owner_exit_side_enqueue :
    forall st source target raw owner,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      owner_exit_ready st owner ->
      owner_exit_ready
        (R.enqueue_handle (R.side_ready_state st source target raw) target) owner.
  Proof.
    intros st source target raw owner Hrank Hqueue Htarget Hready.
    destruct (V.eq_dec (R.handle_variable owner)
      (R.handle_variable target)) as [Heq | Hneq].
    - right. rewrite Heq. apply enqueue_handle_queues_variable.
      + apply rank_valid_side_ready. exact Hrank.
      + apply queue_valid_side_ready. exact Hqueue.
      + eapply handle_valid_extended; [|exact Htarget].
        apply rank_extends_side_ready.
    - apply owner_exit_enqueue_handle, owner_exit_side_other; assumption.
  Qed.

  Lemma continuation_exit_side_enqueue :
    forall st source target raw k,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      continuation_exit_ready st k ->
      continuation_exit_ready
        (R.enqueue_handle (R.side_ready_state st source target raw) target) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H2].
    intros. eapply owner_exit_side_enqueue; eauto.
  Qed.

  Lemma continuation_exit_with_started :
    forall st started k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.with_started st started) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
      intros owner [Hsound | Hqueued]; [left |right]; exact Hsound || exact Hqueued.
  Qed.

  Lemma continuation_exit_add_reader :
    forall st target reader k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.add_reader st target reader) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros owner [Hsound | Hqueued]; [left |right]; exact Hsound || exact Hqueued.
  Qed.

  Lemma continuation_exit_remember_dormant :
    forall st target k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.remember_dormant st target) k.
  Proof.
    intros. eapply continuation_exit_map; [|exact H].
    intros owner [Hsound | Hqueued]; [left |right]; exact Hsound || exact Hqueued.
  Qed.

  Lemma same_variable_valid_handle_equal :
    forall st left right,
      handle_valid st left -> handle_valid st right ->
      R.handle_variable left = R.handle_variable right -> left = right.
  Proof.
    intros st [left_variable left_rank] [right_variable right_rank]
      Hleft Hright Hvariable. cbn in Hvariable. subst right_variable.
    unfold handle_valid in Hleft, Hright. cbn in Hleft, Hright.
    rewrite Hleft in Hright. inversion Hright. reflexivity.
  Qed.

  Lemma continuation_exit_ready_continue :
    forall st k,
      continuation_exit_ready st k -> control_exit_ready st (R.continue k).
  Proof. intros st k Hready. destruct k; exact Hready. Qed.

  Lemma continuation_exit_side_recursive :
    forall st source body k target raw next target_handle,
      handles_valid
        {| R.cfg_state := st; R.cfg_control := R.RunRhs source body k |} ->
      ControlStack.continuation_ordered source k ->
      R.observe st target = (next, target_handle) ->
      andb
        (Nat.ltb (R.handle_rank source) (R.handle_rank target_handle))
        (negb (R.is_materialized next target)) = true ->
      continuation_exit_ready st k ->
      continuation_exit_ready
        (R.side_ready_state next source target_handle raw) k.
  Proof.
    intros st source body k target raw next target_handle
      Hvalid Hordered Hobserve Hbranch Hready.
    apply Bool.andb_true_iff in Hbranch as [Hhigher _].
    assert (Hlt : R.handle_rank source < R.handle_rank target_handle).
    { destruct (R.handle_rank target_handle) as [|rank] eqn:Htarget;
        cbn in Hhigher; try discriminate.
      apply Nat.leb_le in Hhigher. lia. }
    pose proof (handles_control_valid Hvalid) as Hcontrol.
    cbn in Hcontrol.
    eapply continuation_exit_side_above with (upper := source).
    - eapply continuation_valid_extended;
        [eapply rank_extends_observe; eauto |exact (proj2 Hcontrol)].
    - eapply observed_handle_valid; eauto.
    - exact Hlt.
    - exact Hordered.
    - eapply continuation_exit_observe; eauto.
  Qed.

  Lemma continuation_exit_side_enqueued :
    forall st source body k target raw next target_handle,
      handles_valid
        {| R.cfg_state := st; R.cfg_control := R.RunRhs source body k |} ->
      R.observe st target = (next, target_handle) ->
      continuation_exit_ready st k ->
      continuation_exit_ready
        (R.enqueue_handle
          (R.side_ready_state next source target_handle raw) target_handle) k.
  Proof.
    intros st source body k target raw next target_handle
      Hvalid Hobserve Hready.
    eapply continuation_exit_side_enqueue.
    - eapply rank_valid_observe;
        [exact (handles_rank_valid Hvalid) |exact Hobserve].
    - eapply queue_valid_observe;
        [exact (handles_queue_valid Hvalid) |exact Hobserve].
    - eapply observed_handle_valid; eauto.
    - eapply continuation_exit_observe; eauto.
  Qed.

  Lemma continuation_exit_side_not_grew :
    forall st source target raw next target_handle k,
      R.observe st target = (next, target_handle) ->
      R.aggregate_grew next
        (R.side_ready_state next source target_handle raw) target = false ->
      continuation_exit_ready st k ->
      continuation_exit_ready
        (R.side_ready_state next source target_handle raw) k.
  Proof.
    intros st source target raw next target_handle k
      Hobserve Hgrew Hready.
    unfold R.aggregate_grew in Hgrew.
    apply Bool.negb_false_iff in Hgrew.
    pose proof (@observed_handle_variable st target next target_handle Hobserve)
      as Hvariable.
    eapply continuation_exit_side_covered.
    - rewrite Hvariable. exact Hgrew.
    - eapply continuation_exit_observe; eauto.
  Qed.

  Lemma continuation_exit_mark_side_dirty :
    forall st target k,
      continuation_exit_ready st k ->
      continuation_exit_ready (R.mark_side_dirty st target) k.
  Proof.
    intros st target k Hready.
    eapply continuation_exit_map; [|exact Hready].
    intros owner Howner. exact Howner.
  Qed.

  Lemma continuation_exit_enqueue_mark_side_dirty :
    forall st inserted target k,
      continuation_exit_ready (R.enqueue_handle st inserted) k ->
      continuation_exit_ready
        (R.enqueue_handle (R.mark_side_dirty st target) inserted) k.
  Proof.
    intros st inserted target k Hready.
    eapply continuation_exit_map; [|exact Hready].
    intros owner Howner. exact Howner.
  Qed.

  Lemma continuation_exit_request_spawn : forall st target k,
    continuation_exit_ready st k ->
    continuation_exit_ready (R.request_spawn st target) k.
  Proof.
    intros st target k Hready. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); [exact Hready|].
    eapply continuation_exit_map; [|exact Hready].
    intros owner Howner. exact Howner.
  Qed.

  Lemma continuation_exit_dirty_observe : forall tf st owner body k target next entry,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunRhs owner body k |} ->
    R.observe st target = (next, entry) ->
    continuation_exit_ready st k ->
    continuation_exit_ready (R.dirty_get_ready_state tf next owner entry) k.
  Proof.
    intros tf st owner body k target next entry Hv Ho Hr.
    eapply continuation_exit_dirty_get_ready.
    - eapply rank_valid_observe; eauto using handles_rank_valid.
    - eapply queue_valid_observe; eauto using handles_queue_valid.
    - eapply observed_handle_valid; eauto.
    - eapply continuation_valid_extended.
      + eapply rank_extends_observe; eauto.
      + exact (proj2 (handles_control_valid Hv)).
    - eapply continuation_exit_observe; eauto.
  Qed.

  Lemma control_exit_pop_same : forall st owner k popped tail,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    ControlStack.continuation_ordered owner k ->
    control_exit_ready st (R.RunSolveOneLoop owner k) ->
    R.queue_pop (R.queue st) = Some (popped, tail) ->
    R.handle_variable popped = R.handle_variable owner ->
    continuation_exit_ready (R.with_queue st tail) k.
  Proof.
    intros st owner k popped tail Hv Ho Hr Hp He.
    pose proof (handles_queue_valid Hv) as Hq.
    pose proof (handles_control_valid Hv) as Hc.
    assert (popped = owner).
    { eapply same_variable_valid_handle_equal.
      - exact (proj1 (@queue_pop_valid st popped tail Hq Hp)).
      - exact (proj1 Hc).
      - exact He. }
    subst popped. eapply continuation_exit_pop; eauto.
    - exact (proj2 Hc).
    - exact (proj2 Hr).
  Qed.

  Lemma control_exit_pop_higher : forall st owner k popped tail,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    ControlStack.continuation_ordered owner k ->
    control_exit_ready st (R.RunSolveOneLoop owner k) ->
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (popped, tail) ->
    R.handle_variable popped <> R.handle_variable owner ->
    continuation_exit_ready (R.with_queue st tail) (R.KSolveOneLoop owner k).
  Proof.
    intros st owner k popped tail Hv Ho Hr Hmay Hp Hneq.
    pose proof (handles_control_valid Hv) as Hc.
    assert (Hhigher : R.handle_rank owner < R.handle_rank popped).
    { apply Nat.ltb_lt. eapply ControlStack.owner_may_pop_higher; eauto. }
    split.
    - eapply owner_exit_pop_other; [exact Hp|congruence|exact (proj1 Hr)].
    - eapply continuation_exit_pop; eauto.
      + exact (handles_queue_valid Hv).
      + exact (proj2 Hc).
      + exact (proj2 Hr).
  Qed.

  Lemma control_exit_ready_step : forall tf before after,
    handles_valid before -> ControlStack.control_ordered (R.cfg_control before) ->
    control_exit_ready (R.cfg_state before) (R.cfg_control before) ->
    Sem.step tf before after ->
    control_exit_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hvalid Hordered Hready Hstep.
    unfold Sem.step in Hstep. cbn in Hvalid, Hordered, Hready, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I; try exact Hready.
    all: try solve [eauto 5 using continuation_exit_add_reader,
      continuation_exit_remember_dormant, continuation_exit_get_ready,
      continuation_exit_enqueue_handle, continuation_exit_materialize,
      continuation_exit_observe, continuation_exit_with_started,
      continuation_exit_start, continuation_exit_request_spawn].
    all: try solve [eapply continuation_exit_dirty_observe; eauto].
    all: try solve [eapply control_exit_pop_same; eauto].
    all: try solve [eapply control_exit_pop_higher; eauto].
    all: try solve [apply continuation_exit_ready_continue; exact (proj2 Hready)].
    all: try solve [split; [left; apply set_value_aggregate_bounded |
      now apply continuation_exit_set_value]].
    all: try solve [eauto 5 using continuation_exit_side_recursive,
      continuation_exit_side_enqueued, continuation_exit_side_not_grew,
      continuation_exit_mark_side_dirty, continuation_exit_enqueue_handle,
      continuation_exit_enqueue_mark_side_dirty].
  Qed.

  Lemma control_exit_ready_steps :
    forall tf before after,
      handles_valid before ->
      ControlStack.control_ordered (R.cfg_control before) ->
      control_exit_ready (R.cfg_state before) (R.cfg_control before) ->
      Sem.steps tf before after ->
      control_exit_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf before after Hvalid Hordered Hready Hsteps.
    induction Hsteps; [exact Hready |].
    apply IHHsteps.
    - eapply next_config_handles_valid; eauto.
    - eapply ControlStack.next_config_control_ordered; eauto.
    - eapply control_exit_ready_step; eauto.
  Qed.

  Theorem reachable_control_exit_ready :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      control_exit_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots after Hsteps. eapply control_exit_ready_steps.
    - apply initial_handles_valid.
    - exact I.
    - exact I.
    - exact Hsteps.
  Qed.

  Lemma reachable_drain_aggregate_bounded : forall tf roots st owner k,
    Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    R.owner_may_still_be_queued st owner = false ->
    aggregate_bounded st (R.handle_variable owner).
  Proof.
    intros tf roots st owner k Hsteps Hmay.
    pose proof (reachable_control_exit_ready Hsteps) as Hexit.
    destruct Hexit as [[Hbound | [entry [Hin Hvariable]]] _]; [exact Hbound|].
    pose proof (reachable_handles_valid Hsteps) as Hhandles.
    pose proof (handles_control_valid Hhandles) as Hcontrol.
    pose proof (@reachable_owner_may_false_queue_below tf roots _ owner
      Hsteps (proj1 Hcontrol) Hmay) as Hbelow.
    specialize (Hbelow entry Hin).
    assert (He : handle_valid st entry).
    { pose proof (handles_queue_valid Hhandles) as Hqueue.
      eapply Forall_forall; eauto. }
    pose proof (@same_variable_valid_rank st entry owner He
      (proj1 Hcontrol) Hvariable). lia.
  Qed.

  Lemma owner_may_true_queue_nonempty : forall st owner,
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) <> None.
  Proof.
    intros st owner Hmay. unfold R.owner_may_still_be_queued in Hmay.
    destruct (R.queue st); cbn in *; discriminate.
  Qed.

  Theorem reachable_stopped_is_terminal : forall tf roots after,
    Sem.steps tf (R.initial_config roots) after ->
    R.next_config tf after = None ->
    R.terminal_state after = Some (R.cfg_state after).
  Proof.
    intros tf roots [st control] Hsteps Hstop.
    destruct control; cbn in Hstop;
      repeat match type of Hstop with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate.
    - unfold R.terminal_state. cbn.
      unfold R.queue_pop in Hcase. destruct (R.queue st); try discriminate.
      cbn. now rewrite Hcase0.
    - exfalso. eapply owner_may_true_queue_nonempty; eauto.
    - pose proof (@reachable_drain_aggregate_bounded tf roots st h c Hsteps Hcase).
      unfold aggregate_bounded in H. congruence.
    - pose proof (Progress.reachable_after_get_materialized Hsteps). congruence.
  Qed.
  Fixpoint continuation_active (x : V.t) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => False
    | R.KSolveOneLoop owner rest
    | R.KAfterGet owner _ _ rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        x = R.handle_variable owner \/ continuation_active x rest
    end.

  Definition control_active (x : V.t) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
    | R.RunSolveOne owner rest
    | R.RunSolveOneLoop owner rest
    | R.RunRhs owner _ rest
    | R.AfterGet owner _ _ rest
    | R.AfterSide owner _ rest
    | R.AfterSpawn owner _ rest =>
        x = R.handle_variable owner \/ continuation_active x rest
    end.

  Lemma queued_dirty_get_ready_other_early :
    forall tf st owner target tracked,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      tracked <> R.handle_variable target ->
      queued st tracked ->
      queued (R.dirty_get_ready_state tf st owner target) tracked.
  Proof.
    intros tf st owner target tracked Hrank Hqueue Htarget Hneq Hqueued.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_rank : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrank. }
    assert (Hprepared_queue : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hqueue. }
    assert (Hprepared_target : handle_valid prepared target).
    { eapply handle_valid_extended; [|exact Htarget].
      subst prepared. eapply (@rank_extends_trans st
        (R.get_control_state st owner target));
        [|apply rank_extends_materialize].
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        apply rank_extends_same_ranking; reflexivity. }
    assert (Hprepared_queued : queued prepared tracked).
    { subst prepared. unfold R.get_control_state, R.materialize.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); exact Hqueued. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; unfold R.add_reader.
    - change (queued next tracked).
      eapply queued_try_dirty_read_other; eauto.
    - change (queued prepared tracked). exact Hprepared_queued.
  Qed.

  Definition aggregate_guarded (c : R.config) : Prop :=
    forall target,
      queued (R.cfg_state c) target \/
      control_active target (R.cfg_control c) \/
      aggregate_bounded (R.cfg_state c) target.

  Lemma queued_or_aggregate_bounded_dirty_get_ready_target :
    forall tf st owner target,
      queued st (R.handle_variable target) ->
      queued (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target) \/
      aggregate_bounded (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target).
  Proof.
    intros tf st owner target Hqueued. unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_queued : queued prepared (R.handle_variable target)).
    { subst prepared. unfold R.get_control_state, R.materialize.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); exact Hqueued. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; unfold R.add_reader.
    - right. change (aggregate_bounded next (R.handle_variable target)).
      eapply try_dirty_read_aggregate_bounded; eauto.
    - left. change (queued prepared (R.handle_variable target)).
      exact Hprepared_queued.
  Qed.

  Lemma aggregate_bounded_empty :
    forall target, aggregate_bounded R.empty_state target.
  Proof.
    intros. unfold aggregate_bounded,
      R.aggregate, R.lookup_map, R.sigma_value. cbn.
    rewrite ML.lookup_empty, ML.values_empty, ML.lookup_empty.
    cbn. apply DL.leq_refl.
  Qed.

  Lemma aggregate_bounded_with_queue :
    forall st queue target,
      aggregate_bounded st target ->
      aggregate_bounded (R.with_queue st queue) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_bounded_with_started :
    forall st started target,
      aggregate_bounded st target ->
      aggregate_bounded (R.with_started st started) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_bounded_enqueue_handle :
    forall st inserted target,
      aggregate_bounded st target ->
      aggregate_bounded (R.enqueue_handle st inserted) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_bounded_materialize :
    forall st inserted target,
      aggregate_bounded st target ->
      aggregate_bounded (R.materialize st inserted) target.
  Proof.
    intros st inserted target Hsound.
    unfold aggregate_bounded in *.
    rewrite materialize_aggregate,
      materialize_value. exact Hsound.
  Qed.

  Lemma initial_aggregate_guarded :
    forall roots, aggregate_guarded (R.initial_config roots).
  Proof.
    intros roots target. right. right. apply aggregate_bounded_empty.
  Qed.

  Lemma continuation_active_continue :
    forall x k,
      continuation_active x k -> control_active x (R.continue k).
  Proof. intros x k Hactive. destruct k; exact Hactive. Qed.

  Lemma queued_pop_other :
    forall st popped tail target,
      R.queue_pop (R.queue st) = Some (popped, tail) ->
      target <> R.handle_variable popped ->
      queued st target -> queued (R.with_queue st tail) target.
  Proof.
    intros st popped tail target Hpop Hneq
      [entry [Hentry Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.queue_pop in Hpop.
    destruct (R.queue st) as [|head rest] eqn:Hqueue;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst head rest. cbn in Hentry.
    destruct Hentry as [-> | Hentry].
    - exfalso. apply Hneq. symmetry. exact Hvariable.
    - exact Hentry.
  Qed.

  Lemma aggregate_guarded_map : forall before after old next,
    (forall x, queued before x -> queued after x) ->
    (forall x, aggregate_bounded before x -> aggregate_bounded after x) ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := before; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := after; R.cfg_control := next |}.
  Proof.
    intros before after old next Hq Hb Ha Hg x.
    destruct (Hg x) as [H|[H|H]]; [left|right;left|right;right]; auto.
  Qed.

  Lemma queued_materialize : forall st target x,
    queued st x -> queued (R.materialize st target) x.
  Proof.
    intros. unfold R.materialize. destruct (R.is_materialized st target); exact H.
  Qed.

  Lemma aggregate_guarded_pop : forall st old popped tail next,
    R.queue_pop (R.queue st) = Some (popped, tail) ->
    control_active (R.handle_variable popped) next ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := R.with_queue st tail; R.cfg_control := next |}.
  Proof.
    intros st old popped tail next Hp Hactive Hmap Hg x.
    destruct (V.eq_dec x (R.handle_variable popped)) as [->|Hneq].
    - right; left; exact Hactive.
    - destruct (Hg x) as [Hq|[Ha|Hb]].
      + left. eapply queued_pop_other; eauto.
      + right; left; auto.
      + right; right; exact Hb.
  Qed.

  Lemma aggregate_guarded_observe : forall st target observed entry old next,
    R.observe st target = (observed, entry) ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := observed; R.cfg_control := next |}.
  Proof.
    intros st target observed entry old next Ho Ha Hg.
    eapply aggregate_guarded_map; [| |exact Ha|exact Hg].
    - intros. eapply queued_observe; eauto.
    - intros. eapply aggregate_bounded_observe; eauto.
  Qed.

  Lemma aggregate_guarded_dirty_read : forall tf st owner target control,
    rank_valid st -> queue_valid st -> handle_valid st target ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := control |} ->
    aggregate_guarded {| R.cfg_state := R.dirty_get_ready_state tf st owner target;
      R.cfg_control := control |}.
  Proof.
    intros tf st owner target control Hr Hq Ht Hg x.
    destruct (Hg x) as [Hqueued|[Ha|Hb]].
    - destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
      + destruct (@queued_or_aggregate_bounded_dirty_get_ready_target tf st owner target Hqueued);
          [now left|now right;right].
      + left. eapply queued_dirty_get_ready_other_early; eauto.
    - now right; left.
    - right; right. now apply dirty_get_ready_state_preserves_aggregate_bound.
  Qed.
  Lemma aggregate_guarded_continue : forall st owner k,
    aggregate_bounded st (R.handle_variable owner) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := R.continue k |}.
  Proof.
    intros st owner k Hb Hg x. destruct (Hg x) as [Hq|[[->|Ha]|Hsound]].
    - now left.
    - now right; right.
    - right; left. now apply continuation_active_continue.
    - now right; right.
  Qed.

  Lemma aggregate_guarded_side_recursive : forall st source target raw old next,
    control_active (R.handle_variable target) next ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := R.side_ready_state st source target raw;
      R.cfg_control := next |}.
  Proof.
    intros st source target raw old next Ht Ha Hg x.
    destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
    - now right; left.
    - destruct (Hg x) as [Hq|[Hactive|Hb]].
      + left. now apply queued_side_ready.
      + right; left. auto.
      + right; right. now apply side_ready_state_other.
  Qed.

  Lemma aggregate_guarded_side_enqueued : forall st source target raw old next,
    rank_valid st -> queue_valid st -> handle_valid st target ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := R.enqueue_handle
      (R.side_ready_state st source target raw) target; R.cfg_control := next |}.
  Proof.
    intros st source target raw old next Hr Hq Ht Ha Hg x.
    destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
    - left. apply enqueue_handle_queues_variable.
      + now apply rank_valid_side_ready.
      + now apply queue_valid_side_ready.
      + now apply handle_valid_side_ready.
    - destruct (Hg x) as [Hqueued|[Hactive|Hb]].
      + left. now apply queued_enqueue_handle, queued_side_ready.
      + right; left. auto.
      + right; right. apply aggregate_bounded_enqueue_handle.
        now apply side_ready_state_other.
  Qed.

  Lemma aggregate_guarded_side_covered : forall st source target raw old next,
    R.aggregate_grew st (R.side_ready_state st source target raw)
      (R.handle_variable target) = false ->
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := R.side_ready_state st source target raw;
      R.cfg_control := next |}.
  Proof.
    intros st source target raw old next Hgrow Ha Hg.
    eapply aggregate_guarded_map; [| |exact Ha|exact Hg].
    - intros. now apply queued_side_ready.
    - intros x Hb. destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
      + now apply side_ready_state_not_grown.
      + now apply side_ready_state_other.
  Qed.

  Lemma aggregate_guarded_mark_side_dirty : forall st target control,
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := control |} ->
    aggregate_guarded {| R.cfg_state := R.mark_side_dirty st target;
      R.cfg_control := control |}.
  Proof. intros st target control H. exact H. Qed.

  Lemma aggregate_guarded_enqueue_mark_side_dirty : forall st entry target control,
    aggregate_guarded {| R.cfg_state := R.enqueue_handle st entry; R.cfg_control := control |} ->
    aggregate_guarded {| R.cfg_state := R.enqueue_handle (R.mark_side_dirty st target) entry;
      R.cfg_control := control |}.
  Proof. intros st entry target control H. exact H. Qed.

  Lemma aggregate_guarded_request_spawn : forall st target old next,
    (forall x, control_active x old -> control_active x next) ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := old |} ->
    aggregate_guarded {| R.cfg_state := R.request_spawn st target; R.cfg_control := next |}.
  Proof.
    intros st target old next Ha Hg. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st));
      eapply aggregate_guarded_map; [| |exact Ha|exact Hg| | |exact Ha|exact Hg];
      intros; assumption.
  Qed.

  Lemma aggregate_guarded_observed_facts : forall st control target next entry,
    handles_valid {| R.cfg_state := st; R.cfg_control := control |} ->
    aggregate_guarded {| R.cfg_state := st; R.cfg_control := control |} ->
    R.observe st target = (next, entry) ->
    aggregate_guarded {| R.cfg_state := next; R.cfg_control := control |} /\
    rank_valid next /\ queue_valid next /\ handle_valid next entry.
  Proof.
    intros st control target next entry Hv Hg Ho. repeat split.
    - eapply aggregate_guarded_observe; [exact Ho| |exact Hg]; auto.
    - eapply rank_valid_observe; [exact (handles_rank_valid Hv)|exact Ho].
    - eapply queue_valid_observe; [exact (handles_queue_valid Hv)|exact Ho].
    - eapply observed_handle_valid; exact Ho.
  Qed.

  Lemma aggregate_guarded_step : forall tf before after,
    handles_valid before -> aggregate_guarded before ->
    Sem.step tf before after -> aggregate_guarded after.
  Proof.
    intros tf [st control] after Hvalid Hguard Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst.
    all: try exact Hguard.
    all: try solve [eapply aggregate_guarded_pop; [| | |exact Hguard]; [eassumption|cbn; tauto|cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_observe; [| |exact Hguard]; [eassumption|cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hguard]; [intros; assumption|intros; assumption|cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hguard]; [intros; apply queued_get_ready; assumption|
      intros; apply aggregate_bounded_get_ready; assumption|cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hguard]; [intros; apply queued_set_value; assumption|
      intros; apply set_value_preserves_aggregate_bound; assumption|cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_continue; eassumption].
    all: try solve [eapply aggregate_guarded_request_spawn; [|exact Hguard]; cbn; intros; tauto].
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hguard];
      [intros; apply queued_start; assumption|
       intros; apply aggregate_bounded_start; assumption|cbn; intros; tauto]].
    all: try match goal with
    | Ho : Sem.R.observe ?before ?target = (?observed, ?entry) |- _ =>
      destruct (@aggregate_guarded_observed_facts before _ target observed entry Hvalid Hguard Ho)
        as [Hobserved [Hr [Hq Ht]]]
    end.
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hobserved];
      [intros; apply queued_get_ready, queued_enqueue_handle; assumption|
       intros; apply aggregate_bounded_get_ready, aggregate_bounded_enqueue_handle; assumption|
       cbn; intros; tauto]].
    all: try solve [eapply aggregate_guarded_map; [| | |exact Hobserved];
      [intros; apply queued_materialize, queued_enqueue_handle; assumption|
       intros; apply aggregate_bounded_materialize, aggregate_bounded_enqueue_handle; assumption|
       cbn; intros; tauto]].
    all: try apply aggregate_guarded_enqueue_mark_side_dirty.
    all: try apply aggregate_guarded_mark_side_dirty.
    all: try solve [eapply aggregate_guarded_side_recursive; [| |exact Hobserved]; cbn; intros; tauto].
    all: try solve [eapply aggregate_guarded_side_enqueued; [exact Hr|exact Hq|exact Ht| |exact Hobserved]; cbn; intros; tauto].
    - apply aggregate_guarded_dirty_read; [exact Hr|exact Hq|exact Ht|].
      eapply aggregate_guarded_map; [| | |exact Hobserved]; cbn; intros; assumption.
    - eapply aggregate_guarded_side_covered; [| |exact Hobserved].
      + rewrite (@observed_handle_variable st t s h0 Hcase0). exact Hcase2.
      + cbn; intros; assumption.
  Qed.
  Lemma aggregate_guarded_steps :
    forall tf first final,
      handles_valid first ->
      aggregate_guarded first ->
      Sem.steps tf first final ->
      aggregate_guarded final.
  Proof.
    intros tf first final Hvalid Hguard Hsteps.
    induction Hsteps; [exact Hguard |].
    apply IHHsteps.
    - eapply next_config_handles_valid; eauto.
    - eapply aggregate_guarded_step; eauto.
  Qed.

  Theorem terminal_aggregate_bounded :
    forall tf roots final,
      Sem.terminates_to tf roots final ->
      forall target, aggregate_bounded final target.
  Proof.
    intros tf roots final [Hsteps [Hquiet Hpending]] target.
    pose proof (@aggregate_guarded_steps tf
      (R.initial_config roots) (Sem.terminal_config final)
      (initial_handles_valid roots)
      (initial_aggregate_guarded roots) Hsteps target) as Hguard.
    destruct Hguard as [Hqueued | [Hactive | Hsound]].
    - destruct Hqueued as [entry [Hentry _]].
      cbn in Hentry.
      unfold R.queue_peek in Hquiet.
      destruct (R.queue final) as [|head tail] eqn:Hqueue.
      + exfalso. exact Hentry.
      + discriminate Hquiet.
    - contradiction.
    - exact Hsound.
  Qed.

  Lemma read_guarded_materialize :
    forall st reader event target,
      read_guarded st reader event ->
      read_guarded (R.materialize st target) reader event.
  Proof.
    intros st reader [observed value] target
      [Hsolved [Hregistered Hvalue]]. repeat split.
    - apply E.materialize_solved. exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued].
      + left. now apply reader_registered_materialize.
      + right. unfold queued in *. unfold R.materialize.
        destruct (R.is_materialized st target); exact Hqueued.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. now apply semantic_lookup_materialize_solved.
      + right. unfold queued in *. unfold R.materialize.
        destruct (R.is_materialized st target); exact Hqueued.
  Qed.

  Lemma effects_recorded_side_other :
    forall st active target raw source effects,
      source <> R.handle_variable active ->
      effects_recorded st source effects ->
      effects_recorded (R.side_ready_state st active target raw)
        source effects.
  Proof.
    intros st active target raw source effects Hneq Hrecorded.
    eapply Forall_impl; [|exact Hrecorded].
    intros [observed value] [contribution [Hlookup Hbelow]].
    exists contribution. split; [|exact Hbelow].
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank active));
      [|unfold R.promote_controlled];
      unfold R.record_side_payload; cbn.
    all: destruct (V.eq_dec observed (R.handle_variable target))
      as [-> | Htarget].
    all: try (rewrite lookup_update_map_other_outer
      by exact Htarget; exact Hlookup).
    all: rewrite lookup_update_map_other_inner by exact Hneq;
      exact Hlookup.
  Qed.

  Fixpoint continuation_history
    (tf : R.ConstraintSystem.system) (st : R.state)
    (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop _ rest => continuation_history tf st rest
    | R.KAfterGet owner target next rest =>
        rhs_progress tf st (R.handle_variable owner)
          (R.ConstraintSystem.Get (R.handle_variable target) next) /\
        continuation_history tf st rest
    | R.KAfterSide owner next rest
    | R.KAfterSpawn owner next rest =>
        rhs_progress tf st (R.handle_variable owner) next /\
        continuation_history tf st rest
    end.

  Definition control_history
    (tf : R.ConstraintSystem.system) (st : R.state)
    (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne _ rest | R.RunSolveOneLoop _ rest =>
        continuation_history tf st rest
    | R.RunRhs owner body rest =>
        rhs_progress tf st (R.handle_variable owner) body /\
        continuation_history tf st rest
    | R.AfterGet owner target next rest =>
        rhs_progress tf st (R.handle_variable owner)
          (R.ConstraintSystem.Get (R.handle_variable target) next) /\
        continuation_history tf st rest
    | R.AfterSide owner next rest | R.AfterSpawn owner next rest =>
        rhs_progress tf st (R.handle_variable owner) next /\
        continuation_history tf st rest
    end.

  Lemma continuation_history_continue :
    forall tf st k,
      continuation_history tf st k -> control_history tf st (R.continue k).
  Proof. intros tf st k H; destruct k; exact H. Qed.

  Lemma local_sides_enqueue_all :
    forall xs st, R.local_sides (R.enqueue_all st xs) = R.local_sides st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma effects_accumulated_write_changed_value :
    forall st source effects owner value,
      effects_accumulated st source effects ->
      effects_accumulated (R.write_changed_value st owner value)
        source effects.
  Proof.
    intros st source effects owner value Haccumulated.
    unfold effects_accumulated, effect_accumulated in *.
    unfold R.write_changed_value. cbn.
    rewrite local_sides_enqueue_all. exact Haccumulated.
  Qed.

  Lemma effects_accumulated_set_value :
    forall st source effects owner direct,
      effects_accumulated st source effects ->
      effects_accumulated (R.set_value st owner direct) source effects.
  Proof.
    intros st source effects owner direct Haccumulated.
    unfold effects_accumulated, effect_accumulated in *.
    unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Haccumulated |].
    destruct (S.mem owner (R.controlled st));
      [|now apply effects_accumulated_write_changed_value].
    destruct (U.update false owner (R.stored_phase st owner)
      (R.sigma_value st owner)
      (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
    destruct (R.equivalent value (R.sigma_value st owner));
      [exact Haccumulated |now apply effects_accumulated_write_changed_value].
  Qed.

  Lemma rhs_progress_set_value :
    forall tf st source body owner direct,
      rank_valid st -> queue_valid st ->
      rhs_progress tf st source body ->
      rhs_progress tf (R.set_value st owner direct) source body.
  Proof.
    intros tf st source body owner direct Hrank Hqueue
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply reads_guarded_set_value; eauto.
    - apply effects_recorded_set_value. exact Hrecorded.
    - apply effects_accumulated_set_value. exact Haccumulated.
  Qed.

  Lemma effects_accumulated_side_other :
    forall st active target raw source effects,
      source <> R.handle_variable active ->
      effects_accumulated st source effects ->
      effects_accumulated (R.side_ready_state st active target raw)
        source effects.
  Proof.
    intros st active target raw source effects Hneq Haccumulated.
    eapply Forall_impl; [|exact Haccumulated].
    intros [observed value] [accumulated [Hlookup Hbelow]].
    exists accumulated. split; [|exact Hbelow].
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank active));
      [|unfold R.promote_controlled]; unfold R.record_side_payload; cbn.
    all: rewrite lookup_update_map_other_outer by exact Hneq;
      exact Hlookup.
  Qed.

  Lemma rhs_progress_side_other :
    forall tf st active target raw source body,
      source <> R.handle_variable active ->
      rhs_progress tf st source body ->
      rhs_progress tf (R.side_ready_state st active target raw) source body.
  Proof.
    intros tf st active target raw source body Hneq
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - apply reads_guarded_side_ready. exact Hreads.
    - eapply effects_recorded_side_other; eauto.
    - eapply effects_accumulated_side_other; eauto.
  Qed.

  Lemma rhs_progress_materialize :
    forall tf st owner body target,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.materialize st target) owner body.
  Proof.
    intros tf st owner body target
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads].
      intros. now apply read_guarded_materialize.
    - unfold R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) target); exact Hrecorded.
    - unfold R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) target); exact Haccumulated.
  Qed.

  Lemma rhs_progress_start_other :
    forall tf st active source body,
      source <> active -> rhs_progress tf st source body ->
      rhs_progress tf (R.start_evaluation st active) source body.
  Proof.
    intros tf st active source body Hneq
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads]. intros.
      unfold R.start_evaluation, R.reset_local_sides.
      now apply read_guarded_materialize.
    - unfold R.start_evaluation, R.reset_local_sides,
        R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) active); exact Hrecorded.
    - unfold R.start_evaluation, R.reset_local_sides,
        effects_accumulated, effect_accumulated in *.
      unfold R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) active).
      + eapply Forall_impl; [|exact Haccumulated].
        intros [observed value] [accumulated [Hlookup Hbelow]].
        exists accumulated. split; [|exact Hbelow]. cbn.
        unfold R.lookup_map.
        rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      + eapply Forall_impl; [|exact Haccumulated].
        intros [observed value] [accumulated [Hlookup Hbelow]].
        exists accumulated. split; [|exact Hbelow]. cbn.
        unfold R.lookup_map.
        rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
  Qed.



  Lemma rhs_progress_add_reader :
    forall tf st target added owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.add_reader st target added) owner body.
  Proof.
    intros tf st target added owner body
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - now apply reads_guarded_add_reader.
    - unfold effects_recorded, effect_recorded, R.add_reader,
        R.promote_controlled in *; exact Hrecorded.
    - unfold effects_accumulated, effect_accumulated, R.add_reader,
        R.promote_controlled in *; exact Haccumulated.
  Qed.

  Lemma rhs_progress_remember_dormant :
    forall tf st target owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.remember_dormant st target) owner body.
  Proof.
    intros tf st target owner body
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - now apply reads_guarded_remember_dormant.
    - unfold effects_recorded, effect_recorded, R.remember_dormant,
        R.with_dormant_bottom in *; exact Hrecorded.
    - unfold effects_accumulated, effect_accumulated,
        R.remember_dormant, R.with_dormant_bottom in *; exact Haccumulated.
  Qed.

  Lemma rhs_progress_get_dormant :
    forall tf st owner target next,
      R.is_dormant st target = true ->
      rhs_progress tf st owner (R.ConstraintSystem.Get target next) ->
      rhs_progress tf (R.add_reader st target owner) owner
        (next D.bottom).
  Proof.
    intros tf st owner target next Hdormant
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists (reads ++ [(target, D.bottom)]), effects. repeat split.
    - eapply rhs_prefix_snoc_get. exact Hprefix.
    - apply Forall_app. split.
      + now apply reads_guarded_add_reader.
      + constructor; [|constructor]. repeat split.
        * apply E.add_reader_solved. exists D.bottom.
          now apply semantic_lookup_dormant.
        * left. apply reader_registered_add.
        * left. rewrite semantic_lookup_add_reader.
          now apply semantic_lookup_dormant.
    - unfold effects_recorded, effect_recorded, R.add_reader,
        R.promote_controlled in *; exact Hrecorded.
    - unfold effects_accumulated, effect_accumulated, R.add_reader,
        R.promote_controlled in *; exact Haccumulated.
  Qed.

  Lemma rhs_progress_get_remembered :
    forall tf st owner target next,
      R.is_dormant (R.remember_dormant st target) target = true ->
      rhs_progress tf st owner (R.ConstraintSystem.Get target next) ->
      rhs_progress tf
        (R.add_reader (R.remember_dormant st target) target owner) owner
        (next D.bottom).
  Proof.
    intros. apply rhs_progress_get_dormant; [exact H |].
    now apply rhs_progress_remember_dormant.
  Qed.

  Lemma rhs_progress_get_ready_preserved :
    forall tf st source body owner target,
      rhs_progress tf st source body ->
      rhs_progress tf (R.get_ready_state st owner target) source body.
  Proof.
    intros tf st source body owner target
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads].
      intros [observed value] [Hsolved [Hregistered Hvalue]].
      repeat split.
      + apply E.get_ready_state_solved. exact Hsolved.
      + destruct Hregistered as [Hregistered | Hqueued].
        * left. unfold R.get_ready_state.
          apply reader_registered_materialize,
            reader_registered_add_preserved.
          unfold R.promote_controlled.
          destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
            exact Hregistered.
        * right. unfold queued in *.
          now apply queued_get_ready.
      + destruct Hvalue as [Hvalue | Hqueued].
        * left. now apply semantic_lookup_get_ready_solved.
        * right. unfold queued in *.
          now apply queued_get_ready.
    - unfold effects_recorded, effect_recorded in *.
      unfold R.get_ready_state, R.materialize, R.is_materialized.
      destruct (M.lookup
        (R.sigma (R.add_reader
          (if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
           then st else R.promote_controlled st (R.handle_variable target))
          (R.handle_variable target) (R.handle_variable owner)))
        (R.handle_variable target));
        unfold R.add_reader, R.promote_controlled;
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrecorded.
    - unfold effects_accumulated, effect_accumulated in *.
      unfold R.get_ready_state, R.materialize, R.is_materialized.
      destruct (M.lookup
        (R.sigma (R.add_reader
          (if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
           then st else R.promote_controlled st (R.handle_variable target))
          (R.handle_variable target) (R.handle_variable owner)))
        (R.handle_variable target));
        unfold R.add_reader, R.promote_controlled;
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Haccumulated.
  Qed.

  Lemma rhs_progress_pop_other :
    forall tf st popped rest owner body,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      owner <> R.handle_variable popped ->
      rhs_progress tf st owner body ->
      rhs_progress tf (R.with_queue st rest) owner body.
  Proof.
    intros tf st popped rest owner body Hpop Hneq
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads].
      intros [target value] [Hsolved [Hregistered Hvalue]].
      repeat split; [exact Hsolved | |].
      + destruct Hregistered as [Hregistered | Hqueued]; [now left |].
        right. eapply queued_pop_other; eauto.
      + destruct Hvalue as [Hvalue | Hqueued]; [now left |].
        right. eapply queued_pop_other; eauto.
    - exact Hrecorded.
    - exact Haccumulated.
  Qed.

  Fixpoint continuation_excludes
    (x : V.t) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest
    | R.KAfterGet owner _ _ rest
    | R.KAfterSide owner _ rest
    | R.KAfterSpawn owner _ rest =>
        R.handle_variable owner <> x /\ continuation_excludes x rest
    end.

  Lemma continuation_ordered_weaken :
    forall lower upper k,
      R.handle_rank lower < R.handle_rank upper ->
      ControlStack.continuation_ordered lower k ->
      ControlStack.continuation_ordered upper k.
  Proof.
    intros lower upper k Hlt Hordered. destruct k; cbn in *; try exact I.
    all: destruct Hordered as [Hhead Htail].
    all: split; [|exact Htail].
    all: apply Nat.ltb_lt in Hhead; apply Nat.ltb_lt; lia.
  Qed.

  Lemma continuation_ordered_excludes :
    forall st upper k,
      handle_valid st upper ->
      continuation_valid st k ->
      ControlStack.continuation_ordered upper k ->
      continuation_excludes (R.handle_variable upper) k.
  Proof.
    intros st upper k Hupper. revert upper Hupper.
    induction k; intros upper Hupper Hvalid Hordered; cbn in *; try exact I.
    all: destruct Hvalid as [Hhead_valid Htail_valid].
    all: destruct Hordered as [Hhead_order Htail_order].
    all: apply Nat.ltb_lt in Hhead_order; split.
    all: try (eapply valid_ranked_variables_differ; eauto).
    all: eapply IHk; eauto using continuation_ordered_weaken.
    exact (proj2 Htail_valid).
  Qed.

  Lemma continuation_history_map :
    forall tf before after,
      (forall owner body,
        rhs_progress tf before owner body ->
        rhs_progress tf after owner body) ->
      forall k,
        continuation_history tf before k ->
        continuation_history tf after k.
  Proof.
    intros tf before after Hmap k. induction k; cbn; intros Hhistory;
      try exact I.
    - now apply IHk.
    - destruct Hhistory. split; eauto.
    - destruct Hhistory. split; eauto.
    - destruct Hhistory. split; eauto.
  Qed.

  Lemma continuation_history_add_reader :
    forall tf st target added k,
      continuation_history tf st k ->
      continuation_history tf (R.add_reader st target added) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_add_reader.
  Qed.

  Lemma continuation_history_remember_dormant :
    forall tf st target k,
      continuation_history tf st k ->
      continuation_history tf (R.remember_dormant st target) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_remember_dormant.
  Qed.

  Lemma continuation_history_observe :
    forall tf st observed next entry k,
      R.observe st observed = (next, entry) ->
      continuation_history tf st k -> continuation_history tf next k.
  Proof.
    intros. eapply continuation_history_map; [|exact H0].
    intros. eapply rhs_progress_observe; eauto.
  Qed.

  Lemma continuation_history_enqueue_handle :
    forall tf st inserted k,
      continuation_history tf st k ->
      continuation_history tf (R.enqueue_handle st inserted) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_enqueue_handle.
  Qed.

  Lemma continuation_history_materialize :
    forall tf st target k,
      continuation_history tf st k ->
      continuation_history tf (R.materialize st target) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_materialize.
  Qed.

  Lemma continuation_history_get_ready :
    forall tf st owner target k,
      continuation_history tf st k ->
      continuation_history tf (R.get_ready_state st owner target) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_get_ready_preserved.
  Qed.

  Lemma continuation_history_set_value :
    forall tf st owner direct k,
      rank_valid st -> queue_valid st ->
      continuation_history tf st k ->
      continuation_history tf (R.set_value st owner direct) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H1].
    intros. eapply rhs_progress_set_value; eauto.
  Qed.

  Lemma continuation_history_start :
    forall tf st active k,
      continuation_excludes active k ->
      continuation_history tf st k ->
      continuation_history tf (R.start_evaluation st active) k.
  Proof.
    intros tf st active k. induction k; cbn;
      intros Hexcludes Hhistory; try exact I.
    - apply IHk; [exact (proj2 Hexcludes) |exact Hhistory].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_start_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_start_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_start_other; eauto |eauto].
  Qed.

  Lemma continuation_history_side :
    forall tf st active target raw k,
      continuation_excludes (R.handle_variable active) k ->
      continuation_history tf st k ->
      continuation_history tf (R.side_ready_state st active target raw) k.
  Proof.
    intros tf st active target raw k. induction k; cbn;
      intros Hexcludes Hhistory; try exact I.
    - apply IHk; [exact (proj2 Hexcludes) |exact Hhistory].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_side_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_side_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_side_other; eauto |eauto].
  Qed.

  Lemma continuation_history_pop :
    forall tf st popped rest k,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      continuation_excludes (R.handle_variable popped) k ->
      continuation_history tf st k ->
      continuation_history tf (R.with_queue st rest) k.
  Proof.
    intros tf st popped rest k Hpop. induction k; cbn;
      intros Hexcludes Hhistory; try exact I.
    - apply IHk; [exact (proj2 Hexcludes) |exact Hhistory].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_pop_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_pop_other; eauto |eauto].
    - destruct Hexcludes, Hhistory. split;
        [eapply rhs_progress_pop_other; eauto |eauto].
  Qed.

  Lemma rhs_progress_with_started :
    forall tf st started owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.with_started st started) owner body.
  Proof. intros. exact H. Qed.

  Lemma continuation_history_with_started :
    forall tf st started k,
      continuation_history tf st k ->
      continuation_history tf (R.with_started st started) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply rhs_progress_with_started.
  Qed.

  Lemma rhs_progress_with_phases :
    forall tf st phases owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.with_phases st phases) owner body.
  Proof. intros. exact H. Qed.

  Lemma summary_materialize :
    forall tf st owner target,
      summary_valid tf st owner ->
      summary_valid tf (R.materialize st target) owner.
  Proof.
    intros tf st owner target
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads].
      intros. now apply read_guarded_materialize.
    - unfold R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) target); exact Hrecorded.
    - rewrite materialize_value. exact Hdirect.
  Qed.

  Lemma summary_observe :
    forall tf st observed next entry owner,
      R.observe st observed = (next, entry) ->
      summary_valid tf st owner -> summary_valid tf next owner.
  Proof.
    intros tf st observed next entry owner Hobserve
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply reads_guarded_observe; eauto.
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) observed);
        inversion Hobserve; subst; exact Hrecorded.
    - unfold R.observe in Hobserve. destruct (R.Ranking.observe _ _);
        inversion Hobserve; subst; exact Hdirect.
  Qed.

  Lemma summary_enqueue_handle :
    forall tf st owner inserted,
      summary_valid tf st owner ->
      summary_valid tf (R.enqueue_handle st inserted) owner.
  Proof.
    intros tf st owner inserted
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - apply reads_guarded_enqueue_handle. exact Hreads.
    - exact Hrecorded.
    - exact Hdirect.
  Qed.

  Lemma summary_start_other :
    forall tf st active owner,
      owner <> active ->
      summary_valid tf st owner ->
      summary_valid tf (R.start_evaluation st active) owner.
  Proof.
    intros tf st active owner Hneq
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads]. intros.
      unfold R.start_evaluation, R.reset_local_sides.
      now apply read_guarded_materialize.
    - unfold R.start_evaluation, R.reset_local_sides,
        R.materialize, R.is_materialized.
      destruct (M.lookup (R.sigma st) active); exact Hrecorded.
    - change (D.leq direct (R.sigma_value (R.materialize st active) owner) = true).
      now rewrite materialize_value.
  Qed.

  Lemma summary_get_ready :
    forall tf st summary_owner owner target,
      summary_valid tf st summary_owner ->
      summary_valid tf (R.get_ready_state st owner target) summary_owner.
  Proof.
    intros tf st summary_owner owner target
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads].
      intros [observed value] [Hsolved [Hregistered Hvalue]].
      repeat split.
      + apply E.get_ready_state_solved. exact Hsolved.
      + destruct Hregistered as [Hregistered | Hqueued].
        * left. unfold R.get_ready_state.
          apply reader_registered_materialize,
            reader_registered_add_preserved.
          unfold R.promote_controlled.
          destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
            exact Hregistered.
        * right. unfold queued in *.
          now apply queued_get_ready.
      + destruct Hvalue as [Hvalue | Hqueued].
        * left. now apply semantic_lookup_get_ready_solved.
        * right. unfold queued in *.
          now apply queued_get_ready.
    - unfold effects_recorded, effect_recorded in *.
      unfold R.get_ready_state, R.materialize, R.is_materialized.
      destruct (M.lookup
        (R.sigma (R.add_reader
          (if Nat.ltb (R.handle_rank owner) (R.handle_rank target)
           then st else R.promote_controlled st (R.handle_variable target))
          (R.handle_variable target) (R.handle_variable owner)))
        (R.handle_variable target));
        unfold R.add_reader, R.promote_controlled;
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrecorded.
    - rewrite get_ready_state_value. exact Hdirect.
  Qed.

  Lemma read_guarded_cancel_dirty_target_other :
    forall st target reader event,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      reader <> R.handle_variable target ->
      read_guarded st reader event ->
      read_guarded (R.cancel_dirty_target st target) reader event.
  Proof.
    intros st target reader [observed value] Hrank Hqueue Htarget Hneq
      [Hsolved [Hregistered Hvalue]]. repeat split.
    - exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued]; [now left |right].
      eapply queued_cancel_dirty_target_other; eauto.
    - destruct Hvalue as [Hvalue | Hqueued]; [now left |right].
      eapply queued_cancel_dirty_target_other; eauto.
  Qed.

  Lemma summary_cancel_dirty_target_other :
    forall tf st target owner,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      owner <> R.handle_variable target ->
      summary_valid tf st owner ->
      summary_valid tf (R.cancel_dirty_target st target) owner.
  Proof.
    intros tf st target owner Hrank Hqueue Htarget Hneq
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hbelow]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads]. intros event Hguarded.
      eapply read_guarded_cancel_dirty_target_other; eauto.
    - unfold effects_recorded, effect_recorded, R.cancel_dirty_target,
        R.clear_side_dirty, R.with_dirty_side_targets, R.with_queue in *.
      exact Hrecorded.
    - exact Hbelow.
  Qed.

  Lemma summary_write_changed_value_other :
    forall tf st changed value owner,
      rank_valid st -> queue_valid st ->
      owner <> changed ->
      summary_valid tf st owner ->
      summary_valid tf (R.write_changed_value st changed value) owner.
  Proof.
    intros tf st changed value owner Hrank Hqueue Hneq
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hbelow]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads]. intros event Hguarded.
      eapply read_guarded_write_changed_value; eauto.
    - now apply effects_recorded_write_changed_value.
    - rewrite write_changed_value_other by exact Hneq.
      exact Hbelow.
  Qed.

  Lemma summary_with_started :
    forall tf st started owner,
      summary_valid tf st owner ->
      summary_valid tf (R.with_started st started) owner.
  Proof.
    intros tf st started owner [direct [reads [effects Hsummary]]].
    now exists direct, reads, effects.
  Qed.

  Lemma summary_with_phases :
    forall tf st phases owner,
      summary_valid tf st owner ->
      summary_valid tf (R.with_phases st phases) owner.
  Proof.
    intros tf st phases owner [direct [reads [effects Hsummary]]].
    now exists direct, reads, effects.
  Qed.

  Lemma rank_valid_with_started_state :
    forall st started,
      rank_valid st -> rank_valid (R.with_started st started).
  Proof. intros; exact H. Qed.

  Lemma rank_valid_with_phases_state :
    forall st phases,
      rank_valid st -> rank_valid (R.with_phases st phases).
  Proof. intros; exact H. Qed.

  Lemma queue_valid_with_started_state :
    forall st started,
      queue_valid st -> queue_valid (R.with_started st started).
  Proof. intros; exact H. Qed.

  Lemma queue_valid_with_phases_state :
    forall st phases,
      queue_valid st -> queue_valid (R.with_phases st phases).
  Proof. intros; exact H. Qed.

  Lemma summary_try_dirty_read_target : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next ->
    summary_valid tf next (R.handle_variable target).
  Proof.
    intros tf st owner target next Hread.
    destruct (@try_dirty_read_candidate tf st owner target next Hread)
      as [direct [Htf Hbound]].
    exists direct, [], []. repeat split.
    - rewrite Htf. constructor.
    - constructor.
    - constructor.
    - eapply DL.leq_trans; [apply DL.join_upper_left|exact Hbound].
  Qed.

  Lemma summary_try_dirty_read_other :
    forall tf st owner target next tracked,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      tracked <> R.handle_variable target ->
      summary_valid tf st tracked ->
      R.try_dirty_read tf st owner target = Some next ->
      summary_valid tf next tracked.
  Proof.
    intros tf st owner target next tracked Hrank Hqueue Htarget Hneq
      Hsummary Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try apply summary_with_started in Hsummary.
    all: try apply summary_with_phases in Hsummary.
    all: try (eapply summary_cancel_dirty_target_other; eauto).
    all: eapply summary_write_changed_value_other.
    all: try (apply rank_valid_cancel_dirty_target; exact Hrank).
    all: try (apply queue_valid_cancel_dirty_target; exact Hqueue).
    all: try exact Hneq.
    all: eapply summary_cancel_dirty_target_other;
      try exact Hrank; try exact Hqueue; try exact Htarget; try exact Hneq.
    all: repeat first [apply summary_with_started | apply summary_with_phases].
    all: exact Hsummary.
  Qed.

  Lemma summary_get_control_state :
    forall tf st owner target tracked,
      summary_valid tf st tracked ->
      summary_valid tf (R.get_control_state st owner target) tracked.
  Proof.
    intros tf st owner target tracked Hsummary. unfold R.get_control_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      [exact Hsummary |].
    unfold R.promote_controlled.
    destruct Hsummary as [direct [reads [effects Hsummary]]].
    now exists direct, reads, effects.
  Qed.

  Lemma summary_add_reader_early :
    forall tf st target added owner,
      summary_valid tf st owner ->
      summary_valid tf (R.add_reader st target added) owner.
  Proof.
    intros tf st target added owner
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - now apply reads_guarded_add_reader.
    - unfold effects_recorded, effect_recorded, R.add_reader,
        R.promote_controlled in *; exact Hrecorded.
    - unfold R.sigma_value, R.add_reader, R.promote_controlled.
      exact Hdirect.
  Qed.

  Lemma summary_dirty_get_ready :
    forall tf st owner target tracked,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      summary_valid tf st tracked ->
      summary_valid tf (R.dirty_get_ready_state tf st owner target) tracked.
  Proof.
    intros tf st owner target tracked Hrank Hqueue Htarget Hsummary.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_summary : summary_valid tf prepared tracked).
    { subst prepared. apply summary_materialize, summary_get_control_state.
      exact Hsummary. }
    assert (Hprepared_rank : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrank. }
    assert (Hprepared_queue : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hqueue. }
    assert (Hprepared_target : handle_valid prepared target).
    { eapply handle_valid_extended; [|exact Htarget].
      subst prepared. eapply (@rank_extends_trans st
        (R.get_control_state st owner target));
        [|apply rank_extends_materialize].
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        apply rank_extends_same_ranking; reflexivity. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; apply summary_add_reader_early.
    - destruct (V.eq_dec tracked (R.handle_variable target)) as [-> | Hneq].
      + eapply summary_try_dirty_read_target; eauto.
      + eapply summary_try_dirty_read_other; eauto.
    - exact Hprepared_summary.
  Qed.

  Lemma summary_set_value_other :
    forall tf st active direct owner,
      rank_valid st -> queue_valid st ->
      owner <> active -> summary_valid tf st owner ->
      summary_valid tf (R.set_value st active direct) owner.
  Proof.
    intros tf st active direct owner Hrank Hqueue Hneq
      [summary_direct [reads [effects
        [Htrace [Hreads [Hrecorded Hbelow]]]]]].
    exists summary_direct, reads, effects. repeat split; try exact Htrace.
    - eapply reads_guarded_set_value; eauto.
    - apply effects_recorded_set_value. exact Hrecorded.
    - rewrite set_value_other by exact Hneq.
      exact Hbelow.
  Qed.

  Lemma summary_side_other :
    forall tf st active target raw owner,
      owner <> R.handle_variable active ->
      summary_valid tf st owner ->
      summary_valid tf (R.side_ready_state st active target raw) owner.
  Proof.
    intros tf st active target raw owner Hneq
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hbelow]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - apply reads_guarded_side_ready. exact Hreads.
    - eapply effects_recorded_side_other; eauto.
    - unfold R.side_ready_state. destruct (Nat.ltb _ _); exact Hbelow.
  Qed.

  Lemma summary_pop_other :
    forall tf st popped rest owner,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      owner <> R.handle_variable popped ->
      summary_valid tf st owner ->
      summary_valid tf (R.with_queue st rest) owner.
  Proof.
    intros tf st popped rest owner Hpop Hneq
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hbelow]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - eapply Forall_impl; [|exact Hreads].
      intros [target value] [Hsolved [Hregistered Hvalue]].
      repeat split; [exact Hsolved | |].
      + destruct Hregistered as [Hregistered | Hqueued]; [now left |].
        right. eapply queued_pop_other; eauto.
      + destruct Hvalue as [Hvalue | Hqueued]; [now left |].
        right. eapply queued_pop_other; eauto.
    - exact Hrecorded.
    - exact Hbelow.
  Qed.

  Lemma try_dirty_read_ret : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next ->
    exists direct, tf (R.handle_variable target) = R.ConstraintSystem.Ret direct.
  Proof.
    intros. destruct (@try_dirty_read_candidate tf st owner target next H) as [direct [Heq _]]. eauto.
  Qed.

  Lemma semantic_solved_of_materialized : forall st x,
    Progress.solved st x -> Sem.solved st x.
  Proof. intros. apply E.solved_characterization. now left. Qed.

  Lemma rhs_prefix_from_ret :
    forall direct current reads effects,
      rhs_prefix (R.ConstraintSystem.Ret direct) current reads effects ->
      current = R.ConstraintSystem.Ret direct /\ reads = [] /\ effects = [].
  Proof.
    intros direct current reads effects Hprefix.
    inversion Hprefix; subst; repeat split; reflexivity.
  Qed.

  Lemma rhs_progress_cancel_dirty_target_other :
    forall tf st target owner body,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      owner <> R.handle_variable target ->
      rhs_progress tf st owner body ->
      rhs_progress tf (R.cancel_dirty_target st target) owner body.
  Proof.
    intros tf st target owner body Hrank Hqueue Htarget Hneq
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads]. intros event Hguarded.
      eapply read_guarded_cancel_dirty_target_other; eauto.
    - unfold effects_recorded, effect_recorded, R.cancel_dirty_target,
        R.clear_side_dirty, R.with_dirty_side_targets, R.with_queue in *.
      exact Hrecorded.
    - unfold effects_accumulated, effect_accumulated,
        R.cancel_dirty_target, R.clear_side_dirty,
        R.with_dirty_side_targets, R.with_queue in *.
      exact Haccumulated.
  Qed.

  Lemma rhs_progress_write_changed_value :
    forall tf st changed value owner body,
      rank_valid st -> queue_valid st ->
      rhs_progress tf st owner body ->
      rhs_progress tf (R.write_changed_value st changed value) owner body.
  Proof.
    intros tf st changed value owner body Hrank Hqueue
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply Forall_impl; [|exact Hreads]. intros event Hguarded.
      eapply read_guarded_write_changed_value; eauto.
    - now apply effects_recorded_write_changed_value.
    - now apply effects_accumulated_write_changed_value.
  Qed.

  Lemma rhs_progress_try_dirty_read_other :
    forall tf st owner target next tracked body,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      tracked <> R.handle_variable target ->
      rhs_progress tf st tracked body ->
      R.try_dirty_read tf st owner target = Some next ->
      rhs_progress tf next tracked body.
  Proof.
    intros tf st owner target next tracked body Hrank Hqueue Htarget Hneq
      Hprogress Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try apply rhs_progress_with_started in Hprogress.
    all: try apply rhs_progress_with_phases in Hprogress.
    all: try (eapply rhs_progress_cancel_dirty_target_other; eauto).
    all: eapply rhs_progress_write_changed_value.
    all: try (apply rank_valid_cancel_dirty_target; exact Hrank).
    all: try (apply queue_valid_cancel_dirty_target; exact Hqueue).
    all: eapply rhs_progress_cancel_dirty_target_other;
      try exact Hrank; try exact Hqueue; try exact Htarget; try exact Hneq.
    all: repeat first
      [apply rhs_progress_with_started | apply rhs_progress_with_phases].
    all: exact Hprogress.
  Qed.

  Lemma rhs_progress_try_dirty_read :
    forall tf st owner target next tracked body,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      rhs_progress tf st tracked body ->
      R.try_dirty_read tf st owner target = Some next ->
      rhs_progress tf next tracked body.
  Proof.
    intros tf st owner target next tracked body Hrank Hqueue Htarget
      Hprogress Hread.
    destruct (V.eq_dec tracked (R.handle_variable target)) as [-> | Hneq].
    - destruct (@try_dirty_read_ret tf st owner target next Hread)
        as [direct Htf].
      destruct Hprogress as [reads [effects
        [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
      rewrite Htf in Hprefix.
      apply rhs_prefix_from_ret in Hprefix.
      destruct Hprefix as [-> [-> ->]].
      unfold rhs_progress. rewrite Htf.
      exists [], []. repeat split; constructor.
    - eapply rhs_progress_try_dirty_read_other; eauto.
  Qed.

  Lemma rhs_progress_dirty_get_ready_preserved :
    forall tf st owner target tracked body,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      rhs_progress tf st tracked body ->
      rhs_progress tf (R.dirty_get_ready_state tf st owner target)
        tracked body.
  Proof.
    intros tf st owner target tracked body Hrank Hqueue Htarget Hprogress.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_progress : rhs_progress tf prepared tracked body).
    { subst prepared. apply rhs_progress_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        [exact Hprogress |].
      unfold R.promote_controlled. exact Hprogress. }
    assert (Hprepared_rank : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrank. }
    assert (Hprepared_queue : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hqueue. }
    assert (Hprepared_target : handle_valid prepared target).
    { eapply handle_valid_extended; [|exact Htarget].
      subst prepared. eapply (@rank_extends_trans st
        (R.get_control_state st owner target));
        [|apply rank_extends_materialize].
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        apply rank_extends_same_ranking; reflexivity. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; apply rhs_progress_add_reader.
    - eapply rhs_progress_try_dirty_read; eauto.
    - exact Hprepared_progress.
  Qed.

  Lemma semantic_solved_dirty_get_ready_target :
    forall tf st owner target,
      Sem.solved (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target).
  Proof.
    intros tf st owner target. apply semantic_solved_of_materialized.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : Progress.solved prepared (R.handle_variable target)).
    { subst prepared. apply Progress.solved_materialize_self. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; unfold R.add_reader.
    - change (Progress.solved next (R.handle_variable target)).
      eapply Progress.solved_try_dirty_read; eauto.
    - exact Hprepared.
  Qed.

  Lemma rhs_progress_dirty_get :
    forall tf st owner target next,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      rhs_progress tf st (R.handle_variable owner)
        (R.ConstraintSystem.Get (R.handle_variable target) next) ->
      rhs_progress tf (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable owner)
        (next (R.sigma_value (R.dirty_get_ready_state tf st owner target)
          (R.handle_variable target))).
  Proof.
    intros tf st owner target next Hrank Hqueue Htarget Hprogress.
    pose proof (@rhs_progress_dirty_get_ready_preserved tf st owner target
      (R.handle_variable owner)
      (R.ConstraintSystem.Get (R.handle_variable target) next)
      Hrank Hqueue Htarget Hprogress) as Hpreserved.
    destruct Hpreserved as [reads [effects
      [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists (reads ++ [(R.handle_variable target,
      R.sigma_value (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target))]), effects.
    repeat split.
    - eapply rhs_prefix_snoc_get. exact Hprefix.
    - apply Forall_app. split; [exact Hreads |].
      constructor; [|constructor]. repeat split.
      + apply semantic_solved_dirty_get_ready_target.
      + left. unfold R.dirty_get_ready_state.
        set (prepared := R.materialize
          (R.get_control_state st owner target) (R.handle_variable target)).
        destruct (R.try_dirty_read tf prepared owner target);
          apply reader_registered_add.
      + left. apply semantic_lookup_solved.
        apply semantic_solved_dirty_get_ready_target.
    - exact Hrecorded.
    - exact Haccumulated.
  Qed.

  Lemma continuation_history_dirty_get_ready :
    forall tf st owner target k,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      continuation_history tf st k ->
      continuation_history tf (R.dirty_get_ready_state tf st owner target) k.
  Proof.
    intros tf st owner target k Hrank Hqueue Htarget Hhistory.
    eapply continuation_history_map; [|exact Hhistory].
    intros tracked body Hprogress.
    eapply rhs_progress_dirty_get_ready_preserved; eauto.
  Qed.

  Lemma rhs_progress_mark_side_dirty :
    forall tf st target owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.mark_side_dirty st target) owner body.
  Proof.
    intros tf st target owner body [reads [effects Hprogress]].
    now exists reads, effects.
  Qed.

  Lemma continuation_history_mark_side_dirty :
    forall tf st target k,
      continuation_history tf st k ->
      continuation_history tf (R.mark_side_dirty st target) k.
  Proof.
    intros tf st target k Hhistory.
    eapply continuation_history_map; [|exact Hhistory].
    intros owner body Hprogress. now apply rhs_progress_mark_side_dirty.
  Qed.

  Lemma continuation_valid_observe :
    forall st observed next entry k,
      R.observe st observed = (next, entry) ->
      continuation_valid st k ->
      continuation_valid next k.
  Proof.
    intros. eapply continuation_valid_extended; [|exact H0].
    eapply rank_extends_observe; eauto.
  Qed.

  Lemma rhs_progress_spawn : forall tf st owner target next,
    spawned target ->
    rhs_progress tf st owner (R.ConstraintSystem.Spawn target next) ->
    rhs_progress tf st owner next.
  Proof.
    intros tf st owner target next Hspawn [reads [effects [Hp [Hr [He Hl]]]]].
    exists reads, effects. repeat split; auto. eapply rhs_prefix_snoc_spawn; eassumption.
  Qed.

  Lemma continuation_history_request_spawn : forall tf st target k,
    continuation_history tf st k ->
    continuation_history tf (R.request_spawn st target) k.
  Proof.
    intros. eapply continuation_history_map; [|exact H].
    intros. now apply request_spawn_progress.
  Qed.

  Lemma control_history_start : forall tf st owner k,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunSolveOne owner k |} ->
    ControlStack.continuation_ordered owner k ->
    continuation_history tf st k ->
    control_history tf
      (R.with_started (R.start_evaluation st (R.handle_variable owner))
        (S.add (R.handle_variable owner) (R.started (R.materialize st (R.handle_variable owner)))))
      (R.RunRhs owner (tf (R.handle_variable owner)) k).
  Proof.
    intros tf st owner k Hv Ho Hh. split.
    - apply rhs_progress_with_started, initial_rhs_progress.
    - apply continuation_history_with_started, continuation_history_start; [|exact Hh].
      pose proof (handles_control_valid Hv) as Hc.
      eapply continuation_ordered_excludes; [exact (proj1 Hc)|exact (proj2 Hc)|exact Ho].
  Qed.

  Lemma continuation_history_drain_pop : forall tf st owner k popped rest,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    ControlStack.continuation_ordered owner k ->
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (popped, rest) ->
    continuation_history tf st k ->
    continuation_history tf (R.with_queue st rest) k.
  Proof.
    intros tf st owner k popped rest Hv Ho Hmay Hp Hh.
    pose proof (handles_control_valid Hv) as Hc.
    pose proof (proj1 (@queue_pop_valid st popped rest (handles_queue_valid Hv) Hp)) as Hpop.
    eapply continuation_history_pop; [exact Hp| |exact Hh].
    eapply continuation_ordered_excludes; [exact Hpop|exact (proj2 Hc)|].
    destruct (V.eq_dec (R.handle_variable popped) (R.handle_variable owner)) as [Heq|Hneq].
    - assert (popped = owner) by (eapply same_variable_valid_handle_equal; eauto; exact (proj1 Hc)).
      now subst popped.
    - eapply continuation_ordered_weaken; [|exact Ho].
      apply Nat.ltb_lt. eapply ControlStack.owner_may_pop_higher; eauto.
  Qed.

  Lemma continuation_history_observed_side : forall tf st owner body k target observed entry raw,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunRhs owner body k |} ->
    ControlStack.continuation_ordered owner k ->
    R.observe st target = (observed, entry) ->
    continuation_history tf st k ->
    continuation_history tf (R.side_ready_state observed owner entry raw) k.
  Proof.
    intros tf st owner body k target observed entry raw Hv Ho Hobs Hh.
    apply continuation_history_side.
    - eapply continuation_ordered_excludes.
      + eapply handle_valid_extended; [eapply rank_extends_observe; eauto|exact (proj1 (handles_control_valid Hv))].
      + eapply continuation_valid_observe; [exact Hobs|exact (proj2 (handles_control_valid Hv))].
      + exact Ho.
    - eapply continuation_history_observe; eauto.
  Qed.

  Lemma control_history_remembered_get : forall tf st owner target next k,
    R.Ranking.lookup (R.ranking st) target = None ->
    andb (R.pure_bottom_rhs tf target) (negb (R.is_materialized st target)) = true ->
    control_history tf st (R.RunRhs owner (R.ConstraintSystem.Get target next) k) ->
    control_history tf (R.add_reader (R.remember_dormant st target) target (R.handle_variable owner))
      (R.RunRhs owner (next D.bottom) k).
  Proof.
    intros tf st owner target next k Hr Hp [Hprogress Hrest].
    apply Bool.andb_true_iff in Hp as [Hp Hm]. apply Bool.negb_true_iff in Hm.
    split.
    - eapply rhs_progress_get_remembered; [eapply remember_dormant_active; eauto|exact Hprogress].
    - now apply continuation_history_add_reader, continuation_history_remember_dormant.
  Qed.

  Definition step_spawned (before : R.config) : Prop :=
    match R.cfg_control before with
    | R.RunRhs _ (R.ConstraintSystem.Spawn target _) _ => spawned target
    | _ => True
    end.
  Definition spawned_path tf first final : Prop :=
    forall before after, Sem.steps tf first before -> Sem.step tf before after ->
      Sem.steps tf after final -> step_spawned before.

  Lemma control_history_step : forall tf before after,
    step_spawned before ->
    handles_valid before -> ControlStack.control_ordered (R.cfg_control before) ->
    control_history tf (R.cfg_state before) (R.cfg_control before) ->
    Sem.step tf before after -> control_history tf (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hspawn Hvalid Hordered Hhistory Hstep.
    unfold step_spawned in Hspawn. cbn in Hspawn.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I; try exact Hhistory.
    all: try solve [eapply control_history_start; eauto].
    all: try solve [eapply continuation_history_drain_pop; eauto].
    all: try solve [now apply continuation_history_continue].
    all: try solve [eapply continuation_history_set_value;
      [exact (handles_rank_valid Hvalid)|exact (handles_queue_valid Hvalid)|exact (proj2 Hhistory)]].
    all: try solve [eapply control_history_remembered_get; eauto].
    all: try match goal with
    | Hobs : Sem.R.observe ?before ?target = (?observed, ?entry) |- _ =>
      pose proof (@observed_handle_variable before target observed entry Hobs) as Hvariable;
      rewrite <- Hvariable in Hhistory; try rewrite <- Hvariable in Hspawn; try rewrite <- Hvariable
    end.
    all: try (destruct Hhistory as [Hprogress Hrest]; split).
    all: try solve [eauto 5 using rhs_progress_get_dormant, rhs_progress_get,
      rhs_progress_enqueue_handle, rhs_progress_observe, rhs_progress_spawn,
      rhs_progress_materialize, rhs_progress_remember_dormant,
      rhs_progress_side, rhs_progress_mark_side_dirty, rhs_progress_deferred_spawn].
    all: try solve [eauto 4 using continuation_history_add_reader,
      continuation_history_get_ready, continuation_history_enqueue_handle,
      continuation_history_materialize, continuation_history_remember_dormant,
      continuation_history_observe, continuation_history_request_spawn].
    all: try solve [eauto 4 using continuation_history_mark_side_dirty,
      continuation_history_enqueue_handle, continuation_history_observed_side].
    all: try solve [eapply rhs_progress_dirty_get;
      [eapply rank_valid_observe; [exact (handles_rank_valid Hvalid)|eassumption]|
       eapply queue_valid_observe; [exact (handles_queue_valid Hvalid)|eassumption]|
       eapply observed_handle_valid; eassumption|eapply rhs_progress_observe; eauto]].
    all: try solve [eapply continuation_history_dirty_get_ready;
      [eapply rank_valid_observe; [exact (handles_rank_valid Hvalid)|eassumption]|
       eapply queue_valid_observe; [exact (handles_queue_valid Hvalid)|eassumption]|
       eapply observed_handle_valid; eassumption|eapply continuation_history_observe; eauto]].
  Qed.
  Fixpoint continuation_completed
    (tf : R.ConstraintSystem.system) (st : R.state)
    (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KSolveOneLoop owner rest =>
        summary_valid tf st (R.handle_variable owner) /\
        continuation_completed tf st rest
    | R.KAfterGet _ _ _ rest
    | R.KAfterSide _ _ rest
    | R.KAfterSpawn _ _ rest => continuation_completed tf st rest
    end.

  Definition control_completed
    (tf : R.ConstraintSystem.system) (st : R.state)
    (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.RunSolveOne _ rest | R.RunRhs _ _ rest
    | R.AfterGet _ _ _ rest | R.AfterSide _ _ rest
    | R.AfterSpawn _ _ rest => continuation_completed tf st rest
    | R.RunSolveOneLoop owner rest =>
        summary_valid tf st (R.handle_variable owner) /\
        continuation_completed tf st rest
    end.

  Lemma continuation_completed_continue :
    forall tf st k,
      continuation_completed tf st k ->
      control_completed tf st (R.continue k).
  Proof. intros tf st k H; destruct k; exact H. Qed.

  Lemma continuation_completed_map :
    forall tf before after,
      (forall owner,
        summary_valid tf before owner -> summary_valid tf after owner) ->
      forall k,
        continuation_completed tf before k ->
        continuation_completed tf after k.
  Proof.
    intros tf before after Hmap k. induction k; cbn; intros Hcompleted;
      try exact I.
    - destruct Hcompleted. split; eauto.
    - now apply IHk.
    - now apply IHk.
    - now apply IHk.
  Qed.

  Lemma summary_add_reader :
    forall tf st target added owner,
      summary_valid tf st owner ->
      summary_valid tf (R.add_reader st target added) owner.
  Proof.
    intros tf st target added owner
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - now apply reads_guarded_add_reader.
    - unfold effects_recorded, effect_recorded, R.add_reader,
        R.promote_controlled in *; exact Hrecorded.
    - unfold R.sigma_value, R.add_reader, R.promote_controlled.
      exact Hdirect.
  Qed.

  Lemma summary_remember_dormant :
    forall tf st target owner,
      summary_valid tf st owner ->
      summary_valid tf (R.remember_dormant st target) owner.
  Proof.
    intros tf st target owner
      [direct [reads [effects [Htrace [Hreads [Hrecorded Hdirect]]]]]].
    exists direct, reads, effects. repeat split; try exact Htrace.
    - now apply reads_guarded_remember_dormant.
    - unfold effects_recorded, effect_recorded, R.remember_dormant,
        R.with_dormant_bottom in *; exact Hrecorded.
    - unfold R.sigma_value, R.remember_dormant, R.with_dormant_bottom.
      exact Hdirect.
  Qed.

  Lemma continuation_completed_add_reader :
    forall tf st target added k,
      continuation_completed tf st k ->
      continuation_completed tf (R.add_reader st target added) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply summary_add_reader.
  Qed.

  Lemma continuation_completed_remember_dormant :
    forall tf st target k,
      continuation_completed tf st k ->
      continuation_completed tf (R.remember_dormant st target) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply summary_remember_dormant.
  Qed.

  Lemma continuation_completed_observe :
    forall tf st observed next entry k,
      R.observe st observed = (next, entry) ->
      continuation_completed tf st k ->
      continuation_completed tf next k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H0].
    intros. eapply summary_observe; eauto.
  Qed.

  Lemma continuation_completed_enqueue_handle :
    forall tf st inserted k,
      continuation_completed tf st k ->
      continuation_completed tf (R.enqueue_handle st inserted) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply summary_enqueue_handle.
  Qed.

  Lemma continuation_completed_materialize :
    forall tf st target k,
      continuation_completed tf st k ->
      continuation_completed tf (R.materialize st target) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply summary_materialize.
  Qed.

  Lemma continuation_completed_get_ready :
    forall tf st owner target k,
      continuation_completed tf st k ->
      continuation_completed tf (R.get_ready_state st owner target) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply summary_get_ready.
  Qed.

  Lemma continuation_completed_with_started :
    forall tf st started k,
      continuation_completed tf st k ->
      continuation_completed tf (R.with_started st started) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros owner [direct [reads [effects Hsummary]]].
    now exists direct, reads, effects.
  Qed.

  Lemma continuation_completed_start :
    forall tf st active k,
      continuation_excludes active k ->
      continuation_completed tf st k ->
      continuation_completed tf (R.start_evaluation st active) k.
  Proof.
    intros tf st active k. induction k; cbn;
      intros Hexcludes Hcompleted; try exact I.
    - destruct Hexcludes, Hcompleted. split;
        [eapply summary_start_other; eauto |eauto].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
  Qed.

  Lemma continuation_completed_set_value :
    forall tf st active direct k,
      rank_valid st -> queue_valid st ->
      continuation_excludes active k ->
      continuation_completed tf st k ->
      continuation_completed tf (R.set_value st active direct) k.
  Proof.
    intros tf st active direct k Hrank Hqueue.
    induction k; cbn; intros Hexcludes Hcompleted; try exact I.
    - destruct Hexcludes, Hcompleted. split.
      + eapply summary_set_value_other; eauto.
      + eapply IHk; eauto.
    - eapply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - eapply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - eapply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
  Qed.

  Lemma continuation_completed_side :
    forall tf st active target raw k,
      continuation_excludes (R.handle_variable active) k ->
      continuation_completed tf st k ->
      continuation_completed tf (R.side_ready_state st active target raw) k.
  Proof.
    intros tf st active target raw k. induction k; cbn;
      intros Hexcludes Hcompleted; try exact I.
    - destruct Hexcludes, Hcompleted. split;
        [eapply summary_side_other; eauto |eauto].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
  Qed.

  Lemma continuation_completed_pop :
    forall tf st popped rest k,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      continuation_excludes (R.handle_variable popped) k ->
      continuation_completed tf st k ->
      continuation_completed tf (R.with_queue st rest) k.
  Proof.
    intros tf st popped rest k Hpop. induction k; cbn;
      intros Hexcludes Hcompleted; try exact I.
    - destruct Hexcludes, Hcompleted. split;
        [eapply summary_pop_other; eauto |eauto].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
    - apply IHk; [exact (proj2 Hexcludes) |exact Hcompleted].
  Qed.

  Lemma continuation_completed_dirty_get_ready :
    forall tf st owner target k,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      continuation_completed tf st k ->
      continuation_completed tf (R.dirty_get_ready_state tf st owner target) k.
  Proof.
    intros tf st owner target k Hrank Hqueue Htarget Hcompleted.
    eapply continuation_completed_map; [|exact Hcompleted].
    intros tracked Hsummary. eapply summary_dirty_get_ready; eauto.
  Qed.

  Lemma continuation_completed_mark_side_dirty :
    forall tf st target k,
      continuation_completed tf st k ->
      continuation_completed tf (R.mark_side_dirty st target) k.
  Proof.
    intros tf st target k Hcompleted.
    eapply continuation_completed_map; [|exact Hcompleted].
    intros tracked [direct [reads [effects Hsummary]]].
    now exists direct, reads, effects.
  Qed.

  Lemma continuation_completed_drain_pop : forall tf st owner k popped rest,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner k |} ->
    ControlStack.continuation_ordered owner k ->
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (popped, rest) ->
    continuation_completed tf st k ->
    continuation_completed tf (R.with_queue st rest) k.
  Proof.
    intros tf st owner k popped rest Hv Ho Hmay Hp Hh.
    pose proof (handles_control_valid Hv) as Hc.
    pose proof (proj1 (@queue_pop_valid st popped rest (handles_queue_valid Hv) Hp)) as Hpop.
    eapply continuation_completed_pop; [exact Hp| |exact Hh].
    eapply continuation_ordered_excludes; [exact Hpop|exact (proj2 Hc)|].
    destruct (V.eq_dec (R.handle_variable popped) (R.handle_variable owner)) as [Heq|Hneq].
    - assert (popped = owner) by (eapply same_variable_valid_handle_equal; eauto; exact (proj1 Hc)).
      now subst popped.
    - eapply continuation_ordered_weaken; [|exact Ho].
      apply Nat.ltb_lt. eapply ControlStack.owner_may_pop_higher; eauto.
  Qed.

  Lemma continuation_completed_observed_side : forall tf st owner body k target observed entry raw,
    handles_valid {| R.cfg_state := st; R.cfg_control := R.RunRhs owner body k |} ->
    ControlStack.continuation_ordered owner k ->
    R.observe st target = (observed, entry) ->
    continuation_completed tf st k ->
    continuation_completed tf (R.side_ready_state observed owner entry raw) k.
  Proof.
    intros tf st owner body k target observed entry raw Hv Ho Hobs Hh.
    apply continuation_completed_side.
    - eapply continuation_ordered_excludes.
      + eapply handle_valid_extended; [eapply rank_extends_observe; eauto|exact (proj1 (handles_control_valid Hv))].
      + eapply continuation_valid_observe; [exact Hobs|exact (proj2 (handles_control_valid Hv))].
      + exact Ho.
    - eapply continuation_completed_observe; eauto.
  Qed.

  Lemma continuation_completed_request_spawn : forall tf st target k,
    continuation_completed tf st k ->
    continuation_completed tf (R.request_spawn st target) k.
  Proof.
    intros. eapply continuation_completed_map; [|exact H].
    intros. now apply request_spawn_summary.
  Qed.

  Lemma control_completed_commit : forall tf st owner direct k,
    handles_valid {| R.cfg_state := st;
      R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |} ->
    ControlStack.continuation_ordered owner k ->
    rhs_progress tf st (R.handle_variable owner) (R.ConstraintSystem.Ret direct) ->
    continuation_completed tf st k ->
    control_completed tf (R.set_value st (R.handle_variable owner) direct)
      (R.RunSolveOneLoop owner k).
  Proof.
    intros tf st owner direct k Hv Ho Hp Hc. split.
    - eapply rhs_progress_ret_summary;
        [exact (handles_rank_valid Hv)|exact (handles_queue_valid Hv)|exact Hp].
    - eapply continuation_completed_set_value;
        [exact (handles_rank_valid Hv)|exact (handles_queue_valid Hv)| |exact Hc].
      eapply continuation_ordered_excludes;
        [exact (proj1 (handles_control_valid Hv))|exact (proj2 (handles_control_valid Hv))|exact Ho].
  Qed.

  Lemma control_completed_step : forall tf before after,
    handles_valid before -> ControlStack.control_ordered (R.cfg_control before) ->
    control_history tf (R.cfg_state before) (R.cfg_control before) ->
    control_completed tf (R.cfg_state before) (R.cfg_control before) ->
    Sem.step tf before after -> control_completed tf (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hvalid Hordered Hhistory Hcompleted Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I; try exact Hcompleted.
    all: try solve [eapply control_completed_commit; eauto; exact (proj1 Hhistory)].
    all: try solve [apply continuation_completed_continue; exact (proj2 Hcompleted)].
    all: try solve [eapply continuation_completed_drain_pop; eauto; exact (proj2 Hcompleted)].
    all: try solve [eauto 5 using continuation_completed_add_reader,
      continuation_completed_get_ready, continuation_completed_enqueue_handle,
      continuation_completed_materialize, continuation_completed_remember_dormant,
      continuation_completed_observe, continuation_completed_request_spawn].
    all: try solve [eauto 4 using continuation_completed_mark_side_dirty,
      continuation_completed_enqueue_handle, continuation_completed_observed_side].
    all: try solve [eapply continuation_completed_dirty_get_ready;
      [eapply rank_valid_observe; [exact (handles_rank_valid Hvalid)|eassumption]|
       eapply queue_valid_observe; [exact (handles_queue_valid Hvalid)|eassumption]|
       eapply observed_handle_valid; eassumption|eapply continuation_completed_observe; eauto]].
    - apply continuation_completed_with_started, continuation_completed_start; [|exact Hcompleted].
      eapply continuation_ordered_excludes;
        [exact (proj1 (handles_control_valid Hvalid))|exact (proj2 (handles_control_valid Hvalid))|exact Hordered].
    - split.
      + eapply summary_pop_other; [eassumption|congruence|exact (proj1 Hcompleted)].
      + eapply continuation_completed_drain_pop; eauto. exact (proj2 Hcompleted).
  Qed.
  Lemma solved_materialize_origin :
    forall st target x,
      Progress.solved (R.materialize st target) x ->
      x = target \/ Progress.solved st x.
  Proof.
    intros st target x Hsolved.
    unfold R.materialize, R.is_materialized in Hsolved.
    destruct (M.lookup (R.sigma st) target) eqn:Htarget.
    - right. exact Hsolved.
    - destruct Hsolved as [value Hlookup]. cbn in Hlookup.
      destruct (V.eq_dec x target) as [-> | Hneq].
      + left. reflexivity.
      + right. exists value.
        rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        exact Hlookup.
  Qed.

  Lemma sigma_observe :
    forall st target next entry,
      R.observe st target = (next, entry) -> R.sigma next = R.sigma st.
  Proof.
    intros st target next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; reflexivity.
  Qed.

  Lemma solved_observe_origin :
    forall st target next entry x,
      R.observe st target = (next, entry) ->
      Progress.solved next x -> Progress.solved st x.
  Proof.
    intros st target next entry x Hobserve [value Hlookup].
    exists value.
    now rewrite (@sigma_observe st target next entry Hobserve) in Hlookup.
  Qed.

  Lemma sigma_enqueue :
    forall st target, R.sigma (R.enqueue st target) = R.sigma st.
  Proof.
    intros st target. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    unfold R.enqueue_handle. cbn. now apply sigma_observe in Hobserve.
  Qed.

  Lemma sigma_enqueue_all :
    forall targets st, R.sigma (R.enqueue_all st targets) = R.sigma st.
  Proof.
    induction targets as [|target rest IH]; intros st; cbn; [reflexivity |].
    rewrite IH, sigma_enqueue. reflexivity.
  Qed.

  Lemma solved_write_origin :
    forall st owner value x,
      Progress.solved (R.write_changed_value st owner value) x ->
      x = owner \/ Progress.solved st x.
  Proof.
    intros st owner value x [observed Hlookup].
    unfold R.write_changed_value in Hlookup. cbn in Hlookup.
    rewrite sigma_enqueue_all in Hlookup.
    cbn in Hlookup.
    destruct (V.eq_dec x owner) as [-> | Hneq].
    - left. reflexivity.
    - right. exists observed.
      rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      exact Hlookup.
  Qed.

  Lemma solved_try_dirty_read_origin :
    forall tf st owner target next x,
      R.try_dirty_read tf st owner target = Some next ->
      Progress.solved next x ->
      x = R.handle_variable target \/ Progress.solved st x.
  Proof.
    intros tf st owner target next x Hread Hsolved.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try (apply solved_write_origin in Hsolved;
      destruct Hsolved as [Htarget | Hsolved]; [now left |]).
    all: right; exact Hsolved.
  Qed.

  Lemma solved_dirty_get_ready_origin :
    forall tf st owner target x,
      Progress.solved (R.dirty_get_ready_state tf st owner target) x ->
      x = R.handle_variable target \/ Progress.solved st x.
  Proof.
    intros tf st owner target x Hsolved.
    unfold R.dirty_get_ready_state in Hsolved.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target))
      in Hsolved.
    assert (Hprepared_origin : forall observed,
      Progress.solved prepared observed ->
      observed = R.handle_variable target \/ Progress.solved st observed).
    { intros observed Hprepared. subst prepared.
      destruct (@solved_materialize_origin
        (R.get_control_state st owner target)
        (R.handle_variable target) observed Hprepared)
        as [Htarget | Horigin]; [now left |right].
      unfold R.get_control_state in Horigin.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        [exact Horigin |].
      unfold R.promote_controlled in Horigin. exact Horigin. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - change (Progress.solved next x) in Hsolved.
      pose proof (@solved_try_dirty_read_origin tf prepared owner target
        next x Hread Hsolved) as Horigin.
      destruct Horigin as [Htarget | Hprepared_solved]; [now left |].
      exact (Hprepared_origin x Hprepared_solved).
    - change (Progress.solved prepared x) in Hsolved.
      exact (Hprepared_origin x Hsolved).
  Qed.

  Lemma queued_add_reader_early :
    forall st target reader tracked,
      queued st tracked -> queued (R.add_reader st target reader) tracked.
  Proof.
    intros st target reader tracked Hqueued.
    unfold queued, R.add_reader in *.
    exact Hqueued.
  Qed.

  Lemma queued_dirty_get_ready_other :
    forall tf st owner target tracked,
      rank_valid st -> queue_valid st -> handle_valid st target ->
      tracked <> R.handle_variable target ->
      queued st tracked ->
      queued (R.dirty_get_ready_state tf st owner target) tracked.
  Proof.
    intros tf st owner target tracked Hrank Hqueue Htarget Hneq Hqueued.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_rank : rank_valid prepared).
    { subst prepared. apply rank_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hrank. }
    assert (Hprepared_queue : queue_valid prepared).
    { subst prepared. apply queue_valid_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hqueue. }
    assert (Hprepared_target : handle_valid prepared target).
    { eapply handle_valid_extended; [|exact Htarget].
      subst prepared. eapply (@rank_extends_trans st
        (R.get_control_state st owner target));
        [|apply rank_extends_materialize].
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        apply rank_extends_same_ranking; reflexivity. }
    assert (Hprepared_queued : queued prepared tracked).
    { subst prepared. unfold R.get_control_state, R.materialize.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); exact Hqueued. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread; apply queued_add_reader_early.
    - eapply queued_try_dirty_read_other; eauto.
    - exact Hprepared_queued.
  Qed.

  Lemma queued_or_summary_dirty_get_ready_target :
    forall tf st owner target,
      queued st (R.handle_variable target) ->
      queued (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target) \/
      summary_valid tf (R.dirty_get_ready_state tf st owner target)
        (R.handle_variable target).
  Proof.
    intros tf st owner target Hqueued.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared_queued : queued prepared (R.handle_variable target)).
    { subst prepared. unfold R.get_control_state, R.materialize.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); exact Hqueued. }
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - right. apply summary_add_reader_early.
      eapply summary_try_dirty_read_target; eauto.
    - left. now apply queued_add_reader_early.
  Qed.

  Lemma solved_set_value_origin :
    forall st owner direct x,
      Progress.solved (R.set_value st owner direct) x ->
      x = owner \/ Progress.solved st x.
  Proof.
    intros st owner direct x Hsolved. unfold R.set_value in Hsolved.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner))
      (R.sigma_value st owner)); [now right |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value].
      cbn in Hsolved.
      destruct (R.equivalent value (R.sigma_value st owner)).
      + right. exact Hsolved.
      + apply solved_write_origin in Hsolved.
        destruct Hsolved as [-> | Hsolved]; [now left |].
        right. exact Hsolved.
    - apply solved_write_origin in Hsolved. exact Hsolved.
  Qed.

  Lemma solved_start_origin :
    forall st owner x,
      Progress.solved
        (R.with_started (R.start_evaluation st owner)
          (S.add owner (R.started (R.start_evaluation st owner)))) x ->
      x = owner \/ Progress.solved st x.
  Proof.
    intros st owner x Hsolved. cbn in Hsolved.
    unfold R.start_evaluation, R.reset_local_sides in Hsolved.
    now apply solved_materialize_origin in Hsolved.
  Qed.

  Lemma solved_get_ready_origin :
    forall st owner target x,
      Progress.solved (R.get_ready_state st owner target) x ->
      x = R.handle_variable target \/ Progress.solved st x.
  Proof.
    intros st owner target x Hsolved.
    unfold R.get_ready_state in Hsolved.
    apply solved_materialize_origin in Hsolved.
    destruct Hsolved as [-> | Hsolved]; [now left |].
    right. unfold R.add_reader, R.promote_controlled in Hsolved.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      exact Hsolved.
  Qed.

  Lemma solved_side_ready_origin :
    forall st owner target raw x,
      Progress.solved (R.side_ready_state st owner target raw) x ->
      Progress.solved st x.
  Proof.
    intros st owner target raw x Hsolved.
    unfold R.side_ready_state, R.record_side_payload in Hsolved.
    destruct (side_update_result st (R.handle_variable owner)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank owner));
      exact Hsolved.
  Qed.

  Lemma solved_observed_dirty_origin : forall tf st target observed entry owner x,
    R.observe st target = (observed, entry) -> R.is_materialized observed target = true ->
    Progress.solved (R.dirty_get_ready_state tf observed owner entry) x -> Progress.solved st x.
  Proof.
    intros tf st target observed entry owner x Ho Hm Hs.
    apply solved_dirty_get_ready_origin in Hs. eapply solved_observe_origin; [exact Ho|].
    destruct Hs as [->|Hs]; [|exact Hs].
    rewrite (@observed_handle_variable st target observed entry Ho).
    now apply Progress.solved_is_materialized.
  Qed.

  Lemma solved_observed_enqueued_get_origin : forall st control target observed entry owner x,
    handles_valid {| R.cfg_state := st; R.cfg_control := control |} ->
    R.observe st target = (observed, entry) ->
    Progress.solved (R.get_ready_state (R.enqueue_handle observed entry) owner entry) x ->
    Progress.solved st x \/ queued (R.get_ready_state (R.enqueue_handle observed entry) owner entry) x.
  Proof.
    intros st control target observed entry owner x Hv Ho Hs.
    apply solved_get_ready_origin in Hs. destruct Hs as [->|Hs].
    - right. apply queued_get_ready, enqueue_handle_queues_variable.
      + eapply rank_valid_observe; [exact (handles_rank_valid Hv)|exact Ho].
      + eapply queue_valid_observe; [exact (handles_queue_valid Hv)|exact Ho].
      + eapply observed_handle_valid; exact Ho.
    - left. eapply solved_observe_origin; eauto.
  Qed.

  Lemma solved_observed_enqueued_materialize_origin : forall st control target observed entry x,
    handles_valid {| R.cfg_state := st; R.cfg_control := control |} ->
    R.observe st target = (observed, entry) ->
    Progress.solved (R.materialize (R.enqueue_handle observed entry) target) x ->
    Progress.solved st x \/ queued (R.materialize (R.enqueue_handle observed entry) target) x.
  Proof.
    intros st control target observed entry x Hv Ho Hs.
    apply solved_materialize_origin in Hs. destruct Hs as [->|Hs].
    - right. apply queued_materialize. rewrite <- (@observed_handle_variable st target observed entry Ho).
      apply enqueue_handle_queues_variable.
      + eapply rank_valid_observe; [exact (handles_rank_valid Hv)|exact Ho].
      + eapply queue_valid_observe; [exact (handles_queue_valid Hv)|exact Ho].
      + eapply observed_handle_valid; exact Ho.
    - left. eapply solved_observe_origin; eauto.
  Qed.

  Lemma solved_origin_step : forall tf before after x,
    handles_valid before -> Sem.step tf before after ->
    Progress.solved (R.cfg_state after) x ->
    Progress.solved (R.cfg_state before) x \/ queued (R.cfg_state after) x \/
    control_active x (R.cfg_control after).
  Proof.
    intros tf [st control] after x Hvalid Hstep Hsolved.
    unfold Sem.step in Hstep. cbn in Hstep, Hsolved.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in *.
    all: try solve [left; exact Hsolved].
    all: try solve [left; eapply solved_observe_origin; [eassumption|exact Hsolved]].
    all: try solve [left; eapply solved_observe_origin; [eassumption|];
      now apply solved_side_ready_origin in Hsolved].
    all: try solve [left; eapply solved_observed_dirty_origin; eauto].
    all: try solve [destruct (@solved_observed_enqueued_get_origin st _ _ _ _ _ x
      Hvalid ltac:(eassumption) Hsolved); auto].
    all: try solve [destruct (@solved_observed_enqueued_materialize_origin st _ _ _ _ x
      Hvalid ltac:(eassumption) Hsolved); auto].
    - apply solved_start_origin in Hsolved. destruct Hsolved as [->|Hsolved];
        [right;right;now left|now left].
    - apply solved_set_value_origin in Hsolved. destruct Hsolved as [->|Hsolved];
        [right;right;now left|now left].
    - unfold R.request_spawn in Hsolved. destruct (S.mem t (R.requested_spawns st)); now left.
    - apply solved_get_ready_origin in Hsolved. destruct Hsolved as [->|Hsolved]; left;
        [apply Progress.solved_is_materialized; assumption|exact Hsolved].
  Qed.
  Lemma queued_dirty_get_scheduled : forall tf st owner target x,
    rank_valid st -> queue_valid st -> handle_valid st target -> queued st x ->
    queued (R.dirty_get_ready_state tf st owner target) x \/
    summary_valid tf (R.dirty_get_ready_state tf st owner target) x.
  Proof.
    intros tf st owner target x Hr Hq Ht Hqueued.
    destruct (V.eq_dec x (R.handle_variable target)) as [->|Hneq].
    - now apply queued_or_summary_dirty_get_ready_target.
    - left. eapply queued_dirty_get_ready_other; eauto.
  Qed.

  Lemma queued_step_scheduled : forall tf before after x,
    handles_valid before -> queued (R.cfg_state before) x -> Sem.step tf before after ->
    queued (R.cfg_state after) x \/ control_active x (R.cfg_control after) \/
    summary_valid tf (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x Hvalid Hqueued Hstep.
    unfold Sem.step in Hstep. cbn in Hstep, Hqueued.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in *.
    all: try solve [left; exact Hqueued].
    all: try match goal with
    | Hp : Sem.R.queue_pop (Sem.R.queue ?before) = Some (?popped, ?rest) |- _ =>
      destruct (V.eq_dec x (R.handle_variable popped)) as [->|Hneq];
      [right;left;cbn;tauto|left;eapply queued_pop_other;eauto]
    end.
    all: try solve [left; eauto 4 using queued_start, queued_set_value,
      queued_get_ready, queued_enqueue_handle, queued_side_ready, queued_observe,
      queued_materialize].
    all: try solve [left; apply queued_start; exact Hqueued].
    all: try solve [left; apply queued_side_ready; eapply queued_observe; eauto].
    all: try solve [left; apply queued_enqueue_handle, queued_side_ready; eapply queued_observe; eauto].
    - destruct (@queued_dirty_get_scheduled tf s h h0 x) as [Hq|Hs].
      + eapply rank_valid_observe; [exact (handles_rank_valid Hvalid)|eassumption].
      + eapply queue_valid_observe; [exact (handles_queue_valid Hvalid)|eassumption].
      + eapply observed_handle_valid; eassumption.
      + eapply queued_observe; eauto.
      + now left.
      + now right; right.
    - unfold R.request_spawn. destruct (S.mem t (R.requested_spawns st)); now left.
  Qed.

  Lemma active_step_scheduled_or_summary :
    forall tf before after x,
      control_completed tf
        (R.cfg_state before) (R.cfg_control before) ->
      control_active x (R.cfg_control before) ->
      Sem.step tf before after ->
      control_active x (R.cfg_control after) \/
      summary_valid tf (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x Hcompleted Hactive Hstep.
    unfold Sem.step in Hstep.
    cbn in Hcompleted, Hactive, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try (left; exact Hactive); try contradiction.
    all: try (left; right; exact Hactive).
    destruct Hactive as [-> | Hactive].
    - right. exact (proj1 Hcompleted).
    - left. now apply continuation_active_continue.
  Qed.

  Lemma summary_step_guarded : forall tf before after x,
    handles_valid before -> summary_valid tf (R.cfg_state before) x ->
    Sem.step tf before after ->
    queued (R.cfg_state after) x \/ control_active x (R.cfg_control after) \/
    summary_valid tf (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x Hvalid Hsummary Hstep.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in *.
    all: try solve [right;right;exact Hsummary].
    all: try match goal with
    | Hp : Sem.R.queue_pop (Sem.R.queue ?before) = Some (?popped, ?rest) |- _ =>
      destruct (V.eq_dec x (R.handle_variable popped)) as [->|Hneq];
      [right;left;cbn;tauto|right;right;eapply summary_pop_other;eauto]
    end.
    all: try solve [right;right;eauto 4 using summary_observe, summary_get_ready,
      summary_enqueue_handle, summary_materialize, summary_add_reader,
      summary_remember_dormant, request_spawn_summary].
    all: try solve [right;right;eapply summary_dirty_get_ready;
      [eapply rank_valid_observe; [exact (handles_rank_valid Hvalid)|eassumption]|
       eapply queue_valid_observe; [exact (handles_queue_valid Hvalid)|eassumption]|
       eapply observed_handle_valid; eassumption|eapply summary_observe; eauto]].
    all: destruct (V.eq_dec x (R.handle_variable h)) as [->|Hneq];
      [right;left;cbn;tauto|right;right].
    all: try solve [eapply summary_start_other; eauto].
    all: try solve [eapply summary_set_value_other;
      [exact (handles_rank_valid Hvalid)|exact (handles_queue_valid Hvalid)|exact Hneq|exact Hsummary]].
    all: try solve [eapply summary_side_other; [exact Hneq|]; eapply summary_observe; eauto].
    all: apply summary_enqueue_handle; eapply summary_side_other;
      [exact Hneq|]; eapply summary_observe; eauto.
  Qed.
  Definition summaries_guarded
    (tf : R.ConstraintSystem.system) (c : R.config) : Prop :=
    forall owner,
      Progress.solved (R.cfg_state c) owner ->
      queued (R.cfg_state c) owner \/
      control_active owner (R.cfg_control c) \/
      summary_valid tf (R.cfg_state c) owner.

  Lemma initial_summaries_guarded :
    forall tf roots, summaries_guarded tf (R.initial_config roots).
  Proof.
    intros tf roots owner [value Hlookup]. cbn in Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma summaries_guarded_step :
    forall tf before after,
      handles_valid before ->
      control_completed tf
        (R.cfg_state before) (R.cfg_control before) ->
      summaries_guarded tf before ->
      Sem.step tf before after ->
      summaries_guarded tf after.
  Proof.
    intros tf before after Hvalid Hcompleted Hguard Hstep owner Hsolved.
    destruct (@solved_origin_step tf before after owner
      Hvalid Hstep Hsolved) as [Hbefore | [Hqueued | Hactive]].
    - destruct (Hguard owner Hbefore)
        as [Hqueued | [Hactive | Hsummary]].
      + destruct (@queued_step_scheduled tf before after owner
          Hvalid Hqueued Hstep) as [Hqueued' | [Hactive' | Hsummary']]; auto.
      + destruct (@active_step_scheduled_or_summary
          tf before after owner Hcompleted Hactive Hstep)
          as [Hactive' | Hsummary']; auto.
      + eapply summary_step_guarded; eauto.
    - now left.
    - now right; left.
  Qed.

  Record history_invariant (tf : R.ConstraintSystem.system) (config : R.config) : Prop := {
    history_handles : handles_valid config;
    history_ordered : ControlStack.control_ordered (R.cfg_control config);
    history_active : control_history tf (R.cfg_state config) (R.cfg_control config);
    history_completed : control_completed tf (R.cfg_state config) (R.cfg_control config);
    history_summaries : summaries_guarded tf config
  }.

  Lemma initial_history_invariant : forall tf roots,
    history_invariant tf (R.initial_config roots).
  Proof.
    intros. constructor; try exact I.
    - apply initial_handles_valid.
    - apply initial_summaries_guarded.
  Qed.

  Lemma history_invariant_step : forall tf before after,
    step_spawned before ->
    history_invariant tf before -> Sem.step tf before after -> history_invariant tf after.
  Proof.
    intros tf before after Hspawn [Hv Ho Hh Hc Hs] Hstep. constructor.
    - eapply next_config_handles_valid; eauto.
    - eapply ControlStack.next_config_control_ordered; eauto.
    - eapply control_history_step; eauto.
    - eapply control_completed_step; eauto.
    - eapply summaries_guarded_step; eauto.
  Qed.

  Lemma history_invariant_steps : forall tf before after,
    history_invariant tf before -> Sem.steps tf before after ->
    spawned_path tf before after -> history_invariant tf after.
  Proof.
    intros tf before after Hi Hsteps. revert Hi.
    induction Hsteps as [first |first next final Hstep Htail IH]; intros Hi Hspawn.
    - exact Hi.
    - apply IH.
      + eapply history_invariant_step; [|exact Hi |exact Hstep].
        exact (Hspawn first next (@Sem.StepsRefl tf first) Hstep Htail).
      + intros before after Hprefix Hnext Hsuffix.
        apply (Hspawn before after); [|exact Hnext |exact Hsuffix].
        eapply Sem.StepsStep; eassumption.
  Qed.

  Theorem tracked_terminal_materialized_post_solution : forall tf roots final owner,
    spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
    Sem.terminates_to tf roots final -> Progress.solved final owner ->
    Sem.rhs_post_solution final owner (tf owner).
  Proof.
    intros tf roots final owner Hspawn Hterm Hsolved.
    destruct Hterm as [Hsteps Hquiet].
    pose proof (@history_invariant_steps tf (R.initial_config roots)
      (Sem.terminal_config final) (initial_history_invariant tf roots) Hsteps Hspawn) as Hi.
    destruct (history_summaries Hi Hsolved) as [Hqueued|[Hactive|Hsummary]].
    - exfalso. eapply quiescent_not_queued; eauto.
    - contradiction.
    - eapply terminal_summary_post_solution; [exact Hquiet| |exact Hsummary].
      eapply terminal_aggregate_bounded. split; eassumption.
  Qed.

  Theorem tracked_successful_run_all_post_solution : forall fuel tf roots final owner,
    spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
    R.solve_fuel fuel tf roots = Some final -> Sem.solved final owner ->
    Sem.rhs_post_solution final owner (tf owner).
  Proof.
    intros fuel tf roots final owner Hspawn Hrun Hsolved.
    apply E.solved_characterization in Hsolved as [Hmaterialized|Hdormant].
    - eapply tracked_terminal_materialized_post_solution;
        [exact Hspawn|eapply E.successful_run_terminates_to; exact Hrun|exact Hmaterialized].
    - eapply successful_run_dormant_post_solution; eauto.
  Qed.

  Theorem tracked_successful_run_correct : forall fuel tf roots final,
    spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
    R.solve_fuel fuel tf roots = Some final ->
    Sem.correct_final_state tf roots final /\
    (forall owner, Sem.solved final owner -> Sem.rhs_post_solution final owner (tf owner)) /\
    R.pending_spawns final = [] /\
    (forall target, S.mem target (R.requested_spawns final) = true -> Sem.solved final target).
  Proof.
    intros fuel tf roots final Hspawn Hrun. split.
    - intros owner Hin. split.
      + eapply E.successful_run_roots_solved; eauto.
      + eapply tracked_successful_run_all_post_solution; [exact Hspawn|exact Hrun|].
        eapply E.successful_run_roots_solved; eauto.
    - split; [intros; eapply tracked_successful_run_all_post_solution; eauto|].
      split.
      + exact (proj2 (@E.successful_run_quiescent fuel tf roots final Hrun)).
      + eapply E.successful_run_requests_solved; exact Hrun.
  Qed.
  End SpawnTracesFinal.

  Lemma numerical_spawned_path tf first final : spawned_path (fun _ => True) tf first final.
  Proof. intros before after Hprefix Hstep Hsuffix. unfold step_spawned.
    destruct (R.cfg_control before); try exact I. destruct r; exact I. Qed.

  Definition terminal_materialized_post_solution tf roots final owner
    (Hterm : Sem.terminates_to tf roots final) (Hsolved : Progress.solved final owner) :=
    @tracked_terminal_materialized_post_solution (fun _ => True) tf roots final owner
      (@numerical_spawned_path tf (R.initial_config roots) (Sem.terminal_config final)) Hterm Hsolved.
  Definition successful_run_all_post_solution fuel tf roots final owner
    (Hrun : R.solve_fuel fuel tf roots = Some final) (Hsolved : Sem.solved final owner) :=
    @tracked_successful_run_all_post_solution (fun _ => True) fuel tf roots final owner
      (@numerical_spawned_path tf (R.initial_config roots) (Sem.terminal_config final)) Hrun Hsolved.
  Definition successful_run_correct fuel tf roots final
    (Hrun : R.solve_fuel fuel tf roots = Some final) :=
    @tracked_successful_run_correct (fun _ => True) fuel tf roots final
      (@numerical_spawned_path tf (R.initial_config roots) (Sem.terminal_config final)) Hrun.
  Lemma steps_started_safe tf first final : Sem.steps tf first final ->
    E.started_safe (R.cfg_state first) -> E.started_safe (R.cfg_state final).
  Proof.
    intros Hsteps. induction Hsteps; intros Hsafe; [exact Hsafe|].
    apply IHHsteps. eapply E.next_config_started_safe; eauto.
  Qed.

  Lemma steps_accounted tf first final target : Sem.steps tf first final ->
    E.started_safe (R.cfg_state first) -> E.accounted first target -> E.accounted final target.
  Proof.
    intros Hsteps. induction Hsteps; intros Hsafe Haccounted; [exact Haccounted|].
    apply IHHsteps.
    - eapply E.next_config_started_safe; eauto.
    - eapply E.next_config_accounted; eauto.
  Qed.

  Lemma steps_requests_accounted tf first final : Sem.steps tf first final ->
    E.started_safe (R.cfg_state first) -> E.requests_accounted first -> E.requests_accounted final.
  Proof.
    intros Hsteps. induction Hsteps; intros Hsafe Haccounted; [exact Haccounted|].
    apply IHHsteps.
    - eapply E.next_config_started_safe; eauto.
    - eapply E.next_config_requests_accounted; eauto.
  Qed.

  Lemma spawn_accounted tf st owner target next k after :
    E.started_safe st ->
    E.requests_accounted {|R.cfg_state := st;
      R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Spawn target next) k|} ->
    Sem.step tf {|R.cfg_state := st;
      R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Spawn target next) k|} after ->
    E.accounted after target.
  Proof.
    intros Hsafe Hrequests Hstep.
    unfold Sem.step in Hstep.
    cbn -[R.request_spawn R.observe R.is_dormant R.is_materialized
      R.materialize R.enqueue_handle R.remember_dormant] in Hstep.
    destruct Features.defer_spawns eqn:Hdefer.
    - inversion Hstep; subst. unfold R.request_spawn.
      destruct (S.mem target (R.requested_spawns st)) eqn:Hseen.
      + exact (Hrequests target Hseen).
      + right; left. cbn. apply in_or_app. right. cbn. auto.
    - destruct (R.is_dormant st target) eqn:Hdormant.
      + inversion Hstep; subst. left. now apply E.dormant_solved.
      + destruct (R.Ranking.lookup (R.ranking st) target);
          repeat match type of Hstep with
          | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
          | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
          end; inversion Hstep; subst; unfold E.accounted;
          cbn [R.cfg_state R.cfg_control E.waiting E.continuation_seeds].
        all: try solve [left; apply E.materialize_solves].
        all: try solve [left; apply E.remember_dormant_solves].
        all: try solve [left; apply E.solved_characterization; left;
          match goal with Hmat : Sem.R.is_materialized ?st ?target = true |- _ =>
            unfold R.is_materialized in Hmat;
            destruct (M.lookup (R.sigma st) target); [eexists; reflexivity|discriminate]
          end].
        all: right; right;
          match goal with Hobs : Sem.R.observe ?base ?t = (?observed, ?entry) |- _ =>
            pose proof (@E.observe_variable base t observed entry Hobs) as Hvariable;
            cbn; rewrite Hvariable; auto
          end.
  Qed.

  Lemma successful_spawned_path tf roots final : Sem.terminates_to tf roots final ->
    spawned_path (Sem.solved final) tf (R.initial_config roots) (Sem.terminal_config final).
  Proof.
    intros [Hrun Hquiet] [st control] after Hprefix Hstep Hsuffix.
    unfold step_spawned; cbn. destruct control; try exact I. destruct r; try exact I.
    assert (Hsafe : E.started_safe st).
    { exact (@steps_started_safe tf _ _ Hprefix (@E.initial_started_safe roots)). }
    assert (Hrequests : E.requests_accounted
      {|R.cfg_state := st; R.cfg_control := R.RunRhs h (R.ConstraintSystem.Spawn t r) c|}).
    { eapply steps_requests_accounted; [exact Hprefix |apply E.initial_started_safe
      |apply E.initial_requests_accounted]. }
    eapply E.terminal_accounted_solved; [exact Hquiet|].
    eapply steps_accounted; [exact Hsuffix| |].
    - eapply E.next_config_started_safe; eauto.
    - eapply spawn_accounted; eauto.
  Qed.

  Theorem successful_run_spawn_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> Spec.correct_final_state tf roots final.
  Proof.
    intros fuel tf roots final Hrun.
    pose proof (@E.successful_run_terminates_to fuel tf roots final Hrun) as Hterm.
    assert (Hinv : history_invariant (Sem.solved final) tf (Sem.terminal_config final)).
    { eapply history_invariant_steps; [apply initial_history_invariant |exact (proj1 Hterm)
      |exact (successful_spawned_path Hterm)]. }
    pose proof (proj2 Hterm) as Hquiet.
    split.
    - intros owner Hin. exact (@E.successful_run_roots_solved fuel tf roots final Hrun owner Hin).
    - intros owner Hsolved.
      apply E.solved_characterization in Hsolved as [Hmaterialized|Hdormant].
      + destruct (history_summaries Hinv Hmaterialized) as [Hqueued|[Hactive|Hsummary]];
          [exfalso; eapply quiescent_not_queued; eauto |contradiction|].
        destruct Hsummary as [direct [reads [effects [Htrace [Hreads [Heffects Hdirect]]]]]].
        assert (Hnotqueued : ~ queued final owner) by (eapply quiescent_not_queued; eauto).
        assert (Hagree : forall target value, In (target,value) reads ->
          R.semantic_lookup final target = Some value).
        { intros target value Hin. apply Forall_forall with (x := (target,value)) in Hreads;
            [|exact Hin]. destruct Hreads as [_ [_ [Heq|Hq]]]; [exact Heq|contradiction]. }
        split.
        * exists direct, reads, effects. eapply guarded_trace_evaluates; eauto.
        * split.
          -- eapply terminal_summary_post_solution; [exact Hquiet | |].
             ++ exact (@terminal_aggregate_bounded (fun _ => True) tf roots final Hterm).
             ++ exists direct, reads, effects. exact (conj Htrace (conj Hreads (conj Heffects Hdirect))).
          -- exact (@rhs_trace_spawn_closed (Sem.solved final) final (tf owner)
               direct reads effects Htrace Hagree).
      + assert (Hpure : R.pure_bottom_rhs tf owner = true).
        { pose proof (@reachable_dormant_sound fuel tf roots) as Hsound.
          pose proof Hrun as Hshape. unfold R.solve_fuel in Hshape.
          apply E.terminal_state_shape in Hshape as [Hshape _].
          rewrite Hshape in Hsound. exact (Hsound owner Hdormant). }
        split.
        * unfold R.pure_bottom_rhs in Hpure. destruct (tf owner); try discriminate.
          exists t, [], []. constructor.
        * split.
          -- exact (@successful_run_dormant_post_solution fuel tf roots final owner Hrun Hdormant).
          -- intros result [Hobs Hreads] target Hin.
             unfold R.pure_bottom_rhs in Hpure. destruct (tf owner); try discriminate.
             inversion Hobs; subst. contradiction.
  Qed.

End Make.
