From TcSolvers Require Export
  solvers.slr.deferred_simple.proofs.Semantics.
Import ListNotations.
Set Implicit Arguments.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : DeferredSimple.FEATURES) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Sem := Semantics.Make V D U SU S M Rk Features.
  Module R := Sem.R.

  Lemma run_fuel_steps : forall fuel tf start,
    Sem.steps tf start (R.run_fuel fuel tf start).
  Proof.
    induction fuel as [|fuel IH]; intros tf start; cbn.
    - constructor.
    - destruct (R.next_config tf start) as [next|] eqn:Hnext.
      + econstructor; [exact Hnext|apply IH].
      + constructor.
  Qed.

  Lemma terminal_state_shape : forall config final,
    R.terminal_state config = Some final ->
    config = Sem.terminal_config final /\ Sem.quiescent final.
  Proof.
    intros [st control] final H. destruct control; cbn in H; try discriminate.
    destruct (R.queue_peek (R.queue st)) eqn:Hq; try discriminate.
    destruct (R.pending_spawns st) eqn:Hp; try discriminate.
    inversion H; subst. split; [reflexivity|].
    unfold Sem.quiescent. auto.
  Qed.

  Theorem successful_run_terminates_to : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> Sem.terminates_to tf roots final.
  Proof.
    intros fuel tf roots final H. unfold R.solve_fuel in H.
    apply terminal_state_shape in H. destruct H as [Hshape Hquiet].
    split; [|exact Hquiet]. rewrite <- Hshape. apply run_fuel_steps.
  Qed.

  Theorem successful_run_quiescent : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> Sem.quiescent final.
  Proof.
    intros fuel tf roots final H.
    now apply successful_run_terminates_to in H as [_ H].
  Qed.

  Lemma terminal_has_no_step : forall tf st,
    Sem.quiescent st -> R.next_config tf (Sem.terminal_config st) = None.
  Proof.
    intros tf st [Hq Hp].
    unfold R.queue_peek in Hq. destruct (R.queue st) eqn:Hqueue; try discriminate.
    cbn. now rewrite Hqueue, Hp.
  Qed.

  Lemma run_fuel_stopped : forall fuel tf c,
    R.next_config tf c = None -> R.run_fuel fuel tf c = c.
  Proof.
    intros [|fuel] tf c H; cbn; [reflexivity|now rewrite H].
  Qed.

  Lemma run_fuel_add : forall fuel extra tf c,
    R.run_fuel (fuel + extra) tf c = R.run_fuel extra tf (R.run_fuel fuel tf c).
  Proof.
    induction fuel as [|fuel IH]; intros extra tf c; cbn; [reflexivity|].
    destruct (R.next_config tf c) as [next|] eqn:Hnext.
    - apply IH.
    - symmetry. now apply run_fuel_stopped.
  Qed.

  Theorem successful_run_more_fuel : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final ->
    forall extra, R.solve_fuel (fuel + extra) tf roots = Some final.
  Proof.
    intros fuel tf roots final H extra. unfold R.solve_fuel in *.
    pose proof (@terminal_state_shape _ _ H) as [Hshape Hquiet].
    rewrite run_fuel_add, Hshape.
    rewrite run_fuel_stopped by now apply terminal_has_no_step.
    now rewrite <- Hshape.
  Qed.

  Lemma steps_transitive : forall tf first middle final,
    Sem.steps tf first middle -> Sem.steps tf middle final -> Sem.steps tf first final.
  Proof.
    intros tf first middle final Hfirst Hlast. induction Hfirst; [exact Hlast|].
    econstructor; eauto.
  Qed.

  Lemma steps_have_exact_fuel : forall tf first final,
    Sem.steps tf first final -> exists fuel, R.run_fuel fuel tf first = final.
  Proof.
    intros tf first final Hsteps. induction Hsteps.
    - exists 0. reflexivity.
    - destruct IHHsteps as [fuel Hfuel]. exists (S fuel). cbn.
      now rewrite H, Hfuel.
  Qed.

  Definition queue_invariant (st : R.state) : Prop :=
    NoDup (R.pending_spawns st) /\
    forall x, In x (R.pending_spawns st) -> S.mem x (R.requested_spawns st) = true.

  Lemma empty_queue_invariant : queue_invariant R.empty_state.
  Proof. split; [constructor|intros x H; contradiction]. Qed.

  Lemma request_registered : forall st target,
    S.mem target (R.requested_spawns (R.request_spawn st target)) = true.
  Proof.
    intros st target. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)) eqn:H; [exact H|].
    cbn. apply SL.add_spec. now left.
  Qed.

  Lemma request_idempotent : forall st target,
    R.request_spawn (R.request_spawn st target) target = R.request_spawn st target.
  Proof.
    intros st target. unfold R.request_spawn at 1.
    now rewrite request_registered.
  Qed.

  Lemma request_preserves_ranking : forall st target,
    R.ranking (R.request_spawn st target) = R.ranking st.
  Proof.
    intros st target. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); reflexivity.
  Qed.

  Lemma request_preserves_queue_invariant : forall st target,
    queue_invariant st -> queue_invariant (R.request_spawn st target).
  Proof.
    intros st target [Hnd Hmem]. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)) eqn:Hseen.
    - split; assumption.
    - unfold queue_invariant; cbn. split.
      + apply NoDup_app; repeat split; auto.
        * constructor; [intro H; contradiction|constructor].
        * intros x Hin [Heq|Hfalse]; [subst x|contradiction].
          specialize (Hmem target Hin). congruence.
      + intros x Hin. apply in_app_iff in Hin. apply SL.add_spec.
        destruct Hin as [Hin|[Heq|Hfalse]]; auto; contradiction.
  Qed.

  Lemma pop_preserves_queue_invariant : forall st target rest,
    R.pending_spawns st = target :: rest -> queue_invariant st ->
    queue_invariant (R.with_spawns st rest (R.requested_spawns st)).
  Proof.
    intros st target rest Heq [Hnd Hmem]. unfold queue_invariant; cbn.
    rewrite Heq in Hnd, Hmem. inversion Hnd; subst.
    split; [assumption|intros x H; apply Hmem; now right].
  Qed.

  Definition supported (support : list V.t) (st : R.state) : Prop :=
    forall target, S.mem target (R.requested_spawns st) = true -> In target support.

  Lemma request_preserves_support : forall support st target,
    supported support st -> In target support -> supported support (R.request_spawn st target).
  Proof.
    intros support st target Hsupport Htarget x Hx.
    unfold R.request_spawn in Hx.
    destruct (S.mem target (R.requested_spawns st)); cbn in Hx.
    - now apply Hsupport.
    - apply SL.add_spec in Hx. destruct Hx as [->|Hx]; auto.
  Qed.

  Lemma requests_monotone : forall st target x,
    S.mem x (R.requested_spawns st) = true ->
    S.mem x (R.requested_spawns (R.request_spawn st target)) = true.
  Proof.
    intros st target x H. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); cbn; [exact H|].
    apply SL.add_spec. now right.
  Qed.

  (** Count unseen supported variables, rather than trusting set enumeration
      to be duplicate-free (SET_LAWS does not require that). *)
  Definition unseen (support : list V.t) (requested : S.t) : nat :=
    length (filter (fun x => negb (S.mem x requested)) support).

  Lemma add_mem_other : forall requested target x,
    x <> target -> S.mem x (S.add target requested) = S.mem x requested.
  Proof.
    intros requested target x Hneq.
    destruct (S.mem x (S.add target requested)) eqn:Ha,
      (S.mem x requested) eqn:Hb; try reflexivity.
    - apply SL.add_spec in Ha. destruct Ha; congruence.
    - assert (S.mem x (S.add target requested) = true) by
        (apply SL.add_spec; now right).
      congruence.
  Qed.

  Lemma unseen_add_le : forall support requested target,
    unseen support (S.add target requested) <= unseen support requested.
  Proof.
    induction support as [|x xs IH]; intros requested target;
      unfold unseen in *; cbn; [lia|].
    specialize (IH requested target).
    destruct (V.eq_dec x target) as [->|Hneq].
    - assert (S.mem target (S.add target requested) = true) as H by
        (apply SL.add_spec; now left).
      rewrite H; cbn. destruct (S.mem target requested); cbn; lia.
    - rewrite add_mem_other by exact Hneq.
      destruct (S.mem x requested); cbn; lia.
  Qed.

  Lemma unseen_add_lt : forall support requested target,
    In target support -> S.mem target requested = false ->
    unseen support (S.add target requested) < unseen support requested.
  Proof.
    induction support as [|x xs IH]; intros requested target Hin Hfresh;
      [contradiction|].
    destruct (V.eq_dec x target) as [->|Hneq].
    - pose proof (unseen_add_le xs requested target) as Hle.
      assert (S.mem target (S.add target requested) = true) as H by
        (apply SL.add_spec; now left).
      unfold unseen in *; cbn. rewrite H, Hfresh; cbn; lia.
    - destruct Hin as [Heq|Hin]; [congruence|].
      specialize (IH requested target Hin Hfresh).
      unfold unseen in *; cbn. rewrite add_mem_other by exact Hneq.
      destruct (S.mem x requested); cbn; lia.
  Qed.

  Definition spawn_credit (support : list V.t) (st : R.state) : nat :=
    2 * unseen support (R.requested_spawns st) + length (R.pending_spawns st).

  Lemma fresh_request_decreases_credit : forall support st target,
    In target support -> S.mem target (R.requested_spawns st) = false ->
    spawn_credit support (R.request_spawn st target) < spawn_credit support st.
  Proof.
    intros support st target Hin Hfresh.
    pose proof (@unseen_add_lt support (R.requested_spawns st) target Hin Hfresh).
    unfold R.request_spawn. rewrite Hfresh.
    unfold spawn_credit; cbn. rewrite length_app; cbn; lia.
  Qed.

  Lemma dispatch_decreases_credit : forall support st target rest,
    R.pending_spawns st = target :: rest ->
    spawn_credit support (R.with_spawns st rest (R.requested_spawns st)) <
      spawn_credit support st.
  Proof.
    intros support st target rest H. unfold spawn_credit; cbn.
    rewrite H; cbn; lia.
  Qed.

  (** Only first requests and dispatches are charged here. Ordinary solver
      transitions and duplicate requests require the separate episode proof. *)
  Inductive scheduling_step (support : list V.t) : R.state -> R.state -> Prop :=
  | ScheduleRequest : forall st target,
      In target support -> S.mem target (R.requested_spawns st) = false ->
      scheduling_step support st (R.request_spawn st target)
  | ScheduleDispatch : forall st target rest,
      R.pending_spawns st = target :: rest ->
      scheduling_step support st (R.with_spawns st rest (R.requested_spawns st)).

  Lemma scheduling_step_decreases : forall support before after,
    scheduling_step support before after ->
    spawn_credit support after < spawn_credit support before.
  Proof.
    intros support before after H. destruct H.
    - now apply fresh_request_decreases_credit.
    - eapply dispatch_decreases_credit; eauto.
  Qed.

  Theorem scheduling_well_founded : forall support,
    well_founded (fun after before => scheduling_step support before after).
  Proof.
    intro support. apply (wf_incl _ _ (ltof R.state (spawn_credit support))).
    - intros after before H. now apply scheduling_step_decreases.
    - apply well_founded_ltof.
  Qed.

  Definition snapshot (st : R.state) :=
    (R.pending_spawns st, R.requested_spawns st).
  Create HintDb spawns.
  Lemma with_sigma_snapshot : forall st next,
    snapshot (R.with_sigma st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_sigma_snapshot : spawns.

  Lemma with_ranking_snapshot : forall st next,
    snapshot (R.with_ranking st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_ranking_snapshot : spawns.

  Lemma with_queue_snapshot : forall st next,
    snapshot (R.with_queue st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_queue_snapshot : spawns.

  Lemma with_started_snapshot : forall st next,
    snapshot (R.with_started st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_started_snapshot : spawns.

  Lemma with_readers_snapshot : forall st next,
    snapshot (R.with_readers st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_readers_snapshot : spawns.

  Lemma with_contributions_snapshot : forall st next,
    snapshot (R.with_contributions st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_contributions_snapshot : spawns.

  Lemma with_phases_snapshot : forall st next,
    snapshot (R.with_phases st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_phases_snapshot : spawns.

  Lemma with_side_phases_snapshot : forall st next,
    snapshot (R.with_side_phases st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_side_phases_snapshot : spawns.

  Lemma with_local_sides_snapshot : forall st next,
    snapshot (R.with_local_sides st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_local_sides_snapshot : spawns.

  Lemma with_dormant_bottom_snapshot : forall st next,
    snapshot (R.with_dormant_bottom st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_dormant_bottom_snapshot : spawns.

  Lemma with_controlled_snapshot : forall st next,
    snapshot (R.with_controlled st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_controlled_snapshot : spawns.

  Lemma with_dirty_side_targets_snapshot : forall st next,
    snapshot (R.with_dirty_side_targets st next) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite with_dirty_side_targets_snapshot : spawns.

  Lemma remember_dormant_snapshot : forall st x,
    snapshot (R.remember_dormant st x) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite remember_dormant_snapshot : spawns.

  Lemma enqueue_handle_snapshot : forall st entry,
    snapshot (R.enqueue_handle st entry) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite enqueue_handle_snapshot : spawns.

  Lemma mark_side_dirty_snapshot : forall st target,
    snapshot (R.mark_side_dirty st target) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite mark_side_dirty_snapshot : spawns.

  Lemma clear_side_dirty_snapshot : forall st target,
    snapshot (R.clear_side_dirty st target) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite clear_side_dirty_snapshot : spawns.

  Lemma cancel_dirty_target_snapshot : forall st target,
    snapshot (R.cancel_dirty_target st target) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite cancel_dirty_target_snapshot : spawns.

  Lemma promote_controlled_snapshot : forall st x,
    snapshot (R.promote_controlled st x) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite promote_controlled_snapshot : spawns.

  Lemma add_reader_snapshot : forall st target owner,
    snapshot (R.add_reader st target owner) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite add_reader_snapshot : spawns.

  Lemma reset_local_sides_snapshot : forall st owner,
    snapshot (R.reset_local_sides st owner) = snapshot st.
  Proof. reflexivity. Qed.
  #[local] Hint Rewrite reset_local_sides_snapshot : spawns.

  Lemma observe_snapshot : forall st target next entry,
    R.observe st target = (next, entry) -> snapshot next = snapshot st.
  Proof.
    intros st target next entry H. unfold R.observe in H.
    destruct (R.Ranking.observe (R.ranking st) target).
    inversion H; reflexivity.
  Qed.

  Lemma enqueue_snapshot : forall st target,
    snapshot (R.enqueue st target) = snapshot st.
  Proof.
    intros. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) target); reflexivity.
  Qed.
  #[local] Hint Rewrite enqueue_snapshot : spawns.

  Lemma enqueue_all_snapshot : forall xs st,
    snapshot (R.enqueue_all st xs) = snapshot st.
  Proof.
    induction xs; intros st; cbn; [reflexivity|].
    rewrite IHxs. apply enqueue_snapshot.
  Qed.
  #[local] Hint Rewrite enqueue_all_snapshot : spawns.

  Lemma materialize_snapshot : forall st x,
    snapshot (R.materialize st x) = snapshot st.
  Proof.
    intros. unfold R.materialize.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite materialize_snapshot : spawns.

  Lemma get_control_state_snapshot : forall st owner target,
    snapshot (R.get_control_state st owner target) = snapshot st.
  Proof.
    intros. unfold R.get_control_state.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite get_control_state_snapshot : spawns.

  Lemma get_ready_state_snapshot : forall st owner target,
    snapshot (R.get_ready_state st owner target) = snapshot st.
  Proof.
    intros. unfold R.get_ready_state.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite get_ready_state_snapshot : spawns.

  Lemma start_evaluation_snapshot : forall st owner,
    snapshot (R.start_evaluation st owner) = snapshot st.
  Proof.
    intros. unfold R.start_evaluation.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite start_evaluation_snapshot : spawns.

  Lemma record_side_payload_snapshot : forall st owner target raw,
    snapshot (R.record_side_payload st owner target raw) = snapshot st.
  Proof.
    intros. unfold R.record_side_payload.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite record_side_payload_snapshot : spawns.

  Lemma side_ready_state_snapshot : forall st owner target raw,
    snapshot (R.side_ready_state st owner target raw) = snapshot st.
  Proof.
    intros. unfold R.side_ready_state.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite side_ready_state_snapshot : spawns.

  Lemma write_changed_value_snapshot : forall st owner value,
    snapshot (R.write_changed_value st owner value) = snapshot st.
  Proof.
    intros. unfold R.write_changed_value.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite write_changed_value_snapshot : spawns.

  Lemma set_value_snapshot : forall st owner direct,
    snapshot (R.set_value st owner direct) = snapshot st.
  Proof.
    intros. unfold R.set_value.
    autorewrite with spawns.
    repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x eqn:?
    end; autorewrite with spawns; reflexivity.
  Qed.
  #[local] Hint Rewrite set_value_snapshot : spawns.

  Lemma try_dirty_read_snapshot : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next -> snapshot next = snapshot st.
  Proof.
    intros tf st owner target next H. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end; try discriminate; inversion H; subst;
      autorewrite with spawns; reflexivity.
  Qed.

  Lemma dirty_get_ready_state_snapshot : forall tf st owner target,
    snapshot (R.dirty_get_ready_state tf st owner target) = snapshot st.
  Proof.
    intros. unfold R.dirty_get_ready_state. autorewrite with spawns.
    destruct (R.try_dirty_read tf _ _ _) eqn:H.
    - rewrite (@try_dirty_read_snapshot _ _ _ _ _ H). now autorewrite with spawns.
    - now autorewrite with spawns.
  Qed.
  #[local] Hint Rewrite dirty_get_ready_state_snapshot : spawns.

  Lemma next_config_spawn_cases : forall tf before after,
    R.next_config tf before = Some after ->
    snapshot (R.cfg_state after) = snapshot (R.cfg_state before) \/
    (exists target, snapshot (R.cfg_state after) =
      snapshot (R.request_spawn (R.cfg_state before) target)) \/
    (exists target rest,
      R.pending_spawns (R.cfg_state before) = target :: rest /\
      snapshot (R.cfg_state after) = (rest, R.requested_spawns (R.cfg_state before)) /\
      R.cfg_control after = R.RunSeeds [target]).
  Proof.
    intros tf [st control] after H.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control] in H |- *;
      repeat match type of H with
      | context [match ?x with _ => _ end] => destruct x eqn:?
      end; try discriminate; inversion H; subst; cbn [R.cfg_state];
      try (left; autorewrite with spawns; reflexivity);
      try (right; left; eexists; reflexivity);
      try (right; right; match goal with
      | Hp : R.pending_spawns st = ?target :: ?rest |- _ =>
          exists target, rest; repeat split; assumption || reflexivity
      end).
    all: left; autorewrite with spawns.
    all: match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      rewrite (@observe_snapshot base target next entry Hobs)
    end.
    all: now autorewrite with spawns.
  Qed.

  Lemma snapshot_queue_invariant : forall before after,
    snapshot after = snapshot before -> queue_invariant before -> queue_invariant after.
  Proof.
    intros before after H. unfold snapshot in H. injection H as Hp Hr.
    unfold queue_invariant. now rewrite Hp, Hr.
  Qed.

  Lemma next_config_queue_invariant : forall tf before after,
    R.next_config tf before = Some after ->
    queue_invariant (R.cfg_state before) -> queue_invariant (R.cfg_state after).
  Proof.
    intros tf before after Hnext Hinv.
    destruct (@next_config_spawn_cases tf before after Hnext)
      as [Hsame|[[target Hrequest]|[target [rest [Hpop [Hsame Hcontrol]]]]]].
    - eapply snapshot_queue_invariant; eauto.
    - eapply snapshot_queue_invariant; [exact Hrequest|].
      now apply request_preserves_queue_invariant.
    - eapply snapshot_queue_invariant with
        (before := R.with_spawns (R.cfg_state before) rest
          (R.requested_spawns (R.cfg_state before))); [exact Hsame|].
      eapply pop_preserves_queue_invariant; eauto.
  Qed.

  Theorem run_fuel_queue_invariant : forall fuel tf start,
    queue_invariant (R.cfg_state start) ->
    queue_invariant (R.cfg_state (R.run_fuel fuel tf start)).
  Proof.
    induction fuel as [|fuel IH]; intros tf start Hinv; cbn; [exact Hinv|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|exact Hinv].
    apply IH. eapply next_config_queue_invariant; eauto.
  Qed.

  Theorem reachable_queue_invariant : forall fuel tf roots,
    queue_invariant (R.cfg_state (R.run_fuel fuel tf (R.initial_config roots))).
  Proof. intros. apply run_fuel_queue_invariant, empty_queue_invariant. Qed.

  Lemma next_config_requests_monotone : forall tf before after target,
    R.next_config tf before = Some after ->
    S.mem target (R.requested_spawns (R.cfg_state before)) = true ->
    S.mem target (R.requested_spawns (R.cfg_state after)) = true.
  Proof.
    intros tf before after target Hnext Hrequested.
    destruct (@next_config_spawn_cases tf before after Hnext)
      as [Hsame|[[requested Hrequest]|[head [rest [Hpop [Hsame Hcontrol]]]]]].
    - unfold snapshot in Hsame. injection Hsame as Hp Hr. now rewrite Hr.
    - unfold snapshot in Hrequest. injection Hrequest as Hp Hr.
      rewrite Hr. now apply requests_monotone.
    - unfold snapshot in Hsame. injection Hsame as Hp Hr. now rewrite Hr.
  Qed.

  Lemma steps_requests_monotone : forall tf before after target,
    Sem.steps tf before after ->
    S.mem target (R.requested_spawns (R.cfg_state before)) = true ->
    S.mem target (R.requested_spawns (R.cfg_state after)) = true.
  Proof.
    intros tf before after target Hsteps. induction Hsteps; intros Hrequested.
    - exact Hrequested.
    - apply IHHsteps. eapply next_config_requests_monotone; eauto.
  Qed.

  Lemma request_credit_nonincreasing : forall support st target,
    In target support ->
    spawn_credit support (R.request_spawn st target) <= spawn_credit support st.
  Proof.
    intros support st target Hin.
    destruct (S.mem target (R.requested_spawns st)) eqn:Hmem.
    - unfold R.request_spawn. rewrite Hmem. apply Nat.le_refl.
    - pose proof (@fresh_request_decreases_credit support st target Hin Hmem). lia.
  Qed.

  Lemma snapshot_credit : forall support before after,
    snapshot after = snapshot before -> spawn_credit support after = spawn_credit support before.
  Proof.
    intros support before after H. unfold snapshot in H. injection H as Hp Hr.
    unfold spawn_credit. now rewrite Hp, Hr.
  Qed.

  Lemma next_config_spawn_credit : forall support tf before after,
    R.next_config tf before = Some after -> supported support (R.cfg_state after) ->
    spawn_credit support (R.cfg_state after) <= spawn_credit support (R.cfg_state before).
  Proof.
    intros support tf before after Hnext Hsupport.
    destruct (@next_config_spawn_cases tf before after Hnext)
      as [Hsame|[[target Hrequest]|[target [rest [Hpop [Hsame Hcontrol]]]]]].
    - rewrite (@snapshot_credit support _ _ Hsame). apply Nat.le_refl.
    - rewrite (@snapshot_credit support _ _ Hrequest). apply request_credit_nonincreasing.
      apply Hsupport. unfold snapshot in Hrequest. injection Hrequest as Hp Hr.
      rewrite Hr. apply request_registered.
    - change (snapshot (R.cfg_state after) =
        snapshot (R.with_spawns (R.cfg_state before) rest
          (R.requested_spawns (R.cfg_state before)))) in Hsame.
      rewrite (@snapshot_credit support _ _ Hsame).
      pose proof (@dispatch_decreases_credit support (R.cfg_state before) target rest Hpop).
      lia.
  Qed.

  Definition handle_in support (entry : R.handle) := In (R.handle_variable entry) support.
  Definition queue_in support (queue : R.work_queue) := Forall (handle_in support) queue.
  Definition readers_in support (table : R.readers_table) :=
    forall target owner, S.mem owner (R.lookup_set table target) = true -> In owner support.
  Record state_in support (st : R.state) : Prop := {
    state_queue_in : queue_in support (R.queue st);
    state_readers_in : readers_in support (R.readers st);
    state_pending_in : incl (R.pending_spawns st) support;
    state_requested_in : supported support st
  }.

  Fixpoint continuation_in support (k : R.continuation) : Prop :=
    match k with
    | R.KLoop => True
    | R.KSeedLoop roots => incl roots support
    | R.KSolveOneLoop owner rest => handle_in support owner /\ continuation_in support rest
    | R.KAfterGet owner target next rest => handle_in support owner /\
        handle_in support target /\
        (forall value, Sem.rhs_supported (fun x => In x support) (next value)) /\
        continuation_in support rest
    | R.KAfterSide owner next rest | R.KAfterSpawn owner next rest =>
        handle_in support owner /\ Sem.rhs_supported (fun x => In x support) next /\
        continuation_in support rest
    end.
  Definition control_in support (control : R.control) : Prop :=
    match control with
    | R.RunLoop => True
    | R.RunSeeds roots | R.RunSeedLoop roots => incl roots support
    | R.RunSolveOne owner k | R.RunSolveOneLoop owner k =>
        handle_in support owner /\ continuation_in support k
    | R.RunRhs owner body k | R.AfterSide owner body k | R.AfterSpawn owner body k =>
        handle_in support owner /\ Sem.rhs_supported (fun x => In x support) body /\
        continuation_in support k
    | R.AfterGet owner target next k => handle_in support owner /\
        handle_in support target /\
        (forall value, Sem.rhs_supported (fun x => In x support) (next value)) /\
        continuation_in support k
    end.
  Definition config_in support c :=
    state_in support (R.cfg_state c) /\ control_in support (R.cfg_control c).

  Create HintDb finite_support.

  Lemma queue_insert_fresh_in : forall support queue entry,
    queue_in support queue -> handle_in support entry ->
    queue_in support (R.queue_insert_fresh entry queue).
  Proof.
    intros support queue entry Hqueue Hin. induction Hqueue; cbn [R.queue_insert_fresh].
    - now constructor.
    - destruct (Nat.ltb (R.handle_rank x) (R.handle_rank entry));
        repeat constructor; assumption.
  Qed.
  Lemma queue_insert_in : forall support queue entry,
    queue_in support queue -> handle_in support entry ->
    queue_in support (R.queue_insert entry queue).
  Proof.
    intros. unfold R.queue_insert. destruct (R.queue_contains_rank _ _);
      auto using queue_insert_fresh_in.
  Qed.
  Lemma queue_remove_in : forall support queue rank,
    queue_in support queue -> queue_in support (R.queue_remove_rank rank queue).
  Proof.
    intros support queue rank Hqueue. induction Hqueue; cbn; [constructor|].
    destruct (Nat.eqb rank (R.handle_rank x)); auto. now constructor.
  Qed.
  Lemma queue_pop_in : forall support queue entry rest,
    queue_in support queue -> R.queue_pop queue = Some (entry, rest) ->
    handle_in support entry /\ queue_in support rest.
  Proof.
    intros support [|head tail] entry rest Hqueue Hpop; cbn in Hpop; try discriminate.
    inversion Hpop; subst. inversion Hqueue; subst. auto.
  Qed.

  Lemma with_queue_in : forall support st next,
    state_in support st -> queue_in support next -> state_in support (R.with_queue st next).
  Proof. intros support st next Hst Hnext. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_queue_in : finite_support.

  Lemma with_readers_in : forall support st next,
    state_in support st -> readers_in support next -> state_in support (R.with_readers st next).
  Proof. intros support st next Hst Hnext. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_readers_in : finite_support.
  Lemma with_sigma_in : forall support st next,
    state_in support st -> state_in support (R.with_sigma st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_sigma_in : finite_support.

  Lemma with_ranking_in : forall support st next,
    state_in support st -> state_in support (R.with_ranking st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_ranking_in : finite_support.

  Lemma with_started_in : forall support st next,
    state_in support st -> state_in support (R.with_started st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_started_in : finite_support.

  Lemma with_contributions_in : forall support st next,
    state_in support st -> state_in support (R.with_contributions st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_contributions_in : finite_support.

  Lemma with_phases_in : forall support st next,
    state_in support st -> state_in support (R.with_phases st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_phases_in : finite_support.

  Lemma with_side_phases_in : forall support st next,
    state_in support st -> state_in support (R.with_side_phases st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_side_phases_in : finite_support.

  Lemma with_local_sides_in : forall support st next,
    state_in support st -> state_in support (R.with_local_sides st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_local_sides_in : finite_support.

  Lemma with_dormant_bottom_in : forall support st next,
    state_in support st -> state_in support (R.with_dormant_bottom st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_dormant_bottom_in : finite_support.

  Lemma with_controlled_in : forall support st next,
    state_in support st -> state_in support (R.with_controlled st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_controlled_in : finite_support.

  Lemma with_dirty_side_targets_in : forall support st next,
    state_in support st -> state_in support (R.with_dirty_side_targets st next).
  Proof. intros support st next Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve with_dirty_side_targets_in : finite_support.

  Lemma remember_dormant_in : forall support st x,
    state_in support st -> state_in support (R.remember_dormant st x).
  Proof. intros support st x Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve remember_dormant_in : finite_support.

  Lemma promote_controlled_in : forall support st x,
    state_in support st -> state_in support (R.promote_controlled st x).
  Proof. intros support st x Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve promote_controlled_in : finite_support.

  Lemma mark_side_dirty_in : forall support st target,
    state_in support st -> state_in support (R.mark_side_dirty st target).
  Proof. intros support st target Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve mark_side_dirty_in : finite_support.

  Lemma clear_side_dirty_in : forall support st target,
    state_in support st -> state_in support (R.clear_side_dirty st target).
  Proof. intros support st target Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve clear_side_dirty_in : finite_support.

  Lemma reset_local_sides_in : forall support st owner,
    state_in support st -> state_in support (R.reset_local_sides st owner).
  Proof. intros support st owner Hst. destruct Hst; constructor; assumption. Qed.
  #[local] Hint Resolve reset_local_sides_in : finite_support.


  Lemma observe_in : forall support st target next entry,
    state_in support st -> In target support -> R.observe st target = (next, entry) ->
    state_in support next /\ handle_in support entry.
  Proof.
    intros support st target next entry Hst Hin Hobs. unfold R.observe in Hobs.
    destruct (R.Ranking.observe (R.ranking st) target); inversion Hobs; subst.
    split; [now apply with_ranking_in|exact Hin].
  Qed.
  Lemma enqueue_handle_in : forall support st entry,
    state_in support st -> handle_in support entry -> state_in support (R.enqueue_handle st entry).
  Proof.
    intros support st entry Hst Hin. apply with_queue_in; [exact Hst|].
    apply queue_insert_in; [exact (state_queue_in Hst)|exact Hin].
  Qed.
  #[local] Hint Resolve enqueue_handle_in : finite_support.
  Lemma enqueue_in : forall support st target,
    state_in support st -> In target support -> state_in support (R.enqueue st target).
  Proof.
    intros support st target Hst Hin. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobs.
    destruct (@observe_in support st target next entry Hst Hin Hobs).
    now apply enqueue_handle_in.
  Qed.
  Lemma enqueue_all_in : forall support xs st,
    incl xs support -> state_in support st -> state_in support (R.enqueue_all st xs).
  Proof.
    intros support xs. induction xs as [|x xs IH]; intros st Hin Hst; cbn; [exact Hst|].
    apply IH; [intros y Hy; apply Hin; now right|].
    apply enqueue_in; [exact Hst|apply Hin; now left].
  Qed.
  Lemma readers_update_in : forall support readers target next,
    readers_in support readers ->
    (forall owner, S.mem owner next = true -> In owner support) ->
    readers_in support (M.update readers target next).
  Proof.
    intros support readers target next Hr Hnext observed owner Hmem.
    unfold R.lookup_set in Hmem.
    destruct (V.eq_dec observed target) as [->|Hneq].
    - rewrite ML.lookup_update_same in Hmem. now apply Hnext.
    - rewrite ML.lookup_update_other in Hmem by exact Hneq. exact (Hr observed owner Hmem).
  Qed.
  Lemma add_reader_in : forall support st target owner,
    state_in support st -> In owner support -> state_in support (R.add_reader st target owner).
  Proof.
    intros support st target owner Hst Hin. apply with_readers_in; [exact Hst|].
    apply readers_update_in; [exact (state_readers_in Hst)|].
    intros x Hmem. apply SL.add_spec in Hmem. destruct Hmem as [->|Hmem]; [exact Hin|].
    exact (@state_readers_in support st Hst target x Hmem).
  Qed.
  #[local] Hint Resolve add_reader_in : finite_support.
  Lemma materialize_in : forall support st target,
    state_in support st -> state_in support (R.materialize st target).
  Proof.
    intros. unfold R.materialize. destruct (R.is_materialized st target); eauto with finite_support.
  Qed.
  #[local] Hint Resolve materialize_in : finite_support.
  Lemma cancel_dirty_target_in : forall support st target,
    state_in support st -> state_in support (R.cancel_dirty_target st target).
  Proof.
    intros support st target Hst. apply clear_side_dirty_in, with_queue_in; [exact Hst|].
    apply queue_remove_in. exact (state_queue_in Hst).
  Qed.
  #[local] Hint Resolve cancel_dirty_target_in : finite_support.
  Lemma get_control_state_in : forall support st owner target,
    state_in support st ->  state_in support (R.get_control_state st owner target).
  Proof.
    intros. unfold R.get_control_state.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; eauto 8 with finite_support.
  Qed.
  #[local] Hint Resolve get_control_state_in : finite_support.

  Lemma get_ready_state_in : forall support st owner target,
    state_in support st -> handle_in support owner -> state_in support (R.get_ready_state st owner target).
  Proof.
    intros. unfold R.get_ready_state.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; eauto 8 with finite_support.
  Qed.
  #[local] Hint Resolve get_ready_state_in : finite_support.

  Lemma start_evaluation_in : forall support st owner,
    state_in support st ->  state_in support (R.start_evaluation st owner).
  Proof.
    intros. unfold R.start_evaluation.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; eauto 8 with finite_support.
  Qed.
  #[local] Hint Resolve start_evaluation_in : finite_support.

  Lemma record_side_payload_in : forall support st source target raw,
    state_in support st ->  state_in support (R.record_side_payload st source target raw).
  Proof.
    intros. unfold R.record_side_payload.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; eauto 8 with finite_support.
  Qed.
  #[local] Hint Resolve record_side_payload_in : finite_support.

  Lemma side_ready_state_in : forall support st owner target raw,
    state_in support st ->  state_in support (R.side_ready_state st owner target raw).
  Proof.
    intros. unfold R.side_ready_state.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    end; eauto 8 with finite_support.
  Qed.
  #[local] Hint Resolve side_ready_state_in : finite_support.


  Lemma write_changed_value_in : forall support st owner value,
    state_in support st -> state_in support (R.write_changed_value st owner value).
  Proof.
    intros support st owner value Hst. unfold R.write_changed_value.
    assert (Hqueued : state_in support
      (R.enqueue_all (R.with_sigma st (M.update (R.sigma st) owner value))
        (S.elements (R.lookup_set (R.readers st) owner)))).
    { apply enqueue_all_in; [|now apply with_sigma_in].
      intros target Hin. apply SL.mem_spec in Hin.
      exact (@state_readers_in support st Hst owner target Hin). }
    apply with_readers_in; [exact Hqueued|].
    apply readers_update_in; [exact (state_readers_in Hqueued)|].
    intros target Hmem. rewrite SL.empty_spec in Hmem. discriminate.
  Qed.
  #[local] Hint Resolve write_changed_value_in : finite_support.

  Lemma set_value_in : forall support st owner direct,
    state_in support st -> state_in support (R.set_value st owner direct).
  Proof.
    intros. unfold R.set_value.
    repeat match goal with | |- context [if ?b then _ else _] => destruct b eqn:? end;
      eauto with finite_support.
  Qed.
  #[local] Hint Resolve set_value_in : finite_support.

  Lemma try_dirty_read_in : forall support tf st owner target next,
    state_in support st -> R.try_dirty_read tf st owner target = Some next -> state_in support next.
  Proof.
    intros support tf st owner target next Hst Hread. unfold R.try_dirty_read in Hread.
    repeat match type of Hread with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end; try discriminate; inversion Hread; subst; eauto 8 with finite_support.
  Qed.
  Lemma dirty_get_ready_state_in : forall support tf st owner target,
    state_in support st -> handle_in support owner ->
    state_in support (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros support tf st owner target Hst Hin. unfold R.dirty_get_ready_state.
    apply add_reader_in; [|exact Hin].
    destruct (R.try_dirty_read tf _ _ _) eqn:Hread.
    - eapply try_dirty_read_in; [|exact Hread]. eauto with finite_support.
    - eauto with finite_support.
  Qed.
  #[local] Hint Resolve dirty_get_ready_state_in : finite_support.

  Lemma request_spawn_in : forall support st target,
    state_in support st -> In target support -> state_in support (R.request_spawn st target).
  Proof.
    intros support st target Hst Hin. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); [exact Hst|].
    destruct Hst as [Hq Hr Hp Hs]. constructor; cbn; try assumption.
    - intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|Hfalse]]; auto; contradiction.
    - intros x Hx. cbn in Hx. apply SL.add_spec in Hx. destruct Hx as [->|Hx]; auto.
  Qed.
  #[local] Hint Resolve request_spawn_in : finite_support.

  Lemma dispatch_in : forall support st target rest,
    state_in support st -> R.pending_spawns st = target :: rest ->
    state_in support (R.with_spawns st rest (R.requested_spawns st)) /\ In target support.
  Proof.
    intros support st target rest [Hq Hr Hp Hs] Hpending. rewrite Hpending in Hp.
    split; [constructor; cbn; try assumption|apply Hp; now left].
    intros x Hx. apply Hp. now right.
  Qed.
  Lemma continue_in : forall support k,
    continuation_in support k -> control_in support (R.continue k).
  Proof. intros support k. destruct k; cbn; auto. Qed.
  #[local] Hint Resolve continue_in : finite_support.

  Lemma next_config_in : forall support tf before after,
    (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    config_in support before -> R.next_config tf before = Some after -> config_in support after.
  Proof.
    intros support tf [st control] after Htf [Hst Hcontrol] Hnext.
    destruct control; cbn [control_in R.cfg_control R.cfg_state] in Hcontrol;
      cbn [R.next_config R.cfg_control R.cfg_state] in Hnext.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: repeat match type of Hnext with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end; try discriminate.
    all: repeat match goal with
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Ret _) |- _ => inversion Hrhs; clear Hrhs
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Get _ _) |- _ => inversion Hrhs; clear Hrhs
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Side _ _ _) |- _ => inversion Hrhs; clear Hrhs
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Spawn _ _) |- _ => inversion Hrhs; clear Hrhs
    end.
    all: try match goal with
    | Hpop : R.queue_pop (R.queue ?base) = Some (?entry, ?rest) |- _ =>
      destruct (@queue_pop_in support (R.queue base) entry rest (state_queue_in Hst) Hpop)
    end.
    all: try match goal with
    | Hp : R.pending_spawns ?base = ?target :: ?rest |- _ =>
      destruct (@dispatch_in support base target rest Hst Hp)
    end.
    all: try match goal with
    | Hroots : incl (?root :: ?remaining) ?sup |- _ =>
      assert (In root sup) by (apply Hroots; now left);
      assert (incl remaining sup) by (intros x Hx; apply Hroots; now right)
    end.
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      destruct (@observe_in support base target next entry Hst ltac:(assumption) Hobs)
    end.
    all: inversion Hnext; subst; split; cbn [R.cfg_state R.cfg_control control_in continuation_in].
    all: try solve [eauto 10 with finite_support].
    all: repeat split; eauto 8 with finite_support.
    all: intros x [<-|Hfalse]; [assumption|contradiction].
  Qed.
  Lemma empty_state_in : forall support, state_in support R.empty_state.
  Proof.
    intros support. constructor; cbn.
    - constructor.
    - intros target owner Hmem. unfold R.lookup_set in Hmem.
      rewrite ML.lookup_empty, SL.empty_spec in Hmem. discriminate.
    - intros x Hx. contradiction.
    - intros x Hmem. cbn in Hmem. rewrite SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma run_fuel_in : forall fuel support tf start,
    (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    config_in support start -> config_in support (R.run_fuel fuel tf start).
  Proof.
    induction fuel as [|fuel IH]; intros support tf start Htf Hstart; cbn; auto.
    destruct (R.next_config tf start) as [next|] eqn:Hnext; auto.
    apply IH; auto. eapply next_config_in; eauto.
  Qed.

  Theorem reachable_config_in : forall fuel tf roots (finite : Sem.finite_system tf roots),
    config_in (Sem.support finite) (R.run_fuel fuel tf (R.initial_config roots)).
  Proof.
    intros fuel tf roots finite. apply run_fuel_in; [apply Sem.system_supported|].
    split; [apply empty_state_in|exact (Sem.initial_supported finite)].
  Qed.

  Lemma run_fuel_spawn_credit : forall fuel support tf start,
    (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    config_in support start ->
    spawn_credit support (R.cfg_state (R.run_fuel fuel tf start)) <=
    spawn_credit support (R.cfg_state start).
  Proof.
    induction fuel as [|fuel IH]; intros support tf start Htf Hstart; cbn [R.run_fuel]; [lia|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|lia].
    assert (Hafter : config_in support next) by (eapply next_config_in; eauto).
    specialize (IH support tf next Htf Hafter).
    pose proof (@next_config_spawn_credit support tf start next Hnext
      (state_requested_in (proj1 Hafter))). lia.
  Qed.

  Lemma empty_spawn_credit : forall support,
    spawn_credit support R.empty_state = 2 * length support.
  Proof.
    intros support. unfold spawn_credit, unseen. cbn.
    induction support as [|x xs IH]; cbn; [reflexivity|].
    rewrite SL.empty_spec. cbn. lia.
  Qed.

  Theorem reachable_spawn_credit : forall fuel tf roots (finite : Sem.finite_system tf roots),
    spawn_credit (Sem.support finite)
      (R.cfg_state (R.run_fuel fuel tf (R.initial_config roots))) <=
    2 * length (Sem.support finite).
  Proof.
    intros fuel tf roots finite. rewrite <- empty_spawn_credit.
    apply run_fuel_spawn_credit; [apply Sem.system_supported|].
    split; [apply empty_state_in|exact (Sem.initial_supported finite)].
  Qed.
  Lemma steps_in : forall support tf first final,
    (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    config_in support first -> Sem.steps tf first final -> config_in support final.
  Proof.
    intros support tf first final Htf Hfirst Hsteps. induction Hsteps; auto.
    apply IHHsteps. eapply next_config_in; eauto.
  Qed.

  Lemma steps_spawn_credit : forall support tf first final,
    (forall owner, In owner support -> Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    config_in support first -> Sem.steps tf first final ->
    spawn_credit support (R.cfg_state final) <= spawn_credit support (R.cfg_state first).
  Proof.
    intros support tf first final Htf Hfirst Hsteps. induction Hsteps; [lia|].
    assert (Hnext : config_in support next) by (eapply next_config_in; eauto).
    specialize (IHHsteps Hnext).
    pose proof (@next_config_spawn_credit support tf first next H
      (state_requested_in (proj1 Hnext))). lia.
  Qed.
  Create HintDb solved.

  Lemma solved_characterization : forall st x,
    Sem.solved st x <->
    (exists value, M.lookup (R.sigma st) x = Some value) \/
    S.mem x (R.dormant_bottom st) = true.
  Proof.
    intros st x. unfold Sem.solved, Sem.StateSpec.solved, R.semantic_lookup.
    destruct (M.lookup (R.sigma st) x) eqn:Hlookup.
    - split; [intros; left; eauto|intros; eauto].
    - destruct (S.mem x (R.dormant_bottom st)) eqn:Hmem.
      + split; [intros; now right|intros; eauto].
      + split; [intros [v H]; discriminate|].
        intros [[v H]|H]; discriminate.
  Qed.

  Lemma update_sigma_solved : forall st owner value x,
    Sem.solved st x ->
    Sem.solved (R.with_sigma st (M.update (R.sigma st) owner value)) x.
  Proof.
    intros st owner value x H. apply solved_characterization in H.
    apply solved_characterization; cbn. destruct (V.eq_dec owner x) as [->|Hneq].
    - left. exists value. apply ML.lookup_update_same.
    - rewrite ML.lookup_update_other by congruence. exact H.
  Qed.
  #[local] Hint Resolve update_sigma_solved : solved.

  Lemma update_sigma_solves : forall st owner value,
    Sem.solved (R.with_sigma st (M.update (R.sigma st) owner value)) owner.
  Proof.
    intros. apply solved_characterization; left; cbn.
    exists value. apply ML.lookup_update_same.
  Qed.

  Lemma remember_dormant_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.remember_dormant st target) x.
  Proof.
    intros st target x H. apply solved_characterization in H.
    apply solved_characterization; cbn. destruct H as [H|H]; [now left|].
    right. apply SL.add_spec. now right.
  Qed.
  #[local] Hint Resolve remember_dormant_solved : solved.

  Lemma remember_dormant_solves : forall st target,
    Sem.solved (R.remember_dormant st target) target.
  Proof.
    intros. apply solved_characterization; right; cbn.
    apply SL.add_spec. now left.
  Qed.

  Lemma with_spawns_solved : forall st pending requested x,
    Sem.solved st x -> Sem.solved (R.with_spawns st pending requested) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_spawns_solved : solved.

  Lemma with_ranking_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_ranking st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_ranking_solved : solved.

  Lemma with_queue_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_queue st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_queue_solved : solved.

  Lemma with_started_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_started st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_started_solved : solved.

  Lemma with_readers_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_readers st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_readers_solved : solved.

  Lemma with_contributions_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_contributions st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_contributions_solved : solved.

  Lemma with_phases_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_phases st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_phases_solved : solved.

  Lemma with_side_phases_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_side_phases st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_side_phases_solved : solved.

  Lemma with_local_sides_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_local_sides st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_local_sides_solved : solved.

  Lemma with_controlled_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_controlled st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_controlled_solved : solved.

  Lemma with_dirty_side_targets_solved : forall st next x,
    Sem.solved st x -> Sem.solved (R.with_dirty_side_targets st next) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve with_dirty_side_targets_solved : solved.

  Lemma add_reader_solved : forall st target owner x,
    Sem.solved st x -> Sem.solved (R.add_reader st target owner) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve add_reader_solved : solved.

  Lemma enqueue_handle_solved : forall st entry x,
    Sem.solved st x -> Sem.solved (R.enqueue_handle st entry) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve enqueue_handle_solved : solved.

  Lemma mark_side_dirty_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.mark_side_dirty st target) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve mark_side_dirty_solved : solved.

  Lemma clear_side_dirty_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.clear_side_dirty st target) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve clear_side_dirty_solved : solved.

  Lemma cancel_dirty_target_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.cancel_dirty_target st target) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve cancel_dirty_target_solved : solved.

  Lemma promote_controlled_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.promote_controlled st target) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve promote_controlled_solved : solved.

  Lemma reset_local_sides_solved : forall st owner x,
    Sem.solved st x -> Sem.solved (R.reset_local_sides st owner) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve reset_local_sides_solved : solved.

  Lemma record_side_payload_solved : forall st source target raw x,
    Sem.solved st x -> Sem.solved (R.record_side_payload st source target raw) x.
  Proof. intros; assumption. Qed.
  #[local] Hint Resolve record_side_payload_solved : solved.

  Lemma materialize_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.materialize st target) x.
  Proof.
    intros. unfold R.materialize, R.is_materialized.
    destruct (M.lookup (R.sigma st) target); eauto with solved.
  Qed.
  #[local] Hint Resolve materialize_solved : solved.

  Lemma materialize_solves : forall st target,
    Sem.solved (R.materialize st target) target.
  Proof.
    intros. unfold R.materialize, R.is_materialized.
    destruct (M.lookup (R.sigma st) target) eqn:H.
    - apply solved_characterization; left; eauto.
    - apply update_sigma_solves.
  Qed.

  Lemma observe_solved : forall st target x,
    Sem.solved st x -> Sem.solved (fst (R.observe st target)) x.
  Proof.
    intros. unfold R.observe.
    destruct (R.Ranking.observe (R.ranking st) target); cbn; eauto with solved.
  Qed.
  #[local] Hint Resolve observe_solved : solved.

  Lemma request_spawn_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.request_spawn st target) x.
  Proof.
    intros. unfold R.request_spawn.
    destruct (S.mem target (R.requested_spawns st)); eauto with solved.
  Qed.
  #[local] Hint Resolve request_spawn_solved : solved.

  #[local] Hint Resolve materialize_solved request_spawn_solved : solved.

  Lemma observe_solved_result : forall st target next entry x,
    R.observe st target = (next, entry) -> Sem.solved st x -> Sem.solved next x.
  Proof.
    intros st target next entry x Hobs H. pose proof (@observe_solved st target x H) as Hkeep.
    now rewrite Hobs in Hkeep.
  Qed.

  Lemma enqueue_solved : forall st target x,
    Sem.solved st x -> Sem.solved (R.enqueue st target) x.
  Proof.
    intros st target x H. unfold R.enqueue. destruct (R.observe st target) eqn:Hobs.
    apply enqueue_handle_solved. eapply observe_solved_result; eauto.
  Qed.
  #[local] Hint Resolve enqueue_solved : solved.

  Lemma enqueue_all_solved : forall xs st x,
    Sem.solved st x -> Sem.solved (R.enqueue_all st xs) x.
  Proof. induction xs; intros; cbn; eauto with solved. Qed.
  #[local] Hint Resolve enqueue_all_solved : solved.

  Lemma write_changed_value_solved : forall st owner value x,
    Sem.solved st x -> Sem.solved (R.write_changed_value st owner value) x.
  Proof. intros. unfold R.write_changed_value. eauto with solved. Qed.
  #[local] Hint Resolve write_changed_value_solved : solved.

  Lemma start_evaluation_solved : forall st owner x,
    Sem.solved st x -> Sem.solved (R.start_evaluation st owner) x.
  Proof. intros. unfold R.start_evaluation. eauto with solved. Qed.
  #[local] Hint Resolve start_evaluation_solved : solved.

  Lemma start_evaluation_solves : forall st owner,
    Sem.solved (R.start_evaluation st owner) owner.
  Proof. intros. unfold R.start_evaluation. apply materialize_solves. Qed.

  Lemma get_control_state_solved : forall st owner target x,
    Sem.solved st x -> Sem.solved (R.get_control_state st owner target) x.
  Proof. intros. unfold R.get_control_state. destruct (Nat.ltb _ _); eauto with solved. Qed.
  #[local] Hint Resolve get_control_state_solved : solved.

  Lemma get_ready_state_solved : forall st owner target x,
    Sem.solved st x -> Sem.solved (R.get_ready_state st owner target) x.
  Proof. intros. unfold R.get_ready_state. destruct (Nat.ltb _ _); eauto with solved. Qed.
  #[local] Hint Resolve get_ready_state_solved : solved.

  Lemma side_ready_state_solved : forall st owner target raw x,
    Sem.solved st x -> Sem.solved (R.side_ready_state st owner target raw) x.
  Proof. intros. unfold R.side_ready_state. destruct (Nat.ltb _ _); eauto with solved. Qed.
  #[local] Hint Resolve side_ready_state_solved : solved.

  Lemma set_value_solved : forall st owner direct x,
    Sem.solved st x -> Sem.solved (R.set_value st owner direct) x.
  Proof.
    intros st owner direct x H. unfold R.set_value.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      eauto with solved.
  Qed.
  #[local] Hint Resolve set_value_solved : solved.

  Lemma try_dirty_read_solved : forall tf st owner target next x,
    R.try_dirty_read tf st owner target = Some next ->
    Sem.solved st x -> Sem.solved next x.
  Proof.
    intros tf st owner target next x H Hsolved. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?b with _ => _ end] => destruct b eqn:?
    end; try discriminate; inversion H; subst; eauto 8 with solved.
  Qed.

  Lemma dirty_get_ready_state_solved : forall tf st owner target x,
    Sem.solved st x -> Sem.solved (R.dirty_get_ready_state tf st owner target) x.
  Proof.
    intros tf st owner target x H. unfold R.dirty_get_ready_state.
    destruct (R.try_dirty_read _ _ _ _) eqn:Htry; apply add_reader_solved;
      [eapply try_dirty_read_solved; [exact Htry|]|]; eauto with solved.
  Qed.
  #[local] Hint Resolve dirty_get_ready_state_solved : solved.

  Lemma next_config_solved : forall tf before after x,
    R.next_config tf before = Some after ->
    Sem.solved (R.cfg_state before) x -> Sem.solved (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x H Hsolved.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control] in H, Hsolved |- *;
      repeat match type of H with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion H; subst; cbn [R.cfg_state].
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      pose proof (@observe_solved_result base target next entry x Hobs Hsolved)
    end.
    all: eauto 8 with solved.
  Qed.

  Definition started_safe (st : R.state) : Prop :=
    forall x, S.mem x (R.started st) = true -> Sem.solved st x.

  Lemma started_safe_transport : forall before after,
    (forall x, Sem.solved before x -> Sem.solved after x) ->
    R.started after = R.started before -> started_safe before -> started_safe after.
  Proof. intros before after Hkeep Heq Hsafe x Hmem. apply Hkeep, Hsafe. now rewrite <- Heq. Qed.

  Create HintDb started_safe.
  Lemma with_spawns_started_safe : forall st pending requested,
    started_safe st -> started_safe (R.with_spawns st pending requested).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_spawns_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_spawns_started_safe : started_safe.

  Lemma with_ranking_started_safe : forall st next,
    started_safe st -> started_safe (R.with_ranking st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_ranking_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_ranking_started_safe : started_safe.

  Lemma with_queue_started_safe : forall st next,
    started_safe st -> started_safe (R.with_queue st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_queue_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_queue_started_safe : started_safe.

  Lemma with_readers_started_safe : forall st next,
    started_safe st -> started_safe (R.with_readers st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_readers_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_readers_started_safe : started_safe.

  Lemma with_contributions_started_safe : forall st next,
    started_safe st -> started_safe (R.with_contributions st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_contributions_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_contributions_started_safe : started_safe.

  Lemma with_phases_started_safe : forall st next,
    started_safe st -> started_safe (R.with_phases st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_phases_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_phases_started_safe : started_safe.

  Lemma with_side_phases_started_safe : forall st next,
    started_safe st -> started_safe (R.with_side_phases st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_side_phases_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_side_phases_started_safe : started_safe.

  Lemma with_local_sides_started_safe : forall st next,
    started_safe st -> started_safe (R.with_local_sides st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_local_sides_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_local_sides_started_safe : started_safe.

  Lemma with_controlled_started_safe : forall st next,
    started_safe st -> started_safe (R.with_controlled st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_controlled_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_controlled_started_safe : started_safe.

  Lemma with_dirty_side_targets_started_safe : forall st next,
    started_safe st -> started_safe (R.with_dirty_side_targets st next).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply with_dirty_side_targets_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve with_dirty_side_targets_started_safe : started_safe.

  Lemma add_reader_started_safe : forall st target owner,
    started_safe st -> started_safe (R.add_reader st target owner).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply add_reader_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve add_reader_started_safe : started_safe.

  Lemma enqueue_handle_started_safe : forall st entry,
    started_safe st -> started_safe (R.enqueue_handle st entry).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply enqueue_handle_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve enqueue_handle_started_safe : started_safe.

  Lemma mark_side_dirty_started_safe : forall st target,
    started_safe st -> started_safe (R.mark_side_dirty st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply mark_side_dirty_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve mark_side_dirty_started_safe : started_safe.

  Lemma clear_side_dirty_started_safe : forall st target,
    started_safe st -> started_safe (R.clear_side_dirty st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply clear_side_dirty_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve clear_side_dirty_started_safe : started_safe.

  Lemma cancel_dirty_target_started_safe : forall st target,
    started_safe st -> started_safe (R.cancel_dirty_target st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply cancel_dirty_target_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve cancel_dirty_target_started_safe : started_safe.

  Lemma promote_controlled_started_safe : forall st target,
    started_safe st -> started_safe (R.promote_controlled st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply promote_controlled_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve promote_controlled_started_safe : started_safe.

  Lemma reset_local_sides_started_safe : forall st owner,
    started_safe st -> started_safe (R.reset_local_sides st owner).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply reset_local_sides_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve reset_local_sides_started_safe : started_safe.

  Lemma record_side_payload_started_safe : forall st source target raw,
    started_safe st -> started_safe (R.record_side_payload st source target raw).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply record_side_payload_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve record_side_payload_started_safe : started_safe.

  Lemma remember_dormant_started_safe : forall st target,
    started_safe st -> started_safe (R.remember_dormant st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply remember_dormant_solved; assumption| |assumption].
    reflexivity.
  Qed.
  #[local] Hint Resolve remember_dormant_started_safe : started_safe.

  Lemma materialize_started_safe : forall st target,
    started_safe st -> started_safe (R.materialize st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply materialize_solved; assumption| |assumption].
    unfold R.materialize. destruct (R.is_materialized st target); reflexivity.
  Qed.
  #[local] Hint Resolve materialize_started_safe : started_safe.

  Lemma request_spawn_started_safe : forall st target,
    started_safe st -> started_safe (R.request_spawn st target).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply request_spawn_solved; assumption| |assumption].
    unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); reflexivity.
  Qed.
  #[local] Hint Resolve request_spawn_started_safe : started_safe.

  Lemma start_evaluation_started_safe : forall st owner,
    started_safe st -> started_safe (R.start_evaluation st owner).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply start_evaluation_solved; assumption| |assumption].
    unfold R.start_evaluation, R.reset_local_sides, R.clear_side_dirty; cbn. unfold R.materialize. destruct (R.is_materialized st owner); reflexivity.
  Qed.
  #[local] Hint Resolve start_evaluation_started_safe : started_safe.

  Lemma update_sigma_started_safe : forall st target value,
    started_safe st -> started_safe (R.with_sigma st (M.update (R.sigma st) target value)).
  Proof.
    intros. eapply started_safe_transport with (before := st); [intros; apply update_sigma_solved; assumption|reflexivity|assumption].
  Qed.
  #[local] Hint Resolve update_sigma_started_safe : started_safe.

  Lemma mark_started_safe : forall st target,
    started_safe st -> Sem.solved st target ->
    started_safe (R.with_started st (S.add target (R.started st))).
  Proof.
    intros st target Hsafe Hsolved x Hmem. cbn in Hmem.
    apply SL.add_spec in Hmem as [->|Hmem]; [exact Hsolved|now apply Hsafe].
  Qed.
  #[local] Hint Resolve mark_started_safe : started_safe.

  Lemma observe_started_safe : forall st target next entry,
    R.observe st target = (next, entry) -> started_safe st -> started_safe next.
  Proof.
    intros st target next entry H Hsafe. unfold R.observe in H.
    destruct (R.Ranking.observe _ _); inversion H; subst. now apply with_ranking_started_safe.
  Qed.

  Lemma enqueue_started_safe : forall st target,
    started_safe st -> started_safe (R.enqueue st target).
  Proof.
    intros st target Hsafe. unfold R.enqueue. destruct (R.observe st target) eqn:Hobs.
    apply enqueue_handle_started_safe. eapply observe_started_safe; eauto.
  Qed.
  #[local] Hint Resolve enqueue_started_safe : started_safe.

  Lemma enqueue_all_started_safe : forall xs st,
    started_safe st -> started_safe (R.enqueue_all st xs).
  Proof. induction xs; intros; cbn; eauto with started_safe. Qed.
  #[local] Hint Resolve enqueue_all_started_safe : started_safe.

  Lemma write_changed_value_started_safe : forall st owner value,
    started_safe st -> started_safe (R.write_changed_value st owner value).
  Proof. intros. unfold R.write_changed_value. eauto with started_safe. Qed.
  #[local] Hint Resolve write_changed_value_started_safe : started_safe.
  Lemma get_control_state_started_safe : forall st owner target,
    started_safe st -> started_safe (R.get_control_state st owner target).
  Proof.
    intros. unfold R.get_control_state.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      eauto with started_safe.
  Qed.
  #[local] Hint Resolve get_control_state_started_safe : started_safe.
  Lemma get_ready_state_started_safe : forall st owner target,
    started_safe st -> started_safe (R.get_ready_state st owner target).
  Proof.
    intros. unfold R.get_ready_state.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      eauto with started_safe.
  Qed.
  #[local] Hint Resolve get_ready_state_started_safe : started_safe.
  Lemma side_ready_state_started_safe : forall st owner target raw,
    started_safe st -> started_safe (R.side_ready_state st owner target raw).
  Proof.
    intros. unfold R.side_ready_state.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      eauto with started_safe.
  Qed.
  #[local] Hint Resolve side_ready_state_started_safe : started_safe.
  Lemma set_value_started_safe : forall st owner direct,
    started_safe st -> started_safe (R.set_value st owner direct).
  Proof.
    intros. unfold R.set_value.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      eauto with started_safe.
  Qed.
  #[local] Hint Resolve set_value_started_safe : started_safe.

  Lemma try_dirty_read_started_safe : forall tf st owner target next,
    R.try_dirty_read tf st owner target = Some next ->
    started_safe st -> Sem.solved st (R.handle_variable target) -> started_safe next.
  Proof.
    intros tf st owner target next H Hsafe Hsolved. unfold R.try_dirty_read in H.
    repeat match type of H with
    | context [match ?b with _ => _ end] => destruct b eqn:?
    end; try discriminate; inversion H; subst; eauto 8 with started_safe solved.
  Qed.

  Lemma dirty_get_ready_state_started_safe : forall tf st owner target,
    started_safe st -> started_safe (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target H. unfold R.dirty_get_ready_state.
    destruct (R.try_dirty_read _ _ _ _) eqn:Htry; apply add_reader_started_safe.
    - eapply try_dirty_read_started_safe; [exact Htry|eauto with started_safe|apply materialize_solves].
    - eauto with started_safe.
  Qed.
  #[local] Hint Resolve dirty_get_ready_state_started_safe : started_safe.

  Lemma next_config_started_safe : forall tf before after,
    R.next_config tf before = Some after ->
    started_safe (R.cfg_state before) -> started_safe (R.cfg_state after).
  Proof.
    intros tf [st control] after H Hsafe.
    destruct control; cbn [R.next_config R.cfg_state R.cfg_control] in H, Hsafe |- *;
      repeat match type of H with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion H; subst; cbn [R.cfg_state].
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      pose proof (@observe_started_safe base target next entry Hobs Hsafe)
    end.
    all: eauto 8 using start_evaluation_solves with started_safe solved.
    exact (@mark_started_safe (R.start_evaluation st (R.handle_variable h)) (R.handle_variable h)
      (start_evaluation_started_safe (R.handle_variable h) Hsafe)
      (start_evaluation_solves st (R.handle_variable h))).
  Qed.

  Lemma run_fuel_started_safe : forall fuel tf start,
    started_safe (R.cfg_state start) -> started_safe (R.cfg_state (R.run_fuel fuel tf start)).
  Proof.
    induction fuel as [|fuel IH]; intros tf start Hsafe; cbn; [exact Hsafe|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|exact Hsafe].
    apply IH. eapply next_config_started_safe; eauto.
  Qed.

  Lemma initial_started_safe : forall roots, started_safe (R.cfg_state (R.initial_config roots)).
  Proof. intros roots x Hmem. cbn in Hmem. rewrite SL.empty_spec in Hmem. discriminate. Qed.

  Fixpoint continuation_seeds (k : R.continuation) : list V.t :=
    match k with
    | R.KLoop => []
    | R.KSeedLoop roots => roots
    | R.KAfterGet _ _ _ next | R.KAfterSide _ _ next
    | R.KAfterSpawn _ _ next | R.KSolveOneLoop _ next => continuation_seeds next
    end.

  Definition waiting (control : R.control) : list V.t :=
    match control with
    | R.RunLoop => []
    | R.RunSeeds roots | R.RunSeedLoop roots => roots
    | R.RunSolveOne owner k => R.handle_variable owner :: continuation_seeds k
    | R.RunRhs _ _ k | R.RunSolveOneLoop _ k | R.AfterGet _ _ _ k
    | R.AfterSide _ _ k | R.AfterSpawn _ _ k => continuation_seeds k
    end.

  Lemma continue_waiting : forall k, waiting (R.continue k) = continuation_seeds k.
  Proof. destruct k; reflexivity. Qed.

  Definition accounted (c : R.config) (target : V.t) : Prop :=
    Sem.solved (R.cfg_state c) target \/
    In target (R.pending_spawns (R.cfg_state c)) \/
    In target (waiting (R.cfg_control c)).

  Lemma dormant_solved : forall st x,
    R.is_dormant st x = true -> Sem.solved st x.
  Proof.
    intros st x H. unfold R.is_dormant in H.
    apply Bool.andb_true_iff in H as [H _].
    apply solved_characterization; now right.
  Qed.

  Lemma observe_variable : forall st target next entry,
    R.observe st target = (next, entry) -> R.handle_variable entry = target.
  Proof.
    intros st target next entry H. unfold R.observe in H.
    destruct (R.Ranking.observe _ _); inversion H; reflexivity.
  Qed.

  Lemma next_config_waiting_accounted : forall tf before after x,
    R.next_config tf before = Some after -> started_safe (R.cfg_state before) ->
    In x (waiting (R.cfg_control before)) -> accounted after x.
  Proof.
    intros tf [st control] after x H Hsafe Hwaiting.
    destruct control;
      cbn [R.next_config R.cfg_state R.cfg_control waiting] in H, Hsafe, Hwaiting;
      try contradiction;
      repeat match type of H with
      | context [match ?b with _ => _ end] => destruct b eqn:?
      end; try discriminate; inversion H; subst; unfold accounted;
      cbn [R.cfg_state R.cfg_control waiting continuation_seeds] in *;
      try rewrite continue_waiting; try tauto.
    all: try match goal with
    | Hobs : R.observe ?base ?target = (?next, ?entry) |- _ =>
      let Hv := fresh "Hvariable" in
      pose proof (@observe_variable base target next entry Hobs) as Hv;
      cbn [In] in *; rewrite Hv; try tauto
    end.
    all: cbn [In] in *; try tauto.
    - destruct Hwaiting as [<-|Hin]; [left|tauto].
      apply Bool.orb_true_iff in Heqb as [Hs|Hd];
        [now apply Hsafe|now apply dormant_solved].
    - destruct Hwaiting as [<-|Hin]; [left; apply remember_dormant_solves|tauto].
    - destruct Hwaiting as [<-|Hin]; [left; apply with_started_solved, start_evaluation_solves|tauto].
  Qed.
  Lemma next_config_pending_accounted : forall tf before after x,
    R.next_config tf before = Some after ->
    In x (R.pending_spawns (R.cfg_state before)) -> accounted after x.
  Proof.
    intros tf before after x H Hin. apply next_config_spawn_cases in H.
    destruct H as [H|[[target H]|[target [rest [Hp [Hs Hc]]]]]].
    - unfold snapshot in H. injection H as Hp Hr.
      right; left. now rewrite Hp.
    - unfold R.request_spawn in H.
      destruct (S.mem target (R.requested_spawns (R.cfg_state before)));
        unfold snapshot in H; cbn in H; injection H as Hp Hr;
        right; left; rewrite Hp; [exact Hin|apply in_or_app; now left].
    - unfold snapshot in Hs. injection Hs as Hpending Hrequested.
      rewrite Hp in Hin. destruct Hin as [<-|Hin].
      + right; right. rewrite Hc. cbn. auto.
      + right; left. now rewrite Hpending.
  Qed.

  Lemma next_config_accounted : forall tf before after x,
    R.next_config tf before = Some after -> started_safe (R.cfg_state before) ->
    accounted before x -> accounted after x.
  Proof.
    intros tf before after x H Hsafe [Hsolved|[Hpending|Hwaiting]].
    - left. eapply next_config_solved; eauto.
    - eapply next_config_pending_accounted; eauto.
    - eapply next_config_waiting_accounted; eauto.
  Qed.

  Lemma run_fuel_accounted : forall fuel tf start x,
    started_safe (R.cfg_state start) ->
    accounted start x -> accounted (R.run_fuel fuel tf start) x.
  Proof.
    induction fuel as [|fuel IH]; intros tf start x Hsafe H; cbn; [exact H|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|exact H].
    apply IH; [eapply next_config_started_safe; eauto|].
    eapply next_config_accounted; eauto.
  Qed.

  Lemma next_config_request_origin : forall tf before after x,
    R.next_config tf before = Some after ->
    S.mem x (R.requested_spawns (R.cfg_state after)) = true ->
    S.mem x (R.requested_spawns (R.cfg_state before)) = true \/
    In x (R.pending_spawns (R.cfg_state after)).
  Proof.
    intros tf before after x H Hmem. apply next_config_spawn_cases in H.
    destruct H as [Hsame|[[target Hrequest]|[target [rest [Hpop [Hsame Hcontrol]]]]]].
    - unfold snapshot in Hsame. injection Hsame as Hp Hr.
      rewrite Hr in Hmem. now left.
    - unfold R.request_spawn in Hrequest.
      destruct (S.mem target (R.requested_spawns (R.cfg_state before))) eqn:Hseen.
      + unfold snapshot in Hrequest. injection Hrequest as Hp Hr.
        rewrite Hr in Hmem. now left.
      + unfold snapshot in Hrequest; cbn in Hrequest.
        injection Hrequest as Hp Hr. rewrite Hr in Hmem.
        apply SL.add_spec in Hmem as [->|Hmem]; [right|now left].
        rewrite Hp. apply in_or_app; right; cbn; auto.
    - unfold snapshot in Hsame. injection Hsame as Hp Hr.
      rewrite Hr in Hmem. now left.
  Qed.

  Definition requests_accounted (c : R.config) : Prop :=
    forall x, S.mem x (R.requested_spawns (R.cfg_state c)) = true -> accounted c x.

  Lemma next_config_requests_accounted : forall tf before after,
    R.next_config tf before = Some after ->
    started_safe (R.cfg_state before) ->
    requests_accounted before -> requests_accounted after.
  Proof.
    intros tf before after H Hsafe Hinv x Hmem.
    destruct (@next_config_request_origin tf before after x H Hmem) as [Hold|Hnew].
    - eapply next_config_accounted; [exact H|exact Hsafe|now apply Hinv].
    - right; now left.
  Qed.

  Lemma run_fuel_requests_accounted : forall fuel tf start,
    started_safe (R.cfg_state start) ->
    requests_accounted start -> requests_accounted (R.run_fuel fuel tf start).
  Proof.
    induction fuel as [|fuel IH]; intros tf start Hsafe H; cbn; [exact H|].
    destruct (R.next_config tf start) as [next|] eqn:Hnext; [|exact H].
    apply IH; [eapply next_config_started_safe; eauto|].
    eapply next_config_requests_accounted; eauto.
  Qed.

  Lemma initial_requests_accounted : forall roots,
    requests_accounted (R.initial_config roots).
  Proof.
    intros roots x H. cbn in H. rewrite SL.empty_spec in H. discriminate.
  Qed.

  Lemma terminal_accounted_solved : forall final x,
    Sem.quiescent final -> accounted (Sem.terminal_config final) x ->
    Sem.solved final x.
  Proof.
    intros final x [_ Hpending] [Hsolved|[Hpendingx|Hwaiting]]; [exact Hsolved| |].
    - cbn in Hpendingx. rewrite Hpending in Hpendingx. contradiction.
    - contradiction.
  Qed.

  Theorem successful_run_requests_solved : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final ->
    forall target, S.mem target (R.requested_spawns final) = true ->
      Sem.solved final target.
  Proof.
    intros fuel tf roots final H target Hmem. unfold R.solve_fuel in H.
    apply terminal_state_shape in H as [Hshape Hquiet].
    pose proof (@run_fuel_requests_accounted fuel tf (R.initial_config roots)
      (@initial_started_safe roots) (@initial_requests_accounted roots)) as Hinv.
    rewrite Hshape in Hinv.
    eapply terminal_accounted_solved; [exact Hquiet|now apply Hinv].
  Qed.

  Theorem successful_run_roots_solved : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final ->
    forall root, In root roots -> Sem.solved final root.
  Proof.
    intros fuel tf roots final H root Hin. unfold R.solve_fuel in H.
    apply terminal_state_shape in H as [Hshape Hquiet].
    assert (accounted (R.initial_config roots) root) as Hroot by (right; right; exact Hin).
    pose proof (@run_fuel_accounted fuel tf (R.initial_config roots) root (@initial_started_safe roots) Hroot) as Hfinal.
    rewrite Hshape in Hfinal. eapply terminal_accounted_solved; eauto.
  Qed.

End Make.
