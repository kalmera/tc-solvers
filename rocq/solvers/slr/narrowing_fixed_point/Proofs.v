From Stdlib Require Import List Bool Lia Arith.PeanoNat Arith.Wf_nat Sorting.Sorted.
From TcSolvers Require Import common.Assumptions common.SolverSpecifications
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.narrowing_fixed_point.Foundation
  solvers.slr.narrowing_fixed_point.NarrowingFixedPoint.
Import ListNotations.
Set Implicit Arguments.

(** Termination, correctness, and leastness of the narrowing-fixpoint
    machine, using one instance of the core foundation. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
Module Ranks := ListDiscoveryOrder V.
Module RL := ListDiscoveryOrderLaws V.
Module RF := ListFiniteDiscoveryOrderLaws V.
Module B := Foundation.Make V D U S M Ranks Features RL RF DL UL SL ML.
Module N := NarrowingFixedPoint.WithCore V D U S M Ranks Features B.R.
Module R := B.R.
Module Sem := B.Sem.
Module Spec := B.Spec.
Include Spec.

Definition step tf before after := N.next_config tf before = Some after.
Definition steps := N.steps.
Definition steps_refl := N.steps_refl.
Definition steps_cons := N.steps_next.
Definition reachable tf roots c := steps tf (R.initial_config roots) c.
Definition terminates_to tf roots final :=
  reachable tf roots (B.terminal final) /\ B.quiescent final.

Lemma steps_append tf a b c : steps tf a b -> steps tf b c -> steps tf a c.
Proof.
  intros H1 H2; induction H1 as [first|first next last Hnext Htail IH].
  - exact H2.
  - eapply steps_cons; [exact Hnext |exact (IH H2)].
Qed.
Lemma steps_snoc tf a b c : steps tf a b -> step tf b c -> steps tf a c.
Proof. intros Hpath Hstep; eapply steps_append; [exact Hpath |eapply steps_cons; [exact Hstep |constructor]]. Qed.
Lemma fuel_path fuel tf c : steps tf c (N.run_fuel fuel tf c).
Proof.
  exact (N.fuel_steps fuel tf c).
Qed.
Lemma path_fuel tf a b : steps tf a b -> exists fuel, N.run_fuel fuel tf a = b.
Proof.
  intro H; induction H as [a|a next b Hnext Htail [fuel Hfuel]].
  - exists 0; reflexivity.
  - exists (S fuel); cbn; unfold step in Hnext; now rewrite Hnext.
Qed.
Lemma final_shape fuel tf roots final : N.solve_fuel fuel tf roots = Some final ->
  N.run_fuel fuel tf (R.initial_config roots) = B.terminal final /\ B.quiescent final.
Proof.
  unfold N.solve_fuel, R.terminal_state.
  destruct (N.run_fuel fuel tf (R.initial_config roots)) as [st ctrl].
  destruct ctrl; cbn; try discriminate.
  destruct (R.queue st) eqn:Hq; cbn; try discriminate.
  intro H; inversion H; subst; split; [reflexivity |exact Hq].
Qed.
Lemma successful_path fuel tf roots final : N.solve_fuel fuel tf roots = Some final ->
  terminates_to tf roots final.
Proof.
  intro H; destruct (@final_shape fuel tf roots final H) as [Heq Hq]; split; auto.
  rewrite <- Heq; apply fuel_path.
Qed.

Lemma pending_spec st owner target rest : N.pending_above st owner = Some (target,rest) ->
  S.mem owner (R.controlled st) = true /\ R.queue_pop (R.queue st) = Some (target,rest) /\
  R.rank_lt st owner target = true.
Proof.
  unfold N.pending_above; destruct (S.mem owner (R.controlled st)) eqn:Hc; try discriminate.
  destruct (R.queue_pop (R.queue st)) as [[head tail]|] eqn:Hp; try discriminate.
  destruct (R.rank_lt st owner head) eqn:Hr; try discriminate.
  intro H; inversion H; subst; auto.
Qed.

Arguments pending_spec {st owner target rest} _.

(** One transition view avoids repeating the dispatch tree in each invariant. *)
Definition core_rule ctrl :=
  match ctrl with
  | R.StartEpisode _ _ | R.RunRhs _ (R.ConstraintSystem.Side _ _ _) _
  | R.RunDead _ _ [] _ | R.Return (R.KAfterSide _ _ _) => False
  | R.RunDead fr _ (target::_) _ => S.mem target (R.frame_current_targets fr) = true
  | _ => True
  end.
Inductive transition tf : R.config -> R.config -> Prop :=
| CoreStep before after : B.step tf before after -> core_rule (R.cfg_control before) -> transition tf before after
| StartFresh st owner k : transition tf (B.configuration st (R.StartEpisode owner k))
    (B.configuration (R.materialize (N.clear_owner st owner) owner)
      (R.RunRhs (R.fresh_frame (R.materialize (N.clear_owner st owner) owner)
        owner (U.initial_phase false owner)) (tf owner) k))
| DeferredSide st fr target raw body k : transition tf
    (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Side target raw body) k))
    (B.configuration (R.observe st target)
      (R.RunRhs (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) body k))
| PublishSides st fr direct k : transition tf (B.configuration st (R.RunDead fr direct [] k))
    (B.configuration (R.publish_targets (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr)
      (R.RunCommit fr direct k))
| RemoveSide st fr direct target rest k next changed :
    R.write_side_contribution st fr target D.bottom = (next,changed) ->
    transition tf (B.configuration st (R.RunDead fr direct (target::rest) k))
      (R.continue_dead (N.requeue_source st next (R.frame_owner fr) target)
        fr direct target rest k changed)
| CommitHigher st fr direct k target rest :
    N.pending_above st (R.frame_owner fr) = Some (target,rest) ->
    transition tf (B.configuration st (R.RunCommit fr direct k))
      (N.suspend_commit tf st fr k target rest)
| CommitRetry st fr direct k : transition tf (B.configuration st (R.RunCommit fr direct k))
    (N.retry_current tf st fr k)
| ResumeHigher st fr body k target rest :
    N.pending_above st (R.frame_owner fr) = Some (target,rest) ->
    transition tf (B.configuration st (R.Return (R.KAfterSide fr body k)))
      (N.suspend_commit tf st fr k target rest)
| ResumeFresh st fr body k : transition tf
    (B.configuration st (R.Return (R.KAfterSide fr body k)))
    (B.configuration (N.clear_owner st (R.frame_owner fr)) (R.RunRhs fr body k)).

Lemma step_view tf before after : step tf before after -> transition tf before after.
Proof.
  destruct before as [st ctrl]; intro H.
  destruct ctrl as [|roots|roots|owner k|fr body k|fr direct pending k|fr direct k|fr k|k].
  all: unfold step, N.next_config, N.next_repaired, N.next_fresh, N.next_batched,
    N.next_precommit in H; cbn -[R.next_config N.pending_above N.publish N.retry_current
      N.clear_owner N.suspend_commit R.record_side_input R.write_side_contribution] in H.
  all: try solve [apply CoreStep; [exact H |exact I]].
  - cbn [R.next_config] in H. inversion H; subst; apply StartFresh.
  - destruct body; cbn -[R.next_config R.record_side_input R.observe] in H;
      try solve [apply CoreStep; [exact H |exact I]].
    unfold R.record_side_input in H; inversion H; subst; apply DeferredSide.
  - destruct pending as [|target rest].
    + inversion H; subst; apply PublishSides.
    + destruct (S.mem target (R.frame_current_targets fr)) eqn:Hmem.
      * apply CoreStep; [unfold B.step, R.next_config; cbn; now rewrite Hmem |exact Hmem].
      * destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
        inversion H; subst; eapply RemoveSide; exact Hw.
  - destruct (N.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp.
    + inversion H; subst; apply CommitHigher; exact Hp.
    + destruct (R.queue_contains (R.frame_owner fr) (R.queue st)).
      * inversion H; subst; apply CommitRetry.
      * apply CoreStep; [exact H |exact I].
  - destruct k; cbn -[R.next_config N.pending_above N.suspend_commit N.clear_owner] in H;
      try solve [apply CoreStep; [exact H |exact I]].
    destruct (N.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
    + inversion H; subst; apply ResumeHigher; exact Hp.
    + cbn [R.next_config] in H; inversion H; subst; apply ResumeFresh.
Qed.

Lemma clear_members st owner x : In x (R.queue (N.clear_owner st owner)) <->
  In x (R.queue st) /\ x <> owner.
Proof.
  unfold N.clear_owner; cbn; rewrite filter_In.
  destruct (V.eq_dec x owner); split; intros [H1 H2];
    try discriminate; try contradiction; auto.
Qed.
Lemma clear_not_queued st owner : ~ In owner (R.queue (N.clear_owner st owner)).
Proof. intro H; apply clear_members in H; tauto. Qed.
Lemma sorted_filter (A : Type) (order : A -> A -> Prop) (test : A -> bool) xs :
  StronglySorted order xs -> StronglySorted order (filter test xs).
Proof.
  intro H; induction H; cbn; [constructor |].
  destruct (test a); auto; constructor; auto.
  apply Forall_forall; intros x Hx; apply filter_In in Hx.
  eapply Forall_forall; [exact H0 |exact (proj1 Hx)].
Qed.
Lemma clear_store support st owner : B.store_wf support st -> B.store_wf support (N.clear_owner st owner).
Proof.
  intro H; apply B.store_queue; auto.
  - apply Forall_forall; intros x Hx; apply filter_In in Hx.
    eapply Forall_forall; [exact (B.refs_queue (B.store_references H)) |exact (proj1 Hx)].
  - unfold N.clear_owner; apply sorted_filter; exact (B.store_ordered H).
  - unfold N.clear_owner; apply NoDup_filter; exact (B.store_distinct H).
Qed.
Lemma clear_config support st ctrl owner : B.config_wf support (B.configuration st ctrl) ->
  B.config_wf support (B.configuration (N.clear_owner st owner) ctrl).
Proof. intros [Hs Hc]; split; [apply clear_store; exact Hs |exact Hc]. Qed.

Lemma requeue_store support before after source target : B.store_wf support after ->
  B.known support after source -> B.store_wf support (N.requeue_source before after source target).
Proof. unfold N.requeue_source; destruct N.cell_changed; auto using B.store_enqueue. Qed.
Lemma requeue_rank before after source target :
  R.ranking (N.requeue_source before after source target) = R.ranking after.
Proof. unfold N.requeue_source; destruct N.cell_changed; reflexivity. Qed.
Lemma requeue_sigma before after source target :
  R.sigma (N.requeue_source before after source target) = R.sigma after.
Proof. unfold N.requeue_source; destruct N.cell_changed; reflexivity. Qed.
Lemma finish_rank before after fr target changed :
  R.ranking (N.finish_write before after fr target changed) = R.ranking after.
Proof. unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; reflexivity. Qed.
Lemma finish_store support before after fr target changed : B.store_wf support after ->
  B.known support after (R.frame_owner fr) -> B.known support after target ->
  B.store_wf support (N.finish_write before after fr target changed).
Proof.
  unfold N.finish_write; intros H Ho Ht; destruct changed;
    auto using requeue_store.
  apply B.store_enqueue; [apply requeue_store; auto |].
  unfold B.known; rewrite requeue_rank; exact Ht.
Qed.
Lemma publish_rank targets st fr : R.ranking (N.publish targets st fr) = R.ranking st.
Proof.
  revert st; induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution N.finish_write]; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  rewrite IH, finish_rank; eapply B.write_rank; exact Hw.
Qed.
Lemma publish_store support targets st fr : B.store_wf support st ->
  B.frame_refs (B.known support st) fr -> Forall (B.known support st) targets ->
  B.store_wf support (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hs Hfr Htargets; cbn -[R.write_side_contribution N.finish_write]; auto.
  inversion Htargets as [|? ? Ht Hr]; subst.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  assert (Hrank : R.ranking (N.finish_write st next fr target changed) = R.ranking st).
  { rewrite finish_rank; eapply B.write_rank; exact Hw. }
  apply IH.
  - apply finish_store; [eapply B.store_write; eauto | |]; unfold B.known;
      rewrite (B.write_rank Hw); [exact (B.ref_owner Hfr) |exact Ht].
  - eapply B.frame_rank_change; [exact Hrank |exact Hfr].
  - eapply Forall_impl; [|exact Hr]. intros x Hx; unfold B.known; rewrite Hrank; exact Hx.
Qed.

Lemma suspend_wf support tf st fr k target rest :
  (forall owner, support owner -> Sem.rhs_supported support (tf owner)) ->
  B.store_wf support st -> B.frame_refs (B.known support st) fr ->
  B.stack_refs (B.known support st) support k ->
  N.pending_above st (R.frame_owner fr) = Some (target,rest) ->
  B.config_wf support (N.suspend_commit tf st fr k target rest).
Proof.
  intros Htf Hs Hfr Hk Hp.
  destruct (pending_spec Hp) as [_ [Hpop _]].
  destruct (B.store_pop Hs Hpop) as [Hnext Htarget].
  split; [exact Hnext |].
  cbn [N.suspend_commit B.control_refs B.stack_refs R.fresh_frame R.frame_owner].
  split; [exact Htarget |]. split.
  - apply B.frame_fresh; [exact (B.store_references Hs) |exact (B.ref_owner Hfr)].
  - split; [apply Htf; exact (proj1 (B.ref_owner Hfr)) |exact Hk].
Qed.

Theorem next_configuration_wf support tf before after :
  (forall owner, support owner -> Sem.rhs_supported support (tf owner)) ->
  B.config_wf support before -> step tf before after -> B.config_wf support after.
Proof.
  intros Htf Hwf Hstep; apply step_view in Hstep.
  destruct Hstep as [before after Hcore Hguard|st owner k|st fr target raw body k|
    st fr direct k|st fr direct target rest k next changed Hw|
    st fr direct k target rest Hp|st fr direct k|st fr body k target rest Hp|st fr body k].
  - eapply B.next_configuration_wf; eauto.
  - eapply B.next_configuration_wf; [exact Htf |apply clear_config; exact Hwf |].
    unfold B.step, R.next_config; reflexivity.
  - destruct Hwf as [Hs [Hfr [Hcode Hk]]].
    destruct (B.code_child_supported Hcode) as [Ht Hbody].
    destruct (B.observed_context Hs Ht Hfr Hk) as [Hnext [Htarget [Hfr1 Hk1]]].
    split; [exact Hnext |]. cbn [B.control_refs B.configuration R.cfg_control R.cfg_state].
    split; [apply B.frame_side; auto |auto].
  - destruct Hwf as [Hs [Hfr [_ Hk]]].
    assert (Hpublish : B.store_wf support (N.publish (S.elements (R.frame_current_targets fr)) st fr)).
    { apply publish_store; auto. apply B.set_elements; exact (B.ref_current Hfr). }
    assert (Hrank : R.ranking (R.publish_targets (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr) = R.ranking st).
    { cbn; apply publish_rank. }
    split.
    + apply B.store_publish; [exact Hpublish |]. eapply B.frame_rank_change; [apply publish_rank |exact Hfr].
    + cbn [B.control_refs B.configuration R.cfg_control R.cfg_state]. split;
        [eapply B.frame_rank_change |eapply B.stack_rank_change]; eauto.
  - destruct Hwf as [Hs [Hfr [Hpending Hk]]].
    inversion Hpending as [|? ? Htarget Hrest]; subst.
    assert (Hrank : R.ranking (N.requeue_source st next (R.frame_owner fr) target) = R.ranking st).
    { rewrite requeue_rank; eapply B.write_rank; exact Hw. }
    eapply B.continuation_dead_wf.
    + apply requeue_store; [eapply B.store_write; eauto |]. unfold B.known; rewrite (B.write_rank Hw); exact (B.ref_owner Hfr).
    + eapply B.frame_rank_change; eauto.
    + unfold B.known; rewrite Hrank; exact Htarget.
    + eapply Forall_impl; [|exact Hrest]. intros x Hx; unfold B.known; rewrite Hrank; exact Hx.
    + eapply B.stack_rank_change; eauto.
  - destruct Hwf as [Hs [Hfr Hk]]; eapply suspend_wf; eauto.
  - destruct Hwf as [Hs [Hfr Hk]]. split; [apply clear_store; exact Hs |].
    cbn [N.retry_current B.control_refs B.configuration R.cfg_control R.cfg_state]. split.
    + apply B.frame_fresh; [apply B.references_queue; [exact (B.store_references Hs) |] |exact (B.ref_owner Hfr)].
      apply Forall_forall; intros x Hx; apply filter_In in Hx.
      eapply Forall_forall; [exact (B.refs_queue (B.store_references Hs)) |exact (proj1 Hx)].
    + split; [apply Htf; exact (proj1 (B.ref_owner Hfr)) |exact Hk].
  - destruct Hwf as [Hs [Hfr [_ Hk]]]; eapply suspend_wf; eauto.
  - eapply B.next_configuration_wf; [exact Htf |apply clear_config; exact Hwf |].
    unfold B.step, R.next_config; reflexivity.
Qed.

Theorem reachable_configuration_wf tf roots (finite : Sem.finite_system tf roots) c :
  reachable tf roots c -> B.config_wf (fun x => In x (@Sem.support tf roots finite)) c.
Proof.
  intro Hpath; assert (Hinitial : B.config_wf (fun x => In x (@Sem.support tf roots finite)) (R.initial_config roots)).
  { split; [apply B.store_initial |apply Forall_forall; intros x Hx; exact (@Sem.initial_supported tf roots finite x Hx)]. }
  revert Hinitial; induction Hpath; auto; intro Hwf; apply IHHpath.
  eapply next_configuration_wf; [|exact Hwf |exact H].
  intros owner Howner; exact (@Sem.system_supported tf roots finite owner Howner).
Qed.

Theorem reachable_rank_configuration tf roots c : reachable tf roots c -> B.config_wf (fun _ => True) c.
Proof.
  intro Hpath; assert (Hinitial : B.config_wf (fun _ => True) (R.initial_config roots)).
  { split; [apply B.store_initial |apply Forall_forall; auto]. }
  revert Hinitial; induction Hpath; auto; intro Hwf; apply IHHpath.
  eapply next_configuration_wf; [intros; apply B.code_unrestricted |exact Hwf |exact H].
Qed.

Lemma publish_layout targets st fr :
  R.sigma (N.publish targets st fr) = R.sigma st /\
  R.readers (N.publish targets st fr) = R.readers st /\
  R.last_targets (N.publish targets st fr) = R.last_targets st.
Proof.
  revert st; induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution N.finish_write]; [auto |].
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  destruct (IH (N.finish_write st next fr target changed)) as [Hs [Hr Ht]].
  unfold N.finish_write, N.requeue_source in Hs, Hr, Ht |- *;
    destruct changed, N.cell_changed;
    destruct (B.write_layout Hw) as [_ [_ [Hsig [Hreaders Htargets]]]];
    cbn in Hs, Hr, Ht |- *; rewrite Hs, Hr, Ht; auto.
Qed.
Lemma publish_preserves_live targets st fr : B.preserves_live st (N.publish targets st fr).
Proof. apply B.preserves_live_layout, (proj1 (publish_layout targets st fr)). Qed.
Lemma next_preserves_live tf before after : step tf before after ->
  B.preserves_live (R.cfg_state before) (R.cfg_state after).
Proof.
  intro H; apply step_view in H; destruct H.
  - eapply B.next_preserves_live; eauto.
  - intros x Hx; apply B.preserves_live_materialize; exact Hx.
  - apply B.preserves_live_layout, B.observe_sigma.
  - apply publish_preserves_live.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |];
      apply B.preserves_live_layout; cbn; rewrite requeue_sigma; exact (proj1 (proj2 (proj2 (B.write_layout H)))).
  - apply B.preserves_live_layout; reflexivity.
  - apply B.preserves_live_layout; reflexivity.
  - apply B.preserves_live_layout; reflexivity.
  - apply B.preserves_live_layout; reflexivity.
Qed.
Lemma paths_preserve_live tf before after : steps tf before after ->
  B.preserves_live (R.cfg_state before) (R.cfg_state after).
Proof. intro H; induction H; intros x Hx; auto; apply IHsteps; eapply next_preserves_live; eauto. Qed.

Lemma publish_ranking_extends targets st fr : B.extends (R.ranking st) (R.ranking (N.publish targets st fr)).
Proof. rewrite publish_rank; apply B.extends_refl. Qed.
Lemma next_ranking_extends tf before after : step tf before after ->
  B.extends (R.ranking (R.cfg_state before)) (R.ranking (R.cfg_state after)).
Proof.
  intro H; apply step_view in H; destruct H.
  - eapply B.next_ranking_extends; eauto.
  - cbn; rewrite B.materialize_rank; apply B.extends_refl.
  - apply B.observe_extends.
  - cbn; rewrite publish_rank; apply B.extends_refl.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; cbn;
      rewrite requeue_rank, (B.write_rank H); apply B.extends_refl.
  - apply B.extends_refl.
  - apply B.extends_refl.
  - apply B.extends_refl.
  - apply B.extends_refl.
Qed.

Theorem next_active_ordered tf support before after : B.config_wf support before ->
  B.active_ordered before -> step tf before after -> B.active_ordered after.
Proof.
  intros Hwf Ho H; apply step_view in H; destruct H.
  - eapply B.next_active_ordered; eauto.
  - unfold B.active_ordered in *; cbn; rewrite B.materialize_rank; exact Ho.
  - unfold B.active_ordered in *; cbn.
    eapply B.ordered_extend; [apply B.observe_extends | |exact Ho].
    eapply Forall_impl with (P := B.known support st); [intros x [_ Hx]; exact Hx |].
    exact (@B.active_references (B.known support st) support
      (R.RunRhs fr (R.ConstraintSystem.Side target raw body) k) (proj2 Hwf)).
  - unfold B.active_ordered in *; cbn; rewrite publish_rank; exact Ho.
  - unfold R.continue_dead; destruct changed;
      [destruct (_ && _)%bool eqn:Hchild |];
      unfold B.active_ordered in *; cbn; rewrite requeue_rank, (B.write_rank H); try exact Ho.
    apply B.ordered_add_child; [|exact Ho].
    apply andb_true_iff in Hchild; destruct Hchild as [Hrank _].
    unfold R.rank_lt in Hrank; rewrite requeue_rank, (B.write_rank H) in Hrank; exact Hrank.
  - unfold B.active_ordered, N.suspend_commit in *; cbn.
    apply B.ordered_add_child; [exact (proj2 (proj2 (pending_spec H))) |exact Ho].
  - unfold B.active_ordered, N.retry_current in *; cbn; exact Ho.
  - unfold B.active_ordered, N.suspend_commit in *; cbn.
    apply B.ordered_add_child; [exact (proj2 (proj2 (pending_spec H))) |exact Ho].
  - exact Ho.
Qed.
Theorem reachable_active_ordered tf roots c : reachable tf roots c -> B.active_ordered c.
Proof.
  intro Hpath; assert (Hwf : B.config_wf (fun _ => True) (R.initial_config roots)) by
    (split; [apply B.store_initial |apply Forall_forall; auto]).
  assert (Ho : B.active_ordered (R.initial_config roots)) by constructor.
  revert Hwf Ho; induction Hpath; auto; intros Hwf Ho; apply IHHpath.
  - eapply next_configuration_wf; [intros; apply B.code_unrestricted |exact Hwf |exact H].
  - eapply next_active_ordered; eauto.
Qed.

Theorem next_frames_live tf before after : B.frames_live before -> step tf before after -> B.frames_live after.
Proof.
  intros Hframes Hstep.
  assert (Hlift : Forall (B.solved (R.cfg_state after)) (B.framed_owners (R.cfg_control before))).
  { eapply Forall_impl; [intros x Hx; eapply next_preserves_live; eauto |exact Hframes]. }
  apply step_view in Hstep; destruct Hstep.
  - eapply B.next_frames_live; eauto.
  - cbn [B.frames_live B.framed_owners B.active_owners B.suspended_owners B.configuration R.cfg_control R.cfg_state].
    constructor; [apply B.materialize_live |exact Hlift].
  - exact Hlift.
  - exact Hlift.
  - unfold R.continue_dead in Hlift |- *; destruct changed; [destruct (_ && _)%bool |]; exact Hlift.
  - exact Hlift.
  - exact Hlift.
  - exact Hlift.
  - exact Hlift.
Qed.
Theorem reachable_frames_live tf roots c : reachable tf roots c -> B.frames_live c.
Proof.
  intro Hpath; assert (Hinitial : B.frames_live (R.initial_config roots)) by constructor.
  revert Hinitial; induction Hpath; auto; intro Hframes; apply IHHpath; eapply next_frames_live; eauto.
Qed.

Lemma requeue_scoped before after source target : B.reset_scoped after ->
  B.reset_scoped (N.requeue_source before after source target).
Proof. unfold N.requeue_source; destruct N.cell_changed; auto using B.scoped_enqueue. Qed.
Lemma finish_scoped before after fr target changed : B.reset_scoped after ->
  B.reset_scoped (N.finish_write before after fr target changed).
Proof. unfold N.finish_write; destruct changed; auto using requeue_scoped, B.scoped_enqueue. Qed.
Lemma publish_scoped targets st fr : B.reset_scoped st -> B.frame_scoped st fr ->
  B.reset_scoped (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hs Hfr; cbn -[R.write_side_contribution N.finish_write]; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH; [apply finish_scoped; eapply B.scoped_write; eauto |].
  unfold B.frame_scoped; rewrite finish_rank, (B.write_rank Hw); exact Hfr.
Qed.
Lemma scoped_transport before after ctrl : R.ranking after = R.ranking before ->
  R.reset_at_close after = R.reset_at_close before ->
  B.scoped_config (B.configuration before ctrl) -> B.scoped_config (B.configuration after ctrl).
Proof.
  intros Hr Hreset [Hs Hc]; unfold B.configuration in *; cbn in *;
  change (B.reset_scoped after /\ B.scoped_control after ctrl); split.
  - eapply B.scoped_layout with (before := before); [rewrite Hr; apply B.extends_refl |exact Hreset |exact Hs].
  - unfold B.scoped_control in *; cbn in *; destruct ctrl; cbn in *; try exact I.
    all: try solve [eapply B.scoped_stack_extends with (before := before); [rewrite Hr; apply B.extends_refl |exact Hc]].
    all: destruct Hc as [Hfr Hk]; split;
      [eapply B.scoped_frame_extends with (before := before) |eapply B.scoped_stack_extends with (before := before)];
      try (rewrite Hr; apply B.extends_refl); eassumption.
Qed.
Lemma continue_dead_scoped st fr direct target rest k changed : B.reset_scoped st ->
  B.frame_scoped st fr -> B.scoped_stack st k ->
  B.scoped_config (R.continue_dead st fr direct target rest k changed).
Proof.
  intros Hs Hfr Hk; unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |].
  - split; [exact Hs |exact (conj Hfr Hk)].
  - eapply scoped_transport with (before := st); [reflexivity |reflexivity |].
    split; [exact Hs |exact (conj Hfr Hk)].
  - split; [exact Hs |exact (conj Hfr Hk)].
Qed.
Theorem next_scoped_config tf before after : B.scoped_config before -> step tf before after -> B.scoped_config after.
Proof.
  intros Hscope H; apply step_view in H; destruct H; unfold B.configuration in *; cbn in Hscope |- *.
  - eapply B.next_scoped_config; eauto.
  - eapply B.next_scoped_config with (before := B.configuration (N.clear_owner st owner) (R.StartEpisode owner k));
      [eapply scoped_transport with (before := st); [reflexivity |reflexivity |exact Hscope] |unfold B.step, R.next_config; reflexivity].
  - destruct Hscope as [Hs [Hfr Hk]]; split; [apply B.scoped_observe; exact Hs |].
    cbn [B.scoped_control B.configuration R.cfg_control R.cfg_state]; split.
    + apply B.scoped_side_frame; apply B.scoped_frame_extends with st; [apply B.observe_extends |exact Hfr].
    + eapply B.scoped_stack_extends; [apply B.observe_extends |exact Hk].
  - destruct Hscope as [Hs [Hfr Hk]]; split.
    + apply B.scoped_publish; apply publish_scoped; auto.
    + cbn [B.scoped_control B.configuration R.cfg_control R.cfg_state].
      split; [unfold B.frame_scoped, R.publish_targets; cbn; rewrite publish_rank; exact Hfr |].
      eapply B.scoped_stack_extends with (before := st); [unfold R.publish_targets; cbn; rewrite publish_rank; apply B.extends_refl |exact Hk].
  - destruct Hscope as [Hs [Hfr Hk]].
    assert (Hrank : R.ranking (N.requeue_source st next (R.frame_owner fr) target) = R.ranking st).
    { rewrite requeue_rank; eapply B.write_rank; exact H. }
    apply continue_dead_scoped.
    + apply requeue_scoped; eapply B.scoped_write; eauto.
    + eapply B.scoped_frame_extends with (before := st); [rewrite Hrank; apply B.extends_refl |exact Hfr].
    + eapply B.scoped_stack_extends with (before := st); [rewrite Hrank; apply B.extends_refl |exact Hk].
  - destruct Hscope as [Hs [_ Hk]]; split; [exact Hs |].
    cbn [N.suspend_commit B.scoped_control B.scoped_stack R.cfg_control R.cfg_state].
    split; [unfold B.frame_scoped; left; reflexivity |eapply B.scoped_stack_extends with (before := st); [apply B.extends_refl |exact Hk]].
  - destruct Hscope as [Hs [_ Hk]]; split; [exact Hs |].
    cbn [N.retry_current B.scoped_control R.cfg_control R.cfg_state].
    split; [unfold B.frame_scoped; left; reflexivity |eapply B.scoped_stack_extends with (before := st); [apply B.extends_refl |exact Hk]].
  - destruct Hscope as [Hs [_ Hk]]; split; [exact Hs |].
    cbn [N.suspend_commit B.scoped_control B.scoped_stack R.cfg_control R.cfg_state].
    split; [unfold B.frame_scoped; left; reflexivity |eapply B.scoped_stack_extends with (before := st); [apply B.extends_refl |exact Hk]].
  - eapply scoped_transport with (before := st); [reflexivity |reflexivity |exact Hscope].
Qed.
Theorem reachable_scoped_config tf roots c : reachable tf roots c -> B.scoped_config c.
Proof.
  intro Hpath; assert (Hinitial : B.scoped_config (R.initial_config roots)).
  { split; [|exact I]. intros scope source target Hin.
    unfold R.lookup_reset_ids in Hin; cbn in Hin; rewrite ML.lookup_empty in Hin; contradiction. }
  revert Hinitial; induction Hpath; auto; intro Hs; apply IHHpath; eapply next_scoped_config; eauto.
Qed.
Lemma publish_controlled targets st fr : B.controlled_mono st (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution N.finish_write]; [intros x Hx; exact Hx |].
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  intros x Hx; apply IH; unfold N.finish_write, N.requeue_source;
    destruct changed, N.cell_changed; change (S.mem x (R.controlled next) = true);
    exact (@B.controlled_write st fr target _ next _ Hw x Hx).
Qed.
Theorem next_controlled_mono tf before after : step tf before after ->
  B.controlled_mono (R.cfg_state before) (R.cfg_state after).
Proof.
  intro H; apply step_view in H; destruct H.
  - eapply B.next_controlled_mono; eauto.
  - apply B.controlled_layout; unfold R.materialize; destruct (M.lookup _ owner); reflexivity.
  - apply B.controlled_layout; unfold R.observe; destruct (Ranks.observe _ target); reflexivity.
  - apply publish_controlled.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |];
      intros x Hx; unfold N.requeue_source; destruct N.cell_changed;
      change (S.mem x (R.controlled next) = true); exact (@B.controlled_write st fr target _ next _ H x Hx).
  - intros x Hx; exact Hx.
  - intros x Hx; exact Hx.
  - intros x Hx; exact Hx.
  - intros x Hx; exact Hx.
Qed.

Lemma requeue_keeps_queue before after source target x : In x (R.queue after) ->
  In x (R.queue (N.requeue_source before after source target)).
Proof. unfold N.requeue_source; destruct N.cell_changed; intro H; [apply B.insert_members; auto |exact H]. Qed.
Lemma finish_keeps_queue before after fr target changed x : In x (R.queue after) ->
  In x (R.queue (N.finish_write before after fr target changed)).
Proof.
  unfold N.finish_write; intro H; destruct changed;
    [apply B.insert_members; right |]; apply requeue_keeps_queue; exact H.
Qed.
Lemma publish_keeps_queue targets st fr x : In x (R.queue st) -> In x (R.queue (N.publish targets st fr)).
Proof.
  revert st; induction targets as [|target rest IH]; intros st H; cbn -[R.write_side_contribution N.finish_write]; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH, finish_keeps_queue; rewrite (B.write_queue Hw); exact H.
Qed.
Lemma quiet_finish_cell before after fr target changed :
  ~ In (R.frame_owner fr) (R.queue (N.finish_write before after fr target changed)) ->
  N.cell_changed before after (R.frame_owner fr) target = false.
Proof.
  unfold N.finish_write, N.requeue_source.
  destruct (N.cell_changed before after (R.frame_owner fr) target) eqn:Hcell; auto.
  intro H; exfalso; apply H; destruct changed; cbn;
    apply B.insert_members; [right; apply B.insert_members |]; auto.
Qed.

Definition cell_stable st source target input :=
  B.eqv (snd (U.update true target (R.side_phase (R.stored_side_cell st source target))
    (R.stored_contribution st source target) input)) (R.stored_contribution st source target).
Lemma installed_cell st source target scope phase value :
  R.side_phase (R.stored_side_cell (R.register_reset (R.with_contributions st
      (R.update_map (R.contributions st) target source value)) source target scope phase) source target) = phase /\
  R.stored_contribution (R.register_reset (R.with_contributions st
      (R.update_map (R.contributions st) target source value)) source target scope phase) source target = value.
Proof.
  unfold R.stored_side_cell, R.stored_contribution, R.register_reset;
    cbn; rewrite !B.row_lookup; auto.
Qed.
Lemma unchanged_cell_stable st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  N.cell_changed st next (R.frame_owner fr) target = false -> cell_stable next (R.frame_owner fr) target input.
Proof.
  intro Hw; unfold R.write_side_contribution in Hw.
  set (base := R.promote_side_target st fr target) in *.
  set (phase := R.side_phase (R.stored_side_cell base (R.frame_owner fr) target)) in *.
  set (old := R.stored_contribution base (R.frame_owner fr) target) in *.
  destruct (U.update true target phase old input) as [next_phase value] eqn:Hu.
  intro Hquiet; inversion Hw; subst next changed.
  destruct (installed_cell base (R.frame_owner fr) target (R.frame_min_scope fr) next_phase value) as [Hphase Hvalue].
  assert (Hold : R.stored_contribution st (R.frame_owner fr) target = old).
  { subst old base; unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
  unfold N.cell_changed in Hquiet; rewrite Hvalue, Hold in Hquiet.
  apply negb_false_iff in Hquiet; apply B.eqv_bool in Hquiet.
  unfold cell_stable; rewrite Hphase, Hvalue.
  pose proof (@UL.update_stutter_closed true target phase old input) as Hclosed.
  rewrite Hu in Hclosed; cbn in Hclosed; apply Hclosed;
    [apply B.eqv_sym; exact Hquiet |apply B.eqv_sym; exact Hquiet |apply B.eqv_refl].
Qed.
Lemma stable_covers_input st source target input : cell_stable st source target input ->
  D.leq input (R.stored_contribution st source target) = true.
Proof. intro H; eapply DL.leq_trans; [apply UL.update_sound |exact (proj1 H)]. Qed.

Lemma changed_cell_consumes_credit st fr target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  N.cell_changed st next (R.frame_owner fr) target = true ->
  B.side_credit next (R.frame_owner fr) target < B.side_credit st (R.frame_owner fr) target.
Proof.
  intro Hw; unfold R.write_side_contribution in Hw.
  set (base := R.promote_side_target st fr target) in *.
  destruct (U.update true target (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
      (R.stored_contribution base (R.frame_owner fr) target) input) as [phase value] eqn:Hu.
  intro Hchanged; inversion Hw; subst next changed.
  rewrite B.side_credit_put.
  destruct (installed_cell base (R.frame_owner fr) target (R.frame_min_scope fr) phase value) as [_ Hvalue].
  assert (Hold : R.stored_contribution st (R.frame_owner fr) target = R.stored_contribution base (R.frame_owner fr) target).
  { subst base; unfold R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
  unfold N.cell_changed in Hchanged; rewrite Hvalue, Hold in Hchanged.
  rewrite <- (B.promoted_side_credit st fr target (R.frame_owner fr) target).
  unfold B.side_credit.
  pose proof (@UL.update_change_consumes true target (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
    (R.stored_contribution base (R.frame_owner fr) target) input) as Hstrict.
  rewrite Hu in Hstrict; cbn in Hstrict; apply Hstrict.
  intro Heq; apply B.eqv_bool in Heq; unfold R.equivalent in *.
  apply negb_true_iff in Hchanged; rewrite andb_comm in Hchanged; congruence.
Qed.

Lemma requeue_cell before after source target observed owner :
  R.stored_side_cell (N.requeue_source before after source target) observed owner =
    R.stored_side_cell after observed owner /\
  R.stored_contribution (N.requeue_source before after source target) observed owner =
    R.stored_contribution after observed owner.
Proof. unfold N.requeue_source; destruct N.cell_changed; auto. Qed.
Lemma finish_cell before after fr target changed source observed :
  R.stored_side_cell (N.finish_write before after fr target changed) source observed =
    R.stored_side_cell after source observed /\
  R.stored_contribution (N.finish_write before after fr target changed) source observed =
    R.stored_contribution after source observed.
Proof. unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; auto. Qed.
Lemma other_cell_write st fr target input next changed source observed :
  R.write_side_contribution st fr target input = (next,changed) ->
  (source,observed) <> (R.frame_owner fr,target) ->
  R.stored_side_cell next source observed = R.stored_side_cell st source observed /\
  R.stored_contribution next source observed = R.stored_contribution st source observed.
Proof.
  intros Hw Hneq; unfold R.write_side_contribution in Hw.
  destruct (U.update _ _ _ _ _) as [phase value]; inversion Hw; subst next.
  unfold R.stored_side_cell, R.stored_contribution, R.register_reset; cbn;
    rewrite !B.row_lookup_other by congruence.
  unfold R.promote_side_target, R.promote_controlled;
    destruct (R.rank_lt st target (R.frame_owner fr)); auto.
Qed.
Lemma publish_other_cell targets st fr source target :
  (source <> R.frame_owner fr \/ ~ In target targets) ->
  R.stored_side_cell (N.publish targets st fr) source target = R.stored_side_cell st source target /\
  R.stored_contribution (N.publish targets st fr) source target = R.stored_contribution st source target.
Proof.
  revert st; induction targets as [|head rest IH]; intros st Hother; cbn -[R.write_side_contribution N.finish_write]; [auto |].
  destruct (R.write_side_contribution st fr head _) as [next changed] eqn:Hw.
  assert (Hneq : (source,target) <> (R.frame_owner fr,head)) by
    (intro Heq; destruct Hother as [Hsource|Htarget];
      [apply Hsource; exact (f_equal fst Heq) |apply Htarget; left; symmetry; exact (f_equal snd Heq)]).
  destruct (IH (N.finish_write st next fr head changed) ltac:(destruct Hother as [Ho|Ht]; [left; exact Ho |right; intro Hin; apply Ht; right; exact Hin])) as [Hcell Hvalue].
  destruct (finish_cell st next fr head changed source target) as [Hc Hv].
  destruct (other_cell_write Hw Hneq) as [Hc0 Hv0].
  rewrite Hcell,Hvalue,Hc,Hv,Hc0,Hv0; auto.
Qed.
Lemma quiet_publication_stable targets st fr target : In target targets ->
  ~ In (R.frame_owner fr) (R.queue (N.publish targets st fr)) ->
  cell_stable (N.publish targets st fr) (R.frame_owner fr) target
    (match M.lookup (R.frame_local_side fr) target with Some value => value |None => D.bottom end).
Proof.
  revert st; induction targets as [|head rest IH]; intros st Hin Hquiet; [contradiction |].
  cbn -[R.write_side_contribution N.finish_write] in Hquiet |- *.
  destruct (R.write_side_contribution st fr head _) as [next changed] eqn:Hw.
  destruct (in_dec V.eq_dec target rest) as [Hrest|Houtside].
  - apply IH; auto.
  - destruct Hin as [Hhead|Hin]; [subst target |contradiction].
    destruct (@publish_other_cell rest (N.finish_write st next fr head changed) fr (R.frame_owner fr) head (or_intror Houtside)) as [Hc Hv].
    unfold cell_stable; rewrite Hc,Hv.
    destruct (finish_cell st next fr head changed (R.frame_owner fr) head) as [Hc1 Hv1].
    rewrite Hc1,Hv1; fold cell_stable.
    eapply unchanged_cell_stable; [exact Hw |apply quiet_finish_cell with (changed := changed)].
    intro Hqueued; apply Hquiet; apply publish_keeps_queue; exact Hqueued.
Qed.

Lemma actual_commit_ready tf st fr direct k after next_fr next_k :
  N.next_config tf (B.configuration st (R.RunCommit fr direct k)) =
    Some (B.configuration after (R.RunDrain next_fr next_k)) ->
  N.pending_above st (R.frame_owner fr) = None /\ ~ In (R.frame_owner fr) (R.queue st).
Proof.
  unfold N.next_config, N.next_repaired, N.next_fresh, N.next_batched, N.next_precommit;
    cbn -[N.pending_above N.suspend_commit N.retry_current R.next_config].
  destruct (N.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp.
  - unfold N.suspend_commit, B.configuration; discriminate.
  - destruct (R.queue_contains (R.frame_owner fr) (R.queue st)) eqn:Hqueued.
    + unfold N.retry_current, B.configuration; discriminate.
    + intros _; split; [reflexivity |]. intro Hin; apply B.contains_spec in Hin; congruence.
Qed.
Theorem committing_publication_stable tf st fr direct k after next_fr next_k target :
  N.next_config tf (B.configuration
    (R.publish_targets (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr)
    (R.RunCommit fr direct k)) = Some (B.configuration after (R.RunDrain next_fr next_k)) ->
  S.mem target (R.frame_current_targets fr) = true ->
  cell_stable (R.publish_targets (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr)
    (R.frame_owner fr) target
    (match M.lookup (R.frame_local_side fr) target with Some value => value |None => D.bottom end).
Proof.
  intros Hstep Hmem; apply quiet_publication_stable; [apply SL.mem_spec; exact Hmem |].
  exact (proj2 (@actual_commit_ready tf _ fr direct k after next_fr next_k Hstep)).
Qed.

Lemma active_forward tf before after : step tf before after -> forall owner,
  In owner (B.active_owners (R.cfg_control before)) ->
  In owner (B.active_owners (R.cfg_control after)) \/ B.closing before after owner.
Proof.
  intro H; apply step_view in H; destruct H; try solve [eapply B.next_active_origin; eauto].
  all: try (unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold B.configuration, N.suspend_commit, N.retry_current;
    cbn [R.cfg_control B.active_owners B.suspended_owners R.frame_owner R.fresh_frame R.with_frame_side];
    intros query Hin; left; cbn; intuition auto.
Qed.
Lemma live_forward tf before after : B.frames_live before -> step tf before after ->
  forall owner, B.live_reference before owner -> B.live_reference after owner.
Proof.
  intros Hframes Hstep owner [Hsolved|Hactive].
  - left; eapply next_preserves_live; eauto.
  - destruct (@active_forward tf before after Hstep owner Hactive) as [Ha|[fr [k [Hbefore [Hafter ->]]]]]; [now right |].
    left; eapply next_preserves_live; [exact Hstep |].
    unfold B.frames_live in Hframes; rewrite Hbefore in Hframes.
    inversion Hframes; assumption.
Qed.

Definition local_members fr := forall target input,
  M.lookup (R.frame_local_side fr) target = Some input -> S.mem target (R.frame_current_targets fr) = true.
Record cursor tf (live : V.t -> Prop) st fr body := {
  reads : list (V.t * D.t);
  sides : list (V.t * D.t);
  spawns : list V.t;
  prefix : B.observation_prefix (tf (R.frame_owner fr)) body reads sides spawns;
  watches : B.quiet_reads st (R.frame_owner fr) reads;
  raw_input : forall target raw, In (target,raw) sides ->
    exists input, M.lookup (R.frame_local_side fr) target = Some input /\ D.leq raw input = true;
  local_targets : local_members fr;
  live_spawns : forall target, In target spawns -> live target
}.
Lemma fresh_cursor tf live st owner phase : cursor tf live st (R.fresh_frame st owner phase) (tf owner).
Proof.
  refine {| reads := []; sides := []; spawns := [] |}.
  - apply B.prefix_fresh.
  - intros _ target value Hin; contradiction.
  - intros target raw Hin; contradiction.
  - intros target input Hlookup; cbn in Hlookup; rewrite ML.lookup_empty in Hlookup; discriminate.
  - intros target Hin; contradiction.
Qed.
Lemma cursor_transfer tf P Q before after fr next_fr body :
  R.frame_owner next_fr = R.frame_owner fr -> R.frame_local_side next_fr = R.frame_local_side fr ->
  R.frame_current_targets next_fr = R.frame_current_targets fr ->
  (forall rs, B.quiet_reads before (R.frame_owner fr) rs -> B.quiet_reads after (R.frame_owner fr) rs) ->
  (forall target, P target -> Q target) -> cursor tf P before fr body -> cursor tf Q after next_fr body.
Proof.
  intros Ho Hl Ht Hw Hlive [rs ss ps Hp Hr Hraw Htargets Hps].
  refine {| reads := rs; sides := ss; spawns := ps |}.
  - rewrite Ho; exact Hp.
  - rewrite Ho; apply Hw; exact Hr.
  - rewrite Hl; exact Hraw.
  - intros target input Hlookup; rewrite Hl in Hlookup; rewrite Ht; apply Htargets with input; exact Hlookup.
  - intros target Hin; apply Hlive, Hps; exact Hin.
Qed.
Lemma get_cursor tf live st fr target next next_fr value tail :
  R.complete_get st fr target = (next,next_fr,value) -> cursor tf live st fr (B.Syntax.Get target tail) ->
  cursor tf live next next_fr (tail value).
Proof.
  intros Hget [rs ss ps Hp Hr Hraw Htargets Hps].
  assert (Hfields : R.frame_owner next_fr = R.frame_owner fr /\
    R.frame_local_side next_fr = R.frame_local_side fr /\ R.frame_current_targets next_fr = R.frame_current_targets fr).
  { unfold R.complete_get in Hget; B.split_program Hget; auto. }
  destruct Hfields as [Ho [Hl Ht]].
  refine {| reads := rs ++ [(target,value)]; sides := ss; spawns := ps |}.
  - rewrite Ho; apply B.prefix_get; exact Hp.
  - rewrite Ho; intro Hquiet; apply B.watched_snoc.
    + apply (B.quiet_get Hget Hr); exact Hquiet.
    + exact (proj1 (B.get_watches_target Hget)).
    + exact (proj2 (B.get_watches_target Hget)).
  - rewrite Hl; exact Hraw.
  - intros observed input Hlookup; rewrite Hl in Hlookup; rewrite Ht; eapply Htargets; exact Hlookup.
  - exact Hps.
Qed.
Lemma spawn_cursor tf live st fr target tail : live target ->
  cursor tf live st fr (B.Syntax.Spawn target tail) -> cursor tf live st fr tail.
Proof.
  intros Htarget [rs ss ps Hp Hr Hraw Htargets Hps].
  refine {| reads := rs; sides := ss; spawns := ps ++ [target];
    prefix := B.prefix_spawn Hp; watches := Hr; raw_input := Hraw; local_targets := Htargets |}.
  intros observed Hin; apply in_app_or in Hin; destruct Hin as [Hin|[<-|Hin]]; auto; contradiction.
Qed.
Lemma side_cursor tf live st fr target raw tail : cursor tf live st fr (B.Syntax.Side target raw tail) ->
  cursor tf live st (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) tail.
Proof.
  intros [rs ss ps Hp Hr Hraw Htargets Hps].
  refine {| reads := rs; sides := ss ++ [(target,raw)]; spawns := ps |}.
  - exact (B.prefix_side Hp).
  - exact Hr.
  - intros observed value Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]]; [| |contradiction].
    + destruct (Hraw observed value Hin) as [input [Hlookup Hle]].
      destruct (V.eq_dec observed target) as [Hsame|Hneq].
      * subst observed; exists (R.accumulated_side_input fr target raw); split; [apply ML.lookup_update_same |].
        eapply DL.leq_trans; [exact Hle |apply B.side_input_old; exact Hlookup].
      * exists input; split; [cbn; rewrite ML.lookup_update_other; auto |exact Hle].
    + inversion Heq; subst observed value; exists (R.accumulated_side_input fr target raw); split;
        [apply ML.lookup_update_same |apply B.side_input_raw].
  - intros observed input Hlookup; cbn in Hlookup |- *; apply SL.add_spec.
    destruct (V.eq_dec observed target) as [Hsame|Hneq]; [auto |right].
    rewrite ML.lookup_update_other in Hlookup; auto; eapply Htargets; exact Hlookup.
  - exact Hps.
Qed.

Lemma publication_covers_input targets st fr target input : In target targets ->
  M.lookup (R.frame_local_side fr) target = Some input ->
  D.leq input (R.stored_contribution (N.publish targets st fr) (R.frame_owner fr) target) = true.
Proof.
  revert st; induction targets as [|head rest IH]; intros st Hin Hinput; [contradiction |].
  cbn -[R.write_side_contribution N.finish_write].
  destruct (R.write_side_contribution st fr head _) as [next changed] eqn:Hw.
  destruct (in_dec V.eq_dec target rest) as [Hrest|Houtside].
  - apply IH; auto.
  - destruct Hin as [Hhead|Hin]; [subst target |contradiction].
    rewrite (proj2 (@publish_other_cell rest (N.finish_write st next fr head changed) fr (R.frame_owner fr) head (or_intror Houtside))),
      (proj2 (finish_cell st next fr head changed (R.frame_owner fr) head)).
    rewrite Hinput in Hw; exact (B.write_contribution_sound Hw).
Qed.
Lemma publication_ledger st fr : local_members fr ->
  B.side_ledger (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr.
Proof.
  intros Hlocal target input Hinput; split; [eapply Hlocal; exact Hinput |].
  apply publication_covers_input; [apply SL.mem_spec; eapply Hlocal; exact Hinput |exact Hinput].
Qed.
Definition empty_cache fr := R.frame_local_side fr = M.empty D.t.
Lemma reset_cursor tf live st fr : empty_cache fr -> cursor tf live st fr (tf (R.frame_owner fr)).
Proof.
  intro Hcache; refine {| reads := []; sides := []; spawns := [] |}.
  - apply B.prefix_fresh.
  - intros _ target value Hin; contradiction.
  - intros target raw Hin; contradiction.
  - intros target input Hinput; rewrite Hcache, ML.lookup_empty in Hinput; discriminate.
  - intros target Hin; contradiction.
Qed.

Fixpoint observing_stack tf (live : V.t -> Prop) st k : Type :=
  match k with
  | R.KLoop |R.KSeedLoop _ => unit
  | R.KAfterGet fr target next rest =>
      (cursor tf live st fr (B.Syntax.Get target next) * observing_stack tf live st rest)%type
  | R.KAfterSide fr body rest =>
      (empty_cache fr * (body = tf (R.frame_owner fr)) * observing_stack tf live st rest)%type
  | R.KAfterSpawn fr next rest => (cursor tf live st fr next * observing_stack tf live st rest)%type
  | R.KDead fr direct _ rest => (cursor tf live st fr (B.Syntax.Ret direct) * observing_stack tf live st rest)%type
  | R.KDrain fr rest =>
      (B.guarded_observation tf live st (R.frame_owner fr) * observing_stack tf live st rest)%type
  end.
Definition observing_control tf c : Type :=
  let live := B.live_reference c in let st := R.cfg_state c in
  match R.cfg_control c with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => unit
  | R.StartEpisode _ k |R.Return k => observing_stack tf live st k
  | R.RunRhs fr body k => (cursor tf live st fr body * observing_stack tf live st k)%type
  | R.RunDead fr direct _ k => (cursor tf live st fr (B.Syntax.Ret direct) * observing_stack tf live st k)%type
  | R.RunCommit fr direct k =>
      (cursor tf live st fr (B.Syntax.Ret direct) * B.side_ledger st fr * observing_stack tf live st k)%type
  | R.RunDrain fr k =>
      (B.guarded_observation tf live st (R.frame_owner fr) * observing_stack tf live st k)%type
  end.
Lemma cursor_move tf P Q before after fr body : B.quiet_preserving before after ->
  (forall target, P target -> Q target) -> cursor tf P before fr body -> cursor tf Q after fr body.
Proof. intros Hw Hl H; eapply cursor_transfer; [reflexivity |reflexivity |reflexivity |exact (Hw _) |exact Hl |exact H]. Qed.
Lemma stack_move tf P Q before after k :
  (forall fr body, In (R.frame_owner fr) (B.suspended_owners k) ->
    cursor tf P before fr body -> cursor tf Q after fr body) ->
  (forall owner, In owner (B.suspended_owners k) ->
    B.guarded_observation tf P before owner -> B.guarded_observation tf Q after owner) ->
  observing_stack tf P before k -> observing_stack tf Q after k.
Proof.
  intros Hcursor Hguard; induction k; cbn [observing_stack B.suspended_owners]; intro Hstack; try exact tt.
  - destruct Hstack as [Hfr Hk]; split; [apply Hcursor; [left; reflexivity |exact Hfr] |].
    apply IHk; [intros head_fr head_body Hin Hc; apply Hcursor; [right; exact Hin |exact Hc]
      |intros head_owner Hin Hc; apply Hguard; [right; exact Hin |exact Hc] |exact Hk].
  - destruct Hstack as [[Hempty Heq] Hk]; split; [auto |].
    apply IHk; [intros head_fr head_body Hin Hc; apply Hcursor; [right; exact Hin |exact Hc]
      |intros head_owner Hin Hc; apply Hguard; [right; exact Hin |exact Hc] |exact Hk].
  - destruct Hstack as [Hfr Hk]; split; [apply Hcursor; [left; reflexivity |exact Hfr] |].
    apply IHk; [intros head_fr head_body Hin Hc; apply Hcursor; [right; exact Hin |exact Hc]
      |intros head_owner Hin Hc; apply Hguard; [right; exact Hin |exact Hc] |exact Hk].
  - destruct Hstack as [Hfr Hk]; split; [apply Hcursor; [left; reflexivity |exact Hfr] |].
    apply IHk; [intros head_fr head_body Hin Hc; apply Hcursor; [right; exact Hin |exact Hc]
      |intros head_owner Hin Hc; apply Hguard; [right; exact Hin |exact Hc] |exact Hk].
  - destruct Hstack as [Hfr Hk]; split; [apply Hguard; [left; reflexivity |exact Hfr] |].
    apply IHk; [intros head_fr head_body Hin Hc; apply Hcursor; [right; exact Hin |exact Hc]
      |intros head_owner Hin Hc; apply Hguard; [right; exact Hin |exact Hc] |exact Hk].
Qed.
Lemma stack_snapshot tf P Q before after k : B.frame_snapshot before after (B.suspended_owners k) ->
  (forall target, P target -> Q target) -> observing_stack tf P before k -> observing_stack tf Q after k.
Proof.
  intros Hsnap Hlive; apply stack_move.
  - intros fr body Hin Hc; eapply cursor_transfer;
      [reflexivity |reflexivity |reflexivity |exact (B.snapshot_reads Hsnap Hin) |exact Hlive |exact Hc].
  - intros owner Hin H; eapply B.guarded_moved; eauto.
Qed.

Lemma cursor_published tf live st fr body : cursor tf live st fr body -> B.side_ledger st fr ->
  B.cursor tf live st fr body.
Proof.
  intros [rs ss ps Hp Hr Hraw Htargets Hps] Hledger.
  exact (@B.Build_cursor tf live st fr body rs ss ps Hp Hr Hraw Hledger Hps).
Qed.
Lemma moved_cursor tf P Q before after fr body owners : B.frame_snapshot before after owners ->
  In (R.frame_owner fr) owners -> (forall target, P target -> Q target) ->
  cursor tf P before fr body -> cursor tf Q after fr body.
Proof.
  intros Hsnapshot Hin Hlive H; eapply cursor_transfer;
    [reflexivity |reflexivity |reflexivity |exact (B.snapshot_reads Hsnapshot Hin) |exact Hlive |exact H].
Qed.
Ltac move_cursor Hsnapshot Hlive Hcursor :=
  eapply moved_cursor; [exact Hsnapshot |left; reflexivity |exact Hlive |exact Hcursor].
Ltac move_stack Hsnapshot Hlive Hstack :=
  eapply stack_snapshot; [exact Hsnapshot |exact Hlive |exact Hstack].
Ltac move_parents Hsnapshot Hlive Hstack :=
  eapply stack_snapshot; [eapply B.snapshot_tail; exact Hsnapshot |exact Hlive |exact Hstack].

Lemma core_observing tf before after : B.frames_live before -> B.active_ordered before ->
  inhabited (observing_control tf before) -> B.step tf before after -> core_rule (R.cfg_control before) ->
  inhabited (observing_control tf after).
Proof.
  intros Hframes Horder [Hobs] Hstep Hcore.
  pose proof (@B.live_reference_forward tf before after Hframes Hstep) as Hlive.
  pose proof (@B.ordered_unique (R.ranking (R.cfg_state before)) _ Horder) as Hunique.
  destruct before as [st ctrl]; destruct ctrl as [|roots|roots|owner k|fr body k|
    fr direct pending k|fr direct k|fr k|k];
    unfold observing_control, B.configuration in Hobs |- *;
    unfold B.step, R.next_config in Hstep; cbn -[R.complete_get R.set_value R.observe R.fresh_frame R.materialize
      R.queue_pop R.queue_peek R.reset_registered_cells R.rank_lt R.is_materialized]
      in Hcore, Hobs, Hstep, Horder, Hunique |- *.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; try discriminate; inversion Hstep; subst; constructor; exact tt.
  - destruct roots as [|root roots]; [|destruct (R.is_materialized (R.observe st root) root)]; inversion Hstep; subst; constructor; exact tt.
  - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; inversion Hstep; subst; constructor; exact tt.
  - contradiction.
  - destruct Hobs as [Hcursor Hstack]; destruct body as [direct|target tail|target raw tail|target tail].
    + inversion Hstep; subst; constructor; split;
        [move_cursor (B.snapshot_identity st (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor
        |move_stack (B.snapshot_identity st (B.suspended_owners k)) Hlive Hstack].
    + destruct (negb (R.is_materialized (R.observe st target) target) && R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
      * inversion Hstep; subst; constructor; split;
          [move_cursor (B.snapshot_observe st target (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor
          |move_stack (B.snapshot_observe st target (B.suspended_owners k)) Hlive Hstack].
      * set (base := if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target) in *.
        assert (Hbase : B.frame_snapshot st base (R.frame_owner fr :: B.suspended_owners k)).
        { unfold base; destruct (R.is_materialized (R.observe st target) target);
          [apply B.snapshot_observe |eapply B.snapshot_compose; [apply B.snapshot_observe |apply B.snapshot_enqueue]]. }
        destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst; constructor; split.
        -- apply get_cursor with (st := base) (fr := fr) (target := target); [exact Hget |move_cursor Hbase Hlive Hcursor].
        -- move_parents (@B.snapshot_compose st base next _ Hbase (B.snapshot_get _ Hget)) Hlive Hstack.
    + contradiction.
    + destruct (R.is_materialized (R.observe st target) target) eqn:Hsolved.
      * inversion Hstep; subst; constructor; split.
        -- apply spawn_cursor with target; [left; apply B.materialized_solved; exact Hsolved |].
           move_cursor (B.snapshot_observe st target (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor.
        -- move_stack (B.snapshot_observe st target (B.suspended_owners k)) Hlive Hstack.
      * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
        -- inversion Hstep; subst; constructor; split.
           ++ apply spawn_cursor with target; [right; left; reflexivity |].
              move_cursor (B.snapshot_observe st target (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor.
           ++ move_stack (B.snapshot_observe st target (B.suspended_owners k)) Hlive Hstack.
        -- inversion Hstep; subst; constructor; split.
           ++ apply spawn_cursor with target; [left; apply B.materialize_live |].
              move_cursor (@B.snapshot_compose st (R.observe st target)
                (R.materialize (R.enqueue (R.observe st target) target) target)
                (R.frame_owner fr :: B.suspended_owners k) (B.snapshot_observe _ _ _)
                (@B.snapshot_compose (R.observe st target) (R.enqueue (R.observe st target) target)
                  (R.materialize (R.enqueue (R.observe st target) target) target) _
                  (B.snapshot_enqueue _ _ _) (B.snapshot_materialize _ _ _))) Hlive Hcursor.
           ++ eapply stack_snapshot; [|exact Hlive |exact Hstack].
              eapply B.snapshot_compose; [apply B.snapshot_observe |].
              eapply B.snapshot_compose; [apply B.snapshot_enqueue |apply B.snapshot_materialize].
  - destruct pending as [|target pending]; [contradiction |].
    change (S.mem target (R.frame_current_targets fr) = true) in Hcore; rewrite Hcore in Hstep.
    inversion Hstep; subst; destruct Hobs as [Hcursor Hstack]; constructor; split;
      [move_cursor (B.snapshot_identity st (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor
      |move_stack (B.snapshot_identity st (B.suspended_owners k)) Hlive Hstack].
  - destruct Hobs as [[Hcursor Hledger] Hstack].
    destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
    inversion Hstep; subst; constructor; split.
    + eapply B.cursor_committed; [exact Hset |exact Hlive |apply cursor_published; auto].
    + eapply stack_snapshot; [|exact Hlive |exact Hstack].
      eapply B.snapshot_compose; [eapply B.snapshot_commit; [exact Hset |apply B.parent_distinct; exact Hunique] |apply B.snapshot_requeue].
  - destruct Hobs as [Hguard Hstack]; destruct (R.queue_peek (R.queue st)) as [next|] eqn:Hpeek.
    + destruct (V.eq_dec next (R.frame_owner fr)) as [Hself|Hnot].
      * destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
        assert (head = next) by (pose proof (@B.peek_popped _ head rest Hpop); congruence); subst head next.
        inversion Hstep; subst; constructor; split; [apply fresh_cursor |].
        eapply stack_snapshot; [|exact Hlive |exact Hstack].
        eapply B.snapshot_pop; [destruct (R.queue st); inversion Hpop; reflexivity |apply B.parent_distinct; exact Hunique].
      * destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
        -- destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop; try discriminate.
           assert (head = next) by (pose proof (@B.peek_popped _ head rest Hpop); congruence); subst head.
           assert (Hsnapshot : B.frame_snapshot st (R.with_queue st rest) (R.frame_owner fr :: B.suspended_owners k)).
           { eapply B.snapshot_pop; [destruct (R.queue st); inversion Hpop; reflexivity |].
             apply B.child_distinct with (order := R.ranking st); auto. }
           inversion Hstep; subst; constructor; split.
           ++ eapply B.guarded_moved; [exact Hsnapshot |left; reflexivity |exact Hlive |exact Hguard].
           ++ move_parents Hsnapshot Hlive Hstack.
        -- inversion Hstep; subst; constructor; move_stack (B.snapshot_close st (R.frame_owner fr) (B.suspended_owners k)) Hlive Hstack.
    + inversion Hstep; subst; constructor; move_stack (B.snapshot_close st (R.frame_owner fr) (B.suspended_owners k)) Hlive Hstack.
  - destruct k as [|roots|fr target tail k|fr body k|fr body k|fr direct rest k|fr k]; cbn in Hobs, Hcore; try contradiction.
    + inversion Hstep; subst; constructor; exact tt.
    + inversion Hstep; subst; constructor; exact tt.
    + destruct Hobs as [Hcursor Hstack]; destruct (R.complete_get st fr target) as [[next next_fr] value] eqn:Hget.
      inversion Hstep; subst; constructor; split.
      * eapply get_cursor; [exact Hget |move_cursor (B.snapshot_identity st (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor].
      * move_stack (B.snapshot_get (B.suspended_owners k) Hget) Hlive Hstack.
    + destruct Hobs as [Hcursor Hstack]; inversion Hstep; subst; constructor; split;
        [move_cursor (B.snapshot_identity st (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor
        |move_stack (B.snapshot_identity st (B.suspended_owners k)) Hlive Hstack].
    + destruct Hobs as [Hcursor Hstack]; inversion Hstep; subst; constructor; split;
        [move_cursor (B.snapshot_identity st (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor
        |move_stack (B.snapshot_identity st (B.suspended_owners k)) Hlive Hstack].
    + destruct Hobs as [Hguard Hstack]; inversion Hstep; subst; constructor; split.
      * eapply B.guarded_moved; [apply B.snapshot_identity with (owners := R.frame_owner fr :: B.suspended_owners k)
          |left; reflexivity |exact Hlive |exact Hguard].
      * move_stack (B.snapshot_identity st (B.suspended_owners k)) Hlive Hstack.
Qed.

Lemma clear_snapshot st owner owners : (forall x, In x owners -> x <> owner) ->
  B.frame_snapshot st (N.clear_owner st owner) owners.
Proof.
  intro Hother; apply B.snapshot_static; try reflexivity.
  intros x Hin Hq; apply clear_members; split; [exact Hq |apply Hother; exact Hin].
Qed.
Lemma requeue_snapshot before after source target owners :
  B.frame_snapshot after (N.requeue_source before after source target) owners.
Proof. unfold N.requeue_source; destruct N.cell_changed; auto using B.snapshot_enqueue, B.snapshot_identity. Qed.
Lemma finish_snapshot before after fr target changed owners :
  B.frame_snapshot after (N.finish_write before after fr target changed) owners.
Proof.
  unfold N.finish_write; destruct changed; [eapply B.snapshot_compose; [apply requeue_snapshot |apply B.snapshot_enqueue] |apply requeue_snapshot].
Qed.
Lemma publication_snapshot targets st fr owners : (forall owner, In owner owners -> owner <> R.frame_owner fr) ->
  B.frame_snapshot st (N.publish targets st fr) owners.
Proof.
  intro Hother; revert st; induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution N.finish_write]; [apply B.snapshot_identity |].
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  eapply B.snapshot_compose; [eapply B.snapshot_side_write; eauto |].
  eapply B.snapshot_compose; [apply finish_snapshot |apply IH].
Qed.
Lemma publication_quiet targets st fr : B.quiet_preserving st (N.publish targets st fr).
Proof.
  destruct (publish_layout targets st fr) as [Hs [Hr _]].
  apply B.quiet_layout; [exact Hs |exact Hr |intros; apply publish_keeps_queue; assumption].
Qed.
Lemma continue_dead_snapshot st fr direct target rest k changed owners :
  B.frame_snapshot st (R.cfg_state (R.continue_dead st fr direct target rest k changed)) owners.
Proof. unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |];
  [exact (B.snapshot_identity st owners) |exact (B.snapshot_enqueue st target owners) |exact (B.snapshot_identity st owners)]. Qed.

Theorem next_observing_control tf before after : B.frames_live before -> B.active_ordered before ->
  inhabited (observing_control tf before) -> step tf before after -> inhabited (observing_control tf after).
Proof.
  intros Hframes Horder [Hobs] Hstep.
  pose proof (@live_forward tf before after Hframes Hstep) as Hlive.
  pose proof (@B.ordered_unique (R.ranking (R.cfg_state before)) _ Horder) as Hunique.
  apply step_view in Hstep; destruct Hstep as [before after Hbase Hguard|st owner k|
    st fr target raw body k|st fr direct k|st fr direct target rest k next changed Hw|
    st fr direct k target rest Hp|st fr direct k|st fr body k target rest Hp|st fr body k].
  - eapply core_observing; eauto; constructor; exact Hobs.
  all: unfold observing_control, B.configuration in Hobs |- *;
    cbn -[R.materialize R.fresh_frame R.set_value R.observe N.publish N.clear_owner N.retry_current N.suspend_commit]
      in Hobs, Hunique, Horder |- *.
  - constructor; split; [apply fresh_cursor |].
    eapply stack_snapshot; [|exact Hlive |exact Hobs].
    eapply B.snapshot_compose; [apply clear_snapshot; apply B.parent_distinct; exact Hunique |apply B.snapshot_materialize].
  - destruct Hobs as [Hcursor Hstack]; constructor; split.
    + apply side_cursor; move_cursor (B.snapshot_observe st target (R.frame_owner fr :: B.suspended_owners k)) Hlive Hcursor.
    + move_stack (B.snapshot_observe st target (B.suspended_owners k)) Hlive Hstack.
  - destruct Hobs as [Hcursor Hstack]; constructor; split; [split |].
    + eapply cursor_move; [|exact Hlive |exact Hcursor].
      eapply B.quiet_layout; [exact (proj1 (publish_layout (S.elements (R.frame_current_targets fr)) st fr)) |exact (proj1 (proj2 (publish_layout _ _ _))) |].
      intros; apply publish_keeps_queue; assumption.
    + apply publication_ledger; exact (local_targets Hcursor).
    + eapply stack_snapshot; [|exact Hlive |exact Hstack].
      eapply B.snapshot_compose; [apply publication_snapshot; apply B.parent_distinct; exact Hunique |apply B.snapshot_publish].
  - destruct Hobs as [Hcursor Hstack].
    assert (Hsnapshot : B.frame_snapshot st (R.cfg_state (R.continue_dead
      (N.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed)) (B.suspended_owners k)).
    { eapply B.snapshot_compose; [eapply B.snapshot_side_write; [exact Hw |apply B.parent_distinct; exact Hunique] |].
      eapply B.snapshot_compose; [apply requeue_snapshot |apply continue_dead_snapshot]. }
    assert (Hquiet : B.quiet_preserving st (R.cfg_state (R.continue_dead
      (N.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed))).
    { intros observed rs Hrs.
      destruct (B.write_layout Hw) as [_ [Hq [Hs [Hr _]]]].
      assert (Hnext : B.quiet_reads next observed rs).
      { eapply B.quiet_layout; [exact Hs |exact Hr |intros x Hin; rewrite Hq; exact Hin |exact Hrs]. }
      eapply (@B.snapshot_reads next _ [observed]);
        [|left; reflexivity |exact Hnext].
      eapply B.snapshot_compose; [apply requeue_snapshot |apply continue_dead_snapshot]. }
    unfold R.continue_dead in Hsnapshot, Hquiet, Hlive |- *; destruct changed; [destruct (_ && _)%bool |]; constructor; split.
    all: try solve [eapply cursor_move; [exact Hquiet |exact Hlive |exact Hcursor]].
    all: move_stack Hsnapshot Hlive Hstack.
  - destruct Hobs as [[Hcursor Hledger] Hstack].
    destruct (pending_spec Hp) as [_ [Hpop Hhigher]].
    assert (Hsnapshot : B.frame_snapshot st (R.with_queue st rest) (R.frame_owner fr :: B.suspended_owners k)).
    { eapply B.snapshot_pop; [destruct (R.queue st); inversion Hpop; reflexivity |].
      apply B.child_distinct with (order := R.ranking st); auto. }
    constructor; split; [split; [reflexivity |reflexivity] |move_parents Hsnapshot Hlive Hstack].
  - destruct Hobs as [[Hcursor Hledger] Hstack]; constructor; split; [apply fresh_cursor |].
    move_stack (@clear_snapshot st (R.frame_owner fr) (B.suspended_owners k) (B.parent_distinct Hunique)) Hlive Hstack.
  - destruct Hobs as [[Hempty Hbody] Hstack].
    destruct (pending_spec Hp) as [_ [Hpop Hhigher]].
    assert (Hsnapshot : B.frame_snapshot st (R.with_queue st rest) (R.frame_owner fr :: B.suspended_owners k)).
    { eapply B.snapshot_pop; [destruct (R.queue st); inversion Hpop; reflexivity |].
      apply B.child_distinct with (order := R.ranking st); auto. }
    constructor; split; [split; [reflexivity |reflexivity] |move_parents Hsnapshot Hlive Hstack].
  - destruct Hobs as [[Hempty ->] Hstack]; constructor; split; [apply reset_cursor; exact Hempty |].
    move_stack (@clear_snapshot st (R.frame_owner fr) (B.suspended_owners k) (B.parent_distinct Hunique)) Hlive Hstack.
Qed.

Lemma continued_queue st fr direct target rest k changed x : In x (R.queue st) ->
  In x (R.queue (R.cfg_state (R.continue_dead st fr direct target rest k changed))).
Proof.
  unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; intro H;
    [exact H |apply B.insert_members; auto |exact H].
Qed.
Lemma clear_queue_origin st owner x : In x (R.queue st) ->
  In x (R.queue (N.clear_owner st owner)) \/ x = owner.
Proof. intro H; destruct (V.eq_dec x owner); auto; left; apply clear_members; auto. Qed.
Lemma next_queue_covered tf before after : step tf before after -> forall x,
  In x (R.queue (R.cfg_state before)) ->
  In x (R.queue (R.cfg_state after)) \/ In x (B.active_owners (R.cfg_control after)).
Proof.
  intro Hstep; apply step_view in Hstep; destruct Hstep;
    unfold B.configuration, N.suspend_commit, N.retry_current in *;
    cbn -[R.materialize N.clear_owner N.publish N.requeue_source R.continue_dead R.observe] in *;
    intros x Hx.
  - eapply B.next_queue_covered; eauto.
  - destruct (clear_queue_origin st owner x Hx) as [Hq | ->];
      [left; rewrite B.materialize_queue; exact Hq |right; left; reflexivity].
  - left; rewrite B.observe_queue; exact Hx.
  - left; apply publish_keeps_queue; exact Hx.
  - left; apply continued_queue, requeue_keeps_queue; rewrite (B.write_queue H); exact Hx.
  - destruct (pending_spec H) as [_ [Hpop _]];
      destruct (@B.popped_members (R.queue st) target rest x Hpop Hx) as [->|Hin];
      [right; left; reflexivity |left; exact Hin].
  - destruct (clear_queue_origin st (R.frame_owner fr) x Hx) as [Hq | ->];
      [left; exact Hq |right; left; reflexivity].
  - destruct (pending_spec H) as [_ [Hpop _]];
      destruct (@B.popped_members (R.queue st) target rest x Hpop Hx) as [->|Hin];
      [right; left; reflexivity |left; exact Hin].
  - destruct (clear_queue_origin st (R.frame_owner fr) x Hx) as [Hq | ->];
      [left; exact Hq |right; left; reflexivity].
Qed.
Lemma next_idle_origin tf before after : step tf before after -> forall owner,
  B.idle after owner -> B.idle before owner \/ B.closing before after owner.
Proof.
  intros Hstep owner [Hq Ha].
  assert (Hbeforeq : ~ In owner (R.queue (R.cfg_state before))).
  { intro Hin; destruct (@next_queue_covered tf before after Hstep owner Hin); contradiction. }
  destruct (in_dec V.eq_dec owner (B.active_owners (R.cfg_control before))) as [Hin|Hnot]; [|left; split; assumption].
  destruct (@active_forward tf before after Hstep owner Hin) as [Hafter|Hclosed]; [contradiction |right; exact Hclosed].
Qed.

Lemma next_drained_origin tf before after : step tf before after -> forall owner,
  In owner (B.drained_owners (R.cfg_control after)) ->
  In owner (B.drained_owners (R.cfg_control before)) \/ B.committing before owner.
Proof.
  intro Hstep; apply step_view in Hstep; destruct Hstep; try solve [eapply B.next_drained_origin; eauto].
  all: try (unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold B.configuration, N.suspend_commit, N.retry_current;
    cbn [R.cfg_control B.drained_owners B.drained_stack]; intros query Hin; left; exact Hin.
Qed.
Lemma next_drained_wakeup tf before after : NoDup (B.active_owners (R.cfg_control after)) ->
  step tf before after -> forall owner, In owner (R.queue (R.cfg_state before)) ->
  In owner (B.drained_owners (R.cfg_control after)) -> In owner (R.queue (R.cfg_state after)).
Proof.
  intros Hunique Hstep; apply step_view in Hstep; destruct Hstep;
    unfold B.configuration, N.suspend_commit, N.retry_current in *;
    cbn -[R.materialize N.clear_owner N.publish N.requeue_source R.continue_dead R.observe] in *;
    intros query Hq Hd.
  - eapply B.next_drained_wakeup; eauto.
  - rewrite B.materialize_queue; apply clear_members; split; [exact Hq |].
    intro Heq; subst query; inversion Hunique as [|head parents Hnot Hrest]; subst; apply Hnot; apply B.drained_parent; exact Hd.
  - rewrite B.observe_queue; exact Hq.
  - apply publish_keeps_queue; exact Hq.
  - apply continued_queue, requeue_keeps_queue; rewrite (B.write_queue H); exact Hq.
  - destruct (pending_spec H) as [_ [Hpop _]].
    destruct (@B.popped_members (R.queue st) target rest query Hpop Hq) as [Heq|Hin]; [|exact Hin].
    subst query; inversion Hunique as [|head parents Hnot Hrest]; subst; exfalso; apply Hnot; right; apply B.drained_parent; exact Hd.
  - apply clear_members; split; [exact Hq |].
    intro Heq; subst query; inversion Hunique as [|head parents Hnot Hrest]; subst; apply Hnot; apply B.drained_parent; exact Hd.
  - destruct (pending_spec H) as [_ [Hpop _]].
    destruct (@B.popped_members (R.queue st) target rest query Hpop Hq) as [Heq|Hin]; [|exact Hin].
    subst query; inversion Hunique as [|head parents Hnot Hrest]; subst; exfalso; apply Hnot; right; apply B.drained_parent; exact Hd.
  - apply clear_members; split; [exact Hq |].
    intro Heq; subst query; inversion Hunique as [|head parents Hnot Hrest]; subst; apply Hnot; apply B.drained_parent; exact Hd.
Qed.
Lemma next_incoming_origin tf before after : NoDup (B.active_owners (R.cfg_control after)) ->
  step tf before after -> forall owner, B.incoming_ready after owner ->
  B.incoming_ready before owner \/ B.committing before owner.
Proof.
  intros Hunique Hstep owner [Hq [Ha|Hd]].
  - destruct (@next_idle_origin tf before after Hstep owner (conj Hq Ha)) as [[Hbeforeq Hbeforea]|Hclose].
    + left; split; auto.
    + left; split.
      * intro Hin; destruct (@next_queue_covered tf before after Hstep owner Hin); contradiction.
      * right; destruct Hclose as [fr [k [Hctrl [Hreturn ->]]]]; rewrite Hctrl; left; reflexivity.
  - destruct (@next_drained_origin tf before after Hstep owner Hd) as [Hbefore|Hcommit]; [|auto].
    left; split; [|right; exact Hbefore]. intro Hin; apply Hq; eapply next_drained_wakeup; eauto.
Qed.

Lemma finish_bound before after fr target changed owner :
  D.leq (R.aggregate after owner) (R.sigma_value after owner) = true ->
  D.leq (R.aggregate (N.finish_write before after fr target changed) owner)
    (R.sigma_value (N.finish_write before after fr target changed) owner) = true.
Proof. unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; auto. Qed.
Lemma publication_incoming targets st fr owner : ~ In owner (R.queue (N.publish targets st fr)) ->
  D.leq (R.aggregate st owner) (R.sigma_value st owner) = true ->
  D.leq (R.aggregate (N.publish targets st fr) owner) (R.sigma_value (N.publish targets st fr) owner) = true.
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hquiet Hbound; cbn -[R.write_side_contribution N.finish_write] in Hquiet |- *; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH; [exact Hquiet |]. apply finish_bound.
  eapply B.write_preserves_incoming; [exact Hw |exact Hbound |].
  intros Hchanged Heq; subst owner changed; apply Hquiet, publish_keeps_queue.
  unfold N.finish_write; apply B.insert_members; auto.
Qed.
Lemma continued_ready_target st fr direct target rest k owner :
  NoDup (B.active_owners (R.cfg_control (R.continue_dead st fr direct target rest k true))) ->
  B.incoming_ready (R.continue_dead st fr direct target rest k true) owner -> owner <> target.
Proof.
  unfold R.continue_dead; destruct (_ && _)%bool.
  - intros Hunique Hready; exact (@B.starting_not_ready st target (R.KDead fr direct rest k) owner Hunique Hready).
  - intros _ [Hq _] Heq; subst owner; apply Hq, B.insert_members; auto.
Qed.
Theorem next_incoming_bound tf before after owner : NoDup (B.active_owners (R.cfg_control after)) ->
  step tf before after -> B.incoming_ready after owner ->
  D.leq (R.aggregate (R.cfg_state before) owner) (R.sigma_value (R.cfg_state before) owner) = true ->
  D.leq (R.aggregate (R.cfg_state after) owner) (R.sigma_value (R.cfg_state after) owner) = true.
Proof.
  intros Hunique Hstep Hready Hbound; apply step_view in Hstep; destruct Hstep.
  - eapply B.next_incoming_bound; eauto.
  - change (D.leq (R.aggregate (R.materialize (N.clear_owner st owner0) owner0) owner)
      (R.sigma_value (R.materialize (N.clear_owner st owner0) owner0) owner) = true).
    rewrite B.aggregate_materialize, B.materialize_sigma_value; exact Hbound.
  - change (D.leq (R.aggregate (R.observe st target) owner) (R.sigma_value (R.observe st target) owner) = true).
    rewrite B.aggregate_observe, B.value_observe; exact Hbound.
  - apply publication_incoming; [exact (proj1 Hready) |exact Hbound].
  - assert (Hnext : D.leq (R.aggregate next owner) (R.sigma_value next owner) = true).
    { eapply B.write_preserves_incoming; [exact H |exact Hbound |].
      intro Hchanged; subst changed; eapply continued_ready_target; eauto. }
    unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |];
      unfold N.requeue_source; destruct N.cell_changed; exact Hnext.
  - exact Hbound.
  - exact Hbound.
  - exact Hbound.
  - exact Hbound.
Qed.
Lemma active_parent_not_ready st child fr body k :
  NoDup (child :: R.frame_owner fr :: B.suspended_owners k) ->
  ~ B.incoming_ready (B.configuration st (R.StartEpisode child (R.KAfterSide fr body k))) (R.frame_owner fr).
Proof.
  intros Hunique [_ [Hidle|Hd]].
  - apply Hidle; right; left; reflexivity.
  - inversion Hunique as [|? ? _ Htail]; subst; inversion Htail as [|? ? Hnot _]; subst.
    apply Hnot, B.drained_parent; exact Hd.
Qed.

Theorem next_incoming_safe tf before after : NoDup (B.active_owners (R.cfg_control after)) ->
  B.incoming_safe before -> step tf before after -> B.incoming_safe after.
Proof.
  intros Hunique Hsafe Hstep owner Hready.
  destruct (@next_incoming_origin tf before after Hunique Hstep owner Hready) as [Hbefore|Hcommit].
  - eapply next_incoming_bound; [exact Hunique |exact Hstep |exact Hready |apply Hsafe; exact Hbefore].
  - apply step_view in Hstep; destruct Hstep;
      destruct Hcommit as [commit_fr [commit_direct [commit_k [Hctrl ->]]]];
      cbn [B.configuration R.cfg_control] in Hctrl; try discriminate.
    + eapply B.next_commit_incoming; [exact H |eexists; eexists; eexists; split; [exact Hctrl |reflexivity]].
    + inversion Hctrl; subst commit_fr commit_direct commit_k; exfalso.
      eapply active_parent_not_ready; [exact Hunique |exact Hready].
    + inversion Hctrl; subst commit_fr commit_direct commit_k; exfalso.
      exact (@B.starting_not_ready (R.cfg_state (N.retry_current tf st fr k))
        (R.frame_owner fr) k (R.frame_owner fr) Hunique Hready eq_refl).
Qed.

Lemma next_waiting_control tf before after : B.frames_live before -> B.waiting_control before ->
  step tf before after -> B.waiting_control after.
Proof.
  intros Hframes Hwaiting Hstep; pose proof (@live_forward tf before after Hframes Hstep) as Hlive.
  apply step_view in Hstep; destruct Hstep; try solve [eapply B.next_waiting_control; eauto].
  all: try (unfold R.continue_dead in Hlive |- *; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold B.waiting_control in Hwaiting |- *;
    unfold B.configuration, N.suspend_commit, N.retry_current in *;
    cbn [R.cfg_control B.waiting_stack] in Hwaiting |- *;
    eapply B.waiting_lift; [exact Hlive |exact Hwaiting].
Qed.
Lemma next_solved_origin tf before after : B.frames_live before -> B.waiting_control before ->
  step tf before after -> forall owner, B.solved (R.cfg_state after) owner ->
  B.solved (R.cfg_state before) owner \/ In owner (R.queue (R.cfg_state after)) \/
    In owner (B.active_owners (R.cfg_control after)).
Proof.
  intros Hframes Hwaiting Hstep; apply step_view in Hstep; destruct Hstep; intros query Hsolved.
  - eapply B.next_solved_origin; eauto.
  - apply B.solved_materialize_back in Hsolved; destruct Hsolved as [Hsolved | ->];
      [left; exact Hsolved |right; right; left; reflexivity].
  - left; eapply B.solved_layout_back; [apply B.observe_sigma |exact Hsolved].
  - left; eapply B.solved_layout_back; [exact (proj1 (publish_layout (S.elements (R.frame_current_targets fr)) st fr)) |exact Hsolved].
  - left; eapply B.solved_layout_back; [|exact Hsolved].
    unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; cbn;
      rewrite requeue_sigma; exact (proj1 (proj2 (proj2 (B.write_layout H)))).
  - left; exact Hsolved.
  - left; exact Hsolved.
  - left; exact Hsolved.
  - left; exact Hsolved.
Qed.
Lemma next_idle_snapshot tf before after owner : step tf before after ->
  B.idle before owner -> B.idle after owner -> B.frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  intros Hstep [Hqbefore Habefore] [Hqafter Haafter]; apply step_view in Hstep; destruct Hstep.
  - eapply B.next_idle_snapshot; [exact H |split; assumption |split; assumption].
  - eapply B.snapshot_compose; [apply clear_snapshot |apply B.snapshot_materialize].
    intros x [<-|Hin]; [intro Heq; apply Habefore; subst owner; left; reflexivity |contradiction].
  - apply B.snapshot_observe.
  - eapply B.snapshot_compose; [apply publication_snapshot |apply B.snapshot_publish].
    intros x [<-|Hin]; [intro Heq; apply Habefore; rewrite Heq; left; reflexivity |contradiction].
  - eapply B.snapshot_compose; [eapply B.snapshot_side_write; [exact H |] |].
    + intros x [<-|Hin]; [intro Heq; apply Habefore; rewrite Heq; left; reflexivity |contradiction].
    + eapply B.snapshot_compose; [apply requeue_snapshot |apply continue_dead_snapshot].
  - destruct (pending_spec H) as [_ [Hpop _]]. eapply B.snapshot_pop.
    + destruct (R.queue st); inversion Hpop; reflexivity.
    + intros x [<-|Hin]; [intro Heq; apply Haafter; subst owner; left; reflexivity |contradiction].
  - apply clear_snapshot; intros x [<-|Hin]; [intro Heq; apply Habefore; rewrite Heq; left; reflexivity |contradiction].
  - destruct (pending_spec H) as [_ [Hpop _]]. eapply B.snapshot_pop.
    + destruct (R.queue st); inversion Hpop; reflexivity.
    + intros x [<-|Hin]; [intro Heq; apply Haafter; subst owner; left; reflexivity |contradiction].
  - apply clear_snapshot; intros x [<-|Hin]; [intro Heq; apply Habefore; rewrite Heq; left; reflexivity |contradiction].
Qed.
Lemma closing_snapshot tf before after owner : step tf before after -> B.closing before after owner ->
  B.frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  intros Hstep [fr [k [Hctrl [Hafter Heq]]]]; apply step_view in Hstep; destruct Hstep;
    cbn [B.configuration R.cfg_control] in Hctrl; try discriminate.
  unfold B.step, R.next_config in H; rewrite Hctrl in H.
  destruct (R.queue_peek (R.queue (R.cfg_state before))) as [head|];
    [destruct (V.eq_dec head (R.frame_owner fr));
      [destruct (R.queue_pop (R.queue (R.cfg_state before))) as [[popped rest]|]; inversion H; subst; discriminate |]
      |].
  - destruct (R.rank_lt (R.cfg_state before) (R.frame_owner fr) head);
      [destruct (R.queue_pop (R.queue (R.cfg_state before))) as [[popped rest]|]; inversion H; subst; discriminate |].
    inversion H; subst; apply B.snapshot_close.
  - inversion H; subst; apply B.snapshot_close.
Qed.
Theorem next_settled_store tf before after : B.frames_live before -> B.waiting_control before ->
  inhabited (observing_control tf before) -> B.settled_store tf before -> step tf before after -> B.settled_store tf after.
Proof.
  intros Hframes Hwaiting [Hobs] Hsettled Hstep owner Hsolved Hidle.
  destruct (@next_idle_origin tf before after Hstep owner Hidle) as [Hbefore|Hclose].
  - destruct (@next_solved_origin tf before after Hframes Hwaiting Hstep owner Hsolved) as [Hold|[Hq|Ha]];
      [|exfalso; exact (proj1 Hidle Hq) |exfalso; exact (proj2 Hidle Ha)].
    destruct (Hsettled owner Hold Hbefore) as [Hdone]; constructor.
    eapply B.completed_moved; [eapply next_idle_snapshot; eauto |eapply next_preserves_live; exact Hstep |exact (proj1 Hidle) |exact Hdone].
  - destruct Hclose as [fr [k [Hctrl [Hreturn ->]]]].
    unfold observing_control in Hobs; rewrite Hctrl in Hobs; destruct Hobs as [Hguard Hstack].
    assert (Hdone : B.completed_observation tf (R.cfg_state before) (R.frame_owner fr)).
    { eapply B.guarded_complete; [| |exact Hguard].
      - eapply B.live_reference_solved; [exact Hframes |rewrite Hctrl; reflexivity].
      - intro Hin; destruct (@next_queue_covered tf before after Hstep (R.frame_owner fr) Hin);
          [exact (proj1 Hidle H) |exact (proj2 Hidle H)]. }
    constructor; eapply B.completed_moved;
      [eapply closing_snapshot; [exact Hstep |eexists; eexists; split; [exact Hctrl |split; [exact Hreturn |reflexivity]]]
        |eapply next_preserves_live; exact Hstep |exact (proj1 Hidle) |exact Hdone].
Qed.
(** One invariant joins the evaluation certificate with quiet completed owners. *)
Record semantic_invariant tf c : Prop := {
  invariant_frames : B.frames_live c;
  invariant_waiting : B.waiting_control c;
  invariant_observing : inhabited (observing_control tf c);
  invariant_settled : B.settled_store tf c;
  invariant_incoming : B.incoming_safe c
}.
Lemma semantic_initial tf roots : semantic_invariant tf (R.initial_config roots).
Proof.
  pose proof (B.semantic_initial tf roots) as Hb; constructor.
  - exact (B.invariant_frames Hb).
  - exact (B.invariant_waiting Hb).
  - constructor; exact tt.
  - exact (B.invariant_settled Hb).
  - exact (B.invariant_incoming Hb).
Qed.
Theorem reachable_semantic_invariant tf roots c : reachable tf roots c -> semantic_invariant tf c.
Proof.
  intro Hpath.
  assert (Hwf : B.config_wf (fun _ => True) (R.initial_config roots)) by
    (split; [apply B.store_initial |apply Forall_forall; auto]).
  assert (Ho : B.active_ordered (R.initial_config roots)) by constructor.
  pose proof (semantic_initial tf roots) as Hinitial.
  revert Hwf Ho Hinitial; induction Hpath; auto; intros Hwf Ho [Hframes Hwaiting Hobs Hsettled Hincoming].
  assert (Hnext : B.active_ordered next) by (eapply next_active_ordered; eauto).
  apply IHHpath; [eapply next_configuration_wf; [intros; apply B.code_unrestricted |exact Hwf |exact H] |exact Hnext |].
  constructor; eauto using next_frames_live, next_waiting_control, next_observing_control, next_settled_store.
  eapply next_incoming_safe; [eapply B.ordered_unique; exact Hnext |exact Hincoming |exact H].
Qed.
Lemma next_work_covered tf before after : B.frames_live before -> step tf before after -> forall x,
  In x (B.active_owners (R.cfg_control before)) \/ In x (B.pending_roots (R.cfg_control before)) ->
  B.solved (R.cfg_state after) x \/ In x (B.active_owners (R.cfg_control after)) \/
    In x (B.pending_roots (R.cfg_control after)).
Proof.
  intros Hframes Hstep; apply step_view in Hstep; destruct Hstep.
  all: try solve [eapply B.next_work_covered; eauto].
  all: try (unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold B.configuration, N.suspend_commit, N.retry_current;
    cbn [R.cfg_state R.cfg_control B.active_owners B.suspended_owners B.pending_roots B.suspended_roots
      R.frame_owner R.fresh_frame R.with_frame_side]; intros x Hin; intuition auto.
  all: right; left; right; assumption.
Qed.
Theorem reachable_roots_covered tf roots c : reachable tf roots c -> B.covered_roots roots c.
Proof.
  intro Hpath.
  assert (Hinitial : B.covered_roots roots (R.initial_config roots)) by (intros x Hx; auto).
  assert (Hframes : B.frames_live (R.initial_config roots)) by constructor.
  revert Hinitial Hframes; induction Hpath; auto; intros Hroots Hframes; apply IHHpath.
  - intros x Hx; destruct (Hroots x Hx) as [Hs|[Hq|[Ha|Hp]]].
    + left; eapply next_preserves_live; eauto.
    + destruct (@next_queue_covered tf before next H x Hq); auto.
    + destruct (@next_work_covered tf before next Hframes H x (or_introl Ha)) as [Hs'|[Ha'|Hp']]; auto.
    + destruct (@next_work_covered tf before next Hframes H x (or_intror Hp)) as [Hs'|[Ha'|Hp']]; auto.
  - eapply next_frames_live; eauto.
Qed.
Theorem successful_roots_materialized fuel tf roots final : N.solve_fuel fuel tf roots = Some final ->
  forall x, In x roots -> B.solved final x.
Proof.
  intro Hrun; destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  pose proof (reachable_roots_covered Hpath) as Hroots; intros x Hx.
  destruct (Hroots x Hx) as [Hs|[Hq|[Ha|Hp]]]; [exact Hs | |contradiction |contradiction].
  change (In x (R.queue final)) in Hq; rewrite Hquiet in Hq; contradiction.
Qed.
Theorem successful_run_correct fuel tf roots final :
  N.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
Proof.
  intro Hrun; split; [eapply successful_roots_materialized; exact Hrun |].
  destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
  pose proof (reachable_semantic_invariant Hpath) as Hsem.
  assert (Hidle : forall owner, B.idle (B.terminal final) owner).
  { intro owner; split; [change (~ In owner (R.queue final)); rewrite Hquiet; auto |cbn; auto]. }
  intros owner Hsolved; destruct (invariant_settled Hsem Hsolved (Hidle owner)) as [Hdone].
  apply (B.completed_is_post_solution Hdone); intros target raw Hin.
  apply (invariant_incoming Hsem); split; [exact (proj1 (Hidle target)) |left; exact (proj2 (Hidle target))].
Qed.
Section UpperBounds.
Variable update_bounded : forall side x phase old input upper,
  D.leq old upper = true -> D.leq input upper = true ->
  D.leq (snd (U.update side x phase old input)) upper = true.
Lemma requeue_bounded upper before after source target : B.bounded_state upper after ->
  B.bounded_state upper (N.requeue_source before after source target).
Proof. unfold N.requeue_source; destruct N.cell_changed; auto using B.bound_enqueue. Qed.
Lemma finish_bounded upper before after fr target changed : B.bounded_state upper after ->
  B.bounded_state upper (N.finish_write before after fr target changed).
Proof. unfold N.finish_write; destruct changed; auto using requeue_bounded, B.bound_enqueue. Qed.
Lemma publication_bounded upper targets st fr : B.bounded_state upper st -> B.bounded_frame upper fr ->
  B.bounded_state upper (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hst Hfr; cbn -[R.write_side_contribution N.finish_write]; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH; [apply finish_bounded |exact Hfr].
  eapply B.bound_write; [exact update_bounded |exact Hst | |exact Hw].
  destruct (M.lookup (R.frame_local_side fr) target) eqn:Hinput;
    [eapply Hfr; exact Hinput |apply DL.bottom_least].
Qed.
Theorem next_configuration_bounded tf support upper before after :
  (forall owner, In owner support -> B.bounded_rhs upper owner (tf owner)) ->
  B.config_wf (fun x => In x support) before -> B.bounded_config upper before ->
  step tf before after -> B.bounded_config upper after.
Proof.
  intros Hcodes Hwf [Hst Hctrl] Hstep; apply step_view in Hstep; destruct Hstep.
  - eapply B.next_configuration_bounded; eauto; split; eauto.
  - eapply B.next_configuration_bounded; [exact update_bounded |exact Hcodes |apply clear_config; exact Hwf | |reflexivity].
    split; [apply B.bound_queue; exact Hst |exact Hctrl].
  - destruct Hctrl as [Hfr [Hbody Hk]].
    inversion Hbody; subst; split; [apply B.bound_observe; exact Hst |].
    cbn [B.bounded_control B.configuration R.cfg_control]; split.
    + apply B.bound_frame_side; [exact Hfr |apply B.bound_accumulated; auto].
    + auto.
  - destruct Hctrl as [Hfr [Hdirect Hk]]; split.
    + apply B.bound_publish, publication_bounded; assumption.
    + exact (conj Hfr (conj Hdirect Hk)).
  - destruct Hctrl as [Hfr [Hdirect Hk]].
    eapply B.bound_continue_dead; [apply requeue_bounded |exact Hfr |exact Hdirect |exact Hk].
    eapply B.bound_write; [exact update_bounded |exact Hst |apply DL.bottom_least |exact H].
  - destruct Hctrl as [Hfr [Hdirect Hk]].
    unfold B.bounded_config, N.suspend_commit; cbn [R.cfg_control R.cfg_state B.bounded_control B.bounded_stack]; split.
    + apply B.bound_queue; exact Hst.
    + split; [apply B.bound_frame_fresh |split; [apply Hcodes |exact Hk]].
      exact (proj1 (B.ref_owner (proj1 (proj2 Hwf)))).
  - destruct Hctrl as [Hfr [Hdirect Hk]].
    unfold B.bounded_config, N.retry_current; cbn [R.cfg_control R.cfg_state B.bounded_control]; split.
    + apply B.bound_queue; exact Hst.
    + split; [apply B.bound_frame_fresh |split; [apply Hcodes |exact Hk]].
      exact (proj1 (B.ref_owner (proj1 (proj2 Hwf)))).
  - destruct Hctrl as [Hfr [Hbody Hk]].
    unfold B.bounded_config, N.suspend_commit; cbn [R.cfg_control R.cfg_state B.bounded_control B.bounded_stack]; split.
    + apply B.bound_queue; exact Hst.
    + split; [apply B.bound_frame_fresh |split; [apply Hcodes |exact Hk]].
      exact (proj1 (B.ref_owner (proj1 (proj2 Hwf)))).
  - split; [apply B.bound_queue; exact Hst |exact Hctrl].
Qed.
Theorem reachable_configuration_bounded tf roots (finite : Sem.finite_system tf roots) upper c :
  Sem.system_monotone_on tf (Sem.support finite) -> Sem.post_solution_on tf (Sem.support finite) upper ->
  reachable tf roots c -> B.bounded_config upper c.
Proof.
  intros Hmono Hupper Hpath.
  assert (Hcodes : forall owner, In owner (Sem.support finite) -> B.bounded_rhs upper owner (tf owner))
    by (intros; eapply B.monotone_code_bounded; eauto).
  assert (Hinitial : B.bounded_config upper (R.initial_config roots)) by (split; [apply B.bound_empty |exact I]).
  assert (Hwf : B.config_wf (fun x => In x (Sem.support finite)) (R.initial_config roots)) by
    (eapply reachable_configuration_wf; constructor).
  revert Hinitial Hwf; induction Hpath; auto; intros Hb Hwf; apply IHHpath.
  - eapply next_configuration_bounded; eauto.
  - eapply next_configuration_wf; [intros; apply Sem.system_supported; assumption |exact Hwf |exact H].
Qed.
Theorem successful_run_least fuel tf roots (finite : Sem.finite_system tf roots) final :
  B.source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  N.solve_fuel fuel tf roots = Some final -> Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hstrict Hmono Hrun; split.
  - eapply B.correct_source_strict_solution; [exact Hstrict |eapply successful_run_correct; exact Hrun].
  - intros upper Hupper owner Hin.
    destruct (@successful_path fuel tf roots final Hrun) as [Hpath Hquiet].
    destruct (@reachable_configuration_bounded tf roots finite upper (B.terminal final) Hmono Hupper Hpath) as [Hb _].
    exact (B.bounded_sigma Hb owner).
Qed.
End UpperBounds.
(** Termination uses only the local core's state certificates and update credit. *)
Definition episode_complete tf start owner k := exists final,
  steps tf start (B.configuration final (R.Return k)) /\ B.queue_below final owner.
Lemma reachable_advance tf roots before after : reachable tf roots before -> step tf before after -> reachable tf roots after.
Proof. intros; eapply steps_snoc; eauto. Qed.
Lemma reachable_follow tf roots before after : reachable tf roots before -> steps tf before after -> reachable tf roots after.
Proof. intros; eapply steps_append; eauto. Qed.
Lemma steps_ranking_extends tf before after : steps tf before after ->
  B.extends (R.ranking (R.cfg_state before)) (R.ranking (R.cfg_state after)).
Proof. intro Hpath; induction Hpath; [apply B.extends_refl |eapply B.extends_trans; [eapply next_ranking_extends; exact H |exact IHHpath]]. Qed.
Lemma next_generated tf support before after : B.config_wf (fun x => In x support) before ->
  RF.generated support (R.ranking (R.cfg_state before)) -> step tf before after ->
  RF.generated support (R.ranking (R.cfg_state after)).
Proof.
  intros Hwf Hg Hstep; apply step_view in Hstep; destruct Hstep.
  - eapply B.next_generated; eauto.
  - cbn; rewrite B.materialize_rank; exact Hg.
  - apply B.generated_observe; [exact Hg |].
    exact (proj1 (B.code_child_supported (proj1 (proj2 (proj2 Hwf))))).
  - cbn; rewrite publish_rank; exact Hg.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; cbn;
      rewrite requeue_rank, (B.write_rank H); exact Hg.
  - exact Hg.
  - exact Hg.
  - exact Hg.
  - exact Hg.
Qed.
Theorem reachable_generated tf roots (finite : Sem.finite_system tf roots) c :
  reachable tf roots c -> RF.generated (Sem.support finite) (R.ranking (R.cfg_state c)).
Proof.
  intro Hpath.
  assert (Hwf : B.config_wf (fun x => In x (Sem.support finite)) (R.initial_config roots)) by
    (eapply reachable_configuration_wf; constructor).
  assert (Hg : RF.generated (Sem.support finite) (R.ranking (R.cfg_state (R.initial_config roots)))) by apply RF.generated_empty.
  revert Hwf Hg; induction Hpath; auto; intros Hwf Hg; apply IHHpath.
  - eapply next_configuration_wf; [intros; apply Sem.system_supported; assumption |exact Hwf |exact H].
  - eapply next_generated; eauto.
Qed.
Theorem reachable_rank_bound tf roots (finite : Sem.finite_system tf roots) c owner rank :
  reachable tf roots c -> Ranks.lookup (R.ranking (R.cfg_state c)) owner = Some rank -> rank < RF.bound (Sem.support finite).
Proof.
  intros Hreach Hrank; eapply RF.generated_lookup_bound; [exact (B.store_valid (proj1 (@reachable_configuration_wf tf roots finite c Hreach))) |eapply reachable_generated; exact Hreach |exact Hrank].
Qed.
Lemma requeue_forward before after source target : B.forward_readers after ->
  B.forward_readers (N.requeue_source before after source target).
Proof. unfold N.requeue_source; destruct N.cell_changed; auto. Qed.
Lemma finish_forward before after fr target changed : B.forward_readers after ->
  B.forward_readers (N.finish_write before after fr target changed).
Proof. intro Hread; unfold N.finish_write; destruct changed; apply requeue_forward; exact Hread. Qed.
Lemma publication_forward targets st fr : B.forward_readers st -> B.forward_readers (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hst; cbn -[R.write_side_contribution N.finish_write]; auto.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH, finish_forward; eapply B.forward_readers_write; eauto.
Qed.
Lemma next_forward_readers tf before after : B.forward_readers (R.cfg_state before) ->
  step tf before after -> B.forward_readers (R.cfg_state after).
Proof.
  intros Hread Hstep; apply step_view in Hstep; destruct Hstep.
  - eapply B.next_forward_readers; eauto.
  - eapply B.next_forward_readers with (before := B.configuration (N.clear_owner st owner) (R.StartEpisode owner k)); [exact Hread |reflexivity].
  - apply B.forward_readers_observe; exact Hread.
  - apply publication_forward; exact Hread.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; apply requeue_forward;
      eapply B.forward_readers_write; eauto.
  - exact Hread.
  - exact Hread.
  - exact Hread.
  - exact Hread.
Qed.
Theorem reachable_forward_readers tf roots c : reachable tf roots c -> B.forward_readers (R.cfg_state c).
Proof.
  intro Hpath; assert (Hinitial : B.forward_readers (R.cfg_state (R.initial_config roots))).
  { intros target reader Hmem; unfold R.lookup_set in Hmem; cbn in Hmem;
      rewrite ML.lookup_empty, SL.empty_spec in Hmem; discriminate. }
  revert Hinitial; induction Hpath; auto; intros Hr; apply IHHpath; eapply next_forward_readers; eauto.
Qed.
Lemma requeue_budget support before after source target owner phase :
  B.round_budget support (N.requeue_source before after source target) owner phase = B.round_budget support after owner phase.
Proof. unfold N.requeue_source; destruct N.cell_changed; reflexivity. Qed.
Lemma finish_budget support before after fr target changed owner phase :
  B.round_budget support (N.finish_write before after fr target changed) owner phase = B.round_budget support after owner phase.
Proof. unfold N.finish_write; destruct changed; apply requeue_budget. Qed.
Lemma publication_budget support targets st fr owner phase :
  B.budget_le (B.round_budget support (N.publish targets st fr) owner phase) (B.round_budget support st owner phase).
Proof.
  revert st; induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution N.finish_write]; [left; reflexivity |].
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  eapply B.budget_le_trans; [apply IH |rewrite finish_budget; eapply B.budget_write; exact Hw].
Qed.
Lemma publication_budget_layout support targets st fr owner phase :
  B.round_budget support (R.publish_targets (N.publish targets st fr) fr) owner phase =
  B.round_budget support (N.publish targets st fr) owner phase.
Proof. apply B.budget_layout; reflexivity. Qed.
Lemma next_lower_phase tf before after owner phase : B.active_ordered before ->
  B.larger_active (R.cfg_state before) (R.cfg_control before) owner ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> step tf before after ->
  B.owner_phase (R.cfg_control after) owner = Some phase.
Proof.
  intros Horder Hlarger Hphase Hstep; apply step_view in Hstep; destruct Hstep.
  all: try solve [eapply B.core_lower_phase; eauto].
  all: unfold B.active_ordered in Horder; unfold B.configuration in *;
    cbn [R.cfg_state R.cfg_control B.active_owners] in *.
  all: try match type of Horder with B.ordered _ (?head :: ?rest) =>
    assert (Hneq : owner <> head) by (eapply B.higher_not_equal; eapply B.larger_below_head; eauto)
  end.
  all: unfold R.continue_dead, N.suspend_commit, N.retry_current;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [R.cfg_control B.owner_phase B.stack_phase R.frame_owner R.frame_phase R.fresh_frame R.with_frame_side] in *;
    try (destruct (V.eq_dec owner owner0); [contradiction |]);
    try (destruct (V.eq_dec owner (R.frame_owner fr)); [contradiction |]);
    try exact Hphase.
  all: destruct (V.eq_dec owner owner0); [contradiction |exact Hphase].
Qed.
Lemma next_budget_below tf support before after owner phase : B.active_ordered before ->
  B.scoped_config before -> B.larger_active (R.cfg_state before) (R.cfg_control before) owner ->
  step tf before after -> B.budget_le (B.round_budget support (R.cfg_state after) owner phase)
    (B.round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Horder Hscoped Hlarger Hstep; apply step_view in Hstep; destruct Hstep; cbn [B.configuration R.cfg_state].
  - eapply B.core_budget_below; eauto.
  - exact (@B.budget_materialize support (N.clear_owner st owner0) owner0 owner phase).
  - left; apply B.budget_observe.
  - rewrite publication_budget_layout; apply publication_budget.
  - unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; cbn -[N.requeue_source R.enqueue B.round_budget];
      try rewrite B.budget_enqueue; rewrite requeue_budget; eapply B.budget_write; exact H.
  - left; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
Qed.
Lemma phase_origin tf before after owner phase next_phase : B.active_ordered before ->
  transition tf before after ->
  B.owner_phase (R.cfg_control before) owner = Some phase ->
  B.owner_phase (R.cfg_control after) owner = Some next_phase -> B.step tf before after \/ phase = next_phase.
Proof.
  intros Horder Hview Hphase Hnext; destruct Hview.
  all: try solve [left; assumption].
  all: right.
  all: pose proof (B.ordered_unique Horder) as Hunique;
    unfold B.active_ordered, B.configuration in *;
    cbn [R.cfg_control R.cfg_state B.active_owners B.owner_phase] in *.
  all: try (unfold R.continue_dead in Hnext; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold N.suspend_commit, N.retry_current in Hnext;
    cbn [R.cfg_control B.owner_phase B.stack_phase R.frame_owner R.frame_phase R.fresh_frame R.with_frame_side] in Hnext.
  all: cbn [B.stack_phase] in Hphase.
  all: repeat match goal with H : context [if V.eq_dec ?x ?y then _ else _] |- _ =>
    destruct (V.eq_dec x y) as [Heq|Hneq]; try subst x end;
    try congruence.
  all: inversion Hunique as [|head parents Hnot Hdup]; subst;
    try solve [exfalso; apply Hnot; eapply B.stack_phase_present; eauto].
  all: inversion Hdup as [|head' parents' Hnot' Hdup']; subst;
    exfalso; apply Hnot'; eapply B.stack_phase_present; eauto.
Qed.
Theorem next_owner_budget tf roots support before after owner phase next_phase : reachable tf roots before ->
  B.owner_phase (R.cfg_control before) owner = Some phase ->
  B.owner_phase (R.cfg_control after) owner = Some next_phase -> step tf before after ->
  B.budget_le (B.round_budget support (R.cfg_state after) owner next_phase)
    (B.round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreach Hphase Hnext Hstep.
  pose proof (reachable_active_ordered Hreach) as Ho.
  pose proof (reachable_scoped_config Hreach) as Hscoped.
  destruct (@phase_origin tf before after owner phase next_phase Ho (step_view Hstep) Hphase Hnext) as [Hcore |Heq].
  - eapply B.core_owner_budget; eauto.
  - subst next_phase; apply step_view in Hstep; destruct Hstep; cbn [B.configuration R.cfg_state].
    + eapply B.core_owner_budget; eauto.
    + exact (@B.budget_materialize support (N.clear_owner st owner0) owner0 owner phase).
    + left; apply B.budget_observe.
    + rewrite publication_budget_layout; apply publication_budget.
    + unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; cbn -[N.requeue_source R.enqueue B.round_budget];
        try rewrite B.budget_enqueue; rewrite requeue_budget; eapply B.budget_write; exact H.
    + left; reflexivity.
    + left; reflexivity.
    + left; reflexivity.
    + left; reflexivity.
Qed.
(** Expose the native rule only at a concrete evaluation transition. Avoid a
    generic dispatch-equality proof that forces the kernel to normalize the
    entire machine for every control constructor. *)
Ltac machine_core :=
  unfold step, N.next_config, N.next_repaired, N.next_fresh, N.next_batched, N.next_precommit;
  cbn -[R.next_config].

Section Evaluation.
Variable tf : R.ConstraintSystem.system.
Variable roots : list V.t.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (B.configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (B.configuration st (R.StartEpisode child k)) child k.
Lemma dead_to_commit pending : forall st fr direct k,
  R.frame_owner fr = owner -> reachable tf roots (B.configuration st (R.RunDead fr direct pending k)) ->
  exists final, steps tf (B.configuration st (R.RunDead fr direct pending k))
    (B.configuration final (R.RunCommit fr direct k)).
Proof.
  induction pending as [|target rest IH]; intros st fr direct k Howner Hreach.
  - eexists; eapply steps_cons; [reflexivity |constructor].
  - destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
    + assert (Hstep : step tf (B.configuration st (R.RunDead fr direct (target::rest) k))
        (B.configuration st (R.RunDead fr direct rest k))).
      { unfold step, N.next_config, N.next_repaired; cbn; rewrite Hcurrent; reflexivity. }
      destruct (IH st fr direct k Howner (reachable_advance Hreach Hstep)) as [final Htail].
      exists final; eapply steps_cons; eauto.
    + destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
      set (repaired := N.requeue_source st next (R.frame_owner fr) target).
      assert (Hstep : step tf (B.configuration st (R.RunDead fr direct (target::rest) k))
        (R.continue_dead repaired fr direct target rest k changed)).
      { unfold step, N.next_config, N.next_repaired; cbn -[R.write_side_contribution]; rewrite Hcurrent, Hw; reflexivity. }
      pose proof (reachable_advance Hreach Hstep) as Hnext.
      unfold R.continue_dead in Hstep, Hnext.
      destruct changed; [destruct (R.rank_lt repaired (R.frame_owner fr) target && negb (R.is_materialized repaired target)) eqn:Hchild |].
      * apply andb_true_iff in Hchild; destruct Hchild as [Hhigher _]; rewrite Howner in Hhigher.
        destruct (higher_episodes Hnext Hhigher) as [returned [Hchildpath Hbelow]].
        assert (Hresume : step tf (B.configuration returned (R.Return (R.KDead fr direct rest k)))
          (B.configuration returned (R.RunDead fr direct rest k))) by reflexivity.
        destruct (IH returned fr direct k Howner (reachable_advance (reachable_follow Hnext Hchildpath) Hresume)) as [final Htail].
        exists final; eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hchildpath |eapply steps_cons; eauto]].
      * destruct (IH (R.enqueue repaired target) fr direct k Howner Hnext) as [final Htail].
        exists final; eapply steps_cons; eauto.
      * destruct (IH repaired fr direct k Howner Hnext) as [final Htail].
        exists final; eapply steps_cons; eauto.
Qed.
Lemma rhs_to_commit body : forall st fr k, R.frame_owner fr = owner ->
  reachable tf roots (B.configuration st (R.RunRhs fr body k)) ->
  exists final final_fr direct, R.frame_owner final_fr = owner /\
    steps tf (B.configuration st (R.RunRhs fr body k)) (B.configuration final (R.RunCommit final_fr direct k)).
Proof.
  induction body as [direct|target tail IH|target raw tail IH|target tail IH]; intros st fr k Howner Hreach.
  - assert (Hret : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Ret direct) k))
      (B.configuration st (R.RunDead fr direct (if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []) k))) by reflexivity.
    destruct (dead_to_commit Howner (reachable_advance Hreach Hret)) as [final Htail].
    exists final, fr, direct; split; [exact Howner |eapply steps_cons; eauto].
  - set (seen := R.observe st target).
    destruct (negb (R.is_materialized seen target) && R.rank_lt seen (R.frame_owner fr) target) eqn:Hcall.
    + assert (Hcallstep : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Get target tail) k))
        (B.configuration seen (R.StartEpisode target (R.KAfterGet fr target tail k)))).
      { machine_core; unfold B.step, R.next_config; cbn -[R.observe R.complete_get]; fold seen; rewrite Hcall; reflexivity. }
      pose proof (reachable_advance Hreach Hcallstep) as Hchild.
      apply andb_true_iff in Hcall; destruct Hcall as [_ Hhigher]; rewrite Howner in Hhigher.
      destruct (higher_episodes Hchild Hhigher) as [returned [Hepisode Hbelow]].
      destruct (R.complete_get returned fr target) as [[next next_fr] value] eqn:Hg.
      assert (Hresume : step tf (B.configuration returned (R.Return (R.KAfterGet fr target tail k)))
        (B.configuration next (R.RunRhs next_fr (tail value) k))).
      { machine_core; unfold B.step, R.next_config; cbn -[R.complete_get]; rewrite Hg; reflexivity. }
      destruct (IH value next next_fr k ltac:(rewrite (B.get_owner Hg); exact Howner)
        (reachable_advance (reachable_follow Hchild Hepisode) Hresume)) as [final [final_fr [direct [Ho Htail]]]].
      exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; [exact Hcallstep |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]]].
    + set (base := if R.is_materialized seen target then seen else R.enqueue seen target).
      destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hg.
      assert (Hget : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Get target tail) k))
        (B.configuration next (R.RunRhs next_fr (tail value) k))).
      { machine_core; unfold B.step, R.next_config; cbn -[R.observe R.complete_get]; fold seen; rewrite Hcall; fold base; rewrite Hg; reflexivity. }
      destruct (IH value next next_fr k ltac:(rewrite (B.get_owner Hg); exact Howner) (reachable_advance Hreach Hget))
        as [final [final_fr [direct [Ho Htail]]]].
      exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; eauto].
  - set (next_fr := R.with_frame_side fr target (R.accumulated_side_input fr target raw)).
    assert (Hside : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Side target raw tail) k))
      (B.configuration (R.observe st target) (R.RunRhs next_fr tail k))) by reflexivity.
    destruct (IH _ next_fr k Howner (reachable_advance Hreach Hside)) as [final [final_fr [direct [Ho Htail]]]].
    exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; eauto].
  - set (seen := R.observe st target).
    destruct (R.is_materialized seen target) eqn:Hmat.
    + assert (Hspawn : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Spawn target tail) k))
        (B.configuration seen (R.RunRhs fr tail k))).
      { machine_core; unfold B.step, R.next_config; cbn -[R.observe]; fold seen; rewrite Hmat; reflexivity. }
      destruct (IH seen fr k Howner (reachable_advance Hreach Hspawn)) as [final [final_fr [direct [Ho Htail]]]].
      exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; eauto].
    + destruct (R.rank_lt seen (R.frame_owner fr) target) eqn:Hhigher.
      * assert (Hspawn : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Spawn target tail) k))
          (B.configuration seen (R.StartEpisode target (R.KAfterSpawn fr tail k)))).
        { machine_core; unfold B.step, R.next_config; cbn -[R.observe]; fold seen; rewrite Hmat, Hhigher; reflexivity. }
        pose proof (reachable_advance Hreach Hspawn) as Hchild; rewrite Howner in Hhigher.
        destruct (higher_episodes Hchild Hhigher) as [returned [Hepisode Hbelow]].
        assert (Hresume : step tf (B.configuration returned (R.Return (R.KAfterSpawn fr tail k)))
          (B.configuration returned (R.RunRhs fr tail k))) by reflexivity.
        destruct (IH returned fr k Howner (reachable_advance (reachable_follow Hchild Hepisode) Hresume))
          as [final [final_fr [direct [Ho Htail]]]].
        exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; [exact Hspawn |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]]].
      * assert (Hspawn : step tf (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Spawn target tail) k))
          (B.configuration (R.materialize (R.enqueue seen target) target) (R.RunRhs fr tail k))).
        { machine_core; unfold B.step, R.next_config; cbn -[R.observe]; fold seen; rewrite Hmat, Hhigher; reflexivity. }
        destruct (IH _ fr k Howner (reachable_advance Hreach Hspawn)) as [final [final_fr [direct [Ho Htail]]]].
        exists final, final_fr, direct; split; [exact Ho |eapply steps_cons; eauto].
Qed.
End Evaluation.
Lemma changed_cell_budget support st fr target input next changed : In target support ->
  R.write_side_contribution st fr target input = (next,changed) ->
  N.cell_changed st next (R.frame_owner fr) target = true ->
  B.budget_lt (B.round_budget support next (R.frame_owner fr) (R.frame_phase fr))
    (B.round_budget support st (R.frame_owner fr) (R.frame_phase fr)).
Proof.
  intros Hin Hw Hchanged; pose proof (changed_cell_consumes_credit Hw Hchanged) as Hcredit.
  apply B.budget_side_strict.
  - apply B.preserves_live_layout; exact (proj1 (proj2 (proj2 (B.write_layout Hw)))).
  - eapply B.controlled_write; exact Hw.
  - unfold B.incident_credit.
    pose proof (@B.sum_over_lt (fun t => B.side_credit next (R.frame_owner fr) t)
      (fun t => B.side_credit st (R.frame_owner fr) t) support target Hin Hcredit
      (fun t _ => B.side_credit_write_all (R.frame_owner fr) t Hw)) as Hout.
    pose proof (@B.sum_over_le (fun s => B.side_credit next s (R.frame_owner fr))
      (fun s => B.side_credit st s (R.frame_owner fr)) support
      (fun s _ => B.side_credit_write_all s (R.frame_owner fr) Hw)) as Hincoming; lia.
  - intros _; unfold R.sigma_value; rewrite (proj1 (proj2 (proj2 (B.write_layout Hw)))); lia.
Qed.
Lemma equal_write_cell support st fr target input next changed : In target support ->
  R.write_side_contribution st fr target input = (next,changed) ->
  B.round_budget support next (R.frame_owner fr) (R.frame_phase fr) =
    B.round_budget support st (R.frame_owner fr) (R.frame_phase fr) ->
  N.cell_changed st next (R.frame_owner fr) target = false.
Proof.
  intros Hin Hw Heq; destruct N.cell_changed eqn:Hchanged; [|reflexivity].
  pose proof (@changed_cell_budget support st fr target input next changed Hin Hw Hchanged) as Hstrict; rewrite Heq in Hstrict;
    exfalso; eapply B.budget_lt_irrefl; exact Hstrict.
Qed.
Lemma equal_publication_queue support targets st fr : In (R.frame_owner fr) support ->
  Forall (fun x => In x support) targets ->
  B.round_budget support (N.publish targets st fr) (R.frame_owner fr) (R.frame_phase fr) =
    B.round_budget support st (R.frame_owner fr) (R.frame_phase fr) ->
  R.queue (N.publish targets st fr) = R.queue st.
Proof.
  revert st; induction targets as [|target rest IH]; intros st Howner Htargets Heq; cbn -[R.write_side_contribution N.finish_write] in Heq |- *; [reflexivity |].
  inversion Htargets as [|head tail Hin Hrest]; subst.
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  assert (Hfirst : B.round_budget support next (R.frame_owner fr) (R.frame_phase fr) =
    B.round_budget support st (R.frame_owner fr) (R.frame_phase fr)).
  { apply B.budget_le_antisym; [eapply B.budget_write; exact Hw |].
    rewrite <- (finish_budget support st next fr target changed (R.frame_owner fr) (R.frame_phase fr)).
    rewrite <- Heq; apply publication_budget. }
  assert (Haggregate : changed = false) by (eapply B.equal_write_unchanged; eauto).
  assert (Hcell : N.cell_changed st next (R.frame_owner fr) target = false) by (eapply equal_write_cell; eauto).
  unfold N.finish_write, N.requeue_source in Heq |- *; rewrite Haggregate, Hcell in Heq |- *.
  rewrite (IH next Howner Hrest ltac:(rewrite Hfirst; exact Heq)); eapply B.write_queue; exact Hw.
Qed.
Lemma below_not_pending st owner : B.queue_below st owner -> N.pending_above st owner = None.
Proof.
  intro Hbelow; unfold N.pending_above; destruct (S.mem owner (R.controlled st)); [|reflexivity].
  destruct (R.queue st) as [|head rest] eqn:Hq; [reflexivity |].
  cbn [R.queue_pop]; unfold B.queue_below in Hbelow; rewrite Hq in Hbelow.
  inversion Hbelow as [|? ? Hlower Hrest]; subst.
  destruct (R.rank_lt st owner head) eqn:Hhigher; [|reflexivity].
  exfalso; pose proof (@B.lt_trans (R.ranking st) owner head owner Hhigher Hlower) as Hcycle.
  rewrite B.lt_irrefl in Hcycle; discriminate.
Qed.
Lemma below_owner_absent st owner : B.queue_below st owner -> ~ In owner (R.queue st).
Proof.
  unfold B.queue_below; rewrite Forall_forall; intros H Hin.
  pose proof (H owner Hin) as Hcycle; unfold R.rank_lt in Hcycle; rewrite B.lt_irrefl in Hcycle; discriminate.
Qed.
Lemma actual_retry_queued tf st fr direct k :
  step tf (B.configuration st (R.RunCommit fr direct k)) (N.retry_current tf st fr k) ->
  In (R.frame_owner fr) (R.queue st).
Proof.
  unfold step, N.next_config, N.next_repaired, N.next_fresh; cbn -[N.pending_above N.retry_current R.next_config].
  destruct (N.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp.
  - unfold N.suspend_commit, N.retry_current; discriminate.
  - destruct (R.queue_contains (R.frame_owner fr) (R.queue st)) eqn:Hqueued; [intros _; apply B.contains_spec; exact Hqueued |].
    unfold N.next_batched, N.next_precommit; cbn -[N.pending_above R.next_config].
    unfold R.next_config; cbn -[R.set_value]; destruct (R.set_value st fr direct); discriminate.
Qed.
Theorem next_quiet_round tf roots (finite : Sem.finite_system tf roots) before after owner phase next_phase :
  reachable tf roots before -> B.quiet_round (Sem.support finite) owner before ->
  B.owner_phase (R.cfg_control before) owner = Some phase ->
  B.owner_phase (R.cfg_control after) owner = Some next_phase ->
  B.round_budget (Sem.support finite) (R.cfg_state after) owner next_phase =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  step tf before after -> B.quiet_round (Sem.support finite) owner after.
Proof.
  intros Hreach [Hbelow Hquiet] Hphase Hnext Heq Hstep.
  pose proof (@reachable_configuration_wf tf roots finite before Hreach) as Hwf.
  pose proof (next_preserves_live Hstep) as Hlive.
  pose proof Hstep as Hactual; apply step_view in Hstep; destruct Hstep;
    cbn [B.configuration R.cfg_control] in Hphase, Hnext;
    cbn [B.configuration R.cfg_state] in Hbelow, Heq.
  - eapply B.core_quiet_round; [exact Hwf |eapply reachable_forward_readers; exact Hreach
      |exact (B.ordered_unique (reachable_active_ordered Hreach)) |split; assumption |exact Hphase |exact Hnext |exact Heq |exact H].
  - destruct Hquiet as [Hin Hmissing]; cbn [B.configuration R.cfg_state] in Hmissing; exfalso.
    eapply (@B.equal_budget_no_discovery (Sem.support finite) st (R.materialize (N.clear_owner st owner0) owner0) owner phase next_phase owner0)
      in Heq; [congruence |exact Hlive |exact Hin |apply B.materialize_live].
  - cbn [B.configuration R.cfg_control B.quiet_round] in Hquiet; subst owner.
    split; [apply B.queue_below_observe; exact Hbelow |reflexivity].
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner.
    rewrite B.phase_dead in Hphase; injection Hphase as <-.
    rewrite B.phase_commit in Hnext; injection Hnext as <-.
    split; [|reflexivity]. unfold B.queue_below, R.rank_lt; cbn [B.configuration R.cfg_state].
    cbn [R.publish_targets R.with_last_targets R.ranking R.queue].
    rewrite publish_rank. change (Forall (fun x => R.rank_lt st x (R.frame_owner fr) = true)
      (R.queue (N.publish (S.elements (R.frame_current_targets fr)) st fr))).
    rewrite (@equal_publication_queue (Sem.support finite) (S.elements (R.frame_current_targets fr)) st fr); [exact Hbelow |exact (proj1 (B.ref_owner (proj1 (proj2 Hwf)))) | |].
    + eapply Forall_impl with (P := B.known (fun x => In x (Sem.support finite)) st);
        [intros x [Hx _]; exact Hx |apply B.set_elements; exact (B.ref_current (proj1 (proj2 Hwf)))].
    + cbn [B.configuration R.cfg_state] in Heq.
      rewrite <- publication_budget_layout; exact Heq.
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner.
    rewrite B.phase_dead in Hphase; injection Hphase as <-.
    cbn [B.configuration R.cfg_state] in Heq; rewrite B.budget_continue_dead, requeue_budget in Heq.
    change (B.owner_phase (R.cfg_control (R.continue_dead (N.requeue_source st next (R.frame_owner fr) target)
      fr direct target rest k changed)) (R.frame_owner fr) = Some next_phase) in Hnext.
    rewrite B.phase_continue_dead in Hnext; injection Hnext as <-.
    destruct Hwf as [Hs [Hfr [Htargets Hk]]]; inversion Htargets as [|head tail Htarget Hrest]; subst.
    assert (Hagg : changed = false) by (eapply B.equal_write_unchanged; [exact H |exact (proj1 (B.ref_owner Hfr)) |exact (proj1 Htarget) |exact Heq]).
    assert (Hcell : N.cell_changed st next (R.frame_owner fr) target = false) by (eapply equal_write_cell; [exact (proj1 Htarget) |exact H |exact Heq]).
    subst changed; unfold R.continue_dead, N.requeue_source; rewrite Hcell; split;
      [eapply B.queue_below_write; eauto |reflexivity].
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner.
    rewrite (below_not_pending Hbelow) in H; discriminate.
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner; exfalso.
    apply (below_owner_absent Hbelow); eapply actual_retry_queued; exact Hactual.
  - contradiction.
  - contradiction.
Qed.
Inductive episode_steps tf owner : R.config -> R.config -> Prop :=
| episode_refl c : episode_steps tf owner c c
| episode_cons before next after : In owner (B.active_owners (R.cfg_control before)) ->
    step tf before next -> episode_steps tf owner next after -> episode_steps tf owner before after.
Lemma episode_path tf owner before after : episode_steps tf owner before after -> steps tf before after.
Proof.
  intro Hpath; induction Hpath; [constructor |eapply steps_cons; eassumption].
Qed.
Lemma episode_append tf owner a b c : episode_steps tf owner a b -> episode_steps tf owner b c -> episode_steps tf owner a c.
Proof. intros Hab Hbc; induction Hab; eauto using episode_steps. Qed.
Lemma next_episode_scope tf before after owner base : B.episode_scope owner base (R.cfg_control before) ->
  step tf before after -> B.episode_scope owner base (R.cfg_control after) \/
  exists fr, R.cfg_control before = R.RunDrain fr base /\ R.frame_owner fr = owner /\ R.cfg_control after = R.Return base.
Proof.
  intros Hscope Hstep; apply step_view in Hstep; destruct Hstep.
  all: try solve [eapply B.next_episode_scope; eauto].
  all: try (unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]).
  all: left; unfold B.configuration, N.suspend_commit, N.retry_current in *;
    cbn [R.cfg_control B.episode_scope B.stack_episode R.frame_owner R.fresh_frame R.with_frame_side] in *;
    intuition auto.
Qed.
Lemma closing_queue_below tf roots before after owner : reachable tf roots before ->
  step tf before after -> B.closing before after owner -> B.queue_below (R.cfg_state after) owner.
Proof.
  intros Hreach Hstep Hclose; pose proof (reachable_rank_configuration Hreach) as Hwf.
  apply step_view in Hstep; destruct Hstep.
  all: try solve [eapply B.core_closing_queue; eauto].
  all: destruct Hclose as [closing_fr [closing_k [Hctrl _]]]; cbn [B.configuration R.cfg_control] in Hctrl; discriminate.
Qed.
Lemma next_framed_origin tf before after : step tf before after -> forall owner,
  In owner (B.framed_owners (R.cfg_control before)) ->
  In owner (B.framed_owners (R.cfg_control after)) \/ B.closing before after owner.
Proof.
  intros Hstep; apply step_view in Hstep; destruct Hstep.
  all: try solve [eapply B.next_framed_origin; eauto].
  all: try (unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]).
  all: unfold B.configuration, N.suspend_commit, N.retry_current;
    cbn [R.cfg_control B.framed_owners B.active_owners B.suspended_owners R.frame_owner R.fresh_frame R.with_frame_side];
    intros query Hin; left; auto.
  right; exact Hin.
Qed.
Lemma next_owner_phase_exists tf roots before after owner phase : reachable tf roots before ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> step tf before after ->
  In owner (B.active_owners (R.cfg_control after)) -> exists p, B.owner_phase (R.cfg_control after) owner = Some p.
Proof.
  intros Hreach Hphase Hstep Hactive.
  destruct (@next_framed_origin tf before after Hstep owner (@B.owner_phase_framed (R.cfg_control before) owner phase Hphase)) as [Hframed|Hclose].
  - apply B.owner_phase_exists; exact Hframed.
  - exfalso; eapply B.closing_owner_inactive;
      [exact (B.ordered_unique (reachable_active_ordered Hreach)) |exact Hclose |exact Hactive].
Qed.
Lemma episode_active_or_equal tf owner before after : episode_steps tf owner before after ->
  before = after \/ In owner (B.active_owners (R.cfg_control before)).
Proof. intro Hpath; destruct Hpath; auto. Qed.
Theorem episode_owner_budget tf roots support owner before after phase next_phase : reachable tf roots before ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> B.owner_phase (R.cfg_control after) owner = Some next_phase ->
  episode_steps tf owner before after ->
  B.budget_le (B.round_budget support (R.cfg_state after) owner next_phase) (B.round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreach Hphase Hlast Hpath; revert phase Hreach Hphase; induction Hpath; intros phase Hreach Hphase.
  - rewrite Hphase in Hlast; injection Hlast as ->; left; reflexivity.
  - pose proof (reachable_advance Hreach H0) as Hnext.
    assert (Hp : exists p, B.owner_phase (R.cfg_control next) owner = Some p).
    { destruct (episode_active_or_equal Hpath) as [->|Hactive]; [exists next_phase; exact Hlast |].
      exact (@next_owner_phase_exists tf roots before next owner phase Hreach Hphase H0 Hactive). }
    destruct Hp as [p Hp]; eapply B.budget_le_trans; [exact (IHHpath Hlast p Hnext Hp) |].
    eapply next_owner_budget; eauto.
Qed.
Theorem higher_episode_parent_budget tf roots support owner child before after phase :
  reachable tf roots before -> R.rank_lt (R.cfg_state before) owner child = true ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> episode_steps tf child before after ->
  B.owner_phase (R.cfg_control after) owner = Some phase /\
  B.budget_le (B.round_budget support (R.cfg_state after) owner phase) (B.round_budget support (R.cfg_state before) owner phase).
Proof.
  intros Hreach Hhigher Hphase Hpath; revert Hreach Hhigher Hphase; induction Hpath; intros Hreach Hhigher Hphase.
  - split; [exact Hphase |left; reflexivity].
  - assert (Hlarger : B.larger_active (R.cfg_state before) (R.cfg_control before) owner) by (exists child; auto).
    pose proof (reachable_active_ordered Hreach) as Ho.
    pose proof (@next_lower_phase tf before next owner phase Ho Hlarger Hphase H0) as Hp.
    assert (Hhigher' : R.rank_lt (R.cfg_state next) owner child = true) by
      (eapply B.lt_extends; [eapply next_ranking_extends; exact H0 |exact Hhigher]).
    destruct (IHHpath (reachable_advance Hreach H0) Hhigher' Hp) as [Hlast Hb]; split; [exact Hlast |].
    eapply B.budget_le_trans; [exact Hb |].
    eapply next_budget_below; [exact Ho |eapply reachable_scoped_config; exact Hreach |exact Hlarger |exact H0].
Qed.
Theorem episode_quiet_round tf roots (finite : Sem.finite_system tf roots) owner before after phase next_phase :
  reachable tf roots before -> B.quiet_round (Sem.support finite) owner before ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> B.owner_phase (R.cfg_control after) owner = Some next_phase ->
  episode_steps tf owner before after ->
  B.round_budget (Sem.support finite) (R.cfg_state after) owner next_phase =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  B.quiet_round (Sem.support finite) owner after.
Proof.
  intros Hreach Hquiet Hphase Hlast Hpath; revert phase Hreach Hquiet Hphase; induction Hpath;
    intros phase Hreach Hquiet Hphase Heq; [exact Hquiet |].
  pose proof (reachable_advance Hreach H0) as Hnext.
  assert (Hp : exists p, B.owner_phase (R.cfg_control next) owner = Some p).
  { destruct (episode_active_or_equal Hpath) as [->|Hactive]; [exists next_phase; exact Hlast |].
    exact (@next_owner_phase_exists tf roots before next owner phase Hreach Hphase H0 Hactive). }
  destruct Hp as [p Hp].
  pose proof (@next_owner_budget tf roots (Sem.support finite) before next owner phase p Hreach Hphase Hp H0) as Hb.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) owner next after p next_phase Hnext Hp Hlast Hpath) as Htail.
  assert (Hsame : B.round_budget (Sem.support finite) (R.cfg_state next) owner p =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase).
  { apply B.budget_le_antisym; [exact Hb |rewrite Heq in Htail; exact Htail]. }
  eapply IHHpath; [exact Hlast |exact Hnext | |exact Hp |rewrite Hsame; exact Heq].
  exact (@next_quiet_round tf roots finite before next owner phase p Hreach Hquiet Hphase Hp Hsame H0).
Qed.
Inductive evaluation_steps tf owner : R.config -> R.config -> Prop :=
| evaluation_refl c : evaluation_steps tf owner c c
| evaluation_cons before next after :
    In owner (B.active_owners (R.cfg_control before)) -> ~ B.committing before owner ->
    step tf before next -> evaluation_steps tf owner next after -> evaluation_steps tf owner before after.
Lemma evaluation_episode tf owner before after : evaluation_steps tf owner before after -> episode_steps tf owner before after.
Proof. intro Hpath; induction Hpath; eauto using episode_steps. Qed.
Lemma evaluation_path tf owner before after : evaluation_steps tf owner before after -> steps tf before after.
Proof. intro Hpath; apply episode_path with (owner := owner), evaluation_episode; exact Hpath. Qed.
Lemma committing_dec c owner : {B.committing c owner} + {~ B.committing c owner}.
Proof.
  destruct c as [st ctrl]; destruct ctrl; try solve
    [right; intros [fr [direct [k [Hctrl _]]]]; cbn [R.cfg_control] in Hctrl; discriminate].
  destruct (V.eq_dec (R.frame_owner f) owner) as [Heq|Hneq].
  - left; exists f, t, c; split; [reflexivity |symmetry; exact Heq].
  - right; intros [fr [direct [k [Hctrl Howner]]]]; cbn [R.cfg_control] in Hctrl.
    inversion Hctrl; subst; contradiction.
Qed.
Lemma owned_commit_base c owner base fr direct k :
  NoDup (B.active_owners (R.cfg_control c)) -> B.episode_scope owner base (R.cfg_control c) ->
  R.cfg_control c = R.RunCommit fr direct k -> R.frame_owner fr = owner -> k = base.
Proof.
  intros Hunique Hscope Hctrl Howner; rewrite Hctrl in Hunique, Hscope; cbn [B.episode_scope B.active_owners] in *.
  destruct Hscope as [[_ Hbase]|Hstack]; [exact Hbase |].
  exfalso; pose proof (@B.stack_episode_active owner base k Hstack) as Hin.
  pose proof (@B.parent_distinct (R.frame_owner fr) (B.suspended_owners k) Hunique owner Hin) as Hneq.
  apply Hneq; symmetry; exact Howner.
Qed.
Lemma next_no_drain tf before after owner : ~ In owner (B.drained_owners (R.cfg_control before)) ->
  ~ B.committing before owner -> step tf before after -> ~ In owner (B.drained_owners (R.cfg_control after)).
Proof.
  intros Hclean Hnot Hstep Hin; destruct (@next_drained_origin tf before after Hstep owner Hin); contradiction.
Qed.
Lemma clean_scope_step tf before after owner base : B.episode_scope owner base (R.cfg_control before) ->
  ~ In owner (B.drained_owners (R.cfg_control before)) -> step tf before after ->
  B.episode_scope owner base (R.cfg_control after).
Proof.
  intros Hscope Hclean Hstep.
  destruct (@next_episode_scope tf before after owner base Hscope Hstep) as [Hnext|[fr [Hctrl [Howner Hreturn]]]]; [exact Hnext |].
  exfalso; apply Hclean; rewrite Hctrl; cbn [B.drained_owners]; left; exact Howner.
Qed.
Lemma rhs_not_drained tf roots st fr body k : reachable tf roots (B.configuration st (R.RunRhs fr body k)) ->
  ~ In (R.frame_owner fr) (B.drained_owners (R.RunRhs fr body k)).
Proof.
  intros Hreach Hin; pose proof (B.ordered_unique (reachable_active_ordered Hreach)) as Hunique.
  cbn [B.configuration R.cfg_control B.active_owners] in Hunique;
    inversion Hunique as [|head parents Hnot Hdup]; subst.
  apply Hnot; eapply B.drained_parent; exact Hin.
Qed.
(** Extract the first owner commit from structural evaluation. The continuation
    remains the same, and no owner commit is hidden in the extracted prefix. *)
Lemma first_owner_commit tf roots owner base before after fr direct :
  reachable tf roots before -> B.episode_scope owner base (R.cfg_control before) ->
  ~ In owner (B.drained_owners (R.cfg_control before)) ->
  steps tf before after -> R.cfg_control after = R.RunCommit fr direct base -> R.frame_owner fr = owner ->
  exists committed commit_fr commit_direct, R.frame_owner commit_fr = owner /\
    evaluation_steps tf owner before (B.configuration committed (R.RunCommit commit_fr commit_direct base)).
Proof.
  intros Hreach Hscope Hclean Hpath; revert Hreach Hscope Hclean; induction Hpath;
    intros Hreach Hscope Hclean Hlast Howner.
  - destruct (committing_dec c owner) as [[current_fr [current_direct [current_k [Hctrl Ho]]]]|Hnot].
    + apply eq_sym in Ho; assert (Hbase : current_k = base) by (eapply owned_commit_base; [exact (B.ordered_unique (reachable_active_ordered Hreach)) |exact Hscope |exact Hctrl |exact Ho]).
      subst current_k; destruct c as [st ctrl]; cbn in Hctrl; subst ctrl.
      exists st, current_fr, current_direct; split; [exact Ho |constructor].
    + exfalso; apply Hnot; exists fr, direct, base; split; [exact Hlast |symmetry; exact Howner].
  - destruct (committing_dec before owner) as [[current_fr [current_direct [current_k [Hctrl Ho]]]]|Hnot].
    + apply eq_sym in Ho; assert (Hbase : current_k = base) by (eapply owned_commit_base; [exact (B.ordered_unique (reachable_active_ordered Hreach)) |exact Hscope |exact Hctrl |exact Ho]).
      subst current_k; destruct before as [st ctrl]; cbn in Hctrl; subst ctrl.
      exists st, current_fr, current_direct; split; [exact Ho |constructor].
    + destruct (IHHpath (reachable_advance Hreach H)
        (@clean_scope_step tf before next owner base Hscope Hclean H)
        (@next_no_drain tf before next owner Hclean Hnot H) Hlast Howner)
        as [committed [commit_fr [commit_direct [Ho Hprefix]]]].
      exists committed, commit_fr, commit_direct; split; [exact Ho |].
      eapply evaluation_cons; [eapply B.episode_scope_active; exact Hscope |exact Hnot |exact H |exact Hprefix].
Qed.
Lemma rhs_evaluation tf roots owner body st fr k :
  (forall st child k, reachable tf roots (B.configuration st (R.StartEpisode child k)) ->
    R.rank_lt st owner child = true -> episode_complete tf (B.configuration st (R.StartEpisode child k)) child k) ->
  R.frame_owner fr = owner -> reachable tf roots (B.configuration st (R.RunRhs fr body k)) ->
  exists committed commit_fr direct, R.frame_owner commit_fr = owner /\
    evaluation_steps tf owner (B.configuration st (R.RunRhs fr body k))
      (B.configuration committed (R.RunCommit commit_fr direct k)).
Proof.
  intros Hhigher Howner Hreach.
  destruct (@rhs_to_commit tf roots owner Hhigher body st fr k Howner Hreach)
    as [committed [commit_fr [direct [Ho Hpath]]]].
  eapply first_owner_commit; [exact Hreach |left; auto | |exact Hpath |reflexivity |exact Ho].
  rewrite <- Howner; exact (@rhs_not_drained tf roots st fr body k Hreach).
Qed.
Theorem next_equal_evaluation tf roots (finite : Sem.finite_system tf roots) before after owner phase next_phase :
  reachable tf roots before -> ~ B.committing before owner -> B.evaluation_quiet (Sem.support finite) owner before ->
  B.owner_phase (R.cfg_control before) owner = Some phase ->
  B.owner_phase (R.cfg_control after) owner = Some next_phase ->
  B.round_budget (Sem.support finite) (R.cfg_state after) owner next_phase =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  step tf before after -> B.evaluation_quiet (Sem.support finite) owner after.
Proof.
  intros Hreach Houtside [Hbelow Hquiet] Hphase Hnext Heq Hstep.
  pose proof (@reachable_configuration_wf tf roots finite before Hreach) as Hwf.
  pose proof (next_preserves_live Hstep) as Hlive.
  pose proof Hstep as Hactual; apply step_view in Hstep; destruct Hstep;
    cbn [B.configuration R.cfg_control] in Hphase, Hnext;
    cbn [B.configuration R.cfg_state] in Hbelow, Heq.
  - eapply B.core_equal_evaluation; [exact Hwf | |split; assumption |exact Hphase |exact Hnext |exact Heq |exact H].
    intros fr direct k Hctrl Howner; apply Houtside; exists fr, direct, k; split; [exact Hctrl |symmetry; exact Howner].
  - destruct Hquiet as [Hin Hmissing]; cbn [B.configuration R.cfg_state] in Hmissing; exfalso.
    eapply (@B.equal_budget_no_discovery (Sem.support finite) st (R.materialize (N.clear_owner st owner0) owner0) owner phase next_phase owner0)
      in Heq; [congruence |exact Hlive |exact Hin |apply B.materialize_live].
  - cbn [B.configuration R.cfg_control B.quiet_round] in Hquiet; subst owner.
    split; [change (~ In (R.frame_owner fr) (R.queue (R.observe st target))); rewrite B.observe_queue; exact Hbelow |reflexivity].
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner.
    rewrite B.phase_dead in Hphase; injection Hphase as <-.
    rewrite B.phase_commit in Hnext; injection Hnext as <-.
    split; [|reflexivity].
    change (~ In (R.frame_owner fr) (R.queue (N.publish (S.elements (R.frame_current_targets fr)) st fr))).
    rewrite (@equal_publication_queue (Sem.support finite) (S.elements (R.frame_current_targets fr)) st fr); [exact Hbelow |exact (proj1 (B.ref_owner (proj1 (proj2 Hwf)))) | |].
    + eapply Forall_impl with (P := B.known (fun x => In x (Sem.support finite)) st);
        [intros x [Hx _]; exact Hx |apply B.set_elements; exact (B.ref_current (proj1 (proj2 Hwf)))].
    + cbn [B.configuration R.cfg_state] in Heq.
      rewrite <- publication_budget_layout; exact Heq.
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner.
    rewrite B.phase_dead in Hphase; injection Hphase as <-.
    cbn [B.configuration R.cfg_state] in Heq; rewrite B.budget_continue_dead, requeue_budget in Heq.
    change (B.owner_phase (R.cfg_control (R.continue_dead (N.requeue_source st next (R.frame_owner fr) target)
      fr direct target rest k changed)) (R.frame_owner fr) = Some next_phase) in Hnext.
    rewrite B.phase_continue_dead in Hnext; injection Hnext as <-.
    destruct Hwf as [Hs [Hfr [Htargets Hk]]]; inversion Htargets as [|head tail Htarget Hrest]; subst.
    assert (Hagg : changed = false) by (eapply B.equal_write_unchanged; [exact H |exact (proj1 (B.ref_owner Hfr)) |exact (proj1 Htarget) |exact Heq]).
    assert (Hcell : N.cell_changed st next (R.frame_owner fr) target = false) by (eapply equal_write_cell; [exact (proj1 Htarget) |exact H |exact Heq]).
    subst changed; unfold R.continue_dead, N.requeue_source; rewrite Hcell; split;
      [change (~ In (R.frame_owner fr) (R.queue next)); rewrite (B.write_queue H); exact Hbelow |reflexivity].
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner; exfalso.
    apply Houtside; exists fr, direct, k; auto.
  - cbn [B.configuration R.cfg_control] in Hquiet; subst owner; exfalso.
    apply Houtside; exists fr, direct, k; auto.
  - contradiction.
  - contradiction.
Qed.
Theorem evaluation_equal_quiet tf roots (finite : Sem.finite_system tf roots) owner before after phase next_phase :
  reachable tf roots before -> B.evaluation_quiet (Sem.support finite) owner before ->
  B.owner_phase (R.cfg_control before) owner = Some phase -> B.owner_phase (R.cfg_control after) owner = Some next_phase ->
  evaluation_steps tf owner before after ->
  B.round_budget (Sem.support finite) (R.cfg_state after) owner next_phase =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase ->
  B.evaluation_quiet (Sem.support finite) owner after.
Proof.
  intros Hreach Hquiet Hphase Hlast Hpath; revert phase Hreach Hquiet Hphase.
  induction Hpath as [c|before next after Hactive Hnot Hstep Hpath IH]; intros phase Hreach Hquiet Hphase Heq;
    [exact Hquiet |].
  pose proof (reachable_advance Hreach Hstep) as Hnext.
  assert (Hp : exists p, B.owner_phase (R.cfg_control next) owner = Some p).
  { destruct (episode_active_or_equal (evaluation_episode Hpath)) as [->|Ha]; [exists next_phase; exact Hlast |].
    exact (@next_owner_phase_exists tf roots before next owner phase Hreach Hphase Hstep Ha). }
  destruct Hp as [p Hp].
  pose proof (@next_owner_budget tf roots (Sem.support finite) before next owner phase p Hreach Hphase Hp Hstep) as Hb.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) owner next after p next_phase Hnext Hp Hlast
    (evaluation_episode Hpath)) as Htail.
  assert (Hsame : B.round_budget (Sem.support finite) (R.cfg_state next) owner p =
    B.round_budget (Sem.support finite) (R.cfg_state before) owner phase).
  { apply B.budget_le_antisym; [exact Hb |rewrite Heq in Htail; exact Htail]. }
  eapply IH; [exact Hlast |exact Hnext | |exact Hp |rewrite Hsame; exact Heq].
  exact (@next_equal_evaluation tf roots finite before next owner phase p Hreach Hnot Hquiet Hphase Hp Hsame Hstep).
Qed.
(** Every precommit self-retry is paid, including an uncontrolled source whose
    changed contribution was masked in the target's aggregate. *)
Theorem precommit_retry_paid tf roots (finite : Sem.finite_system tf roots) st fr body k committed commit_fr direct :
  reachable tf roots (B.configuration st (R.RunRhs fr body k)) -> ~ In (R.frame_owner fr) (R.queue st) ->
  R.frame_owner commit_fr = R.frame_owner fr ->
  evaluation_steps tf (R.frame_owner fr) (B.configuration st (R.RunRhs fr body k))
    (B.configuration committed (R.RunCommit commit_fr direct k)) ->
  step tf (B.configuration committed (R.RunCommit commit_fr direct k)) (N.retry_current tf committed commit_fr k) ->
  B.budget_lt (B.round_budget (Sem.support finite) committed (R.frame_owner fr) (R.frame_phase commit_fr))
    (B.round_budget (Sem.support finite) st (R.frame_owner fr) (R.frame_phase fr)).
Proof.
  intros Hreach Hquiet Ho Hprefix Hretry.
  assert (Hfirst : B.owner_phase (R.RunRhs fr body k) (R.frame_owner fr) = Some (R.frame_phase fr)) by apply B.phase_rhs.
  assert (Hlast : B.owner_phase (R.RunCommit commit_fr direct k) (R.frame_owner fr) = Some (R.frame_phase commit_fr)) by
    (rewrite <- Ho; apply B.phase_commit).
  destruct (@episode_owner_budget tf roots (Sem.support finite) (R.frame_owner fr)
    (B.configuration st (R.RunRhs fr body k)) (B.configuration committed (R.RunCommit commit_fr direct k))
    (R.frame_phase fr) (R.frame_phase commit_fr) Hreach Hfirst Hlast (evaluation_episode Hprefix)) as [Heq|Hpaid]; [|exact Hpaid].
  pose proof (@evaluation_equal_quiet tf roots finite (R.frame_owner fr)
    (B.configuration st (R.RunRhs fr body k)) (B.configuration committed (R.RunCommit commit_fr direct k))
    (R.frame_phase fr) (R.frame_phase commit_fr) Hreach ltac:(split; [exact Hquiet |reflexivity]) Hfirst Hlast Hprefix Heq) as [Hnot _].
  exfalso; apply Hnot; rewrite <- Ho; eapply actual_retry_queued; exact Hretry.
Qed.
Lemma paths_controlled tf before after : steps tf before after ->
  B.controlled_mono (R.cfg_state before) (R.cfg_state after).
Proof.
  intro Hpath; induction Hpath; intros owner Hmem; auto.
  apply IHHpath; eapply next_controlled_mono; eauto.
Qed.
Lemma clear_below support st owner : B.store_wf support st -> B.ranked (R.ranking st) owner ->
  S.mem owner (R.controlled st) = true -> N.pending_above st owner = None ->
  B.queue_below (N.clear_owner st owner) owner.
Proof.
  intros Hstore Howner Hcontrolled Hpending.
  unfold B.queue_below; apply Forall_forall; intros query Hquery.
  apply clear_members in Hquery; destruct Hquery as [Hquery Hneq].
  destruct (R.queue st) as [|head rest] eqn:Hqueue; [contradiction |].
  assert (Hhead : B.ranked (R.ranking st) head).
  { pose proof (B.known_ranked_queue Hstore) as Hknown; rewrite Hqueue in Hknown; inversion Hknown; assumption. }
  assert (Hhigher : R.rank_lt st owner head = false).
  { unfold N.pending_above in Hpending; rewrite Hcontrolled, Hqueue in Hpending; cbn [R.queue_pop] in Hpending.
    destruct (R.rank_lt st owner head); [discriminate |reflexivity]. }
  destruct (V.eq_dec head owner) as [Heq|Hdifferent].
  - subst head; destruct Hquery as [Heq|Hin]; [congruence |].
    pose proof (proj2 (@B.ordered_tail (R.ranking st) owner rest ltac:(rewrite <- Hqueue; exact (B.store_ordered Hstore)))) as Hlower.
    rewrite Forall_forall in Hlower; exact (Hlower query Hin).
  - assert (Hlower : R.rank_lt st head owner = true).
    { destruct (@B.lt_compare (R.ranking st) head owner (B.store_valid Hstore) Hhead Howner Hdifferent) as [Hlt|Hlt];
      [exact Hlt |unfold R.rank_lt in Hhigher; congruence]. }
    destruct Hquery as [<-|Hin]; [exact Hlower |].
    pose proof (proj2 (@B.ordered_tail (R.ranking st) head rest ltac:(rewrite <- Hqueue; exact (B.store_ordered Hstore)))) as Htail.
    rewrite Forall_forall in Htail; unfold R.rank_lt; eapply B.lt_trans; [apply Htail; exact Hin |exact Hlower].
Qed.
Definition round_order support owner (next previous : nat * (R.state * U.phase)) :=
  Relation_Operators.slexprod (nat * (nat * nat)) nat B.budget_lt lt
    (B.round_budget support (fst (snd next)) owner (snd (snd next)), fst next)
    (B.round_budget support (fst (snd previous)) owner (snd (snd previous)), fst previous).
Lemma round_order_well_founded support owner : well_founded (round_order support owner).
Proof.
  unfold round_order; apply Wellfounded.Inverse_Image.wf_inverse_image;
    repeat apply Wellfounded.Lexicographic_Product.wf_slexprod; apply Nat.lt_wf_0.
Qed.
Section ResumeBoundary.
Variable tf : R.ConstraintSystem.system.
Variable roots : list V.t.
Variable finite : Sem.finite_system tf roots.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (B.configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (B.configuration st (R.StartEpisode child k)) child k.
Lemma resume_to_rhs : forall ceiling st fr body k,
  R.frame_owner fr = owner -> body = tf owner -> S.mem owner (R.controlled st) = true ->
  reachable tf roots (B.configuration st (R.Return (R.KAfterSide fr body k))) -> B.queue_ceiling st ceiling ->
  exists final final_fr, steps tf (B.configuration st (R.Return (R.KAfterSide fr body k)))
    (B.configuration final (R.RunRhs final_fr (tf owner) k)) /\
    R.frame_owner final_fr = owner /\ R.frame_phase final_fr = R.frame_phase fr /\
    B.queue_below final owner /\ ~ In owner (R.queue final).
Proof.
  intro ceiling; induction ceiling as [ceiling IH] using (well_founded_induction Nat.lt_wf_0); intros st fr body k Ho Hbody Hcontrolled Hreach Hceiling; subst body.
  destruct (N.pending_above st (R.frame_owner fr)) as [[child rest]|] eqn:Hp.
  - assert (Hstep : step tf (B.configuration st (R.Return (R.KAfterSide fr (tf owner) k)))
      (N.suspend_commit tf st fr k child rest)).
    { unfold step, N.next_config; cbn -[N.pending_above N.suspend_commit]; rewrite Hp; reflexivity. }
    pose proof (reachable_advance Hreach Hstep) as Hchild.
    destruct (pending_spec Hp) as [_ [Hpop Hhigher]]; rewrite Ho in Hhigher.
    destruct (higher_episodes Hchild Hhigher) as [returned [Hepisode Hbelow]].
    assert (Hin : In child (R.queue st)) by (destruct (R.queue st); inversion Hpop; cbn; auto).
    destruct (Hceiling child Hin) as [rank [Hrank Hbound]].
    assert (Hreturned : Ranks.lookup (R.ranking returned) child = Some rank) by
      (exact (steps_ranking_extends Hepisode child Hrank)).
    set (saved := R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)).
    assert (Hreturn_reach : reachable tf roots (B.configuration returned (R.Return (R.KAfterSide saved (tf owner) k)))).
    { rewrite <- Ho; eapply reachable_follow; [exact Hchild |exact Hepisode]. }
    assert (Hcontrolled' : S.mem owner (R.controlled returned) = true).
    { exact (paths_controlled Hepisode Hcontrolled). }
    destruct (IH rank Hbound returned saved (tf owner) k Ho eq_refl Hcontrolled' Hreturn_reach
      (B.queue_below_ceiling Hbelow Hreturned)) as [final [final_fr [Htail [Howner [Hphase [Hfinalbelow Hquiet]]]]]].
    exists final, final_fr; split; [|repeat split; assumption].
    eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |unfold saved in Htail; rewrite Ho; rewrite Ho in Htail; exact Htail]].
  - assert (Hstep : step tf (B.configuration st (R.Return (R.KAfterSide fr (tf owner) k)))
      (B.configuration (N.clear_owner st owner) (R.RunRhs fr (tf owner) k))).
    { unfold step, N.next_config, N.next_repaired, N.next_fresh, N.next_batched, N.next_precommit;
      cbn -[N.pending_above N.clear_owner R.next_config]; rewrite Hp; rewrite Ho; reflexivity. }
    exists (N.clear_owner st owner), fr; split; [eapply steps_cons; [exact Hstep |constructor] |].
    split; [exact Ho |]; split; [reflexivity |]; split; [|apply clear_not_queued].
    pose proof (reachable_rank_configuration Hreach) as [Hstore Hrefs].
    eapply clear_below; [exact Hstore | |exact Hcontrolled |rewrite <- Ho; exact Hp].
    rewrite <- Ho; exact (proj2 (B.ref_owner (proj1 Hrefs))).
Qed.
End ResumeBoundary.

Lemma first_episode_return tf roots owner base before final : reachable tf roots before ->
  B.episode_scope owner base (R.cfg_control before) -> steps tf before (B.configuration final (R.Return base)) ->
  exists returned, episode_steps tf owner before (B.configuration returned (R.Return base)) /\ B.queue_below returned owner.
Proof.
  intros Hreachable Hscope Hpath.
  assert (Houtside : ~ B.episode_scope owner base (R.cfg_control (B.configuration final (R.Return base))))
    by (apply B.episode_return_outside).
  revert Hreachable Hscope Houtside; induction Hpath; intros Hreachable Hscope Houtside.
  - contradiction.
  - destruct (@next_episode_scope tf before next owner base Hscope H) as [Hnext |[fr [Hbefore [Howner Hreturn]]]].
    + destruct (IHHpath (reachable_advance Hreachable H) Hnext Houtside) as [returned [Htail Hbelow]].
      exists returned; split; [eapply episode_cons; [eapply B.episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hbelow].
    + assert (Hclosing : B.closing before next owner) by (exists fr, base; repeat split; auto).
      pose proof (closing_queue_below Hreachable H Hclosing) as Hbelow.
      destruct next as [returned ctrl]; cbn [R.cfg_control R.cfg_state] in Hreturn, Hbelow; subst ctrl.
      exists returned; split; [eapply episode_cons; [eapply B.episode_scope_active; exact Hscope |exact H |constructor] |exact Hbelow].
Qed.
Definition episode_finished tf start owner k := exists final,
  episode_steps tf owner start (B.configuration final (R.Return k)) /\ B.queue_below final owner.
Theorem episode_first_return tf roots st owner k : reachable tf roots (B.configuration st (R.StartEpisode owner k)) ->
  episode_complete tf (B.configuration st (R.StartEpisode owner k)) owner k ->
  episode_finished tf (B.configuration st (R.StartEpisode owner k)) owner k.
Proof.
  intros Hreachable [final [Hpath _]]; eapply first_episode_return;
    [exact Hreachable |left; auto |exact Hpath].
Qed.

Lemma episode_finished_path tf before owner k : episode_finished tf before owner k -> episode_complete tf before owner k.
Proof. intros [returned [Hpath Hbelow]]; exists returned; split; [exact (episode_path Hpath) |exact Hbelow]. Qed.
Lemma trace_or_finish tf roots owner base before after : reachable tf roots before ->
  B.episode_scope owner base (R.cfg_control before) -> steps tf before after ->
  episode_finished tf before owner base \/ (episode_steps tf owner before after /\ B.episode_scope owner base (R.cfg_control after)).
Proof.
  intros Hreachable Hscope Hpath; revert Hreachable Hscope; induction Hpath; intros Hreachable Hscope.
  - right; split; [constructor |exact Hscope].
  - destruct (@next_episode_scope tf before next owner base Hscope H) as [Hnext |[fr [Hbefore [Howner Hreturn]]]].
    + destruct (IHHpath (reachable_advance Hreachable H) Hnext) as [[returned [Htail Hbelow]] |[Htail Hfinal]].
      * left; exists returned; split; [eapply episode_cons; [eapply B.episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hbelow].
      * right; split; [eapply episode_cons; [eapply B.episode_scope_active; exact Hscope |exact H |exact Htail] |exact Hfinal].
    + assert (Hclosing : B.closing before next owner) by (exists fr, base; repeat split; auto).
      pose proof (closing_queue_below Hreachable H Hclosing) as Hbelow.
      destruct next as [returned ctrl]; cbn [R.cfg_state R.cfg_control] in Hreturn, Hbelow; subst ctrl.
      left; exists returned; split; [eapply episode_cons; [eapply B.episode_scope_active; exact Hscope |exact H |constructor] |exact Hbelow].
Qed.


Section Draining.
Variable tf : R.ConstraintSystem.system.
Variable roots : list V.t.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (B.configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (B.configuration st (R.StartEpisode child k)) child k.
Lemma drain_reaches_boundary ceiling st fr k : R.frame_owner fr = owner ->
  reachable tf roots (B.configuration st (R.RunDrain fr k)) -> B.queue_ceiling st ceiling ->
  exists final, steps tf (B.configuration st (R.RunDrain fr k)) final /\
    B.drain_boundary tf owner (R.frame_phase fr) k final.
Proof.
  revert st fr k; induction ceiling using lt_wf_ind; intros st fr k Howner Hreachable Hceiling.
  pose proof (@reachable_rank_configuration tf roots (B.configuration st (R.RunDrain fr k)) Hreachable) as [Hstore Hrefs].
  cbn [B.configuration R.cfg_state R.cfg_control B.control_refs] in Hstore, Hrefs; destruct Hrefs as [Hfr Hk].
  assert (Howner_ranked : B.ranked (R.ranking st) owner) by (rewrite <- Howner; exact (proj2 (B.ref_owner Hfr))).
  destruct (R.queue st) as [|head rest] eqn:Hqueue.
  - exists (B.configuration (R.reset_registered_cells st owner) (R.Return k)); split.
    + apply steps_cons with (next := B.configuration (R.reset_registered_cells st owner) (R.Return k)); [|constructor].
      machine_core; unfold R.next_config, B.configuration; cbn -[R.reset_registered_cells]; rewrite Hqueue; cbn; now rewrite Howner.
    + split; [apply B.queue_below_close; unfold B.queue_below; rewrite Hqueue; constructor |left; reflexivity].
  - destruct (V.eq_dec head owner) as [-> |Hneq].
    + exists (B.configuration (R.with_queue st rest)
        (R.RunRhs (R.fresh_frame (R.with_queue st rest) owner (R.frame_phase fr)) (tf owner) k)); split.
      * apply steps_cons with (next := B.configuration (R.with_queue st rest)
          (R.RunRhs (R.fresh_frame (R.with_queue st rest) owner (R.frame_phase fr)) (tf owner) k)); [|constructor].
        machine_core; unfold R.next_config, B.configuration; cbn -[R.fresh_frame]; rewrite Hqueue, Howner; cbn;
          destruct (V.eq_dec owner owner); [reflexivity |contradiction].
      * split.
        -- unfold B.queue_below; cbn [R.with_queue R.queue R.rank_lt R.ranking];
             pose proof (proj2 (@B.ordered_tail (R.ranking st) owner rest ltac:(rewrite <- Hqueue; exact (B.store_ordered Hstore)))) as Hbelow;
             exact Hbelow.
        -- right; eexists; repeat split; reflexivity.
    + destruct (R.rank_lt st owner head) eqn:Hhigher.
      * assert (Hstep : step tf (B.configuration st (R.RunDrain fr k))
          (B.configuration (R.with_queue st rest) (R.StartEpisode head (R.KDrain fr k)))).
        { machine_core; unfold R.next_config, B.configuration; cbn -[R.rank_lt]; rewrite Hqueue, Howner; cbn;
            destruct (V.eq_dec head owner); [contradiction |rewrite Hhigher; reflexivity]. }
        pose proof (reachable_advance Hreachable Hstep) as Hnext.
        destruct (higher_episodes Hnext Hhigher) as [returned [Hepisode Hbelow]].
        destruct (Hceiling head ltac:(rewrite Hqueue; left; reflexivity)) as [rank [Hrank Hbound]].
        assert (Hreturned_rank : Ranks.lookup (R.ranking returned) head = Some rank).
        { exact (steps_ranking_extends Hepisode head Hrank). }
        assert (Hresume : step tf (B.configuration returned (R.Return (R.KDrain fr k)))
          (B.configuration returned (R.RunDrain fr k))) by reflexivity.
        destruct (H rank Hbound returned fr k Howner
          (reachable_advance (reachable_follow Hnext Hepisode) Hresume)
          (B.queue_below_ceiling Hbelow Hreturned_rank)) as [final [Htail Hboundary]].
        exists final; split; [eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]] |exact Hboundary].
      * assert (Hlower : R.rank_lt st head owner = true).
        { assert (Hhead : B.ranked (R.ranking st) head).
          { pose proof (B.known_ranked_queue Hstore) as Hq; rewrite Hqueue in Hq; inversion Hq; assumption. }
          destruct (@B.lt_compare (R.ranking st) head owner (B.store_valid Hstore) Hhead
            Howner_ranked Hneq) as [Hlt |Hlt]; [exact Hlt |unfold R.rank_lt in Hhigher; congruence]. }
        assert (Hbelow : B.queue_below st owner).
        { unfold B.queue_below; rewrite Hqueue; constructor; [exact Hlower |].
          destruct (@B.ordered_tail (R.ranking st) head rest ltac:(rewrite <- Hqueue; exact (B.store_ordered Hstore))) as [_ Htail].
          rewrite Forall_forall in *; intros x Hin; eapply B.lt_trans; [apply Htail; exact Hin |exact Hlower]. }
        exists (B.configuration (R.reset_registered_cells st owner) (R.Return k)); split.
        -- apply steps_cons with (next := B.configuration (R.reset_registered_cells st owner) (R.Return k)); [|constructor].
           machine_core; unfold R.next_config, B.configuration; cbn -[R.reset_registered_cells R.rank_lt]; rewrite Hqueue, Howner; cbn;
             destruct (V.eq_dec head owner); [contradiction |rewrite Hhigher; reflexivity].
        -- split; [apply B.queue_below_close; exact Hbelow |left; reflexivity].
Qed.
End Draining.

Theorem finite_queue_ceiling tf roots (finite : Sem.finite_system tf roots) st ctrl :
  reachable tf roots (B.configuration st ctrl) -> B.queue_ceiling st (RF.bound (Sem.support finite)).
Proof.
  intros Hreachable owner Hin.
  pose proof (@reachable_configuration_wf tf roots finite (B.configuration st ctrl) Hreachable) as [Hstore _].
  cbn [B.configuration R.cfg_state] in Hstore;
  pose proof (B.known_ranked_queue Hstore) as Hranked; rewrite Forall_forall in Hranked;
    destruct (Hranked owner Hin) as [rank Hrank]; exists rank; split; [exact Hrank |].
  eapply reachable_rank_bound; [exact Hreachable |exact Hrank].
Qed.

Lemma drain_core tf st fr k after : step tf (B.configuration st (R.RunDrain fr k)) after ->
  B.step tf (B.configuration st (R.RunDrain fr k)) after.
Proof.
  intro Hstep; apply step_view in Hstep; inversion Hstep; subst; assumption.
Qed.
Lemma lower_drain_no_round tf roots st fr k after phase : reachable tf roots (B.configuration st (R.RunDrain fr k)) ->
  B.queue_below st (R.frame_owner fr) -> episode_steps tf (R.frame_owner fr) (B.configuration st (R.RunDrain fr k)) after ->
  B.owner_phase (R.cfg_control after) (R.frame_owner fr) = Some phase -> R.cfg_control after <> R.RunDrain fr k -> False.
Proof.
  intros Hreach Hbelow Hpath Hphase Hdifferent.
  inversion Hpath as [|before next final Hactive Hstep Htail]; subst; [contradiction |].
  pose proof (B.drain_lower_returns Hbelow (drain_core Hstep)) as Hreturn.
  assert (Hclosing : B.closing (B.configuration st (R.RunDrain fr k)) next (R.frame_owner fr)) by
    (exists fr, k; repeat split; auto).
  assert (Hinactive : ~ In (R.frame_owner fr) (B.active_owners (R.cfg_control next))).
  { eapply B.closing_owner_inactive; [exact (B.ordered_unique (reachable_active_ordered Hreach)) |exact Hclosing]. }
  destruct (episode_active_or_equal Htail) as [->|Hin];
    [apply Hinactive; eapply B.owner_phase_present; exact Hphase |contradiction].
Qed.
Lemma quiet_prefix_of_equal tf roots (finite : Sem.finite_system tf roots) owner start middle last phase middle_phase last_phase :
  reachable tf roots start -> B.quiet_round (Sem.support finite) owner start ->
  B.owner_phase (R.cfg_control start) owner = Some phase ->
  B.owner_phase (R.cfg_control middle) owner = Some middle_phase ->
  B.owner_phase (R.cfg_control last) owner = Some last_phase ->
  episode_steps tf owner start middle -> episode_steps tf owner middle last ->
  B.round_budget (Sem.support finite) (R.cfg_state last) owner last_phase =
    B.round_budget (Sem.support finite) (R.cfg_state start) owner phase ->
  B.quiet_round (Sem.support finite) owner middle.
Proof.
  intros Hr Hquiet Hp Hm Hl Hprefix Hsuffix Heq.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) owner start middle phase middle_phase Hr Hp Hm Hprefix) as Hfirst.
  pose proof (@episode_owner_budget tf roots (Sem.support finite) owner middle last middle_phase last_phase
    (reachable_follow Hr (episode_path Hprefix)) Hm Hl Hsuffix) as Hlast.
  assert (Hsame : B.round_budget (Sem.support finite) (R.cfg_state middle) owner middle_phase =
    B.round_budget (Sem.support finite) (R.cfg_state start) owner phase) by
    (apply B.budget_le_antisym; [exact Hfirst |rewrite Heq in Hlast; exact Hlast]).
  eapply episode_quiet_round; eauto.
Qed.
Lemma decrease_round support owner flag st phase next next_phase :
  B.budget_le (B.round_budget support next owner next_phase) (B.round_budget support st owner phase) ->
  (flag = 0 -> B.budget_lt (B.round_budget support next owner next_phase) (B.round_budget support st owner phase)) ->
  round_order support owner (0,(next,next_phase)) (flag,(st,phase)).
Proof.
  intros [Heq|Hstrict] Hpaid; unfold round_order; cbn.
  - destruct flag; [apply Relation_Operators.left_slex; apply Hpaid; reflexivity |].
    rewrite Heq; apply Relation_Operators.right_slex; lia.
  - apply Relation_Operators.left_slex; exact Hstrict.
Qed.
Lemma clear_budget support st cleared owner phase :
  B.round_budget support (N.clear_owner st cleared) owner phase = B.round_budget support st owner phase.
Proof. reflexivity. Qed.
Section Rounds.
Variable tf : R.ConstraintSystem.system.
Variable roots : list V.t.
Variable finite : Sem.finite_system tf roots.
Variable owner : V.t.
Hypothesis higher_episodes : forall st child k,
  reachable tf roots (B.configuration st (R.StartEpisode child k)) -> R.rank_lt st owner child = true ->
  episode_complete tf (B.configuration st (R.StartEpisode child k)) child k.
Lemma rounds_finish : forall index : nat * (R.state * U.phase), forall fr k,
  R.frame_owner fr = owner -> R.frame_phase fr = snd (snd index) ->
  reachable tf roots (B.configuration (fst (snd index)) (R.RunRhs fr (tf owner) k)) ->
  ~ In owner (R.queue (fst (snd index))) ->
  (fst index = 0 -> B.queue_below (fst (snd index)) owner) ->
  episode_complete tf (B.configuration (fst (snd index)) (R.RunRhs fr (tf owner) k)) owner k.
Proof.
  intro index; induction index as [index IH] using (well_founded_induction (round_order_well_founded (Sem.support finite) owner)).
  destruct index as [flag [st phase]]; intros fr k Ho Hphase Hr Habsent Hbelow; cbn in Hphase, Hr, Habsent, Hbelow |- *.
  destruct (@rhs_evaluation tf roots owner (tf owner) st fr k higher_episodes Ho Hr)
    as [committed [commit_fr [direct [Hco Heval]]]].
  pose proof (evaluation_episode Heval) as Hprefix.
  pose proof (reachable_follow Hr (evaluation_path Heval)) as Hcommit.
  assert (Hfirst : B.owner_phase (R.RunRhs fr (tf owner) k) owner = Some phase) by
    (rewrite <- Ho, <- Hphase; apply B.phase_rhs).
  assert (Hcp : B.owner_phase (R.RunCommit commit_fr direct k) owner = Some (R.frame_phase commit_fr)) by
    (rewrite <- Hco; apply B.phase_commit).
  destruct (N.pending_above committed (R.frame_owner commit_fr)) as [[child rest]|] eqn:Hp.
  - assert (Hstep : step tf (B.configuration committed (R.RunCommit commit_fr direct k))
      (N.suspend_commit tf committed commit_fr k child rest)).
    { machine_core; rewrite Hp; reflexivity. }
    pose proof (reachable_advance Hcommit Hstep) as Hchild.
    destruct (pending_spec Hp) as [Hcontrolled [Hpop Hhigher]]; rewrite Hco in Hhigher.
    destruct (higher_episodes Hchild Hhigher) as [returned [Hepisode Hchildbelow]].
    set (saved := R.fresh_frame committed (R.frame_owner commit_fr) (R.frame_phase commit_fr)).
    assert (Hreturned : reachable tf roots (B.configuration returned (R.Return (R.KAfterSide saved (tf owner) k)))).
    { rewrite <- Hco; eapply reachable_follow; eauto. }
    assert (Hcontrolled' : S.mem owner (R.controlled returned) = true).
    { rewrite <- Hco; exact (paths_controlled Hepisode Hcontrolled). }
    destruct (@resume_to_rhs tf roots owner higher_episodes (RF.bound (Sem.support finite)) returned saved (tf owner) k
      Hco eq_refl Hcontrolled' Hreturned (finite_queue_ceiling finite Hreturned))
      as [final [final_fr [Hresume [Hfo [Hfp [Hfinalbelow Hfinalquiet]]]]]].
    assert (Hpost : steps tf (B.configuration committed (R.RunCommit commit_fr direct k))
      (B.configuration final (R.RunRhs final_fr (tf owner) k))).
    { eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |]].
      unfold saved in Hresume; rewrite Hco; rewrite Hco in Hresume; exact Hresume. }
    destruct (@trace_or_finish tf roots owner k _ _ Hcommit ltac:(left; auto) Hpost) as [Hdone|[Hsuffix Hscope]].
    + destruct (episode_finished_path Hdone) as [last [Htail Hlastbelow]].
      exists last; split; [eapply steps_append; [exact (evaluation_path Heval) |exact Htail] |exact Hlastbelow].
    + pose proof (episode_append Hprefix Hsuffix) as Hwhole.
      assert (Hlast : B.owner_phase (R.RunRhs final_fr (tf owner) k) owner = Some (R.frame_phase final_fr)) by
        (rewrite <- Hfo; apply B.phase_rhs).
      assert (Hbudget := @episode_owner_budget tf roots (Sem.support finite) owner (B.configuration st (R.RunRhs fr (tf owner) k)) (B.configuration final (R.RunRhs final_fr (tf owner) k)) phase (R.frame_phase final_fr)
        Hr Hfirst Hlast Hwhole).
      assert (Horder : round_order (Sem.support finite) owner (0,(final,R.frame_phase final_fr)) (flag,(st,phase))).
      { apply decrease_round; [exact Hbudget |]. intro Hzero; destruct Hbudget as [Heq|Hpaid]; [|exact Hpaid].
        pose proof (@quiet_prefix_of_equal tf roots finite owner (B.configuration st (R.RunRhs fr (tf owner) k)) (B.configuration committed (R.RunCommit commit_fr direct k)) (B.configuration final (R.RunRhs final_fr (tf owner) k)) phase (R.frame_phase commit_fr) (R.frame_phase final_fr)
          Hr ltac:(split; [apply Hbelow; exact Hzero |exact Ho]) Hfirst Hcp Hlast Hprefix Hsuffix Heq) as [Hquiet _].
        pose proof (below_not_pending Hquiet) as Hnone; cbn [B.configuration R.cfg_state] in Hnone; rewrite <- Hco in Hnone; congruence. }
      destruct (IH (0,(final,R.frame_phase final_fr)) Horder final_fr k Hfo eq_refl
        (reachable_follow Hcommit Hpost) Hfinalquiet ltac:(intros _; exact Hfinalbelow)) as [last [Htail Hlastbelow]].
      exists last; split; [eapply steps_append; [exact (evaluation_path Heval) |eapply steps_append; eauto] |exact Hlastbelow].
  - destruct (R.queue_contains (R.frame_owner commit_fr) (R.queue committed)) eqn:Hqueued.
    + assert (Hretry : step tf (B.configuration committed (R.RunCommit commit_fr direct k)) (N.retry_current tf committed commit_fr k)).
      { machine_core; rewrite Hp, Hqueued; reflexivity. }
      pose proof (@precommit_retry_paid tf roots finite st fr (tf owner) k committed commit_fr direct Hr
        ltac:(rewrite Ho; exact Habsent) ltac:(congruence) ltac:(rewrite Ho; exact Heval) Hretry) as Hpaid.
      set (next := N.clear_owner committed owner).
      set (fresh := R.fresh_frame committed owner (R.frame_phase commit_fr)).
      assert (Horder : round_order (Sem.support finite) owner (1,(next,R.frame_phase fresh)) (flag,(st,phase))).
      { unfold round_order; cbn; apply Relation_Operators.left_slex.
        unfold next, fresh; rewrite clear_budget; cbn [R.fresh_frame R.frame_phase]; rewrite Ho, Hphase in Hpaid; exact Hpaid. }
      assert (Hnew : reachable tf roots (B.configuration next (R.RunRhs fresh (tf owner) k))).
      { unfold next, fresh; pose proof (reachable_advance Hcommit Hretry) as Hnew; unfold N.retry_current in Hnew; rewrite Hco in Hnew; exact Hnew. }
      destruct (IH (1,(next,R.frame_phase fresh)) Horder fresh k eq_refl eq_refl Hnew
        (clear_not_queued committed owner) ltac:(discriminate)) as [last [Htail Hlastbelow]].
      exists last; split; [|exact Hlastbelow].
      eapply steps_append; [exact (evaluation_path Heval) |eapply steps_cons; [exact Hretry |]].
      unfold next, fresh in Htail; unfold N.retry_current; rewrite Hco; exact Htail.
    + destruct (R.set_value committed commit_fr direct) as [drained drain_fr] eqn:Hset.
      set (next := R.requeue_changed_controlled_owner committed drained (R.frame_owner commit_fr)).
      assert (Hstep : step tf (B.configuration committed (R.RunCommit commit_fr direct k))
        (B.configuration next (R.RunDrain drain_fr k))).
      { machine_core; rewrite Hp, Hqueued; unfold R.next_config; cbn -[R.set_value]; rewrite Hset; reflexivity. }
      pose proof (reachable_advance Hcommit Hstep) as Hdrain.
      assert (Hdo : R.frame_owner drain_fr = owner) by
        (rewrite (B.commit_owner (@B.commit_footprint committed commit_fr direct drained drain_fr Hset)); exact Hco).
      destruct (@drain_reaches_boundary tf roots owner higher_episodes (RF.bound (Sem.support finite)) next drain_fr k Hdo Hdrain
        (finite_queue_ceiling finite Hdrain)) as [boundary [Hdraining [Hboundarybelow Hboundary]]].
      destruct (@trace_or_finish tf roots owner k _ _ Hdrain ltac:(left; auto) Hdraining) as [Hdone|[Hsuffix Hscope]].
      * destruct (episode_finished_path Hdone) as [last [Htail Hlastbelow]].
        exists last; split; [|exact Hlastbelow].
        eapply steps_append; [exact (evaluation_path Heval) |eapply steps_cons; eauto].
      * destruct Hboundary as [Hreturn|[final_fr [Hcontrol [Hfo Hfp]]]].
        -- rewrite Hreturn in Hscope; exfalso; eapply B.episode_return_outside; exact Hscope.
        -- destruct boundary as [final ctrl]; cbn [B.configuration R.cfg_state R.cfg_control] in *; subst ctrl.
           assert (Hto_drain : episode_steps tf owner (B.configuration st (R.RunRhs fr (tf owner) k))
             (B.configuration next (R.RunDrain drain_fr k))) by
             (eapply episode_append; [exact Hprefix |eapply episode_cons; [cbn [B.configuration R.cfg_control B.active_owners]; left; exact Hco |exact Hstep |constructor]]).
           assert (Hwhole := episode_append Hto_drain Hsuffix).
           assert (Hdp : B.owner_phase (R.RunDrain drain_fr k) owner = Some (R.frame_phase drain_fr)) by
             (rewrite <- Hdo; apply B.phase_drain).
           assert (Hlast : B.owner_phase (R.RunRhs final_fr (tf owner) k) owner = Some (R.frame_phase final_fr)) by
             (rewrite <- Hfo; apply B.phase_rhs).
           assert (Hbudget := @episode_owner_budget tf roots (Sem.support finite) owner (B.configuration st (R.RunRhs fr (tf owner) k)) (B.configuration final (R.RunRhs final_fr (tf owner) k)) phase (R.frame_phase final_fr)
             Hr Hfirst Hlast Hwhole).
           assert (Horder : round_order (Sem.support finite) owner (0,(final,R.frame_phase final_fr)) (flag,(st,phase))).
           { apply decrease_round; [exact Hbudget |]. intro Hzero; destruct Hbudget as [Heq|Hpaid]; [|exact Hpaid].
             pose proof (@quiet_prefix_of_equal tf roots finite owner (B.configuration st (R.RunRhs fr (tf owner) k)) (B.configuration next (R.RunDrain drain_fr k)) (B.configuration final (R.RunRhs final_fr (tf owner) k)) phase (R.frame_phase drain_fr) (R.frame_phase final_fr)
               Hr ltac:(split; [apply Hbelow; exact Hzero |exact Ho]) Hfirst Hdp Hlast Hto_drain Hsuffix Heq) as [Hquiet _].
             exfalso; eapply lower_drain_no_round;
               [exact Hdrain |rewrite Hdo; exact Hquiet |rewrite Hdo; exact Hsuffix |rewrite Hdo; exact Hlast |discriminate]. }
           destruct (IH (0,(final,R.frame_phase final_fr)) Horder final_fr k Hfo eq_refl (reachable_follow Hdrain Hdraining)
             (below_owner_absent Hboundarybelow) ltac:(intros _; exact Hboundarybelow)) as [last [Htail Hlastbelow]].
           exists last; split; [|exact Hlastbelow].
           eapply steps_append; [exact (evaluation_path Heval) |eapply steps_cons; [exact Hstep |eapply steps_append; eauto]].
Qed.
Theorem episode_finish_from_higher st k : reachable tf roots (B.configuration st (R.StartEpisode owner k)) ->
  episode_complete tf (B.configuration st (R.StartEpisode owner k)) owner k.
Proof.
  intro Hreach; set (first := R.materialize (N.clear_owner st owner) owner).
  set (fr := R.fresh_frame first owner (U.initial_phase false owner)).
  assert (Hstep : step tf (B.configuration st (R.StartEpisode owner k)) (B.configuration first (R.RunRhs fr (tf owner) k))) by reflexivity.
  assert (Hquiet : ~ In owner (R.queue first)) by (unfold first; rewrite B.materialize_queue; apply clear_not_queued).
  destruct (@rounds_finish (1,(first,U.initial_phase false owner)) fr k eq_refl eq_refl
    (reachable_advance Hreach Hstep) Hquiet ltac:(discriminate)) as [last [Htail Hbelow]].
  exists last; split; [eapply steps_cons; eauto |exact Hbelow].
Qed.
End Rounds.
Lemma termination_has_fuel tf roots final : terminates_to tf roots final ->
  exists fuel, N.solve_fuel fuel tf roots = Some final.
Proof.
  intros [Hpath Hquiet]; destruct (path_fuel Hpath) as [fuel Hfuel]. exists fuel.
  unfold N.solve_fuel; rewrite Hfuel; unfold B.terminal, B.configuration, R.terminal_state; cbn; rewrite Hquiet; reflexivity.
Qed.
Theorem termination_iff_fuel tf roots :
  (exists final, terminates_to tf roots final) <-> (exists fuel final, N.solve_fuel fuel tf roots = Some final).
Proof.
  split; [intros [final Hterm]; destruct (termination_has_fuel Hterm) as [fuel Hrun]; eauto |
  intros [fuel [final Hrun]]; exists final; exact (@successful_path fuel tf roots final Hrun)].
Qed.
Lemma step_deterministic tf before left right : step tf before left -> step tf before right -> left = right.
Proof. unfold step; congruence. Qed.
Lemma paths_comparable tf start left right : steps tf start left -> steps tf start right ->
  steps tf left right \/ steps tf right left.
Proof.
  intros Hleft; revert right; induction Hleft; intros right Hright; [left; exact Hright |].
  inversion Hright as [|base next_right final Hnext Htail]; subst; [right; eapply steps_cons; eauto |].
  assert (next = next_right) by (eapply step_deterministic; eauto); subst next_right; apply IHHleft; exact Htail.
Qed.
Lemma reachable_rank_unique tf roots left right owner rank_left rank_right : reachable tf roots left -> reachable tf roots right ->
  Ranks.lookup (R.ranking (R.cfg_state left)) owner = Some rank_left ->
  Ranks.lookup (R.ranking (R.cfg_state right)) owner = Some rank_right -> rank_left = rank_right.
Proof.
  intros Hl Hr Hleft Hright; destruct (paths_comparable Hl Hr) as [Hpath |Hpath].
  - pose proof (steps_ranking_extends Hpath owner Hleft) as Hsame; congruence.
  - pose proof (steps_ranking_extends Hpath owner Hright) as Hsame; congruence.
Qed.
Theorem finite_episodes_finish tf roots (finite : Sem.finite_system tf roots) : forall st owner k,
  reachable tf roots (B.configuration st (R.StartEpisode owner k)) -> episode_complete tf (B.configuration st (R.StartEpisode owner k)) owner k.
Proof.
  assert (Hfinish : forall distance st owner k rank,
    reachable tf roots (B.configuration st (R.StartEpisode owner k)) -> Ranks.lookup (R.ranking st) owner = Some rank ->
    RF.bound (Sem.support finite) - rank = distance -> episode_complete tf (B.configuration st (R.StartEpisode owner k)) owner k).
  { intro distance; induction distance using lt_wf_ind; intros st owner k rank Hreachable Hrank Hdistance.
    refine (@episode_finish_from_higher tf roots finite owner _ st k Hreachable).
    intros next child child_k Hchild Hhigher.
    destruct (@B.lt_ranks (R.ranking next) owner child Hhigher) as [parent_rank [child_rank [Hparent [Hrank_child Hlt]]]].
    assert (Hparent_rank : parent_rank = rank).
    { eapply reachable_rank_unique; [exact Hchild |exact Hreachable |exact Hparent |exact Hrank]. }
    subst parent_rank.
    assert (Hchild_bound : child_rank < RF.bound (Sem.support finite)) by (eapply reachable_rank_bound; [exact Hchild |exact Hrank_child]).
    eapply H with (m := RF.bound (Sem.support finite) - child_rank) (rank := child_rank);
      [lia |exact Hchild |exact Hrank_child |reflexivity]. }
  intros st owner k Hreachable.
  pose proof (@reachable_rank_configuration tf roots (B.configuration st (R.StartEpisode owner k)) Hreachable) as [_ Hrefs].
  cbn [B.configuration R.cfg_control R.cfg_state B.control_refs] in Hrefs; destruct (proj2 (proj1 Hrefs)) as [rank Hrank].
  exact (Hfinish (RF.bound (Sem.support finite) - rank) st owner k rank Hreachable Hrank eq_refl).
Qed.


(** Root seeding and the outer queue share the same drain argument. *)
Definition outer_control remaining := match remaining with
  | None => R.RunLoop | Some roots => R.RunSeedLoop roots end.
Definition outer_stack remaining := match remaining with
  | None => R.KLoop | Some roots => R.KSeedLoop roots end.
Definition outer_done remaining := match remaining with
  | None => R.RunLoop | Some roots => R.RunSeeds roots end.
Lemma outer_drain_finish tf roots (finite : Sem.finite_system tf roots) : forall ceiling st remaining,
  reachable tf roots (B.configuration st (outer_control remaining)) -> B.queue_ceiling st ceiling ->
  exists final, steps tf (B.configuration st (outer_control remaining)) (B.configuration final (outer_done remaining)) /\ B.quiescent final.
Proof.
  intro ceiling; induction ceiling using lt_wf_ind; intros st remaining Hreachable Hceiling.
  destruct (R.queue st) as [|head rest] eqn:Hqueue.
  - exists st; split; [|exact Hqueue]; destruct remaining as [remaining |]; [|constructor].
    eapply steps_cons; [machine_core; unfold R.next_config, B.configuration; cbn [outer_control R.cfg_state R.cfg_control R.next_config R.queue_pop]; rewrite Hqueue; reflexivity |constructor].
  - assert (Hstep : step tf (B.configuration st (outer_control remaining))
      (B.configuration (R.with_queue st rest) (R.StartEpisode head (outer_stack remaining)))).
    { destruct remaining; machine_core; unfold R.next_config, B.configuration; cbn [outer_control outer_stack R.cfg_state R.cfg_control R.next_config R.queue_pop]; rewrite Hqueue; reflexivity. }
    pose proof (reachable_advance Hreachable Hstep) as Hstart.
    destruct (@finite_episodes_finish tf roots finite (R.with_queue st rest) head (outer_stack remaining) Hstart)
      as [returned [Hepisode Hbelow]].
    destruct (Hceiling head ltac:(rewrite Hqueue; left; reflexivity)) as [rank [Hrank Hbound]].
    assert (Hreturned_rank : Ranks.lookup (R.ranking returned) head = Some rank) by (exact (steps_ranking_extends Hepisode head Hrank)).
    assert (Hresume : step tf (B.configuration returned (R.Return (outer_stack remaining))) (B.configuration returned (outer_control remaining)))
      by (destruct remaining; reflexivity).
    pose proof (reachable_advance (reachable_follow Hstart Hepisode) Hresume) as Hcontinued.
    destruct (H rank Hbound returned remaining Hcontinued (B.queue_below_ceiling Hbelow Hreturned_rank)) as [final [Htail Hquiet]].
    exists final; split; [eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; eauto]] |exact Hquiet].
Qed.
Lemma seeds_finish tf roots (finite : Sem.finite_system tf roots) : forall remaining st,
  reachable tf roots (B.configuration st (R.RunSeeds remaining)) ->
  exists final, steps tf (B.configuration st (R.RunSeeds remaining)) (B.terminal final) /\ B.quiescent final.
Proof.
  intro remaining; induction remaining as [|root remaining IH]; intros st Hreachable.
  - assert (Hstep : step tf (B.configuration st (R.RunSeeds [])) (B.configuration st R.RunLoop)) by reflexivity.
    pose proof (reachable_advance Hreachable Hstep) as Hloop.
    destruct (@outer_drain_finish tf roots finite (RF.bound (Sem.support finite)) st None Hloop
      (@finite_queue_ceiling tf roots finite st R.RunLoop Hloop)) as [final [Htail Hquiet]].
    exists final; split; [eapply steps_cons; eauto |exact Hquiet].
  - set (observed := R.observe st root).
    destruct (R.is_materialized observed root) eqn:Hmat.
    + assert (Hstep : step tf (B.configuration st (R.RunSeeds (root :: remaining))) (B.configuration observed (R.RunSeeds remaining))).
      { machine_core; unfold R.next_config, B.configuration; cbn -[R.observe]; fold observed; rewrite Hmat; reflexivity. }
      destruct (IH observed (reachable_advance Hreachable Hstep)) as [final [Htail Hquiet]].
      exists final; split; [eapply steps_cons; eauto |exact Hquiet].
    + assert (Hstep : step tf (B.configuration st (R.RunSeeds (root :: remaining)))
        (B.configuration observed (R.StartEpisode root (R.KSeedLoop remaining)))).
      { machine_core; unfold R.next_config, B.configuration; cbn -[R.observe]; fold observed; rewrite Hmat; reflexivity. }
      pose proof (reachable_advance Hreachable Hstep) as Hstart.
      destruct (@finite_episodes_finish tf roots finite observed root (R.KSeedLoop remaining) Hstart) as [returned [Hepisode Hbelow]].
      assert (Hresume : step tf (B.configuration returned (R.Return (R.KSeedLoop remaining))) (B.configuration returned (R.RunSeedLoop remaining))) by reflexivity.
      pose proof (reachable_advance (reachable_follow Hstart Hepisode) Hresume) as Hdrain.
      destruct (@outer_drain_finish tf roots finite (RF.bound (Sem.support finite)) returned (Some remaining) Hdrain
        (@finite_queue_ceiling tf roots finite returned (R.RunSeedLoop remaining) Hdrain)) as [seeded [Houter Hquiet]].
      pose proof (reachable_follow Hdrain Houter) as Hseeded.
      destruct (IH seeded Hseeded) as [final [Htail Hfinal]].
      exists final; split; [|exact Hfinal].
      eapply steps_cons; [exact Hstep |eapply steps_append; [exact Hepisode |eapply steps_cons; [exact Hresume |eapply steps_append; eauto]]].
Qed.
Theorem solver_terminates tf roots : Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
Proof. intro finite; apply (@seeds_finish tf roots finite roots R.empty_state); constructor. Qed.
Theorem finite_fuel_success tf roots : Sem.finite_system tf roots -> exists fuel final, N.solve_fuel fuel tf roots = Some final.
Proof.
  intro finite; apply (proj1 (@termination_iff_fuel tf roots)); exact (solver_terminates finite).
Qed.
Theorem semantic_total_correct tf roots : Sem.finite_system tf roots ->
  exists final, terminates_to tf roots final /\ correct_final_state tf roots final.
Proof.
  intro finite; destruct (solver_terminates finite) as [final Htermination]; exists final; split; [exact Htermination |].
  destruct (termination_has_fuel Htermination) as [fuel Hsuccess].
  exact (@successful_run_correct fuel tf roots final Hsuccess).
Qed.

Definition semantic_termination := solver_terminates.
Definition sufficient_fuel := finite_fuel_success.
Theorem total_correct tf roots : Sem.finite_system tf roots ->
  exists fuel final, N.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
Proof.
  intro finite; destruct (sufficient_fuel finite) as [fuel [final Hrun]].
  exists fuel, final; split; [exact Hrun |exact (@successful_run_correct fuel tf roots final Hrun)].
Qed.
Theorem total_least_solution tf roots (finite : Sem.finite_system tf roots) :
  (forall side x phase old input upper, D.leq old upper = true -> D.leq input upper = true ->
    D.leq (snd (U.update side x phase old input)) upper = true) ->
  B.source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
  exists fuel final, N.solve_fuel fuel tf roots = Some final /\
    Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
Proof.
  intros Hbounded Hstrict Hmono; destruct (sufficient_fuel finite) as [fuel [final Hrun]].
  exists fuel, final; split; [exact Hrun |].
  exact (@successful_run_least Hbounded fuel tf roots finite final Hstrict Hmono Hrun).
Qed.

End Make.
