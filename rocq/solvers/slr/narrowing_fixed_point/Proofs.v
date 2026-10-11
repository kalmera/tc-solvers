From Stdlib Require Import List Bool Lia Arith.PeanoNat Arith.Wf_nat Sorting.Sorted.
From TcSolvers Require Import common.Assumptions common.SolverSpecifications common.SolverInterfaces
  common.BoxUpdate common.SolverParameters
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
Module Solver := B.Solver.
Module N := Solver.N.
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

(** Precision certificates use historical observations. Monotonicity keeps
    later reads below those observations, so narrowing waves have no growing
    owner input. The certificates are proof-only. *)
Module FixedPoint (Parameters : STABLE_FIXED_POINT_PARAMETERS).
Module V := Parameters.V.
Module D := Parameters.D.
Module WN := Parameters.WN.
Module WNL := Parameters.WNL.
Module WS := Parameters.WS.
Module S := Parameters.S.
Module M := Parameters.M.
Module Features := Parameters.Features.
Module DL := Parameters.DL.
Module SL := Parameters.SL.
Module ML := Parameters.ML.
Module U := Parameters.FixedU.
Module UL := Parameters.FixedUL.
Module P := Make V D U S M Features DL UL SL ML.
Module B := P.B.
Module R := P.R.
Module N := P.N.
Module Sem.
  Include P.Sem.
  Arguments support _ _ _ : clear implicits.
  Module R := P.R.
  Module ConstraintSyntax := P.B.Syntax.
  Definition step := P.B.step.
  Definition steps := P.B.steps.
  Definition StepsRefl := P.B.steps_refl.
  Definition StepsStep := P.B.steps_cons.
  Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
  Definition terminal_config := P.B.terminal.
  Definition terminates_to tf roots final :=
    steps tf (R.initial_config roots) (terminal_config final) /\ quiescent final.
  Definition solved := P.Spec.solved.
  Definition state_valuation (st : R.state) : valuation := R.sigma_value st.
  Definition rhs_eval := P.Spec.replay.
  Definition side_effects_below (st : R.state) (effects : list (V.t * D.t)) :=
    forall target value, In (target,value) effects -> D.leq value (R.sigma_value st target) = true.
  Definition rhs_post_solution (st : R.state) owner (body : R.ConstraintSystem.rhs) :=
    forall direct reads effects, rhs_eval st body direct reads effects ->
      D.leq direct (R.sigma_value st owner) = true /\ side_effects_below st effects.
  Definition correct_final_state tf roots final := forall owner, In owner roots ->
    solved final owner /\ rhs_post_solution final owner (tf owner).
  Definition totally_correct_on tf roots := exists fuel final,
    R.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final.
  Definition rhs_observes_spawns_supported := P.B.supported_spawns.
  Definition observes_at_deterministic := P.B.observation_unique.
End Sem.
Module O := Sem.Observation.
Module Spec := P.Spec.
Include Spec.
Definition values_descend before after := forall target,
  D.leq (R.sigma_value after target) (R.sigma_value before target) = true.
Definition rows_descend before after := forall source target,
  D.leq (R.stored_contribution after source target) (R.stored_contribution before source target) = true.
Definition aggregates_descend before after := forall target,
  D.leq (R.aggregate after target) (R.aggregate before target) = true.
Lemma smaller_update side owner phase old input : D.leq input old = true ->
  D.leq (snd (U.update side owner phase old input)) old = true.
Proof.
  intro H; destruct phase; cbn -[D.leq];
    [rewrite H; apply WNL.narrow_upper; exact H |rewrite H; apply WNL.narrow_upper; exact H |exact (proj1 (WS.widen_stable H))].
Qed.
Record history tf st owner := {
  history_result : O.observation;
  history_trace : Sem.rhs_observes (tf owner) history_result;
  history_floor : forall target value, In (target,value) (O.observed_reads history_result) ->
    D.leq (R.sigma_value st target) value = true;
  history_reads_live : forall target value, In (target,value) (O.observed_reads history_result) -> B.solved st target;
  history_spawns_live : forall target, In target (O.observed_spawns history_result) -> B.solved st target;
  history_value : D.leq (D.join (O.observed_direct history_result) (R.aggregate st owner)) (R.sigma_value st owner) = true;
  history_sides : forall target raw, In (target,raw) (O.observed_sides history_result) ->
    D.leq raw (R.stored_contribution st owner target) = true
}.
Definition common_prefix (upper : O.observation) reads := forall target value upper_value,
  In (target,value) reads -> In (target,upper_value) (O.observed_reads upper) -> D.leq value upper_value = true.
Lemma dependency_values body lower upper : Sem.rhs_dependencies_monotone body ->
  Sem.rhs_observes body lower -> Sem.rhs_observes body upper -> O.common_read_values_le lower upper ->
  O.valued_events_le (O.observed_reads lower) (O.observed_reads upper).
Proof.
  intros Hmono Hl Hu Hcommon target value Hin.
  assert (Htarget : In target (map fst (O.observed_reads lower))) by (apply in_map_iff; exists (target,value); auto).
  apply (Hmono lower upper Hl Hu Hcommon) in Htarget.
  apply in_map_iff in Htarget; destruct Htarget as [[query upper_value] [Heq Hupper]]; cbn in Heq; subst query.
  exists upper_value; split; [exact Hupper |eapply Hcommon; eauto].
Qed.
Lemma prefix_effects tf st fr body reads sides spawns (upper : history tf st (R.frame_owner fr)) lower :
  monotonic_system tf -> B.observation_prefix (tf (R.frame_owner fr)) body reads sides spawns ->
  common_prefix (history_result upper) reads -> Sem.rhs_observes body lower ->
  (forall target value, In (target,value) (O.observed_reads lower) ->
    forall upper_value, In (target,upper_value) (O.observed_reads (history_result upper)) -> D.leq value upper_value = true) ->
  O.effects_le {| O.observed_direct := O.observed_direct lower;
    O.observed_reads := reads ++ O.observed_reads lower;
    O.observed_sides := sides ++ O.observed_sides lower;
    O.observed_spawns := spawns ++ O.observed_spawns lower |} (history_result upper) /\
  O.valued_events_le (reads ++ O.observed_reads lower) (O.observed_reads (history_result upper)).
Proof.
  intros Hmono Hprefix Hcommon Hlower Hfuture.
  set (whole := {| O.observed_direct := O.observed_direct lower;
    O.observed_reads := reads ++ O.observed_reads lower;
    O.observed_sides := sides ++ O.observed_sides lower;
    O.observed_spawns := spawns ++ O.observed_spawns lower |}).
  assert (Htrace : Sem.rhs_observes (tf (R.frame_owner fr)) whole) by (apply Hprefix; exact Hlower).
  assert (Hvalues : O.common_read_values_le whole (history_result upper)).
  { intros target value upper_value Hin Hu; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
    [eapply Hcommon |eapply Hfuture]; eauto. }
  pose proof (dependency_values (proj1 (Hmono (R.frame_owner fr))) Htrace (history_trace upper) Hvalues) as Hreads.
  split; [exact ((proj2 (Hmono (R.frame_owner fr))) whole (history_result upper) Htrace (history_trace upper) Hreads) |exact Hreads].
Qed.
Lemma bottom_future body : exists result, Sem.rhs_observes body result /\
  (forall target value, In (target,value) (O.observed_reads result) -> value = D.bottom).
Proof.
  destruct (B.observation_total (fun _ => D.bottom) body) as [result [Ht Hr]]; exists result; auto.
Qed.
Lemma prefix_get_live tf st fr target tail reads sides spawns (upper : history tf st (R.frame_owner fr)) :
  monotonic_system tf -> B.observation_prefix (tf (R.frame_owner fr)) (R.ConstraintSystem.Get target tail) reads sides spawns ->
  common_prefix (history_result upper) reads -> B.solved st target.
Proof.
  intros Hmono Hp Hcommon.
  destruct (bottom_future (tail (R.sigma_value st target))) as [result [Ht Hbot]].
  pose proof (@prefix_effects tf st fr (R.ConstraintSystem.Get target tail) reads sides spawns upper
    {| O.observed_direct := O.observed_direct result;
       O.observed_reads := (target,R.sigma_value st target)::O.observed_reads result;
       O.observed_sides := O.observed_sides result;
       O.observed_spawns := O.observed_spawns result |}
    Hmono Hp Hcommon (@Sem.ObserveGet target (R.sigma_value st target) tail result Ht)
    ltac:(intros query value [Heq|Hin] upper_value Hu; [inversion Heq; subst; eapply history_floor; exact Hu |rewrite (Hbot query value Hin); apply DL.bottom_least])) as [_ Hr].
  destruct (Hr target (R.sigma_value st target) ltac:(apply in_or_app; right; left; reflexivity)) as [value [Hin _]].
  eapply history_reads_live; exact Hin.
Qed.
Lemma prefix_side_bounded tf st fr target raw body reads sides spawns (upper : history tf st (R.frame_owner fr)) :
  monotonic_system tf -> B.observation_prefix (tf (R.frame_owner fr)) (R.ConstraintSystem.Side target raw body) reads sides spawns ->
  common_prefix (history_result upper) reads -> D.leq raw (R.stored_contribution st (R.frame_owner fr) target) = true.
Proof.
  intros Hmono Hp Hcommon; destruct (bottom_future body) as [result [Ht Hbot]].
  destruct (@prefix_effects tf st fr (R.ConstraintSystem.Side target raw body) reads sides spawns upper
    {| O.observed_direct := O.observed_direct result;
       O.observed_reads := O.observed_reads result;
       O.observed_sides := (target,raw)::O.observed_sides result;
       O.observed_spawns := O.observed_spawns result |}
    Hmono Hp Hcommon (@Sem.ObserveSide target raw body result Ht) ltac:(intros query value Hin upper_value Hu; rewrite (Hbot query value Hin); apply DL.bottom_least)) as [He _].
  destruct (O.side_effects_le He target raw ltac:(apply in_or_app; right; left; reflexivity)) as [value [Hin Hle]].
  eapply DL.leq_trans; [exact Hle |eapply history_sides; exact Hin].
Qed.
Lemma prefix_spawn_live tf st fr target body reads sides spawns (upper : history tf st (R.frame_owner fr)) :
  monotonic_system tf -> B.observation_prefix (tf (R.frame_owner fr)) (R.ConstraintSystem.Spawn target body) reads sides spawns ->
  common_prefix (history_result upper) reads -> B.solved st target.
Proof.
  intros Hmono Hp Hcommon; destruct (bottom_future body) as [result [Ht Hbot]].
  destruct (@prefix_effects tf st fr (R.ConstraintSystem.Spawn target body) reads sides spawns upper
    {| O.observed_direct := O.observed_direct result;
       O.observed_reads := O.observed_reads result;
       O.observed_sides := O.observed_sides result;
       O.observed_spawns := target::O.observed_spawns result |}
    Hmono Hp Hcommon (@Sem.ObserveSpawn target body result Ht) ltac:(intros query value Hin upper_value Hu; rewrite (Hbot query value Hin); apply DL.bottom_least)) as [He _].
  apply (history_spawns_live upper); apply (O.spawn_effects_le He); apply in_or_app; right; left; reflexivity.
Qed.
Definition local_bounded st fr := forall target input,
  M.lookup (R.frame_local_side fr) target = Some input -> D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true.
Definition accumulated fr sides := forall target raw, In (target,raw) sides ->
  exists input, M.lookup (R.frame_local_side fr) target = Some input /\ D.leq raw input = true.
Record running tf st fr body := {
  running_upper : history tf st (R.frame_owner fr);
  running_reads : list (V.t * D.t);
  running_sides : list (V.t * D.t);
  running_spawns : list V.t;
  running_prefix : B.observation_prefix (tf (R.frame_owner fr)) body running_reads running_sides running_spawns;
  running_common : common_prefix (history_result running_upper) running_reads;
  running_floor : forall target value, In (target,value) running_reads -> D.leq (R.sigma_value st target) value = true;
  running_reads_live : forall target value, In (target,value) running_reads -> B.solved st target;
  running_spawns_live : forall target, In target running_spawns -> B.solved st target;
  running_accumulated : accumulated fr running_sides;
  running_local : local_bounded st fr
}.
Record complete tf st fr direct := {
  complete_reads : list (V.t * D.t);
  complete_sides : list (V.t * D.t);
  complete_spawns : list V.t;
  complete_trace : Sem.rhs_observes (tf (R.frame_owner fr))
    {| O.observed_direct := direct; O.observed_reads := complete_reads; O.observed_sides := complete_sides; O.observed_spawns := complete_spawns |};
  complete_floor : forall target value, In (target,value) complete_reads -> D.leq (R.sigma_value st target) value = true;
  complete_reads_live : forall target value, In (target,value) complete_reads -> B.solved st target;
  complete_spawns_live : forall target, In target complete_spawns -> B.solved st target;
  complete_accumulated : accumulated fr complete_sides;
  complete_local : local_bounded st fr;
  complete_value : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true
}.
Lemma complete_history tf st fr direct : complete tf st fr direct -> history tf st (R.frame_owner fr).
Proof.
  intros [rs ss ps Htrace Hfloor Hreads Hspawns Hraw Hcache Hvalue].
  refine (@Build_history tf st (R.frame_owner fr)
    {| O.observed_direct := direct; O.observed_reads := rs; O.observed_sides := ss; O.observed_spawns := ps |}
    Htrace Hfloor Hreads Hspawns Hvalue _).
  intros target raw Hin; destruct (Hraw target raw Hin) as [input [Hlookup Hle]].
  eapply DL.leq_trans; [exact Hle |apply Hcache; exact Hlookup].
Qed.
Lemma running_fresh tf st owner phase : history tf st owner -> running tf st (R.fresh_frame st owner phase) (tf owner).
Proof.
  intro Hh; refine (@Build_running tf st (R.fresh_frame st owner phase) (tf owner) Hh [] [] [] (@B.prefix_fresh (tf owner)) _ _ _ _ _ _).
  all: try solve [intros target value Hin; contradiction].
  all: try solve [intros target value upper_value Hin; contradiction].
  all: try solve [intros target Hin; contradiction].
  intros target input Hlookup; cbn in Hlookup; rewrite ML.lookup_empty in Hlookup; discriminate.
Qed.
Lemma running_complete tf st fr direct : monotonic_system tf -> running tf st fr (R.ConstraintSystem.Ret direct) -> complete tf st fr direct.
Proof.
  intros Hmono [upper rs ss ps Hp Hcommon Hfloor Hreads Hspawns Hraw Hlocal].
  refine (@Build_complete tf st fr direct rs ss ps (B.prefix_return Hp) Hfloor Hreads Hspawns Hraw Hlocal _).
  destruct (@prefix_effects tf st fr (R.ConstraintSystem.Ret direct) rs ss ps upper
    {| O.observed_direct := direct; O.observed_reads := []; O.observed_sides := []; O.observed_spawns := [] |}
    Hmono Hp Hcommon (Sem.ObserveRet direct) ltac:(intros target value Hin; contradiction)) as [He _].
  eapply DL.leq_trans; [apply DL.join_least |exact (history_value upper)].
  - eapply DL.leq_trans; [exact (O.direct_effect_le He) |apply DL.join_upper_left].
  - apply DL.join_upper_right.
Qed.
Lemma history_transport tf before after owner (h : history tf before owner) :
  values_descend before after -> B.preserves_live before after ->
  R.sigma_value after owner = R.sigma_value before owner -> aggregates_descend before after ->
  (forall target, R.stored_contribution after owner target = R.stored_contribution before owner target) ->
  { next : history tf after owner & history_result next = history_result h }.
Proof.
  intros Hvalues Hlive Howner Haggregate Hrow.
  unshelve eexists; [refine {| history_result := history_result h; history_trace := history_trace h |} |reflexivity].
  - intros target value Hin; eapply DL.leq_trans; [apply Hvalues |apply (history_floor h); exact Hin].
  - intros target value Hin; apply Hlive; eapply history_reads_live; exact Hin.
  - intros target Hin; apply Hlive; apply (history_spawns_live h); exact Hin.
  - rewrite Howner; eapply DL.leq_trans; [apply DL.join_least |exact (history_value h)].
    + apply DL.join_upper_left.
    + eapply DL.leq_trans; [apply Haggregate |apply DL.join_upper_right].
  - intros target raw Hin; rewrite Hrow; apply (history_sides h); exact Hin.
Qed.
Lemma aggregate_put_down st source target value : D.leq value (R.stored_contribution st source target) = true ->
  D.leq (R.aggregate (R.with_contributions st (R.update_map (R.contributions st) target source value)) target)
    (R.aggregate st target) = true.
Proof.
  intro Hvalue; unfold R.aggregate, R.update_map; cbn; unfold R.lookup_map at 1; rewrite ML.lookup_update_same.
  set (row := R.lookup_map (R.contributions st) target).
  destruct (ML.values_update row source value) as [rest [Hnew Hold]].
  eapply DL.leq_trans; [exact (proj1 (B.fold_permutation Hnew)) |].
  unfold R.stored_contribution in Hvalue; fold row in Hvalue.
  destruct (M.lookup row source) as [old|] eqn:Ho.
  - eapply DL.leq_trans; [apply DL.join_least |exact (proj2 (B.fold_permutation Hold))].
    + eapply DL.leq_trans; [exact Hvalue |apply DL.join_upper_left].
    + apply DL.join_upper_right.
  - eapply DL.leq_trans; [apply DL.join_least |exact (proj2 (B.fold_permutation Hold))].
    + eapply DL.leq_trans; [exact Hvalue |apply DL.bottom_least].
    + apply DL.leq_refl.
Qed.
Lemma write_descends st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
  rows_descend st next /\ aggregates_descend st next.
Proof.
  intros Hw Hin.
  assert (Hwritten : D.leq (R.stored_contribution next (R.frame_owner fr) target)
    (R.stored_contribution st (R.frame_owner fr) target) = true).
  { unfold R.write_side_contribution in Hw.
    set (base := R.promote_side_target st fr target) in *.
    assert (Hold : R.stored_contribution base (R.frame_owner fr) target = R.stored_contribution st (R.frame_owner fr) target).
    { unfold base, R.promote_side_target; destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
    destruct (U.update true target (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
      (R.stored_contribution base (R.frame_owner fr) target) input) as [phase value] eqn:Hu.
    inversion Hw; subst next changed.
    rewrite (proj2 (P.installed_cell base (R.frame_owner fr) target (R.frame_min_scope fr) phase value)).
    pose proof (@smaller_update true target (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
      (R.stored_contribution base (R.frame_owner fr) target) input ltac:(rewrite Hold; exact Hin)) as Hdown.
    rewrite Hu, Hold in Hdown; exact Hdown. }
  split.
  - intros source observed; destruct (V.eq_dec source (R.frame_owner fr)) as [->|Hs], (V.eq_dec observed target) as [->|Ht];
      [exact Hwritten | | |]; rewrite (B.write_other_contribution Hw) by tauto; apply DL.leq_refl.
  - intro observed; destruct (V.eq_dec observed target) as [->|Hother].
    + unfold R.write_side_contribution in Hw; unfold R.promote_side_target, R.promote_controlled in Hw;
      destruct (R.rank_lt st target (R.frame_owner fr)); cbn -[U.update R.register_reset] in Hw;
      destruct (U.update true target _ _ input) as [phase value] eqn:Hu; inversion Hw; subst next changed;
      change (D.leq (R.aggregate (R.with_contributions st (R.update_map (R.contributions st) target (R.frame_owner fr) value)) target)
        (R.aggregate st target) = true); apply aggregate_put_down;
      change (U.update true target (R.side_phase (R.stored_side_cell st (R.frame_owner fr) target)) (R.stored_contribution st (R.frame_owner fr) target) input = (phase,value)) in Hu;
      pose proof (@smaller_update true target (R.side_phase (R.stored_side_cell st (R.frame_owner fr) target)) (R.stored_contribution st (R.frame_owner fr) target) input Hin) as Hdown;
      rewrite Hu in Hdown; exact Hdown.
    + unfold R.aggregate; destruct (B.write_layout Hw) as [_ [Hcontrib _]].
      unfold R.write_side_contribution in Hw; destruct (U.update _ _ _ _ _) as [phase value]; inversion Hw; subst next;
      unfold R.register_reset; cbn [R.with_cells_and_resets R.with_contributions R.contributions];
      unfold R.lookup_map, R.update_map; rewrite ML.lookup_update_other by exact Hother;
      unfold R.promote_side_target, R.promote_controlled; destruct (R.rank_lt st target (R.frame_owner fr)); apply DL.leq_refl.
Qed.
Lemma values_same before after : R.sigma after = R.sigma before -> values_descend before after.
Proof. intros H target; unfold R.sigma_value; rewrite H; apply DL.leq_refl. Qed.
Lemma aggregates_same before after : R.contributions after = R.contributions before -> aggregates_descend before after.
Proof. intros H target; unfold R.aggregate; rewrite H; apply DL.leq_refl. Qed.
Lemma rows_same before after : R.contributions after = R.contributions before ->
  forall source target, R.stored_contribution after source target = R.stored_contribution before source target.
Proof. intros H source target; unfold R.stored_contribution; now rewrite H. Qed.
Lemma running_transport tf before after fr body : values_descend before after -> B.preserves_live before after ->
  R.sigma_value after (R.frame_owner fr) = R.sigma_value before (R.frame_owner fr) -> aggregates_descend before after ->
  (forall target, R.stored_contribution after (R.frame_owner fr) target = R.stored_contribution before (R.frame_owner fr) target) ->
  running tf before fr body -> running tf after fr body.
Proof.
  intros Hvalues Hlive Howner Haggregate Hrow [upper rs ss ps Hp Hcommon Hfloor Hreads Hspawns Hraw Hlocal].
  destruct (@history_transport tf before after (R.frame_owner fr) upper Hvalues Hlive Howner Haggregate Hrow) as [next Hresult].
  refine (@Build_running tf after fr body next rs ss ps Hp _ _ _ _ Hraw _).
  - rewrite Hresult; exact Hcommon.
  - intros target value Hin; eapply DL.leq_trans; [apply Hvalues |apply Hfloor; exact Hin].
  - intros target value Hin; apply Hlive; eapply Hreads; exact Hin.
  - intros target Hin; apply Hlive, Hspawns; exact Hin.
  - intros target input Hlookup; rewrite Hrow; apply Hlocal; exact Hlookup.
Qed.
Lemma running_payload tf before after fr body : R.sigma after = R.sigma before ->
  R.contributions after = R.contributions before -> running tf before fr body -> running tf after fr body.
Proof.
  intros Hsigma Hrows; apply running_transport;
    [apply values_same; exact Hsigma |apply B.preserves_live_layout; exact Hsigma |
     unfold R.sigma_value; now rewrite Hsigma |apply aggregates_same; exact Hrows |
     apply rows_same; exact Hrows].
Qed.
Lemma complete_transport tf before after fr direct : values_descend before after -> B.preserves_live before after ->
  R.sigma_value after (R.frame_owner fr) = R.sigma_value before (R.frame_owner fr) -> aggregates_descend before after ->
  (forall target, R.stored_contribution after (R.frame_owner fr) target = R.stored_contribution before (R.frame_owner fr) target) ->
  complete tf before fr direct -> complete tf after fr direct.
Proof.
  intros Hvalues Hlive Howner Haggregate Hrow [rs ss ps Ht Hfloor Hreads Hspawns Hraw Hlocal Hvalue].
  refine (@Build_complete tf after fr direct rs ss ps Ht _ _ _ Hraw _ _).
  - intros target value Hin; eapply DL.leq_trans; [apply Hvalues |apply Hfloor; exact Hin].
  - intros target value Hin; apply Hlive; eapply Hreads; exact Hin.
  - intros target Hin; apply Hlive, Hspawns; exact Hin.
  - intros target input Hlookup; rewrite Hrow; apply Hlocal; exact Hlookup.
  - rewrite Howner; eapply DL.leq_trans; [apply DL.join_least |exact Hvalue];
      [apply DL.join_upper_left |eapply DL.leq_trans; [apply Haggregate |apply DL.join_upper_right]].
Qed.
Lemma complete_payload tf before after fr direct : R.sigma after = R.sigma before ->
  R.contributions after = R.contributions before -> complete tf before fr direct -> complete tf after fr direct.
Proof.
  intros Hsigma Hrows; apply complete_transport;
    [apply values_same; exact Hsigma |apply B.preserves_live_layout; exact Hsigma |
     unfold R.sigma_value; now rewrite Hsigma |apply aggregates_same; exact Hrows |
     apply rows_same; exact Hrows].
Qed.
Lemma history_payload tf before after owner (h : history tf before owner) : R.sigma after = R.sigma before ->
  R.contributions after = R.contributions before -> history tf after owner.
Proof.
  intros Hsigma Hrows; destruct (@history_transport tf before after owner h
    (@values_same before after Hsigma) (@B.preserves_live_layout before after Hsigma) ltac:(unfold R.sigma_value; rewrite Hsigma; reflexivity)
    (@aggregates_same before after Hrows) (@rows_same before after Hrows owner)) as [next _]; exact next.
Qed.
Lemma known_get_data st fr target next next_fr value : B.solved st target ->
  R.complete_get st fr target = (next,next_fr,value) -> R.sigma next = R.sigma st /\
  value = R.sigma_value st target.
Proof.
  intros [stored Hstored] Hget; change (M.lookup (R.sigma st) target = Some stored) in Hstored; unfold R.complete_get, R.materialize, R.promote_controlled in Hget.
  destruct (R.rank_lt st (R.frame_owner fr) target); cbn -[M.lookup R.sigma_value] in Hget; rewrite Hstored in Hget;
    inversion Hget; subst; split; reflexivity.
Qed.
Lemma running_get tf st fr target tail next next_fr value : monotonic_system tf ->
  running tf st fr (R.ConstraintSystem.Get target tail) ->
  R.complete_get st fr target = (next,next_fr,value) -> running tf next next_fr (tail value).
Proof.
  intros Hmono Hrun Hget.
  pose proof (@prefix_get_live tf st fr target tail (running_reads Hrun) (running_sides Hrun) (running_spawns Hrun)
    (running_upper Hrun) Hmono (running_prefix Hrun) (running_common Hrun)) as Hknown.
  destruct (known_get_data Hknown Hget) as [Hsigma Hvalue].
  pose proof (proj1 (proj2 (proj2 (B.get_layout Hget)))) as Hrows.
  pose proof (@running_payload tf st next fr (R.ConstraintSystem.Get target tail) Hsigma Hrows Hrun) as Hview.
  destruct Hview as [upper rs ss ps Hp Hcommon Hfloor Hreads Hspawns Hraw Hlocal].
  assert (Hlive : B.solved next target) by (eapply B.preserves_live_layout; eauto).
  assert (Hcurrent : R.sigma_value next target = value) by (unfold R.sigma_value in *; rewrite Hsigma; symmetry; exact Hvalue).
  unfold R.complete_get in Hget; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion Hget; subst next_fr; clear Hget; rewrite H0; rewrite H0 in H2; rewrite H2;
    match goal with |- running _ _ ?actual_fr _ =>
      refine (@Build_running tf next actual_fr (tail value) upper (rs++[(target,value)]) ss ps
        (@B.prefix_get (tf (R.frame_owner fr)) target tail rs ss ps value Hp) _ _ _ Hspawns Hraw Hlocal)
    end.
  all: try solve [intros query v Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]];
    [eapply Hreads; exact Hin |inversion Heq; subst; exact Hlive |contradiction]].
  all: try solve [intros query v Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]];
    [apply Hfloor; exact Hin |inversion Heq; subst; rewrite Hcurrent; apply DL.leq_refl |contradiction]].
  all: intros query v upper_value Hin Hu; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]];
    [eapply Hcommon; eauto |inversion Heq; subst; rewrite <- Hcurrent; eapply history_floor; exact Hu |contradiction].
Qed.
Lemma accumulated_side fr target raw sides : accumulated fr sides ->
  accumulated (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) (sides++[(target,raw)]).
Proof.
  intros Hacc observed value Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]]; [| |contradiction].
  - destruct (Hacc observed value Hin) as [input [Hlookup Hle]].
    destruct (V.eq_dec observed target) as [->|Hother].
    + exists (R.accumulated_side_input fr target raw); split; [apply ML.lookup_update_same |].
      eapply DL.leq_trans; [exact Hle |apply B.side_input_old; exact Hlookup].
    + exists input; split; [cbn; rewrite ML.lookup_update_other; auto |exact Hle].
  - inversion Heq; subst observed value; exists (R.accumulated_side_input fr target raw); split;
      [apply ML.lookup_update_same |apply B.side_input_raw].
Qed.
Lemma running_side tf st fr target raw body : monotonic_system tf ->
  running tf st fr (R.ConstraintSystem.Side target raw body) ->
  running tf (R.observe st target) (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) body.
Proof.
  intros Hmono Hrun.
  pose proof (@prefix_side_bounded tf st fr target raw body (running_reads Hrun) (running_sides Hrun) (running_spawns Hrun)
    (running_upper Hrun) Hmono (running_prefix Hrun) (running_common Hrun)) as Hrawbound.
  assert (Hsigma : R.sigma (R.observe st target) = R.sigma st) by apply B.observe_sigma.
  assert (Hrows : R.contributions (R.observe st target) = R.contributions st) by (unfold R.observe; destruct (P.Ranks.observe _ _); reflexivity).
  pose proof (@running_payload tf st (R.observe st target) fr (R.ConstraintSystem.Side target raw body) Hsigma Hrows Hrun) as Hview.
  destruct Hview as [upper rs ss ps Hp Hcommon Hfloor Hreads Hspawns Hacc Hlocal].
  refine (@Build_running tf (R.observe st target) (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) body
    upper rs (ss++[(target,raw)]) ps (B.prefix_side Hp) Hcommon Hfloor Hreads Hspawns (accumulated_side target raw Hacc) _).
  apply B.bound_frame_side; [exact Hlocal |apply B.bound_accumulated; [exact Hlocal |]].
  unfold R.stored_contribution; rewrite Hrows; exact Hrawbound.
Qed.
Lemma running_spawn tf st fr target body : monotonic_system tf ->
  running tf st fr (R.ConstraintSystem.Spawn target body) -> running tf (R.observe st target) fr body.
Proof.
  intros Hmono Hrun.
  pose proof (@prefix_spawn_live tf st fr target body (running_reads Hrun) (running_sides Hrun) (running_spawns Hrun)
    (running_upper Hrun) Hmono (running_prefix Hrun) (running_common Hrun)) as Htarget.
  assert (Hsigma : R.sigma (R.observe st target) = R.sigma st) by apply B.observe_sigma.
  assert (Hrows : R.contributions (R.observe st target) = R.contributions st) by (unfold R.observe; destruct (P.Ranks.observe _ _); reflexivity).
  destruct (@running_payload tf st (R.observe st target) fr (R.ConstraintSystem.Spawn target body) Hsigma Hrows Hrun)
    as [upper rs ss ps Hp Hcommon Hfloor Hreads Hspawns Hacc Hlocal].
  refine (@Build_running tf (R.observe st target) fr body upper rs ss (ps++[target])
    (B.prefix_spawn Hp) Hcommon Hfloor Hreads _ Hacc Hlocal).
  intros observed Hin; apply in_app_or in Hin; destruct Hin as [Hin|[<-|Hin]];
    [apply Hspawns; exact Hin |eapply B.preserves_live_layout; eauto |contradiction].
Qed.
Lemma complete_write tf st fr direct target input next changed :
  R.write_side_contribution st fr target input = (next,changed) ->
  D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
  (forall value, M.lookup (R.frame_local_side fr) target = Some value -> D.leq value input = true) ->
  complete tf st fr direct -> complete tf next fr direct.
Proof.
  intros Hw Hin Hinput [rs ss ps Ht Hfloor Hreads Hspawns Hacc Hlocal Hvalue].
  destruct (write_descends Hw Hin) as [Hrows Haggregates].
  pose proof (proj1 (proj2 (proj2 (B.write_layout Hw)))) as Hsigma.
  refine (@Build_complete tf next fr direct rs ss ps Ht _ _ _ Hacc _ _).
  - intros observed value Hmem; unfold R.sigma_value; rewrite Hsigma; apply Hfloor; exact Hmem.
  - intros observed value Hmem; eapply B.preserves_live_layout; [exact Hsigma |eapply Hreads; exact Hmem].
  - intros observed Hmem; eapply B.preserves_live_layout; [exact Hsigma |apply Hspawns; exact Hmem].
  - intros observed value Hlookup; destruct (V.eq_dec observed target) as [->|Hother].
    + eapply DL.leq_trans; [apply Hinput; exact Hlookup |exact (B.write_contribution_sound Hw)].
    + rewrite (B.write_other_contribution Hw) by auto; apply Hlocal; exact Hlookup.
  - unfold R.sigma_value; rewrite Hsigma; eapply DL.leq_trans; [apply DL.join_least |exact Hvalue].
    + apply DL.join_upper_left.
    + eapply DL.leq_trans; [apply Haggregates |apply DL.join_upper_right].
Qed.
Lemma complete_publication tf targets st fr direct : complete tf st fr direct -> complete tf (N.publish targets st fr) fr direct.
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hcomplete; [exact Hcomplete |].
  cbn -[R.write_side_contribution N.finish_write].
  destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  apply IH; eapply (@complete_payload tf next (N.finish_write st next fr target changed) fr direct); [| |].
  - unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; reflexivity.
  - unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; reflexivity.
  - eapply complete_write; [exact Hw | | |exact Hcomplete].
    + destruct (M.lookup (R.frame_local_side fr) target) eqn:Hlookup;
        [eapply (complete_local Hcomplete); exact Hlookup |apply DL.bottom_least].
    + intros value Hlookup; rewrite Hlookup; apply DL.leq_refl.
Qed.
Definition region st root owner := owner = root \/ R.rank_lt st root owner = true.
Definition histories tf root st := forall owner, region st root owner -> B.solved st owner -> inhabited (history tf st owner).
Definition higher_queue_live root st := forall owner, In owner (R.queue st) -> R.rank_lt st root owner = true -> B.solved st owner.
Definition eligible root st fr := region st root (R.frame_owner fr) /\ R.frame_phase fr <> U.Widen.
Inductive wave_stack tf root st (base : R.continuation) : R.continuation -> Prop :=
| WaveBase : wave_stack tf root st base base
| WaveDrain fr k : eligible root st fr -> wave_stack tf root st base k -> wave_stack tf root st base (R.KDrain fr k)
| WaveRestart fr k : eligible root st fr -> P.empty_cache fr -> wave_stack tf root st base k ->
    wave_stack tf root st base (R.KAfterSide fr (tf (R.frame_owner fr)) k).
Definition wave_control tf root base st ctrl : Prop :=
  match ctrl with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => False
  | R.StartEpisode owner k => R.rank_lt st root owner = true /\ B.solved st owner /\ wave_stack tf root st base k
  | R.RunRhs fr body k => eligible root st fr /\ inhabited (running tf st fr body) /\ wave_stack tf root st base k
  | R.RunDead fr direct _ k | R.RunCommit fr direct k => eligible root st fr /\ inhabited (complete tf st fr direct) /\ wave_stack tf root st base k
  | R.RunDrain fr k => eligible root st fr /\ wave_stack tf root st base k
  | R.Return k => wave_stack tf root st base k
  end.
Record wave tf root base c : Prop := {
  wave_root : B.solved (R.cfg_state c) root;
  wave_histories : histories tf root (R.cfg_state c);
  wave_queue : higher_queue_live root (R.cfg_state c);
  wave_controlled : wave_control tf root base (R.cfg_state c) (R.cfg_control c)
}.
Lemma region_extends before after root owner : B.extends (R.ranking before) (R.ranking after) ->
  region before root owner -> region after root owner.
Proof. intros H [->|Hgt]; [left; reflexivity |right; eapply B.lt_extends; eauto]. Qed.
Lemma region_back before after root owner : B.extends (R.ranking before) (R.ranking after) ->
  B.ranked (R.ranking before) root -> B.ranked (R.ranking before) owner ->
  region after root owner -> region before root owner.
Proof.
  intros Hext Hr Ho [->|Hlt]; [left; reflexivity |right].
  unfold R.rank_lt in *; rewrite (B.lt_stable Hext Hr Ho) in Hlt; exact Hlt.
Qed.
Lemma clean_history tf roots c owner : P.reachable tf roots c -> B.solved (R.cfg_state c) owner -> B.idle c owner ->
  inhabited (history tf (R.cfg_state c) owner).
Proof.
  intros Hr Hsolved Hidle.
  pose proof (P.reachable_semantic_invariant Hr) as Hsem.
  destruct (P.invariant_settled Hsem Hsolved Hidle) as [done].
  constructor; refine (@Build_history tf (R.cfg_state c) owner (B.completed_result done) (B.completed_trace done) _ _
    (B.completed_spawns done) _ (B.completed_sides done)).
  - intros target value Hin; rewrite (@B.read_value (R.cfg_state c) target value (proj1 (B.completed_reads done target value Hin))); apply DL.leq_refl.
  - intros target value Hin; exists value; exact (proj1 (B.completed_reads done target value Hin)).
  - apply DL.join_least; [exact (B.completed_direct done) |apply (P.invariant_incoming Hsem); destruct Hidle; split; auto].
Qed.
Lemma controlled_higher_clean tf roots st fr direct k after next_fr next_k :
  P.reachable tf roots (B.configuration st (R.RunCommit fr direct k)) ->
  P.step tf (B.configuration st (R.RunCommit fr direct k)) (B.configuration after (R.RunDrain next_fr next_k)) ->
  S.mem (R.frame_owner fr) (R.controlled st) = true -> forall owner, R.rank_lt st (R.frame_owner fr) owner = true ->
  B.idle (B.configuration st (R.RunCommit fr direct k)) owner.
Proof.
  intros Hr Hstep Hcontrolled owner Habove.
  destruct (@P.actual_commit_ready tf st fr direct k after next_fr next_k Hstep) as [Hpending Hquiet].
  destruct (P.reachable_rank_configuration Hr) as [Hstore Hrefs].
  assert (Hrank : B.ranked (R.ranking st) (R.frame_owner fr)) by (exact (proj2 (B.ref_owner (proj1 Hrefs)))).
  pose proof (P.clear_below Hstore Hrank Hcontrolled Hpending) as Hbelow.
  split.
  - change (~ In owner (R.queue st)); intro Hin.
    assert (Hneq : owner <> R.frame_owner fr) by (intro Heq; subst owner; unfold R.rank_lt in Habove; rewrite B.lt_irrefl in Habove; discriminate).
    assert (Hclear : In owner (R.queue (N.clear_owner st (R.frame_owner fr)))) by (apply P.clear_members; auto).
    unfold B.queue_below in Hbelow; rewrite Forall_forall in Hbelow; pose proof (Hbelow owner Hclear) as Hlower.
    pose proof (@B.lt_trans (R.ranking st) (R.frame_owner fr) owner (R.frame_owner fr) Habove Hlower) as Hcycle;
      rewrite B.lt_irrefl in Hcycle; discriminate.
  - change (~ In owner (R.frame_owner fr :: B.suspended_owners k)); intro Hin.
    destruct Hin as [Heq|Hin]; [rewrite Heq in Habove; unfold R.rank_lt in Habove; rewrite B.lt_irrefl in Habove; discriminate |].
    pose proof (proj2 (B.ordered_tail (P.reachable_active_ordered Hr))) as Hparents.
    rewrite Forall_forall in Hparents; pose proof (Hparents owner Hin) as Hlower.
    pose proof (@B.lt_trans (R.ranking st) (R.frame_owner fr) owner (R.frame_owner fr) Habove Hlower) as Hcycle;
      rewrite B.lt_irrefl in Hcycle; discriminate.
Qed.
Lemma set_owner_descends st fr direct next next_fr :
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  R.set_value st fr direct = (next,next_fr) ->
  D.leq (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
  intros Hin Hw; unfold R.set_value in Hw.
  destruct (R.equivalent _ _) eqn:Hcandidate; [inversion Hw; subst; apply DL.leq_refl |].
  destruct (S.mem _ _) eqn:Hcontrolled.
  - destruct (U.update _ _ _ _ _) as [phase value] eqn:Hu; cbn in Hw.
    pose proof (@smaller_update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
      (D.join direct (R.aggregate st (R.frame_owner fr))) Hin) as Hdown.
    rewrite Hu in Hdown; cbn in Hdown.
    destruct (R.equivalent value _) eqn:Hvalue; inversion Hw; subst next next_fr;
      [apply DL.leq_refl |unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; exact Hdown].
  - cbn in Hw; rewrite Hcandidate in Hw; inversion Hw; subst next next_fr.
    unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; exact Hin.
Qed.
Lemma set_values_descend st fr direct next next_fr :
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  R.set_value st fr direct = (next,next_fr) -> values_descend st next.
Proof.
  intros Hin Hw target; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hother].
  - eapply set_owner_descends; eauto.
  - unfold R.sigma_value; rewrite (B.commit_other (@B.commit_footprint st fr direct next next_fr Hw) Hother); apply DL.leq_refl.
Qed.
Lemma commit_history tf st fr direct next next_fr : R.set_value st fr direct = (next,next_fr) ->
  complete tf st fr direct -> history tf next (R.frame_owner fr).
Proof.
  intros Hw Hcomplete; pose proof (@set_values_descend st fr direct next next_fr (complete_value Hcomplete) Hw) as Hdown.
  destruct Hcomplete as [rs ss ps Htrace Hfloor Hreads Hspawns Hacc Hlocal Hvalue].
  pose proof (@B.commit_footprint st fr direct next next_fr Hw) as Hview.
  refine (@Build_history tf next (R.frame_owner fr)
    {| O.observed_direct := direct; O.observed_reads := rs; O.observed_sides := ss; O.observed_spawns := ps |} Htrace _ _ _ _ _).
  - intros target value Hin; eapply DL.leq_trans; [apply Hdown |apply Hfloor; exact Hin].
  - intros target value Hin; eapply B.preserves_live_commit; [exact Hw |eapply Hreads; exact Hin].
  - intros target Hin; eapply B.preserves_live_commit; [exact Hw |apply Hspawns; exact Hin].
  - unfold R.aggregate; rewrite (B.commit_contributions Hview); eapply B.commit_sound; exact Hw.
  - intros target raw Hin; unfold R.stored_contribution; rewrite (B.commit_contributions Hview).
    destruct (Hacc target raw Hin) as [input [Hl Hle]]; eapply DL.leq_trans; [exact Hle |apply Hlocal; exact Hl].
Qed.
Lemma entered_boxn st fr direct next next_fr : R.frame_phase fr = U.BoxW -> R.frame_phase next_fr = U.BoxN ->
  R.set_value st fr direct = (next,next_fr) -> S.mem (R.frame_owner fr) (R.controlled st) = true /\
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
  intros Hp Hnext Hw; unfold R.set_value in Hw.
  destruct (R.equivalent _ _) eqn:Hcandidate; [inversion Hw; subst; congruence |].
  destruct (S.mem _ _) eqn:Hcontrolled.
  - rewrite Hp in Hw; cbn -[D.leq R.equivalent] in Hw;
    destruct (D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr))) eqn:Hin;
    cbn -[R.equivalent] in Hw;
    match type of Hw with context [if R.equivalent ?value ?old then _ else _] => destruct (R.equivalent value old) end;
    inversion Hw; subst next next_fr; cbn in Hnext; try discriminate; split; reflexivity.
  - cbn in Hw; rewrite Hcandidate in Hw; inversion Hw; subst; cbn in Hnext; congruence.
Qed.
Lemma solved_ranked support st owner : B.store_wf support st -> B.solved st owner -> B.ranked (R.ranking st) owner.
Proof.
  intros Hstore [value Hvalue]; exact (proj2 (proj1 (B.refs_sigma (B.store_references Hstore) Hvalue))).
Qed.
Lemma histories_payload tf root before after : B.store_wf (fun _ => True) before -> B.solved before root ->
  B.extends (R.ranking before) (R.ranking after) -> R.sigma after = R.sigma before ->
  R.contributions after = R.contributions before -> histories tf root before -> histories tf root after.
Proof.
  intros Hstore Hroot Hext Hsigma Hrows Hhist owner Hregion Hlive.
  pose proof (@B.solved_layout_back before after Hsigma owner Hlive) as Hbefore.
  destruct (Hhist owner (@region_back before after root owner Hext (solved_ranked Hstore Hroot)
    (solved_ranked Hstore Hbefore) Hregion) Hbefore) as [h].
  constructor; exact (@history_payload tf before after owner h Hsigma Hrows).
Qed.
Lemma histories_replace tf root source before after : B.store_wf (fun _ => True) before -> B.solved before root ->
  B.extends (R.ranking before) (R.ranking after) -> values_descend before after -> B.preserves_live before after ->
  (forall owner, B.solved after owner -> B.solved before owner) -> aggregates_descend before after ->
  (forall owner, owner <> source -> R.sigma_value after owner = R.sigma_value before owner) ->
  (forall owner target, owner <> source -> R.stored_contribution after owner target = R.stored_contribution before owner target) ->
  inhabited (history tf after source) -> histories tf root before -> histories tf root after.
Proof.
  intros Hstore Hroot Hext Hvalues Hlive Hback Hagg Hvalue Hrows Hsource Hhist owner Hregion Hsolved.
  destruct (V.eq_dec owner source) as [->|Hother]; [exact Hsource |].
  pose proof (Hback owner Hsolved) as Hbefore.
  destruct (Hhist owner (@region_back before after root owner Hext (solved_ranked Hstore Hroot)
    (solved_ranked Hstore Hbefore) Hregion) Hbefore) as [h].
  destruct (@history_transport tf before after owner h Hvalues Hlive (Hvalue owner Hother) Hagg
    (fun target => Hrows owner target Hother)) as [next _]; constructor; exact next.
Qed.
Lemma wave_stack_extends tf root base before after k : B.extends (R.ranking before) (R.ranking after) ->
  wave_stack tf root before base k -> wave_stack tf root after base k.
Proof.
  intros Hext Hstack; induction Hstack.
  - apply WaveBase.
  - apply WaveDrain; [destruct H as [Hr Hp]; split; [eapply region_extends; eauto |exact Hp] |exact IHHstack].
  - apply WaveRestart; [destruct H as [Hr Hp]; split; [eapply region_extends; eauto |exact Hp] |exact H0 |exact IHHstack].
Qed.
Lemma higher_queue_subset root before after : B.store_wf (fun _ => True) before -> B.solved before root ->
  B.extends (R.ranking before) (R.ranking after) -> B.preserves_live before after ->
  (forall x, In x (R.queue after) -> In x (R.queue before)) -> higher_queue_live root before -> higher_queue_live root after.
Proof.
  intros Hstore Hroot Hext Hlive Hsubset Hq owner Hin Habove; apply Hlive, Hq; [apply Hsubset; exact Hin |].
  assert (Hrank : B.ranked (R.ranking before) owner).
  { pose proof (B.known_ranked_queue Hstore) as Hknown; rewrite Forall_forall in Hknown; apply Hknown; apply Hsubset; exact Hin. }
  unfold R.rank_lt in *; rewrite (B.lt_stable Hext (solved_ranked Hstore Hroot) Hrank) in Habove; exact Habove.
Qed.
Definition unknown_above_bottom root st := forall owner, R.rank_lt st root owner = true ->
  ~ B.solved st owner -> D.leq (R.aggregate st owner) D.bottom = true.
Lemma wave_unknown_bottom tf roots root c : P.reachable tf roots c -> higher_queue_live root (R.cfg_state c) ->
  Forall (B.solved (R.cfg_state c)) (B.active_owners (R.cfg_control c)) ->
  unknown_above_bottom root (R.cfg_state c).
Proof.
  intros Hr Hq Hframes owner Habove Hmissing.
  assert (Hquiet : ~ In owner (R.queue (R.cfg_state c))) by (intro Hin; apply Hmissing; eapply Hq; eauto).
  assert (Hinactive : ~ In owner (B.active_owners (R.cfg_control c))).
  { intro Hin; apply Hmissing; rewrite Forall_forall in Hframes; apply Hframes; exact Hin. }
  assert (Hvalue : R.sigma_value (R.cfg_state c) owner = D.bottom).
  { unfold R.sigma_value; destruct (M.lookup _ owner) as [value|] eqn:Hv; [exfalso; apply Hmissing; exists value; exact Hv |reflexivity]. }
  rewrite <- Hvalue; apply (P.invariant_incoming (P.reachable_semantic_invariant Hr)); split; auto.
Qed.
Lemma unknown_bottom_payload root before after : R.ranking after = R.ranking before -> R.sigma after = R.sigma before ->
  aggregates_descend before after -> unknown_above_bottom root before -> unknown_above_bottom root after.
Proof.
  intros Hrank Hsigma Hagg Hbottom owner Habove Hmissing; eapply DL.leq_trans; [apply Hagg |apply Hbottom].
  - unfold R.rank_lt in *; rewrite Hrank in Habove; exact Habove.
  - intro Hsolved; apply Hmissing; eapply B.preserves_live_layout; eauto.
Qed.
Lemma write_changed_equation st fr target input next changed : R.write_side_contribution st fr target input = (next,changed) ->
  changed = negb (R.equivalent (R.aggregate next target) (R.aggregate st target)).
Proof.
  unfold R.write_side_contribution; intro Hw; inversion Hw; subst next changed.
  unfold R.promote_side_target, R.promote_controlled; destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
Qed.
Lemma descending_change_live root st fr target input next changed :
  unknown_above_bottom root st -> R.write_side_contribution st fr target input = (next,changed) ->
  aggregates_descend st next -> changed = true -> R.rank_lt st root target = true -> B.solved st target.
Proof.
  intros Hbottom Hw Hdown Hchanged Habove.
  destruct (M.lookup (R.sigma st) target) as [value|] eqn:Hv; [exists value; exact Hv |].
  assert (Hmissing : ~ B.solved st target) by (intros [v H]; change (M.lookup (R.sigma st) target = Some v) in H; congruence).
  pose proof (Hbottom target Habove Hmissing) as Hold.
  assert (Heq : B.eqv (R.aggregate next target) (R.aggregate st target)).
  { split; [apply Hdown |eapply DL.leq_trans; [exact Hold |apply DL.bottom_least]]. }
  pose proof (proj2 (B.eqv_bool _ _) Heq) as Hbool.
  rewrite (write_changed_equation Hw), Hbool in Hchanged; discriminate.
Qed.
Lemma complete_finish_live tf root st fr direct target input next changed :
  higher_queue_live root st -> unknown_above_bottom root st -> B.solved st (R.frame_owner fr) ->
  R.write_side_contribution st fr target input = (next,changed) ->
  D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
  (forall value, M.lookup (R.frame_local_side fr) target = Some value -> D.leq value input = true) ->
  complete tf st fr direct ->
  inhabited (complete tf (N.finish_write st next fr target changed) fr direct) /\
  higher_queue_live root (N.finish_write st next fr target changed) /\
  unknown_above_bottom root (N.finish_write st next fr target changed).
Proof.
  intros Hq Hbottom Hsource Hw Hin Hcache Hcomplete.
  destruct (write_descends Hw Hin) as [Hrows Hagg].
  pose proof (proj1 (proj2 (proj2 (B.write_layout Hw)))) as Hsigma.
  assert (Hfinishsigma : R.sigma (N.finish_write st next fr target changed) = R.sigma st).
  { unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; exact Hsigma. }
  assert (Hfinishrank : R.ranking (N.finish_write st next fr target changed) = R.ranking st) by
    (rewrite P.finish_rank; eapply B.write_rank; exact Hw).
  assert (Hfinishagg : aggregates_descend st (N.finish_write st next fr target changed)).
  { intros owner; unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; exact (Hagg owner). }
  split.
  - constructor; eapply (@complete_payload tf next (N.finish_write st next fr target changed) fr direct);
      [unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; reflexivity |
       unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; reflexivity |
       eapply complete_write; eauto].
  - split; [|eapply unknown_bottom_payload; eauto].
    intros owner Hmem Habove; assert (Hbefore_above : R.rank_lt st root owner = true) by (unfold R.rank_lt in *; rewrite Hfinishrank in Habove; exact Habove).
    eapply B.preserves_live_layout; [exact Hfinishsigma |].
    unfold N.finish_write, N.requeue_source in Hmem; destruct changed eqn:Hch; destruct N.cell_changed;
      repeat (apply B.insert_members in Hmem; destruct Hmem as [Heq|Hmem]);
      try solve [subst owner; exact Hsource];
      try solve [subst owner; eapply descending_change_live; eauto];
      rewrite (B.write_queue Hw) in Hmem; eapply Hq; eauto.
Qed.
Lemma publication_live tf targets root st fr direct : higher_queue_live root st -> unknown_above_bottom root st ->
  B.solved st (R.frame_owner fr) -> complete tf st fr direct ->
  inhabited (complete tf (N.publish targets st fr) fr direct) /\ higher_queue_live root (N.publish targets st fr) /\
  unknown_above_bottom root (N.publish targets st fr) /\ aggregates_descend st (N.publish targets st fr).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hq Hbottom Hsource Hcomplete.
  - split; [constructor; exact Hcomplete |split; [exact Hq |split; [exact Hbottom |intros owner; apply DL.leq_refl]]].
  - cbn -[R.write_side_contribution N.finish_write]; destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
    assert (Hin : D.leq (match M.lookup (R.frame_local_side fr) target with Some value => value |None => D.bottom end)
      (R.stored_contribution st (R.frame_owner fr) target) = true) by
      (destruct (M.lookup (R.frame_local_side fr) target) eqn:Hlookup; [eapply (complete_local Hcomplete); exact Hlookup |apply DL.bottom_least]).
    destruct (@complete_finish_live tf root st fr direct target _ next changed Hq Hbottom Hsource Hw Hin
      ltac:(intros value Hlookup; rewrite Hlookup; apply DL.leq_refl) Hcomplete) as [[Hnext] [Hnextq Hnextbottom]].
    assert (Hlive : B.solved (N.finish_write st next fr target changed) (R.frame_owner fr)).
    { eapply B.preserves_live_layout; [unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed;
      exact (proj1 (proj2 (proj2 (B.write_layout Hw)))) |exact Hsource]. }
    destruct (IH _ Hnextq Hnextbottom Hlive Hnext) as [Hfinal [Hfinalq [Hfinalbottom Hlast]]].
    split; [exact Hfinal |split; [exact Hfinalq |split; [exact Hfinalbottom |]]].
    intros owner; eapply DL.leq_trans; [apply Hlast |].
    unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed;
      exact (proj2 (write_descends Hw Hin) owner).
Qed.
Lemma set_safe_phase st fr direct next next_fr : R.frame_phase fr <> U.Widen ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  R.set_value st fr direct = (next,next_fr) -> R.frame_phase next_fr <> U.Widen.
Proof.
  intros Hsafe Hin Hw; unfold R.set_value in Hw.
  destruct (R.equivalent _ _) eqn:Hcandidate; [inversion Hw; subst; exact Hsafe |].
  destruct (S.mem _ _) eqn:Hcontrolled.
  - destruct (R.frame_phase fr) eqn:Hp; [| |contradiction]; cbn -[D.leq R.equivalent] in Hw; rewrite Hin in Hw;
      cbn -[R.equivalent] in Hw;
      match type of Hw with context [if R.equivalent ?value ?old then _ else _] => destruct (R.equivalent value old) end;
      inversion Hw; subst next next_fr; cbn; discriminate.
  - cbn in Hw; rewrite Hcandidate in Hw; inversion Hw; subst; exact Hsafe.
Qed.
Lemma set_boxw_phase st fr direct next next_fr : R.frame_phase fr = U.BoxW ->
  R.set_value st fr direct = (next,next_fr) -> R.frame_phase next_fr = U.BoxW \/ R.frame_phase next_fr = U.BoxN.
Proof.
  intros Hp Hw; unfold R.set_value in Hw.
  destruct (R.equivalent _ _) eqn:Hcandidate; [inversion Hw; subst; auto |].
  destruct (S.mem _ _) eqn:Hcontrolled.
  - rewrite Hp in Hw; cbn -[D.leq R.equivalent] in Hw;
      destruct (D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)));
      cbn -[R.equivalent] in Hw;
      match type of Hw with context [if R.equivalent ?value ?old then _ else _] => destruct (R.equivalent value old) end;
      inversion Hw; subst next next_fr; cbn; auto.
  - cbn in Hw; rewrite Hcandidate in Hw; inversion Hw; subst; auto.
Qed.
Fixpoint continuation_phases (predicate : U.phase -> Prop) k :=
  match k with
  | R.KLoop |R.KSeedLoop _ => True
  | R.KAfterGet fr _ _ rest |R.KAfterSide fr _ rest |R.KAfterSpawn fr _ rest |R.KDead fr _ _ rest |R.KDrain fr rest =>
      predicate (R.frame_phase fr) /\ continuation_phases predicate rest
  end.
Definition control_phases predicate ctrl :=
  match ctrl with
  | R.RunLoop |R.RunSeeds _ |R.RunSeedLoop _ => True
  | R.StartEpisode _ k |R.Return k => continuation_phases predicate k
  | R.RunRhs fr _ k |R.RunDead fr _ _ k |R.RunCommit fr _ k |R.RunDrain fr k =>
      predicate (R.frame_phase fr) /\ continuation_phases predicate k
  end.
Lemma phases_map p q k : (forall phase, p phase -> q phase) -> continuation_phases p k -> continuation_phases q k.
Proof. intro H; induction k; cbn; intuition auto. Qed.
Lemma wave_stack_safe tf root st base k : continuation_phases (fun phase => phase = U.BoxW) base ->
  wave_stack tf root st base k -> continuation_phases (fun phase => phase <> U.Widen) k.
Proof.
  intros Hbase Hstack; induction Hstack; cbn.
  - eapply (@phases_map (fun phase => phase = U.BoxW) (fun phase => phase <> U.Widen) base); [intros phase ->; discriminate |exact Hbase].
  - split; [exact (proj2 H) |exact IHHstack].
  - split; [exact (proj2 H) |exact IHHstack].
Qed.
Lemma wave_safe tf root base c : continuation_phases (fun phase => phase = U.BoxW) base -> wave tf root base c ->
  control_phases (fun phase => phase <> U.Widen) (R.cfg_control c).
Proof.
  intros Hbase [_ _ _ Hctrl]; destruct (R.cfg_control c); cbn in Hctrl |- *; try contradiction;
    intuition eauto using wave_stack_safe.
  all: unfold eligible in *; tauto.
Qed.
Definition readers_live st := forall target owner, S.mem owner (R.lookup_set (R.readers st) target) = true -> B.solved st owner.
Lemma readers_live_view before after : R.readers after = R.readers before -> B.preserves_live before after -> readers_live before -> readers_live after.
Proof. intros Hr Hlive Hbefore target owner Hmem; apply Hlive, Hbefore with target; now rewrite <- Hr. Qed.
Lemma readers_live_get st fr target next next_fr value : readers_live st -> B.solved st (R.frame_owner fr) ->
  R.complete_get st fr target = (next,next_fr,value) -> readers_live next.
Proof.
  intros Hreaders Howner Hw; pose proof (proj1 (B.preserves_live_get Hw)) as Hlive.
  unfold R.complete_get in Hw; destruct (R.rank_lt st (R.frame_owner fr) target);
    inversion Hw; subst next next_fr value; clear Hw; intros observed reader Hmem;
    rewrite B.materialize_readers in Hmem; unfold R.lookup_set in Hmem; cbn -[M.lookup] in Hmem.
  all: destruct (V.eq_dec observed target) as [->|Hneq].
  all: try rewrite ML.lookup_update_same in Hmem.
  all: try rewrite ML.lookup_update_other in Hmem by exact Hneq.
  all: try solve [apply SL.add_spec in Hmem; destruct Hmem as [->|Hmem]; apply Hlive;
    [exact Howner |eapply Hreaders; exact Hmem]].
  all: apply Hlive; eapply Hreaders; exact Hmem.
Qed.
Lemma readers_live_commit st fr direct next next_fr : readers_live st ->
  R.set_value st fr direct = (next,next_fr) -> readers_live next.
Proof.
  intros Hreaders Hw; pose proof (B.preserves_live_commit Hw) as Hlive.
  unfold R.set_value in Hw; B.split_program Hw; intros target owner Hmem.
  all: apply Hlive; apply Hreaders with (target := target).
  all: cbn [R.with_readers R.enqueue_all R.with_queue R.with_sigma R.readers] in Hmem.
  all: try exact Hmem.
  all: unfold R.lookup_set in Hmem; destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hother].
  all: try (rewrite ML.lookup_update_same in Hmem; rewrite SL.empty_spec in Hmem; discriminate).
  all: rewrite ML.lookup_update_other in Hmem by exact Hother; exact Hmem.
Qed.
Lemma readers_live_observe st target : readers_live st -> readers_live (R.observe st target).
Proof. intro H; eapply (@readers_live_view st (R.observe st target)); [unfold R.observe; destruct (P.Ranks.observe _ _); reflexivity |apply B.preserves_live_layout, B.observe_sigma |exact H]. Qed.
Lemma readers_live_materialize st target : readers_live st -> readers_live (R.materialize st target).
Proof. intro H; eapply (@readers_live_view st (R.materialize st target)); [apply B.materialize_readers |apply B.preserves_live_materialize |exact H]. Qed.
Lemma readers_live_queue st queue : readers_live st -> readers_live (R.with_queue st queue).
Proof. intro H; eapply (@readers_live_view st (R.with_queue st queue)); [reflexivity |apply B.preserves_live_layout; reflexivity |exact H]. Qed.
Lemma readers_live_enqueue st owner : readers_live st -> readers_live (R.enqueue st owner).
Proof. apply readers_live_queue. Qed.
Lemma readers_live_reset st owner : readers_live st -> readers_live (R.reset_registered_cells st owner).
Proof.
  intro H; unfold R.reset_registered_cells; destruct Features.restart_side_phases; [|exact H].
  eapply (@readers_live_view st _); [reflexivity |apply B.preserves_live_layout; reflexivity |exact H].
Qed.
Lemma readers_live_write st fr target input next changed : readers_live st ->
  R.write_side_contribution st fr target input = (next,changed) -> readers_live next.
Proof.
  intros Hreader Hw; eapply (@readers_live_view st next);
    [exact (proj1 (proj2 (proj2 (proj2 (B.write_layout Hw))))) |
     apply B.preserves_live_layout; exact (proj1 (proj2 (proj2 (B.write_layout Hw)))) |exact Hreader].
Qed.
Lemma core_readers_live tf before after : B.frames_live before -> readers_live (R.cfg_state before) ->
  B.step tf before after -> readers_live (R.cfg_state after).
Proof.
  intros Hframes Hreaders Hstep; pose proof (B.next_preserves_live Hstep) as Hlive; unfold B.frames_live in Hframes.
  destruct before as [st ctrl]; unfold B.step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep, Hreaders, Hframes |- *.
  destruct ctrl; cbn [R.cfg_control] in Hstep; unfold R.continue_side, R.continue_dead, R.record_side_input in Hstep; B.split_program Hstep.
  all: cbn [R.cfg_state B.frames_live R.cfg_control B.framed_owners B.active_owners B.suspended_owners] in *.
  all: try match goal with |- readers_live (R.enqueue _ _) => apply readers_live_enqueue end.
  all: repeat match goal with Hg : R.complete_get (if ?b then _ else _) _ _ = (_,_,_) |- _ => destruct b end.
  all: try match goal with |- readers_live (R.requeue_changed_controlled_owner _ _ _) => unfold R.requeue_changed_controlled_owner; apply readers_live_queue end.
  all: try solve [match goal with Hw : R.set_value _ _ _ = (_,_) |- _ => eapply readers_live_commit; [exact Hreaders |exact Hw] end].
  all: try solve [match goal with Hg : R.complete_get ?input ?fr ?target = (?next,?next_fr,?value) |- _ =>
      eapply (@readers_live_get input fr target next next_fr value); [eauto using readers_live_observe, readers_live_queue, readers_live_enqueue |
      eapply B.preserves_live_layout with (before := st); [try reflexivity; try apply B.observe_sigma |
      rewrite Forall_forall in Hframes; apply Hframes; cbn; auto] |exact Hg] end].
  all: try solve [eapply (@readers_live_view st _); [reflexivity |exact Hlive |exact Hreaders]].
  all: try solve [eauto using readers_live_materialize, readers_live_observe, readers_live_queue, readers_live_enqueue, readers_live_reset].
  all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases;
      eapply readers_live_view; [reflexivity |exact Hlive |exact Hreaders]].
  all: match goal with Hw : R.write_side_contribution ?input ?fr ?target ?value = (?next,?changed) |- _ =>
      eapply (@readers_live_write input fr target value next changed); [eauto using readers_live_observe |exact Hw] end.
Qed.
Lemma next_readers_live tf before after : B.frames_live before -> readers_live (R.cfg_state before) ->
  P.step tf before after -> readers_live (R.cfg_state after).
Proof.
  intros Hframes Hreaders Hstep; pose proof (P.next_preserves_live Hstep) as Hlive.
  apply P.step_view in Hstep; destruct Hstep; [eapply core_readers_live; eauto | | | | | | | |].
  all: try solve [eapply (@readers_live_view st _); [reflexivity |exact Hlive |exact Hreaders]].
  - eapply (@readers_live_view st _); [unfold R.materialize; destruct (M.lookup _ owner); reflexivity |exact Hlive |exact Hreaders].
  - eapply (@readers_live_view st _); [unfold R.observe; destruct (P.Ranks.observe _ target); reflexivity |exact Hlive |exact Hreaders].
  - eapply (@readers_live_view st _); [exact (proj1 (proj2 (P.publish_layout _ st fr))) |exact Hlive |exact Hreaders].
  - unfold R.continue_dead in Hlive |- *; destruct changed; [destruct (_ && _)%bool |];
      (eapply (@readers_live_view st _); [unfold N.requeue_source; destruct N.cell_changed; exact (proj1 (proj2 (proj2 (proj2 (B.write_layout H))))) |exact Hlive |exact Hreaders]).
Qed.
Theorem reachable_readers_live tf roots c : P.reachable tf roots c -> readers_live (R.cfg_state c).
Proof.
  intro Hpath; assert (Hinitial : readers_live R.empty_state).
  { intros target owner Hmem; unfold R.lookup_set in Hmem; cbn in Hmem; rewrite ML.lookup_empty, SL.empty_spec in Hmem; discriminate. }
  assert (Hpreserve : forall before after, P.steps tf before after -> B.frames_live before ->
    readers_live (R.cfg_state before) -> readers_live (R.cfg_state after)).
  { intros before after Hsteps; induction Hsteps as [refl_cfg|before next after Hstep Hsteps IH]; intros Hframes Hreaders; [exact Hreaders |].
    apply IH; [eapply P.next_frames_live; eauto |eapply next_readers_live; eauto]. }
  eapply Hpreserve; [exact Hpath |constructor |exact Hinitial].
Qed.
Lemma commit_shape tf st fr direct k after next_fr next_k :
  P.step tf (B.configuration st (R.RunCommit fr direct k)) (B.configuration after (R.RunDrain next_fr next_k)) ->
  exists written, R.set_value st fr direct = (written,next_fr) /\
    after = R.requeue_changed_controlled_owner st written (R.frame_owner fr) /\ next_k = k.
Proof.
  intro Hstep; pose proof (P.step_view Hstep) as Hview; inversion Hview; subst.
  unfold B.step, R.next_config in H; cbn -[R.set_value] in H;
  destruct (R.set_value st fr direct) as [written written_fr] eqn:Hw;
  inversion H; subst; exists written; split; [reflexivity |split; reflexivity].
Qed.
Lemma ready_complete tf roots st fr direct k after next_fr next_k :
  P.reachable tf roots (B.configuration st (R.RunCommit fr direct k)) ->
  P.step tf (B.configuration st (R.RunCommit fr direct k)) (B.configuration after (R.RunDrain next_fr next_k)) ->
  D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
  inhabited (complete tf st fr direct).
Proof.
  intros Hr Hstep Hin; destruct (@P.actual_commit_ready tf st fr direct k after next_fr next_k Hstep) as [_ Hquiet].
  pose proof (P.invariant_observing (P.reachable_semantic_invariant Hr)) as Hobs.
  destruct Hobs as [[[cur Hledger] Hstack]].
  constructor; refine (@Build_complete tf st fr direct (P.reads cur) (P.sides cur) (P.spawns cur)
    (B.prefix_return (P.prefix cur)) _ _ _ (P.raw_input cur) _ Hin).
  - intros target value Hmem; rewrite (@B.read_value st target value (proj1 (P.watches cur Hquiet target value Hmem))); apply DL.leq_refl.
  - intros target value Hmem; exists value; exact (proj1 (P.watches cur Hquiet target value Hmem)).
  - intros target Hmem; exact (@B.live_reference_solved (B.configuration st (R.RunCommit fr direct k)) (P.reachable_frames_live Hr) eq_refl target (P.live_spawns cur target Hmem)).
  - intros target input Hlookup; exact (proj2 (Hledger target input Hlookup)).
Qed.
Lemma commit_queue_live root st fr direct written next_fr : higher_queue_live root st -> readers_live st ->
  B.solved st (R.frame_owner fr) -> R.set_value st fr direct = (written,next_fr) ->
  higher_queue_live root (R.requeue_changed_controlled_owner st written (R.frame_owner fr)).
Proof.
  intros Hq Hreaders Hsource Hw owner Hin Habove.
  pose proof (@B.commit_footprint st fr direct written next_fr Hw) as Hview.
  assert (Hrank : R.rank_lt st root owner = true).
  { unfold R.rank_lt in Habove; cbn [R.requeue_changed_controlled_owner R.with_queue R.ranking] in Habove;
    rewrite (B.commit_ranking Hview) in Habove; exact Habove. }
  eapply B.preserves_live_layout; [reflexivity |apply (B.preserves_live_commit Hw)].
  apply B.requeue_members in Hin; destruct Hin as [->|Hin]; [exact Hsource |].
  destruct (@B.commit_queue st fr direct written next_fr Hw) as [Hsame|Hinsert].
  - rewrite Hsame in Hin; apply Hq; assumption.
  - rewrite Hinsert in Hin; apply B.insert_all_members in Hin; destruct Hin as [Hreader|Hin]; [apply Hreaders with (target := R.frame_owner fr); apply SL.mem_spec; exact Hreader |apply Hq; assumption].
Qed.
Theorem boxn_entry_wave tf roots st fr direct k after next_fr next_k :
  P.reachable tf roots (B.configuration st (R.RunCommit fr direct k)) ->
  P.step tf (B.configuration st (R.RunCommit fr direct k)) (B.configuration after (R.RunDrain next_fr next_k)) ->
  R.frame_phase fr = U.BoxW -> R.frame_phase next_fr = U.BoxN ->
  wave tf (R.frame_owner fr) next_k (B.configuration after (R.RunDrain next_fr next_k)).
Proof.
  intros Hr Hstep Hp Hnext.
  destruct (commit_shape Hstep) as [written [Hw [Hafter Hk]]]; subst after next_k.
  destruct (@entered_boxn st fr direct written next_fr Hp Hnext Hw) as [Hcontrolled Hin].
  destruct (@ready_complete tf roots st fr direct k _ next_fr k Hr Hstep Hin) as [Hcomplete].
  pose proof (@B.commit_footprint st fr direct written next_fr Hw) as Hview.
  pose proof (P.reachable_frames_live Hr) as Hframes; change (Forall (B.solved st) (R.frame_owner fr::B.suspended_owners k)) in Hframes.
  assert (Hsource : B.solved st (R.frame_owner fr)) by (inversion Hframes; assumption).
  set (final := R.requeue_changed_controlled_owner st written (R.frame_owner fr)).
  assert (Hlive : B.preserves_live st final) by (intros owner Hsolved; eapply B.preserves_live_layout; [reflexivity |apply (B.preserves_live_commit Hw); exact Hsolved]).
  assert (Hdown : values_descend st final) by (intro owner; exact (@set_values_descend st fr direct written next_fr Hin Hw owner)).
  assert (Hq : higher_queue_live (R.frame_owner fr) st).
  { intros owner Hmem Habove; exfalso; exact (proj1 (@controlled_higher_clean tf roots st fr direct k final next_fr k Hr Hstep Hcontrolled owner Habove) Hmem). }
  constructor; cbn [B.configuration R.cfg_state R.cfg_control].
  - apply Hlive; exact Hsource.
  - intros owner Hregion Hsolved.
    assert (Hbefore : B.solved st owner) by (eapply B.solved_commit_back; [exact Hw |exact Hsource |exact Hsolved]).
    destruct Hregion as [->|Habove].
    + constructor; exact (@history_payload tf written final (R.frame_owner fr)
        (@commit_history tf st fr direct written next_fr Hw Hcomplete) eq_refl eq_refl).
    + assert (Hbefore_above : R.rank_lt st (R.frame_owner fr) owner = true).
      { unfold R.rank_lt in Habove; cbn [final R.requeue_changed_controlled_owner R.with_queue R.ranking] in Habove;
        rewrite (B.commit_ranking Hview) in Habove; exact Habove. }
      destruct (@clean_history tf roots (B.configuration st (R.RunCommit fr direct k)) owner Hr Hbefore
        (@controlled_higher_clean tf roots st fr direct k final next_fr k Hr Hstep Hcontrolled owner Hbefore_above)) as [h].
      assert (Hneq : owner <> R.frame_owner fr) by (intro Heq; subst owner; unfold R.rank_lt in Hbefore_above; rewrite B.lt_irrefl in Hbefore_above; discriminate).
      destruct (@history_transport tf st final owner h Hdown Hlive
        ltac:(unfold final, R.sigma_value; cbn [R.requeue_changed_controlled_owner R.with_queue R.sigma]; rewrite (B.commit_other Hview Hneq); reflexivity)
        ltac:(apply aggregates_same; exact (B.commit_contributions Hview))
        ltac:(apply rows_same; exact (B.commit_contributions Hview))) as [hnext _]; constructor; exact hnext.
  - eapply commit_queue_live; [exact Hq |exact (@reachable_readers_live tf roots (B.configuration st (R.RunCommit fr direct k)) Hr) |exact Hsource |exact Hw].
  - split.
    + split; [left; exact (B.commit_owner Hview) |rewrite Hnext; discriminate].
    + apply WaveBase.
Qed.
Lemma materialize_known st owner : B.solved st owner -> R.sigma (R.materialize st owner) = R.sigma st.
Proof. intros [value Hv]; change (M.lookup (R.sigma st) owner = Some value) in Hv; unfold R.materialize; rewrite Hv; reflexivity. Qed.
Lemma wave_payload tf roots root base before after ctrl : P.reachable tf roots before -> wave tf root base before ->
  B.extends (R.ranking (R.cfg_state before)) (R.ranking after) ->
  R.sigma after = R.sigma (R.cfg_state before) -> R.contributions after = R.contributions (R.cfg_state before) ->
  (forall owner, In owner (R.queue after) -> In owner (R.queue (R.cfg_state before))) ->
  wave_control tf root base after ctrl -> wave tf root base (B.configuration after ctrl).
Proof.
  intros Hr [Hroot Hhist Hq Hctrl] Hext Hsigma Hrows Hsubset Hnext.
  pose proof (proj1 (P.reachable_rank_configuration Hr)) as Hstore.
  constructor; cbn.
  - eapply B.preserves_live_layout; eauto.
  - eapply histories_payload; eauto.
  - eapply higher_queue_subset; eauto; apply B.preserves_live_layout; exact Hsigma.
  - exact Hnext.
Qed.
Lemma core_boxw tf before after : B.step tf before after ->
  control_phases (fun phase => phase = U.BoxW) (R.cfg_control before) ->
  control_phases (fun phase => phase = U.BoxW) (R.cfg_control after) \/
  exists st fr direct k written next_fr, before = B.configuration st (R.RunCommit fr direct k) /\
    R.frame_phase fr = U.BoxW /\ R.set_value st fr direct = (written,next_fr) /\
    after = B.configuration (R.requeue_changed_controlled_owner st written (R.frame_owner fr)) (R.RunDrain next_fr k) /\
    R.frame_phase next_fr = U.BoxN.
Proof.
  destruct before as [st ctrl]; intros Hstep Hphase.
  destruct ctrl; cbn [R.cfg_control control_phases] in Hphase.
  all: unfold B.step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  all: try match type of Hphase with _ /\ _ => destruct Hphase as [Hphase Hk] end.
  all: unfold R.continue_side, R.continue_dead in Hstep.
  all: B.split_program Hstep; cbn [R.cfg_control control_phases continuation_phases] in *.
  all: try solve [left; cbn [R.fresh_frame R.with_frame_side R.with_frame_read U.initial_phase]; tauto].
  all: try solve [left; unfold R.complete_get in *; B.split_program Hstep; cbn in *; tauto].
  all: try solve [left; unfold R.record_side_input in *; B.split_program Hstep; cbn in *; tauto].
  all: try solve [match goal with Hget : B.R.complete_get _ _ _ = (_,_,_) |- _ =>
    left; rewrite (B.get_phase Hget); tauto end].
  all: try solve [match goal with Hside : B.R.record_side_input _ _ _ = (_,_) |- _ =>
    unfold R.record_side_input in Hside; inversion Hside; subst; left; cbn; tauto end].
  all: try match goal with Hw : R.set_value _ _ _ = (_,_) |- _ =>
    destruct (@set_boxw_phase _ _ _ _ _ Hphase Hw) as [Hwphase|Hnphase];
      [left; split; assumption |right; do 6 eexists; repeat split; eauto]
  end.
Qed.

Definition precision_invariant tf c :=
  control_phases (fun phase => phase = U.BoxW) (R.cfg_control c) \/
  exists root base, continuation_phases (fun phase => phase = U.BoxW) base /\ wave tf root base c.
Lemma outside_step tf roots before after : P.reachable tf roots before -> P.step tf before after ->
  control_phases (fun phase => phase = U.BoxW) (R.cfg_control before) -> precision_invariant tf after.
Proof.
  intros Hr Hstep Hphase; pose proof (P.step_view Hstep) as Hview; destruct Hview.
  - destruct (core_boxw H Hphase) as [Hsame|Hentry]; [left; exact Hsame |].
    destruct Hentry as (st & fr & direct & k & written & next_fr & Heq & Hp & Hw & Ha & Hn); subst before after.
    right; exists (R.frame_owner fr), k; split; [exact (proj2 Hphase) |eapply boxn_entry_wave; eauto].
  - left; cbn [B.configuration R.cfg_state R.cfg_control control_phases R.fresh_frame U.initial_phase]; auto.
  - left; cbn [B.configuration R.cfg_control control_phases R.with_frame_side] in *; exact Hphase.
  - left; exact Hphase.
  - left; unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; exact Hphase.
  - left; unfold N.suspend_commit; cbn [R.cfg_control control_phases continuation_phases R.fresh_frame] in *; exact Hphase.
  - left; unfold N.retry_current; cbn [R.cfg_control control_phases R.fresh_frame] in *; exact Hphase.
  - left; unfold N.suspend_commit; cbn [R.cfg_control control_phases continuation_phases R.fresh_frame] in *; exact Hphase.
  - left; exact Hphase.
Qed.
Lemma wave_state_control tf root base c ctrl : wave tf root base c ->
  wave_control tf root base (R.cfg_state c) ctrl -> wave tf root base (B.configuration (R.cfg_state c) ctrl).
Proof. intros [Hroot Hhist Hq _] Hctrl; constructor; assumption. Qed.
Lemma history_override tf root st source : inhabited (history tf st source) -> histories tf root st -> histories tf root st.
Proof. intros Hnew Hhist owner Hregion Hsolved; destruct (V.eq_dec owner source) as [->|Hother]; auto. Qed.
Lemma region_higher st root source target : region st root source -> R.rank_lt st source target = true -> R.rank_lt st root target = true.
Proof. intros [->|Habove] Htarget; [exact Htarget |unfold R.rank_lt in *; eapply B.lt_trans; eauto]. Qed.
Lemma queue_pop_subset st owner rest : R.queue_pop (R.queue st) = Some (owner,rest) -> forall target, In target rest -> In target (R.queue st).
Proof. destruct (R.queue st); cbn; [discriminate |intro H; inversion H; subst; intros target Hin; right; exact Hin]. Qed.
Lemma pending_known root st fr target rest : higher_queue_live root st -> eligible root st fr ->
  N.pending_above st (R.frame_owner fr) = Some (target,rest) ->
  R.rank_lt st root target = true /\ B.solved st target.
Proof.
  intros Hq [Hregion Hphase] Hp; destruct (P.pending_spec Hp) as [_ [Hpop Habove]].
  assert (Hroot : R.rank_lt st root target = true) by (eapply region_higher; eauto).
  split; [exact Hroot |apply Hq; [destruct (R.queue st); cbn in Hpop; [discriminate |inversion Hpop; subst; left; reflexivity] |exact Hroot]].
Qed.

Lemma wave_commit tf roots root base st fr direct k written next_fr :
  P.reachable tf roots (B.configuration st (R.RunCommit fr direct k)) ->
  wave tf root base (B.configuration st (R.RunCommit fr direct k)) ->
  R.set_value st fr direct = (written,next_fr) ->
  wave tf root base (B.configuration (R.requeue_changed_controlled_owner st written (R.frame_owner fr)) (R.RunDrain next_fr k)).
Proof.
  intros Hr [Hroot Hhist Hq [[Hregion Hphase] [[Hcomplete] Hstack]]] Hw.
  pose proof (proj1 (P.reachable_rank_configuration Hr)) as Hstore.
  pose proof (@B.commit_footprint st fr direct written next_fr Hw) as Hview.
  assert (Hsource : B.solved st (R.frame_owner fr)).
  { pose proof (P.reachable_frames_live Hr) as Hframes; change (Forall (B.solved st) (R.frame_owner fr :: B.suspended_owners k)) in Hframes; inversion Hframes; assumption. }
  set (final := R.requeue_changed_controlled_owner st written (R.frame_owner fr)).
  assert (Hlive : B.preserves_live st final) by (intros owner Hsolved; eapply (@B.preserves_live_layout written final); [reflexivity |exact ((B.preserves_live_commit Hw) owner Hsolved)]).
  assert (Hext : B.extends (R.ranking st) (R.ranking final)) by (unfold final; cbn [R.requeue_changed_controlled_owner R.with_queue R.ranking]; rewrite (B.commit_ranking Hview); apply B.extends_refl).
  constructor; cbn.
  - apply Hlive; exact Hroot.
  - eapply (@histories_replace tf root (R.frame_owner fr) st final); [exact Hstore |exact Hroot |exact Hext | |exact Hlive | | | | | |exact Hhist].
    + intro owner; exact (@set_values_descend st fr direct written next_fr (complete_value Hcomplete) Hw owner).
    + intros owner Hsolved; eapply B.solved_commit_back; [exact Hw |exact Hsource |exact Hsolved].
    + apply aggregates_same; exact (B.commit_contributions Hview).
    + intros owner Hother; unfold final, R.sigma_value; cbn [R.requeue_changed_controlled_owner R.with_queue R.sigma]; rewrite (B.commit_other Hview Hother); reflexivity.
    + intros owner target Hother; apply rows_same; exact (B.commit_contributions Hview).
    + constructor; exact (@history_payload tf written final (R.frame_owner fr) (commit_history Hw Hcomplete) eq_refl eq_refl).
  - eapply commit_queue_live; [exact Hq |exact (@reachable_readers_live tf roots (B.configuration st (R.RunCommit fr direct k)) Hr) |exact Hsource |exact Hw].
  - split; [split |eapply wave_stack_extends; eauto].
    + rewrite (B.commit_owner Hview); eapply region_extends; eauto.
    + eapply set_safe_phase; [exact Hphase |exact (complete_value Hcomplete) |exact Hw].
Qed.
Lemma wave_publication tf roots root base st fr direct k :
  P.reachable tf roots (B.configuration st (R.RunDead fr direct [] k)) ->
  wave tf root base (B.configuration st (R.RunDead fr direct [] k)) ->
  wave tf root base (B.configuration (R.publish_targets (N.publish (S.elements (R.frame_current_targets fr)) st fr) fr) (R.RunCommit fr direct k)).
Proof.
  intros Hr [Hroot Hhist Hq [Helig [[Hcomplete] Hstack]]].
  pose proof (proj1 (P.reachable_rank_configuration Hr)) as Hstore.
  pose proof (P.reachable_frames_live Hr) as Hframes.
  assert (Hsource : B.solved st (R.frame_owner fr)) by (change (Forall (B.solved st) (R.frame_owner fr :: B.suspended_owners k)) in Hframes; inversion Hframes; assumption).
  assert (Hbottom : unknown_above_bottom root st) by (eapply (@wave_unknown_bottom tf roots root (B.configuration st (R.RunDead fr direct [] k))); [exact Hr |exact Hq |exact Hframes]).
  set (published := N.publish (S.elements (R.frame_current_targets fr)) st fr).
  set (final := R.publish_targets published fr).
  destruct (@publication_live tf (S.elements (R.frame_current_targets fr)) root st fr direct Hq Hbottom Hsource Hcomplete) as [[Hdone] [Hnextq [Hnextbottom Hagg]]].
  pose proof (P.publish_layout (S.elements (R.frame_current_targets fr)) st fr) as [Hsigma _].
  assert (Hfinalsigma : R.sigma final = R.sigma st) by exact Hsigma.
  assert (Hlive : B.preserves_live st final) by (apply B.preserves_live_layout; exact Hfinalsigma).
  assert (Hfinalrank : R.ranking final = R.ranking st) by (apply P.publish_rank).
  assert (Hext : B.extends (R.ranking st) (R.ranking final)) by (rewrite Hfinalrank; apply B.extends_refl).
  constructor; cbn.
  - apply Hlive; exact Hroot.
  - eapply (@histories_replace tf root (R.frame_owner fr) st final); [exact Hstore |exact Hroot |exact Hext |apply values_same; exact Hfinalsigma |exact Hlive | |exact Hagg | | | |exact Hhist].
    + intros owner Hsolved; eapply B.solved_layout_back; eauto.
    + intros owner Hother; unfold R.sigma_value; now rewrite Hfinalsigma.
    + intros owner target Hother; exact (proj2 (@P.publish_other_cell (S.elements (R.frame_current_targets fr)) st fr owner target (or_introl Hother))).
    + constructor; exact (@history_payload tf published final (R.frame_owner fr) (complete_history Hdone) eq_refl eq_refl).
  - exact Hnextq.
  - split; [destruct Helig as [Hregion Hphase]; split; [eapply region_extends; eauto |exact Hphase] |split; [constructor; exact (@complete_payload tf published final fr direct eq_refl eq_refl Hdone) |eapply wave_stack_extends; eauto]].
Qed.

Lemma descending_continue_dead root st fr direct target rest k next changed :
  unknown_above_bottom root st -> eligible root st fr ->
  R.write_side_contribution st fr target D.bottom = (next,changed) ->
  R.continue_dead (N.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed =
  B.configuration (N.finish_write st next fr target changed) (R.RunDead fr direct rest k).
Proof.
  intros Hbottom [Hregion Hphase] Hw; unfold R.continue_dead, N.finish_write.
  destruct changed eqn:Hchanged; [|reflexivity].
  destruct (R.rank_lt (N.requeue_source st next (R.frame_owner fr) target) (R.frame_owner fr) target) eqn:Habove; [|reflexivity].
  assert (Hbefore : R.rank_lt st (R.frame_owner fr) target = true) by (unfold R.rank_lt in *; rewrite P.requeue_rank, (B.write_rank Hw) in Habove; exact Habove).
  assert (Hknown : B.solved st target) by (eapply descending_change_live; [exact Hbottom |exact Hw |exact (proj2 (write_descends Hw (DL.bottom_least _))) |reflexivity |eapply region_higher; eauto]).
  assert (Hnext : B.solved (N.requeue_source st next (R.frame_owner fr) target) target) by
    (eapply B.preserves_live_layout; [rewrite P.requeue_sigma; exact (proj1 (proj2 (proj2 (B.write_layout Hw)))) |exact Hknown]).
  rewrite (proj2 (B.materialized_iff_solved _ _) Hnext); reflexivity.
Qed.
Lemma wave_remove tf roots root base st fr direct target rest k next changed :
  P.reachable tf roots (B.configuration st (R.RunDead fr direct (target::rest) k)) ->
  wave tf root base (B.configuration st (R.RunDead fr direct (target::rest) k)) ->
  S.mem target (R.frame_current_targets fr) = false ->
  R.write_side_contribution st fr target D.bottom = (next,changed) ->
  wave tf root base (R.continue_dead (N.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed).
Proof.
  intros Hr [Hroot Hhist Hq [Helig [[Hcomplete] Hstack]]] Habsent Hw.
  pose proof (proj1 (P.reachable_rank_configuration Hr)) as Hstore.
  pose proof (P.reachable_frames_live Hr) as Hframes.
  assert (Hsource : B.solved st (R.frame_owner fr)) by (change (Forall (B.solved st) (R.frame_owner fr :: B.suspended_owners k)) in Hframes; inversion Hframes; assumption).
  assert (Hbottom : unknown_above_bottom root st) by (eapply (@wave_unknown_bottom tf roots root (B.configuration st (R.RunDead fr direct (target::rest) k))); [exact Hr |exact Hq |exact Hframes]).
  assert (Hcache : forall value, M.lookup (R.frame_local_side fr) target = Some value -> D.leq value D.bottom = true).
  { intros value Hl; pose proof (P.invariant_observing (P.reachable_semantic_invariant Hr)) as Hobs.
    destruct Hobs as [[cur Hparents]]; pose proof (P.local_targets cur Hl) as Hmem; congruence. }
  rewrite (@descending_continue_dead root st fr direct target rest k next changed Hbottom Helig Hw).
  set (final := N.finish_write st next fr target changed).
  destruct (@complete_finish_live tf root st fr direct target D.bottom next changed Hq Hbottom Hsource Hw (DL.bottom_least _) Hcache Hcomplete) as [[Hdone] [Hnextq Hnextbottom]].
  assert (Hsigma : R.sigma final = R.sigma st) by (unfold final, N.finish_write, N.requeue_source; destruct changed, N.cell_changed; exact (proj1 (proj2 (proj2 (B.write_layout Hw))))).
  assert (Hrank : R.ranking final = R.ranking st) by (unfold final; rewrite P.finish_rank; exact (B.write_rank Hw)).
  assert (Hext : B.extends (R.ranking st) (R.ranking final)) by (rewrite Hrank; apply B.extends_refl).
  assert (Hlive : B.preserves_live st final) by (apply B.preserves_live_layout; exact Hsigma).
  constructor; cbn.
  - apply Hlive; exact Hroot.
  - eapply (@histories_replace tf root (R.frame_owner fr) st final); [exact Hstore |exact Hroot |exact Hext |apply values_same; exact Hsigma |exact Hlive | | | | |constructor; exact (complete_history Hdone) |exact Hhist].
    + intros owner Hsolved; eapply B.solved_layout_back; eauto.
    + intro owner; unfold final, N.finish_write, N.requeue_source; destruct changed, N.cell_changed; exact (proj2 (write_descends Hw (DL.bottom_least _)) owner).
    + intros owner Hother; unfold R.sigma_value; now rewrite Hsigma.
    + intros owner observed Hother; unfold final, N.finish_write, N.requeue_source; destruct changed, N.cell_changed;
      change (R.stored_contribution next owner observed = R.stored_contribution st owner observed);
      rewrite (B.write_other_contribution Hw) by auto; reflexivity.
  - exact Hnextq.
  - split; [destruct Helig as [Hregion Hphase]; split; [eapply region_extends; eauto |exact Hphase] |split; [constructor; exact Hdone |eapply wave_stack_extends; eauto]].
Qed.

Lemma core_wave tf roots root base before after : monotonic_system tf ->
  P.reachable tf roots before -> P.step tf before after -> B.step tf before after -> P.core_rule (R.cfg_control before) ->
  continuation_phases (fun phase => phase = U.BoxW) base -> wave tf root base before -> precision_invariant tf after.
Proof.
  intros Hmono Hr Hnative Hcore Hrule Hbase Hwave.
  pose proof Hwave as Hbefore.
  destruct Hwave as [Hroot Hhist Hq Hctrl].
  pose proof (proj1 (P.reachable_rank_configuration Hr)) as Hstore.
  destruct before as [st ctrl]; cbn [B.configuration R.cfg_state R.cfg_control] in *.
  destruct ctrl as [|seeds|seeds|owner k|fr body k|fr direct pending k|fr direct k|fr k|k]; cbn [wave_control P.core_rule] in Hctrl, Hrule; try contradiction.
  - destruct Hctrl as [Helig [[Hrun] Hstack]].
    destruct body as [direct|target tail|target raw body|target body]; [| |contradiction |].
    + unfold B.step, R.next_config in Hcore; cbn in Hcore; inversion Hcore; subst after.
      pose proof (running_complete Hmono Hrun) as Hcomplete.
      right; exists root, base; split; [exact Hbase |constructor; cbn; [exact Hroot | |exact Hq |]].
      * apply (@history_override tf root st (R.frame_owner fr)); [constructor; exact (complete_history Hcomplete) |exact Hhist].
      * split; [exact Helig |split; [constructor; exact Hcomplete |exact Hstack]].
    + pose proof (@prefix_get_live tf st fr target tail (running_reads Hrun) (running_sides Hrun) (running_spawns Hrun)
        (running_upper Hrun) Hmono (running_prefix Hrun) (running_common Hrun)) as Hknown.
      assert (Hmat : R.is_materialized (R.observe st target) target = true) by (rewrite B.observe_materialized; apply B.materialized_iff_solved; exact Hknown).
      unfold B.step, R.next_config in Hcore; cbn -[R.complete_get R.observe] in Hcore; rewrite Hmat in Hcore; cbn -[R.complete_get R.observe] in Hcore.
      destruct (R.complete_get (R.observe st target) fr target) as [[next next_fr] value] eqn:Hg; inversion Hcore; subst after.
      pose proof (proj1 (known_get_data ltac:(eapply B.preserves_live_layout; [apply B.observe_sigma |exact Hknown]) Hg)) as Hsigma.
      assert (Hrows : R.contributions next = R.contributions st) by (rewrite (proj1 (proj2 (proj2 (B.get_layout Hg)))); unfold R.observe; destruct (P.Ranks.observe _ target); reflexivity).
      assert (Hext : B.extends (R.ranking st) (R.ranking next)) by (rewrite (B.get_rank Hg); apply B.observe_extends).
      assert (Hsigma0 : R.sigma next = R.sigma st) by (rewrite Hsigma; apply B.observe_sigma).
      right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Get target tail) k)) next (R.RunRhs next_fr (tail value) k)); [exact Hr |exact Hbefore |exact Hext |exact Hsigma0 |exact Hrows | |]].
      * intros owner Hin; rewrite (proj1 (proj2 (B.get_layout Hg))) in Hin; unfold R.observe in Hin; destruct (P.Ranks.observe _ target); exact Hin.
      * split; [destruct Helig as [Hregion Hphase]; split; [rewrite (B.get_owner Hg); eapply region_extends; eauto |rewrite (B.get_phase Hg); exact Hphase] |split].
        -- constructor; apply (@running_get tf (R.observe st target) fr target tail next next_fr value Hmono); [eapply (@running_payload tf st _); [apply B.observe_sigma |unfold R.observe; destruct (P.Ranks.observe _ target); reflexivity |exact Hrun] |exact Hg].
        -- eapply wave_stack_extends; eauto.
    + pose proof (@prefix_spawn_live tf st fr target body (running_reads Hrun) (running_sides Hrun) (running_spawns Hrun)
        (running_upper Hrun) Hmono (running_prefix Hrun) (running_common Hrun)) as Hknown.
      assert (Hmat : R.is_materialized (R.observe st target) target = true) by (rewrite B.observe_materialized; apply B.materialized_iff_solved; exact Hknown).
      unfold B.step, R.next_config in Hcore; cbn -[R.observe] in Hcore; rewrite Hmat in Hcore; inversion Hcore; subst after.
      right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Spawn target body) k)) (R.observe st target) (R.RunRhs fr body k)); [exact Hr |exact Hbefore |apply B.observe_extends |apply B.observe_sigma | | |]].
      * unfold R.observe; destruct (P.Ranks.observe _ target); reflexivity.
      * intros owner Hin; unfold R.observe in Hin; destruct (P.Ranks.observe _ target); exact Hin.
      * split; [destruct Helig as [Hregion Hphase]; split; [eapply region_extends; [apply B.observe_extends |exact Hregion] |exact Hphase] |split; [constructor; apply running_spawn; assumption |eapply wave_stack_extends; [apply B.observe_extends |exact Hstack]]].
  - destruct pending as [|target rest]; [contradiction |].
    unfold B.step, R.next_config in Hcore; cbn in Hcore; rewrite Hrule in Hcore; inversion Hcore; subst after.
    right; exists root, base; split; [exact Hbase |constructor; cbn; [exact Hroot |exact Hhist |exact Hq |exact Hctrl]].
  - unfold B.step, R.next_config in Hcore; cbn -[R.set_value] in Hcore.
    destruct (R.set_value st fr direct) as [written next_fr] eqn:Hw; inversion Hcore; subst after.
    right; exists root, base; split; [exact Hbase |eapply wave_commit; [exact Hr |exact Hbefore |exact Hw]].
  - destruct Hctrl as [Helig Hstack].
    unfold B.step, R.next_config in Hcore; cbn -[R.reset_registered_cells R.fresh_frame] in Hcore.
    destruct (R.queue st) as [|target rest] eqn:Hqueue; cbn [R.queue_peek R.queue_pop] in Hcore.
    + inversion Hcore; subst after.
      right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunDrain fr k)) (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k)); [exact Hr |exact Hbefore | | | | |]].
      all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply B.extends_refl].
      all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity].
      all: try solve [intros owner Hin; unfold R.reset_registered_cells in Hin; destruct Features.restart_side_phases; exact Hin].
      eapply (@wave_stack_extends tf root base st (R.reset_registered_cells st (R.frame_owner fr)) k); [unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply B.extends_refl |exact Hstack].
    + destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hother].
      * inversion Hcore; subst after.
        assert (Hknown : B.solved st (R.frame_owner fr)) by (pose proof (P.reachable_frames_live Hr) as Hframes; change (Forall (B.solved st) (R.frame_owner fr::B.suspended_owners k)) in Hframes; inversion Hframes; assumption).
        destruct (Hhist (R.frame_owner fr) (proj1 Helig) Hknown) as [h].
        right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunDrain fr k)) (R.with_queue st rest) _); [exact Hr |exact Hbefore |apply B.extends_refl |reflexivity |reflexivity | |]].
        -- intros owner Hin; change (In owner (R.queue st)); rewrite Hqueue; right; exact Hin.
        -- split; [exact Helig |split; [constructor; apply running_fresh; exact (@history_payload tf st (R.with_queue st rest) (R.frame_owner fr) h eq_refl eq_refl) |eapply (@wave_stack_extends tf root base st (R.with_queue st rest) k); [apply B.extends_refl |exact Hstack]]].
      * destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Habove.
        -- inversion Hcore; subst after.
           assert (Hrootabove : R.rank_lt st root target = true) by (eapply region_higher; [exact (proj1 Helig) |exact Habove]).
           assert (Hknown : B.solved st target) by (apply Hq; [rewrite Hqueue; left; reflexivity |exact Hrootabove]).
           right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunDrain fr k)) (R.with_queue st rest) _); [exact Hr |exact Hbefore |apply B.extends_refl |reflexivity |reflexivity | |]].
           ++ intros owner Hin; change (In owner (R.queue st)); rewrite Hqueue; right; exact Hin.
           ++ split; [exact Hrootabove |split; [exact Hknown |apply WaveDrain; [exact Helig |eapply (@wave_stack_extends tf root base st (R.with_queue st rest) k); [apply B.extends_refl |exact Hstack]]]].
        -- inversion Hcore; subst after.
           right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunDrain fr k)) (R.reset_registered_cells st (R.frame_owner fr)) _); [exact Hr |exact Hbefore | | | | |]].
           all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply B.extends_refl].
           all: try solve [unfold R.reset_registered_cells; destruct Features.restart_side_phases; reflexivity].
           all: try solve [intros owner Hin; unfold R.reset_registered_cells in Hin; destruct Features.restart_side_phases; exact Hin].
           eapply (@wave_stack_extends tf root base st (R.reset_registered_cells st (R.frame_owner fr)) k); [unfold R.reset_registered_cells; destruct Features.restart_side_phases; apply B.extends_refl |exact Hstack].
  - inversion Hctrl; subst.
    + eapply outside_step; [exact Hr |exact Hnative |exact Hbase].
    + unfold B.step, R.next_config in Hcore; cbn in Hcore; inversion Hcore; subst after.
      right; exists root, base; split; [exact Hbase |constructor; cbn; [exact Hroot |exact Hhist |exact Hq |split; assumption]].
    + contradiction.
Qed.

Lemma running_empty tf st fr : P.empty_cache fr -> history tf st (R.frame_owner fr) -> running tf st fr (tf (R.frame_owner fr)).
Proof.
  intros Hcache h; refine (@Build_running tf st fr (tf (R.frame_owner fr)) h [] [] [] (@B.prefix_fresh _) _ _ _ _ _ _).
  all: try solve [intros target value Hin; contradiction].
  all: try solve [intros target value upper_value Hin; contradiction].
  all: try solve [intros target Hin; contradiction].
  intros target input Hlookup; rewrite Hcache, ML.lookup_empty in Hlookup; discriminate.
Qed.
Lemma wave_suspend tf roots root base st ctrl fr k target rest :
  P.reachable tf roots (B.configuration st ctrl) -> wave tf root base (B.configuration st ctrl) ->
  eligible root st fr -> wave_stack tf root st base k -> N.pending_above st (R.frame_owner fr) = Some (target,rest) ->
  wave tf root base (N.suspend_commit tf st fr k target rest).
Proof.
  intros Hr Hwave Helig Hstack Hp; destruct (@pending_known root st fr target rest (wave_queue Hwave) Helig Hp) as [Habove Hknown].
  pose proof (proj1 (proj2 (P.pending_spec Hp))) as Hpop.
  unfold N.suspend_commit; eapply (@wave_payload tf roots root base (B.configuration st ctrl) (R.with_queue st rest) _);
    [exact Hr |exact Hwave |apply B.extends_refl |reflexivity |reflexivity | |].
  - intros owner Hin; change (In owner (R.queue st)); eapply queue_pop_subset; eauto.
  - split; [exact Habove |split; [exact Hknown |apply (@WaveRestart tf root (R.with_queue st rest) base (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) k); [exact Helig |reflexivity |eapply (@wave_stack_extends tf root base st (R.with_queue st rest) k); [apply B.extends_refl |exact Hstack]]]].
Qed.
Theorem next_precision_invariant tf roots before after : monotonic_system tf ->
  P.reachable tf roots before -> P.step tf before after -> precision_invariant tf before -> precision_invariant tf after.
Proof.
  intros Hmono Hr Hstep [Houtside|[root [base [Hbase Hwave]]]]; [eapply outside_step; eauto |].
  pose proof Hwave as Hbefore; destruct Hwave as [Hroot Hhist Hq Hctrl].
  pose proof (P.step_view Hstep) as Hview; destruct Hview.
  - eapply core_wave; eauto.
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in *; destruct Hctrl as [Habove [Hknown Hstack]].
    set (current := R.materialize (N.clear_owner st owner) owner).
    assert (Hsigma : R.sigma current = R.sigma st) by (unfold current; rewrite materialize_known; [reflexivity |exact Hknown]).
    assert (Hrows : R.contributions current = R.contributions st) by (unfold current, R.materialize; destruct (M.lookup _ owner); reflexivity).
    assert (Hext : B.extends (R.ranking st) (R.ranking current)) by (unfold current; rewrite B.materialize_rank; apply B.extends_refl).
    destruct (Hhist owner (or_intror Habove) Hknown) as [h].
    right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.StartEpisode owner k)) current _); [exact Hr |exact Hbefore |exact Hext |exact Hsigma |exact Hrows | |]].
    + intros query Hin; unfold current in Hin; rewrite B.materialize_queue in Hin; apply P.clear_members in Hin; exact (proj1 Hin).
    + split; [split; [right; unfold R.rank_lt in *; unfold current; rewrite B.materialize_rank; exact Habove |discriminate] |split; [constructor; apply running_fresh; exact (@history_payload tf st current owner h Hsigma Hrows) |eapply wave_stack_extends; eauto]].
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in *; destruct Hctrl as [Helig [[Hrun] Hstack]].
    right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.RunRhs fr (R.ConstraintSystem.Side target raw body) k)) (R.observe st target) _); [exact Hr |exact Hbefore |apply B.observe_extends |apply B.observe_sigma | | |]].
    + unfold R.observe; destruct (P.Ranks.observe _ target); reflexivity.
    + intros owner Hin; unfold R.observe in Hin; destruct (P.Ranks.observe _ target); exact Hin.
    + split; [destruct Helig as [Hregion Hphase]; split; [eapply region_extends; [apply B.observe_extends |exact Hregion] |exact Hphase] |split; [constructor; apply running_side; assumption |eapply wave_stack_extends; [apply B.observe_extends |exact Hstack]]].
  - right; exists root, base; split; [exact Hbase |eapply wave_publication; eauto].
  - destruct (S.mem target (R.frame_current_targets fr)) eqn:Hmem.
    + assert (Heq : R.continue_dead (N.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed = B.configuration st (R.RunDead fr direct rest k)).
      { unfold P.step, N.next_config, N.next_repaired in Hstep; cbn [B.configuration R.cfg_control R.cfg_state] in Hstep; rewrite Hmem in Hstep; injection Hstep as Heq; symmetry; exact Heq. }
      rewrite Heq; right; exists root, base; split; [exact Hbase |constructor; cbn in *; assumption].
    + right; exists root, base; split; [exact Hbase |eapply wave_remove; eauto].
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in Hctrl; destruct Hctrl as [Helig [Hcomplete Hstack]].
    right; exists root, base; split; [exact Hbase |eapply wave_suspend; eauto].
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in *; destruct Hctrl as [Helig [Hcomplete Hstack]].
    assert (Hknown : B.solved st (R.frame_owner fr)) by (pose proof (P.reachable_frames_live Hr) as Hframes; change (Forall (B.solved st) (R.frame_owner fr::B.suspended_owners k)) in Hframes; inversion Hframes; assumption).
    destruct (Hhist (R.frame_owner fr) (proj1 Helig) Hknown) as [h].
    right; exists root, base; split; [exact Hbase |unfold N.retry_current; eapply (@wave_payload tf roots root base (B.configuration st (R.RunCommit fr direct k)) (N.clear_owner st (R.frame_owner fr)) _); [exact Hr |exact Hbefore |apply B.extends_refl |reflexivity |reflexivity | |]].
    + intros owner Hin; apply P.clear_members in Hin; exact (proj1 Hin).
    + split; [exact Helig |split; [constructor; apply running_fresh; exact (@history_payload tf st (N.clear_owner st (R.frame_owner fr)) (R.frame_owner fr) h eq_refl eq_refl) |eapply (@wave_stack_extends tf root base st _ k); [apply B.extends_refl |exact Hstack]]].
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in Hctrl; inversion Hctrl; subst.
    + eapply outside_step; [exact Hr |exact Hstep |exact Hbase].
    + right; exists root, base; split; [exact Hbase |eapply wave_suspend; eauto].
  - cbn [B.configuration R.cfg_state R.cfg_control wave_control] in Hctrl; inversion Hctrl; subst.
    + eapply outside_step; [exact Hr |exact Hstep |exact Hbase].
    + assert (Hknown : B.solved st (R.frame_owner fr)) by (pose proof (P.reachable_frames_live Hr) as Hframes; change (Forall (B.solved st) (R.frame_owner fr::B.suspended_owners k)) in Hframes; inversion Hframes; assumption).
      destruct (Hhist (R.frame_owner fr) (proj1 H2) Hknown) as [h].
      right; exists root, base; split; [exact Hbase |eapply (@wave_payload tf roots root base (B.configuration st (R.Return (R.KAfterSide fr (tf (R.frame_owner fr)) k))) (N.clear_owner st (R.frame_owner fr)) _); [exact Hr |exact Hbefore |apply B.extends_refl |reflexivity |reflexivity | |]].
      * intros owner Hin; apply P.clear_members in Hin; exact (proj1 Hin).
      * split; [exact H2 |split; [constructor; apply running_empty; [exact H3 |exact (@history_payload tf st (N.clear_owner st (R.frame_owner fr)) (R.frame_owner fr) h eq_refl eq_refl)] |eapply (@wave_stack_extends tf root base st _ k); [apply B.extends_refl |exact H4]]].
Qed.

Theorem reachable_precision_invariant tf roots c : P.reachable tf roots c -> monotonic_system tf -> precision_invariant tf c.
Proof.
  intros Hpath Hmono.
  assert (Hpreserve : forall before after, P.steps tf before after -> P.reachable tf roots before ->
    precision_invariant tf before -> precision_invariant tf after).
  { intros before after Hsteps; induction Hsteps as [refl_cfg|before next after Hnext Htail IH]; intros Hr Hinv; [exact Hinv |].
    apply IH; [eapply P.reachable_advance; [exact Hr |exact Hnext] |eapply next_precision_invariant; eauto]. }
  eapply Hpreserve; [exact Hpath |constructor |left; exact I].
Qed.
Definition control_avoids_fallback := control_phases (fun phase => phase <> U.Widen).
Definition avoids_fallback tf roots := forall c, P.reachable tf roots c -> control_avoids_fallback (R.cfg_control c).
Theorem reachable_no_fallback tf roots c : P.reachable tf roots c -> monotonic_system tf -> control_avoids_fallback (R.cfg_control c).
Proof.
  intros Hr Hmono; destruct (reachable_precision_invariant Hr Hmono) as [Houtside|[root [base [Hbase Hwave]]]].
  - unfold control_avoids_fallback; destruct (R.cfg_control c); cbn [control_phases] in *; try tauto;
      try solve [eapply (@phases_map (fun phase => phase = U.BoxW) (fun phase => phase <> U.Widen)); [intros phase ->; discriminate |exact Houtside]].
    all: destruct Houtside as [-> Hk]; split; [discriminate |eapply (@phases_map (fun phase => phase = U.BoxW) (fun phase => phase <> U.Widen)); [intros phase ->; discriminate |exact Hk]].
  - eapply wave_safe; eauto.
Qed.
Theorem monotonic_avoids_fallback tf roots : monotonic_system tf -> avoids_fallback tf roots.
Proof. intros Hmono c Hr; eapply reachable_no_fallback; eauto. Qed.

Lemma evaluating_not_ready st owner k ctrl :
  B.active_owners ctrl = owner :: B.suspended_owners k -> B.drained_owners ctrl = B.drained_stack k ->
  NoDup (B.active_owners ctrl) -> ~ B.incoming_ready (B.configuration st ctrl) owner.
Proof.
  intros Hactive Hdrained Hunique [_ [Hidle|Hdone]].
  - apply Hidle; cbn; rewrite Hactive; left; reflexivity.
  - rewrite Hactive in Hunique; inversion Hunique; subst; apply H1, B.drained_parent.
    cbn in Hdone; rewrite Hdrained in Hdone; exact Hdone.
Qed.
Lemma core_contributions tf before after : P.core_rule (R.cfg_control before) -> B.step tf before after ->
  R.contributions (R.cfg_state after) = R.contributions (R.cfg_state before).
Proof.
  destruct before as [st ctrl]; intros Hrule Hstep; destruct ctrl; cbn [P.core_rule R.cfg_control] in Hrule; try contradiction.
  all: unfold B.step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  all: try match goal with Hstep : context [match ?body with R.ConstraintSystem.Ret _ => _ | _ => _ end] |- _ => destruct body; cbn in Hrule; try contradiction end.
  all: try match goal with Hstep : context [match ?pending with [] => _ | _ => _ end] |- _ => destruct pending; cbn in Hrule; try contradiction; rewrite Hrule in Hstep end.
  all: B.split_program Hstep; cbn [R.cfg_state].
  all: try reflexivity.
  all: try solve [match goal with Hget : B.R.complete_get _ _ _ = (_,_,_) |- _ => rewrite (proj1 (proj2 (proj2 (B.get_layout Hget)))); first [reflexivity |destruct (R.is_materialized (R.observe st t) t); unfold R.observe; destruct (P.Ranks.observe _ t); reflexivity] end].
  all: try solve [match goal with Hw : B.R.set_value _ _ _ = (_,_) |- _ => exact (B.commit_contributions (@B.commit_footprint _ _ _ _ _ Hw)) end].
  all: try solve [unfold R.observe, R.materialize, R.reset_registered_cells; repeat match goal with |- context [match ?p with _ => _ end] => destruct p end; reflexivity].
Qed.
Lemma core_ready_snapshot tf before after owner : P.core_rule (R.cfg_control before) ->
  NoDup (B.active_owners (R.cfg_control before)) -> B.incoming_ready before owner -> ~ B.committing before owner ->
  B.step tf before after -> B.frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  destruct before as [st ctrl]; intros Hrule Hunique Hready Hnot Hstep.
  pose proof (proj1 Hready) as Hquiet.
  destruct ctrl; cbn [P.core_rule R.cfg_control] in Hrule; try contradiction.
  all: unfold B.step, R.next_config in Hstep; cbn [R.cfg_state R.cfg_control] in Hstep.
  all: try match goal with Hstep : context [match ?body with R.ConstraintSystem.Ret _ => _ | _ => _ end] |- _ => destruct body; cbn in Hrule; try contradiction end.
  all: try match goal with Hstep : context [match ?pending with [] => _ | _ => _ end] |- _ => destruct pending; cbn in Hrule; try contradiction; rewrite Hrule in Hstep end.
  all: B.split_program Hstep; cbn [R.cfg_state].
  all: try solve [apply B.snapshot_identity |apply B.snapshot_observe |apply B.snapshot_close].
  all: try solve [apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction]].
  all: try match goal with Hget : B.R.complete_get ?input _ _ = (_,_,_) |- _ =>
    eapply B.snapshot_compose; [|exact (B.snapshot_get [owner] Hget)];
      try solve [apply B.snapshot_observe |apply B.snapshot_identity |
        eapply B.snapshot_compose; [apply B.snapshot_observe |apply B.snapshot_enqueue]] end.
  all: try solve [eapply B.snapshot_compose; [apply B.snapshot_observe |]; eapply B.snapshot_compose; [apply B.snapshot_enqueue |apply B.snapshot_materialize]].
  all: try match goal with Hw : B.R.set_value ?input ?fr ?direct = (_,_) |- _ =>
    eapply B.snapshot_compose; [eapply B.snapshot_commit; [exact Hw |] |apply B.snapshot_requeue];
      intros x [<-|Hin] Heq; [apply Hnot; exists fr, direct, c; split; [reflexivity |exact Heq] |contradiction] end.
  all: try match goal with |- context [if ?b then _ else _] => destruct b;
    [apply B.snapshot_observe |eapply B.snapshot_compose; [apply B.snapshot_observe |apply B.snapshot_enqueue]] end.
Qed.

Lemma ready_other_current st ctrl k source owner :
  B.active_owners ctrl = source :: B.suspended_owners k -> B.drained_owners ctrl = B.drained_stack k ->
  NoDup (B.active_owners ctrl) -> B.incoming_ready (B.configuration st ctrl) owner -> owner <> source.
Proof. intros Hactive Hdrained Hunique Hready ->; eapply evaluating_not_ready; eauto. Qed.
Lemma reachable_unique tf roots c : P.reachable tf roots c -> NoDup (B.active_owners (R.cfg_control c)).
Proof. intro Hr; exact (@B.ordered_unique (R.ranking (R.cfg_state c)) _ (P.reachable_active_ordered Hr)). Qed.
Lemma next_ready_snapshot tf roots before after owner : P.reachable tf roots before -> B.incoming_ready before owner ->
  ~ B.committing before owner -> P.step tf before after -> B.frame_snapshot (R.cfg_state before) (R.cfg_state after) [owner].
Proof.
  intros Hr Hready Hnot Hstep; pose proof (reachable_unique Hr) as Hunique.
  pose proof (proj1 Hready) as Hquiet; apply P.step_view in Hstep; destruct Hstep.
  - eapply core_ready_snapshot; eauto.
  - eapply B.snapshot_compose; [|apply B.snapshot_materialize].
    apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction].
  - apply B.snapshot_observe.
  - eapply B.snapshot_compose; [apply P.publication_snapshot |apply B.snapshot_publish].
    intros x [<-|Hin]; [eapply (@ready_other_current st (R.RunDead fr direct [] k) k (R.frame_owner fr) owner); [reflexivity |reflexivity |exact Hunique |exact Hready] |contradiction].
  - eapply B.snapshot_compose; [eapply B.snapshot_side_write; [exact H |] |].
    + intros x [<-|Hin]; [eapply (@ready_other_current st (R.RunDead fr direct (target::rest) k) k (R.frame_owner fr) owner); [reflexivity |reflexivity |exact Hunique |exact Hready] |contradiction].
    + eapply B.snapshot_compose; [apply P.requeue_snapshot |apply P.continue_dead_snapshot].
  - apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction].
  - apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction].
  - apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction].
  - apply B.snapshot_static; try reflexivity; intros x [<-|Hin] Hqueued; [exfalso; exact (Hquiet Hqueued) |contradiction].
Qed.
Lemma finish_aggregate_quiet st fr target input next changed owner :
  R.write_side_contribution st fr target input = (next,changed) ->
  ~ In owner (R.queue (N.finish_write st next fr target changed)) ->
  B.eqv (R.aggregate (N.finish_write st next fr target changed) owner) (R.aggregate st owner).
Proof.
  intros Hw Hquiet; assert (Hagg : B.eqv (R.aggregate next owner) (R.aggregate st owner)).
  { destruct (V.eq_dec owner target) as [->|Hother].
    - destruct changed; [exfalso; apply Hquiet; unfold N.finish_write; apply B.insert_members; auto |exact (B.aggregate_write_unchanged Hw)].
    - rewrite (B.aggregate_write_other Hw Hother); apply B.eqv_refl. }
  unfold N.finish_write, N.requeue_source; destruct changed, N.cell_changed; exact Hagg.
Qed.
Lemma publication_aggregate_quiet targets st fr owner : ~ In owner (R.queue (N.publish targets st fr)) ->
  B.eqv (R.aggregate (N.publish targets st fr) owner) (R.aggregate st owner).
Proof.
  revert st; induction targets as [|target rest IH]; intros st Hquiet; [apply B.eqv_refl |].
  cbn -[R.write_side_contribution N.finish_write] in Hquiet |- *; destruct (R.write_side_contribution st fr target _) as [next changed] eqn:Hw.
  eapply B.eqv_trans; [apply IH; exact Hquiet |eapply finish_aggregate_quiet; [exact Hw |intro Hin; apply Hquiet, P.publish_keeps_queue; exact Hin]].
Qed.
Lemma next_ready_aggregate tf before after owner : NoDup (B.active_owners (R.cfg_control after)) ->
  P.step tf before after -> B.incoming_ready after owner ->
  B.eqv (R.aggregate (R.cfg_state after) owner) (R.aggregate (R.cfg_state before) owner).
Proof.
  intros Hunique Hstep Hready; apply P.step_view in Hstep; destruct Hstep; cbn [B.configuration R.cfg_state] in Hready, Hunique |- *.
  - unfold R.aggregate; rewrite (core_contributions H0 H); apply B.eqv_refl.
  - rewrite B.aggregate_materialize; apply B.eqv_refl.
  - rewrite B.aggregate_observe; apply B.eqv_refl.
  - apply publication_aggregate_quiet; exact (proj1 Hready).
  - assert (Hagg : B.eqv (R.aggregate next owner) (R.aggregate st owner)).
    { destruct changed; [|destruct (V.eq_dec owner target) as [->|Hother]; [exact (B.aggregate_write_unchanged H) |rewrite (B.aggregate_write_other H Hother); apply B.eqv_refl]].
      assert (Hother : owner <> target) by (eapply P.continued_ready_target; eauto).
      rewrite (B.aggregate_write_other H Hother); apply B.eqv_refl. }
    unfold R.continue_dead; destruct changed; [destruct (_ && _)%bool |]; unfold N.requeue_source; destruct N.cell_changed; exact Hagg.
  - apply B.eqv_refl.
  - apply B.eqv_refl.
  - apply B.eqv_refl.
  - apply B.eqv_refl.
Qed.

Lemma update_narrow owner phase old input : phase <> U.Widen -> D.leq input old = true ->
  snd (U.update false owner phase old input) = WN.narrow old input.
Proof. intros Hsafe Hbelow; destruct phase; cbn -[D.leq]; [rewrite Hbelow; reflexivity |rewrite Hbelow; reflexivity |contradiction]. Qed.
Lemma narrow_equivalent (owner : V.t) old old' input input' : D.leq input old = true -> D.leq input' old' = true ->
  B.eqv old old' -> B.eqv input input' -> B.eqv (WN.narrow old input) (WN.narrow old' input').
Proof.
  intros Hbelow Hbelow' Hold Hinput; pose proof (@UL.update_extensional false owner U.BoxN old old' input input' Hold Hinput) as H.
  rewrite (@update_narrow owner U.BoxN old input ltac:(discriminate) Hbelow),
    (@update_narrow owner U.BoxN old' input' ltac:(discriminate) Hbelow') in H; exact H.
Qed.
Lemma uncontrolled_value st fr direct next next_fr : S.mem (R.frame_owner fr) (R.controlled st) = false ->
  R.set_value st fr direct = (next,next_fr) ->
  B.eqv (R.sigma_value next (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))).
Proof.
  intros Hcontrolled Hw; unfold R.set_value in Hw; rewrite Hcontrolled in Hw.
  destruct (R.equivalent _ _) eqn:Heq; cbn -[R.equivalent] in Hw.
  - inversion Hw; subst; apply B.eqv_sym, B.eqv_bool; exact Heq.
  - inversion Hw; subst; unfold R.sigma_value; cbn; rewrite ML.lookup_update_same; apply B.eqv_refl.
Qed.
Lemma quiet_commit_fixed st fr direct next next_fr : Features.recompute_controlled = true -> R.frame_phase fr <> U.Widen ->
  R.set_value st fr direct = (next,next_fr) ->
  ~ In (R.frame_owner fr) (R.queue (R.requeue_changed_controlled_owner st next (R.frame_owner fr))) ->
  B.eqv (WN.narrow (R.sigma_value next (R.frame_owner fr)) (D.join direct (R.aggregate st (R.frame_owner fr))))
    (R.sigma_value next (R.frame_owner fr)).
Proof.
  intros Henabled Hsafe Hw Hquiet; pose proof (@B.commit_sound st fr direct next next_fr Hw) as Hsound.
  destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
  - pose proof (B.quiet_controlled_commit Henabled Hcontrolled Hquiet) as Hsame.
    pose proof (@B.quiet_commit_narrowing_fixed WN.narrow (fun phase => phase <> U.Widen) update_narrow WNL.narrow_lower WNL.narrow_upper
      st fr direct next next_fr Henabled Hsafe Hcontrolled Hw Hquiet) as Hfixed.
    assert (Hbelow : D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true) by (eapply DL.leq_trans; [exact Hsound |exact (proj1 Hsame)]).
    eapply B.eqv_trans; [eapply (@narrow_equivalent (R.frame_owner fr)); [exact Hsound |exact Hbelow |exact Hsame |apply B.eqv_refl] |].
    eapply B.eqv_trans; [exact Hfixed |apply B.eqv_sym; exact Hsame].
  - pose proof (@uncontrolled_value st fr direct next next_fr Hcontrolled Hw) as Hvalue.
    split; [apply WNL.narrow_upper; exact Hsound |eapply DL.leq_trans; [exact (proj1 Hvalue) |apply WNL.narrow_lower; exact Hsound]].
Qed.
Definition fixed_result tf st owner := exists result,
  Sem.rhs_observes (tf owner) result /\ B.quiet_reads st owner (O.observed_reads result) /\
  D.leq (D.join (O.observed_direct result) (R.aggregate st owner)) (R.sigma_value st owner) = true /\
  B.eqv (WN.narrow (R.sigma_value st owner) (D.join (O.observed_direct result) (R.aggregate st owner))) (R.sigma_value st owner).
Definition fixed_invariant tf c := forall owner, B.solved (R.cfg_state c) owner -> B.incoming_ready c owner -> fixed_result tf (R.cfg_state c) owner.
Lemma fixed_result_move tf before after owner : B.frame_snapshot before after [owner] ->
  B.eqv (R.aggregate after owner) (R.aggregate before owner) -> fixed_result tf before owner -> fixed_result tf after owner.
Proof.
  intros Hsnapshot Hagg [result [Htrace [Hreads [Hbound Hfixed]]]].
  assert (Hinput : B.eqv (D.join (O.observed_direct result) (R.aggregate after owner)) (D.join (O.observed_direct result) (R.aggregate before owner))) by (apply B.join_eqv; [apply B.eqv_refl |exact Hagg]).
  assert (Hnewbound : D.leq (D.join (O.observed_direct result) (R.aggregate after owner)) (R.sigma_value after owner) = true) by
    (rewrite (B.snapshot_values Hsnapshot (or_introl eq_refl)); eapply DL.leq_trans; [exact (proj1 Hinput) |exact Hbound]).
  exists result; split; [exact Htrace |split; [exact (B.snapshot_reads Hsnapshot (or_introl eq_refl) _ Hreads) |split; [exact Hnewbound |]]].
  eapply B.eqv_trans; [eapply (@narrow_equivalent owner); [exact Hnewbound |exact Hbound |rewrite (B.snapshot_values Hsnapshot (or_introl eq_refl)); apply B.eqv_refl |exact Hinput] |].
  rewrite (B.snapshot_values Hsnapshot (or_introl eq_refl)); exact Hfixed.
Qed.
Lemma ready_commit_shape tf roots st fr direct k after :
  P.reachable tf roots (B.configuration st (R.RunCommit fr direct k)) ->
  P.step tf (B.configuration st (R.RunCommit fr direct k)) after -> B.incoming_ready after (R.frame_owner fr) ->
  exists written next_fr, R.set_value st fr direct = (written,next_fr) /\
    after = B.configuration (R.requeue_changed_controlled_owner st written (R.frame_owner fr)) (R.RunDrain next_fr k).
Proof.
  intros Hr Hstep Hready; pose proof (reachable_unique (P.reachable_advance Hr Hstep)) as Hunique.
  pose proof (P.step_view Hstep) as Hview; inversion Hview; subst.
  - unfold B.step, R.next_config in H; cbn -[R.set_value] in H; destruct (R.set_value st fr direct) as [written next_fr] eqn:Hw.
    inversion H; subst; exists written, next_fr; split; reflexivity.
  - exfalso; eapply P.active_parent_not_ready; [exact Hunique |exact Hready].
  - exfalso; eapply (@evaluating_not_ready _ (R.frame_owner fr) k (R.cfg_control (N.retry_current tf st fr k))); [reflexivity |reflexivity |exact Hunique |exact Hready].
Qed.
Lemma committing_fixed_result tf roots before after owner : Features.recompute_controlled = true -> monotonic_system tf ->
  P.reachable tf roots before -> P.step tf before after -> B.committing before owner -> B.incoming_ready after owner ->
  fixed_result tf (R.cfg_state after) owner.
Proof.
  intros Henabled Hmono Hr Hstep [fr [direct [k [Hctrl ->]]]] Hready.
  destruct before as [st ctrl]; cbn [R.cfg_control] in Hctrl; subst ctrl.
  destruct (@ready_commit_shape tf roots st fr direct k after Hr Hstep Hready) as [written [next_fr [Hw ->]]].
  pose proof (P.invariant_observing (P.reachable_semantic_invariant Hr)) as Hobs; destruct Hobs as [[[cur Hledger] Hstack]].
  pose proof (proj1 (reachable_no_fallback Hr Hmono)) as Hsafe.
  pose proof (@B.commit_footprint st fr direct written next_fr Hw) as Hview.
  set (final := R.requeue_changed_controlled_owner st written (R.frame_owner fr)).
  exists {| O.observed_direct := direct; O.observed_reads := P.reads cur; O.observed_sides := P.sides cur; O.observed_spawns := P.spawns cur |}.
  split; [exact (B.prefix_return (P.prefix cur)) |split].
  - eapply B.quiet_layout with (before := written); [reflexivity |reflexivity |apply B.requeue_keeps_queue |exact (@B.quiet_set st fr direct written next_fr Hw (R.frame_owner fr) (P.reads cur) (P.watches cur))].
  - split.
    + unfold final, R.aggregate; cbn [B.configuration R.cfg_state O.observed_direct R.requeue_changed_controlled_owner R.with_queue R.sigma R.contributions]; rewrite (B.commit_contributions Hview); exact (@B.commit_sound st fr direct written next_fr Hw).
    + unfold final, R.aggregate; cbn [B.configuration R.cfg_state O.observed_direct R.requeue_changed_controlled_owner R.with_queue R.sigma R.contributions]; rewrite (B.commit_contributions Hview); exact (@quiet_commit_fixed st fr direct written next_fr Henabled Hsafe Hw (proj1 Hready)).
Qed.

Lemma committing_dec c owner : {B.committing c owner} + {~ B.committing c owner}.
Proof.
  destruct (R.cfg_control c) as [|seeds|seeds|child k|fr body k|fr direct pending k|fr direct k|fr k|k] eqn:Hctrl.
  all: try solve [right; intros [frame [value [rest [Hbefore Howner]]]]; rewrite Hctrl in Hbefore; discriminate].
  destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hother].
  - left; exists fr, direct, k; auto.
  - right; intros [frame [value [rest [Hbefore Howner]]]]; rewrite Hctrl in Hbefore; inversion Hbefore; subst; contradiction.
Qed.
Lemma drained_framed ctrl owner : In owner (B.drained_owners ctrl) -> In owner (B.framed_owners ctrl).
Proof. destruct ctrl; cbn [B.drained_owners B.framed_owners B.active_owners]; cbn; intuition eauto using B.drained_parent. Qed.
Lemma ready_solved_before tf before after owner : B.frames_live before -> B.waiting_control before ->
  ~ B.committing before owner -> P.step tf before after -> B.incoming_ready after owner ->
  B.solved (R.cfg_state after) owner -> B.solved (R.cfg_state before) owner.
Proof.
  intros Hframes Hwaiting Hnot Hstep [Hquiet [Hidle|Hdrained]] Hsolved.
  - destruct (@P.next_solved_origin tf before after Hframes Hwaiting Hstep owner Hsolved) as [Hold|[Hq|Ha]]; auto; contradiction.
  - destruct (@P.next_drained_origin tf before after Hstep owner Hdrained) as [Hold|Hcommit]; [|contradiction].
    unfold B.frames_live in Hframes; rewrite Forall_forall in Hframes; apply Hframes; apply drained_framed; exact Hold.
Qed.
Theorem next_fixed_invariant tf roots before after : Features.recompute_controlled = true -> monotonic_system tf ->
  P.reachable tf roots before -> fixed_invariant tf before -> P.step tf before after -> fixed_invariant tf after.
Proof.
  intros Henabled Hmono Hr Hfixed Hstep owner Hsolved Hready.
  destruct (committing_dec before owner) as [Hcommit|Hnot]; [eapply committing_fixed_result; eauto |].
  pose proof (P.reachable_semantic_invariant Hr) as Hsem.
  assert (Hold : B.solved (R.cfg_state before) owner) by (eapply ready_solved_before; eauto using P.invariant_frames, P.invariant_waiting).
  pose proof (reachable_unique (P.reachable_advance Hr Hstep)) as Hunique.
  destruct (@P.next_incoming_origin tf before after Hunique Hstep owner Hready) as [Hbefore|Hcommit]; [|contradiction].
  eapply fixed_result_move; [eapply next_ready_snapshot; eauto |eapply next_ready_aggregate; eauto |apply Hfixed; assumption].
Qed.
Theorem reachable_fixed_invariant tf roots c : Features.recompute_controlled = true -> monotonic_system tf ->
  P.reachable tf roots c -> fixed_invariant tf c.
Proof.
  intros Henabled Hmono Hpath.
  assert (Hinitial : fixed_invariant tf (R.initial_config roots)).
  { intros owner [value Hlookup] _; change (M.lookup (M.empty D.t) owner = Some value) in Hlookup; rewrite ML.lookup_empty in Hlookup; discriminate. }
  assert (Hpreserve : forall before after, P.steps tf before after -> P.reachable tf roots before ->
    fixed_invariant tf before -> fixed_invariant tf after).
  { intros before after Hsteps; induction Hsteps as [refl_cfg|before next after Hnext Htail IH]; intros Hr Hfixed; [exact Hfixed |].
    apply IH; [eapply P.reachable_advance; eauto |eapply next_fixed_invariant; eauto]. }
  eapply Hpreserve; [exact Hpath |constructor |exact Hinitial].
Qed.
Definition narrowing_fixed := narrowing_fixed_with WN.narrow
  (fun final owner direct => D.join direct (R.aggregate final owner)).
Theorem successful_run_fixed : Features.recompute_controlled = true ->
  forall fuel tf roots final, monotonic_system tf ->
  N.solve_fuel fuel tf roots = Some final -> narrowing_fixed tf final.
Proof.
  intros Henabled fuel tf roots final Hmono Hrun; destruct (@P.successful_path fuel tf roots final Hrun) as [Hpath Hqueue].
  pose proof (@reachable_fixed_invariant tf roots (B.terminal final) Henabled Hmono Hpath) as Hfixed.
  intros owner Hsolved; assert (Hready : B.incoming_ready (B.terminal final) owner).
  { split; [change (~ In owner (R.queue final)); rewrite Hqueue; tauto |left; cbn [B.terminal R.cfg_control B.active_owners]; tauto]. }
  destruct (Hfixed owner Hsolved Hready) as [result [Htrace [Hreads [Hbound Hnarrow]]]].
  assert (Hwatched : B.watched_reads final owner (O.observed_reads result)) by (apply Hreads; exact (proj1 Hready)).
  assert (Hat : Sem.observes_at (R.sigma_value final) (tf owner) result).
  { split; [exact Htrace |intros target value Hin; symmetry; apply B.read_value; exact (proj1 (Hwatched target value Hin))]. }
  split.
  - exists (O.observed_direct result), (O.observed_reads result), (O.observed_sides result).
    apply B.observation_replay; [exact Htrace |intros target value Hin; exact (proj1 (Hwatched target value Hin))].
  - intros direct reads sides Hreplay; destruct (B.replay_observation Hreplay) as [other [Hother [Hd [Hrs Hss]]]].
    assert (Heq : result = other) by (eapply B.observation_unique; eauto); subst other.
    cbn; rewrite <- Hd; exact Hnarrow.
Qed.
Theorem total_correct_and_fixed tf roots : Features.recompute_controlled = true ->
  Sem.finite_system tf roots -> monotonic_system tf ->
  exists fuel final, N.solve_fuel fuel tf roots = Some final /\ correct_final_state tf roots final /\ narrowing_fixed tf final.
Proof.
  intros Henabled Hfinite Hmono; destruct (P.sufficient_fuel Hfinite) as [fuel [final Hrun]].
  exists fuel, final; split; [exact Hrun |split; [exact (@P.successful_run_correct fuel tf roots final Hrun) |eapply successful_run_fixed; eauto]].
Qed.
Definition semantic_termination := P.semantic_termination.
Definition sufficient_fuel := P.sufficient_fuel.
Definition successful_run_correct := P.successful_run_correct.
Definition total_correct := P.total_correct.

(** Concrete-instance precision aliases. *)
Theorem successful_run_fixedpoint : Features.recompute_controlled = true ->
  forall fuel tf roots final, N.solve_fuel fuel tf roots = Some final ->
  monotonic_system tf -> narrowing_fixed tf final.
Proof. intros Hon fuel tf roots final Hrun Hmono; eapply successful_run_fixed; eauto. Qed.
Definition public_reachable_no_fallback := reachable_no_fallback.
Module E.
  Definition reachable_no_fallback := public_reachable_no_fallback.
End E.

End FixedPoint.
