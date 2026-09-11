From Stdlib Require Import List Bool Arith.PeanoNat Lia.
From TcSolvers Require Import common.Assumptions
  solvers.slr.narrowing_fixed_point.Base
  solvers.slr.narrowing_fixed_point.proofs.BaseCorrectness.
Import ListNotations.
Set Implicit Arguments.

Module PreCommit.
(** Precommit scheduling, deferred publication, and retry transitions. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Base := BaseCorrectness.FirstDiscovery V D U S M Features DL UL SL ML.
  Module R := Base.R.

  Definition pending_above (st : R.state) (owner : V.t) :=
    if S.mem owner (R.controlled st) then
      match R.queue_pop (R.queue st) with
      | Some (target, rest) =>
          if R.rank_lt st owner target then Some (target, rest) else None
      | None => None
      end
    else None.

  Definition suspend_commit (tf : R.ConstraintSystem.system)
    (st : R.state) (fr : R.frame) (k : R.continuation)
    (target : V.t) (rest : R.work_queue) : R.config :=
    {| R.cfg_state := R.with_queue st rest;
       R.cfg_control := R.StartEpisode target
         (R.KAfterSide
           (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr))
           (tf (R.frame_owner fr)) k) |}.

  Definition next_config (tf : R.ConstraintSystem.system) (c : R.config) :=
    match R.cfg_control c with
    | R.RunCommit fr direct k =>
        match pending_above (R.cfg_state c) (R.frame_owner fr) with
        | Some (target, rest) =>
            Some (suspend_commit tf (R.cfg_state c) fr k target rest)
        | None => R.next_config tf c
        end
    | _ => R.next_config tf c
    end.

  Lemma pending_above_spec st owner target rest :
    pending_above st owner = Some (target, rest) ->
    S.mem owner (R.controlled st) = true /\
    R.queue_pop (R.queue st) = Some (target, rest) /\
    R.rank_lt st owner target = true.
  Proof.
    unfold pending_above.
    destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled; [|discriminate].
    destruct (R.queue_pop (R.queue st)) as [[x tail]|] eqn:Hpop; [|discriminate].
    destruct (R.rank_lt st owner x) eqn:Hrank; [|discriminate].
    intro H. inversion H; subst. auto.
  Qed.

  Lemma suspend_scopes tf st fr direct k target rest :
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    Base.ScopeBounds.scopes_bounded (suspend_commit tf st fr k target rest).
  Proof.
    intros [Hreset [Hframe Hk]]. split.
    - now apply Base.ScopeBounds.reset_sources_bounded_with_queue.
    - split.
      + unfold Base.ScopeBounds.frame_scope_bounded,
          Base.ScopeBounds.source_not_below_scope. now left.
      + eapply Base.ScopeBounds.continuation_scopes_bounded_extended;
          [apply Base.rank_extends_with_queue |exact Hk].
  Qed.

  Lemma step_scopes tf before after :
    Base.ScopeBounds.scopes_bounded before ->
    next_config tf before = Some after -> Base.ScopeBounds.scopes_bounded after.
  Proof.
    destruct before as [st control]. intros Hbounded Hstep.
    destruct control; cbn -[R.next_config pending_above suspend_commit] in Hstep.
    all: try solve [eapply Base.ScopeBounds.next_config_scopes_bounded; eauto].
    destruct (pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hpending.
    - inversion Hstep; subst. eapply suspend_scopes; exact Hbounded.
    - eapply Base.ScopeBounds.next_config_scopes_bounded; eauto.
  Qed.

  Fixpoint publish_accumulated (targets : list V.t) (st : R.state) (fr : R.frame) :=
    match targets with
    | [] => st
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          | Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        publish_accumulated rest (if changed then R.enqueue next target else next) fr
    end.

  Definition next_batched (tf : R.ConstraintSystem.system) (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.RunRhs fr (R.ConstraintSystem.Side target raw body) k =>
        let '(next_fr, _) := R.record_side_input fr target raw in
        Some {| R.cfg_state := R.observe st target;
                R.cfg_control := R.RunRhs next_fr body k |}
    | R.RunDead fr direct [] k =>
        let next := publish_accumulated (S.elements (R.frame_current_targets fr)) st fr in
        Some {| R.cfg_state := R.publish_targets next fr;
                R.cfg_control := R.RunCommit fr direct k |}
    | _ => next_config tf c
    end.

  Lemma source_credit_queue support st source queue :
    Base.Credits.source_side_credit support (R.with_queue st queue) source =
    Base.Credits.source_side_credit support st source.
  Proof. induction support; cbn; [reflexivity |now rewrite IHsupport]. Qed.

  Lemma source_credit_enqueue support st source target :
    Base.Credits.source_side_credit support (R.enqueue st target) source =
    Base.Credits.source_side_credit support st source.
  Proof. apply source_credit_queue. Qed.

  Lemma publish_credit_nonincreasing targets support st fr :
    Base.Credits.source_side_credit support (publish_accumulated targets st fr)
      (R.frame_owner fr) <= Base.Credits.source_side_credit support st (R.frame_owner fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution]; [reflexivity |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end)) as [next changed] eqn:Hwrite.
    eapply Nat.le_trans; [apply IH |].
    pose proof (Base.Credits.source_side_credit_write_nonincreasing support Hwrite) as Hcredit.
    destruct changed; [rewrite source_credit_enqueue |]; exact Hcredit.
  Qed.

  Fixpoint publication_changes targets st fr : Prop :=
    match targets with
    | [] => False
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          | Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        changed = true \/
        publication_changes rest (if changed then R.enqueue next target else next) fr
    end.

  Lemma changed_publication_consumes_credit targets support st fr :
    List.incl targets support -> publication_changes targets st fr ->
    Base.Credits.source_side_credit support (publish_accumulated targets st fr)
      (R.frame_owner fr) < Base.Credits.source_side_credit support st (R.frame_owner fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hin Hchange;
      cbn -[R.write_side_contribution] in Hchange |- *; [contradiction |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end)) as [next changed] eqn:Hwrite.
    destruct Hchange as [-> |Hrest].
    - eapply Nat.le_lt_trans; [apply publish_credit_nonincreasing |].
      rewrite source_credit_enqueue.
      eapply Base.Credits.source_side_credit_write_decreases;
        [apply Hin; now left |exact Hwrite].
    - eapply Nat.lt_le_trans.
      + apply IH; [intros x H; apply Hin; now right |exact Hrest].
      + pose proof (Base.Credits.source_side_credit_write_nonincreasing support Hwrite) as Hcredit.
        destruct changed; [rewrite source_credit_enqueue |]; exact Hcredit.
  Qed.

  Lemma publication_extends_ranks targets st fr :
    Base.rank_extends st (publish_accumulated targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st; cbn -[R.write_side_contribution].
    - apply Base.rank_extends_refl.
    - destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end)) as [next changed] eqn:Hwrite.
      eapply Base.rank_extends_trans; [|apply IH].
      eapply Base.rank_extends_trans;
        [eapply Base.rank_extends_write_side_contribution; exact Hwrite |].
      destruct changed; [apply Base.rank_extends_enqueue |apply Base.rank_extends_refl].
  Qed.

  Lemma publication_scopes targets st fr :
    Base.ScopeBounds.reset_sources_bounded st ->
    Base.ScopeBounds.frame_scope_bounded st fr ->
    Base.ScopeBounds.reset_sources_bounded (publish_accumulated targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hreset Hframe; cbn -[R.write_side_contribution];
      [exact Hreset |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end)) as [next changed] eqn:Hwrite.
    destruct (Base.ScopeBounds.write_side_scopes Hreset Hframe Hwrite) as [Hreset' Hframe'].
    apply IH.
    - destruct changed; [now apply Base.ScopeBounds.reset_sources_bounded_enqueue |exact Hreset'].
    - eapply Base.ScopeBounds.frame_scope_bounded_extended; [|exact Hframe'].
      destruct changed; [apply Base.rank_extends_enqueue |apply Base.rank_extends_refl].
  Qed.

  Lemma publication_other_row targets st fr observed :
    ~ List.In observed targets ->
    R.lookup_map (R.contributions (publish_accumulated targets st fr)) observed =
    R.lookup_map (R.contributions st) observed.
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Houtside;
      cbn -[R.write_side_contribution]; [reflexivity |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    rewrite IH by (intro H; apply Houtside; now right).
    destruct changed; change (R.lookup_map (R.contributions next) observed =
      R.lookup_map (R.contributions st) observed);
      eapply Base.write_side_contribution_other; [exact Hwrite | |exact Hwrite |];
      intro Heq; apply Houtside; now left.
  Qed.

  Lemma publication_covers_input targets st fr target input :
    List.In target targets -> M.lookup (R.frame_local_side fr) target = Some input ->
    exists contribution,
      M.lookup (R.lookup_map (R.contributions (publish_accumulated targets st fr)) target)
        (R.frame_owner fr) = Some contribution /\ D.leq input contribution = true.
  Proof.
    revert st target input. induction targets as [|head rest IH];
      intros st target input Hin Hinput; [contradiction |].
    cbn -[R.write_side_contribution].
    destruct (R.write_side_contribution st fr head
      (match M.lookup (R.frame_local_side fr) head with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    destruct (List.in_dec V.eq_dec target rest) as [Hrest|Houtside].
    - eapply IH; eauto.
    - destruct Hin as [->|Hin]; [|contradiction].
      rewrite publication_other_row by exact Houtside.
      rewrite Hinput in Hwrite.
      destruct (Base.write_side_contribution_records_input Hwrite)
        as [contribution [Hlookup Hle]].
      exists contribution. split; [destruct changed; exact Hlookup |exact Hle].
  Qed.

  Lemma deferred_side_scopes st fr target raw body k :
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := st;
         R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Side target raw body) k |} ->
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := R.observe st target;
         R.cfg_control := R.RunRhs
           (R.with_frame_side fr target (R.accumulated_side_input fr target raw)) body k |}.
  Proof.
    intros [Hreset [Hframe Hk]]. split.
    - now apply Base.ScopeBounds.reset_sources_bounded_observe.
    - split.
      + apply Base.ScopeBounds.frame_scope_side.
        eapply Base.ScopeBounds.frame_scope_bounded_extended;
          [eapply Base.rank_extends_observe; reflexivity |exact Hframe].
      + eapply Base.ScopeBounds.continuation_scopes_bounded_extended;
          [eapply Base.rank_extends_observe; reflexivity |exact Hk].
  Qed.

  Lemma flush_scopes st fr direct k :
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} ->
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := R.publish_targets
           (publish_accumulated (S.elements (R.frame_current_targets fr)) st fr) fr;
         R.cfg_control := R.RunCommit fr direct k |}.
  Proof.
    intros [Hreset [Hframe Hk]]. split.
    - apply Base.ScopeBounds.reset_sources_bounded_publish_targets.
      now apply publication_scopes.
    - apply Base.ScopeBounds.control_scopes_bounded_extended with st;
        [|split; assumption].
      eapply Base.rank_extends_trans; [apply publication_extends_ranks |].
      apply Base.rank_extends_same_ranking. reflexivity.
  Qed.

  Lemma batched_step_scopes tf before after :
    Base.ScopeBounds.scopes_bounded before ->
    next_batched tf before = Some after -> Base.ScopeBounds.scopes_bounded after.
  Proof.
    destruct before as [st control]. intros Hbounded Hstep.
    destruct control as [|roots|remaining|owner k|fr body k|fr direct pending k|
      fr direct k|fr k|k]; cbn -[next_config publish_accumulated R.publish_targets] in Hstep.
    all: try solve [eapply step_scopes; eauto].
    - destruct body; cbn -[next_config R.observe R.record_side_input] in Hstep.
      all: try solve [eapply step_scopes; eauto].
      unfold R.record_side_input in Hstep.
      inversion Hstep; subst. eapply deferred_side_scopes; exact Hbounded.
    - destruct pending; cbn -[next_config publish_accumulated R.publish_targets] in Hstep.
      + inversion Hstep; subst. now apply flush_scopes.
      + eapply step_scopes; eauto.
  Qed.

  Definition clear_owner (st : R.state) (owner : V.t) :=
    R.with_queue st
      (List.filter (fun x => if V.eq_dec x owner then false else true) (R.queue st)).

  Definition retry_current (tf : R.ConstraintSystem.system)
    (st : R.state) (fr : R.frame) (k : R.continuation) : R.config :=
    let current := clear_owner st (R.frame_owner fr) in
    {| R.cfg_state := current;
       R.cfg_control := R.RunRhs
         (R.fresh_frame current (R.frame_owner fr) (R.frame_phase fr))
         (tf (R.frame_owner fr)) k |}.

  Definition next_fresh (tf : R.ConstraintSystem.system) (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.StartEpisode owner k =>
        next_batched tf {| R.cfg_state := clear_owner st owner;
                           R.cfg_control := R.StartEpisode owner k |}
    | R.Return (R.KAfterSide fr body k) =>
        next_batched tf {| R.cfg_state := clear_owner st (R.frame_owner fr);
                           R.cfg_control := R.Return (R.KAfterSide fr body k) |}
    | R.RunCommit fr direct k =>
        match pending_above st (R.frame_owner fr) with
        | Some (target, rest) => Some (suspend_commit tf st fr k target rest)
        | None =>
            if R.queue_contains (R.frame_owner fr) (R.queue st)
            then Some (retry_current tf st fr k)
            else next_batched tf c
        end
    | _ => next_batched tf c
    end.

  Lemma clear_owner_members st owner x :
    List.In x (R.queue (clear_owner st owner)) <->
    List.In x (R.queue st) /\ x <> owner.
  Proof.
    unfold clear_owner. cbn. rewrite List.filter_In.
    destruct (V.eq_dec x owner); split; intros [Hin H];
      try discriminate; try contradiction; auto.
  Qed.

  Lemma clear_owner_not_queued st owner : ~ Base.queued (clear_owner st owner) owner.
  Proof. intro H. apply clear_owner_members in H. exact (proj2 H eq_refl). Qed.

  Lemma clear_other_guarded_reads st owner reader reads :
    reader <> owner -> Base.guarded_reads st reader reads ->
    Base.guarded_reads (clear_owner st owner) reader reads.
  Proof.
    intros Hother Hreads target value Hin.
    destruct (Hreads target value Hin) as [Hsolved [Hreader Hvalue]].
    assert (Hqueued : Base.queued st reader -> Base.queued (clear_owner st owner) reader).
    { intro H. apply clear_owner_members. now split. }
    split; [exact Hsolved |]. split;
      [destruct Hreader as [H|H]|destruct Hvalue as [H|H]]; auto.
  Qed.

  Lemma fresh_commit_ready tf st fr direct k after next_fr next_k :
    next_fresh tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
      Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
    pending_above st (R.frame_owner fr) = None /\ ~ Base.queued st (R.frame_owner fr).
  Proof.
    cbn -[next_batched pending_above suspend_commit retry_current].
    destruct (pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hpending.
    - discriminate.
    - destruct (R.queue_contains (R.frame_owner fr) (R.queue st)) eqn:Hself;
        [discriminate |].
      intro H. split; [reflexivity |]. now apply Base.queue_contains_false in Hself.
  Qed.

  Lemma queue_view_scopes st queue control :
    Base.ScopeBounds.scopes_bounded {| R.cfg_state := st; R.cfg_control := control |} ->
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := R.with_queue st queue; R.cfg_control := control |}.
  Proof.
    intros [Hreset Hcontrol]. split.
    - now apply Base.ScopeBounds.reset_sources_bounded_with_queue.
    - eapply Base.ScopeBounds.control_scopes_bounded_extended;
        [apply Base.rank_extends_with_queue |exact Hcontrol].
  Qed.

  Lemma retry_scopes tf st fr direct k :
    Base.ScopeBounds.scopes_bounded
      {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    Base.ScopeBounds.scopes_bounded (retry_current tf st fr k).
  Proof.
    intros [Hreset [Hframe Hk]]. split.
    - now apply Base.ScopeBounds.reset_sources_bounded_with_queue.
    - split; [apply Base.ScopeBounds.frame_scope_fresh |].
      eapply Base.ScopeBounds.continuation_scopes_bounded_extended;
        [apply Base.rank_extends_with_queue |exact Hk].
  Qed.

  Lemma fresh_step_scopes tf before after :
    Base.ScopeBounds.scopes_bounded before ->
    next_fresh tf before = Some after -> Base.ScopeBounds.scopes_bounded after.
  Proof.
    destruct before as [st control]. intros Hbounded Hstep.
    destruct control as [|roots|remaining|owner k|fr body k|fr direct pending k|
      fr direct k|fr k|k]; cbn -[next_batched pending_above suspend_commit retry_current] in Hstep.
    all: try solve [eapply batched_step_scopes; eauto].
    - eapply batched_step_scopes; [apply queue_view_scopes; exact Hbounded |exact Hstep].
    - destruct (pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hpending.
      + inversion Hstep; subst. eapply suspend_scopes; exact Hbounded.
      + destruct (R.queue_contains (R.frame_owner fr) (R.queue st)).
        * inversion Hstep; subst. eapply retry_scopes; exact Hbounded.
        * eapply batched_step_scopes; eauto.
    - destruct k; cbn -[next_batched] in Hstep.
      all: try solve [eapply batched_step_scopes; eauto].
      eapply batched_step_scopes; [apply queue_view_scopes; exact Hbounded |exact Hstep].
  Qed.

End Make.
End PreCommit.

Module ReadHistory.
(** Read history for the fresh-retry machine.  Unlike the original correctness
    invariant, this does not assert that unfinished effects are published. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module P := PreCommit.Make V D U S M Features DL UL SL ML.
  Module B := P.Base.
  Module R := P.R.
  Module T := B.Termination.

  Definition evaluation tf st owner current : Prop :=
    exists reads effects,
      B.rhs_context (tf owner) current reads effects /\
      B.guarded_reads st owner reads.

  Definition completed tf st owner direct : Prop :=
    exists reads effects, B.rhs_trace (tf owner) direct reads effects /\
      B.guarded_reads st owner reads.

  Fixpoint continuation tf st k : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr target next rest =>
        evaluation tf st (R.frame_owner fr) (R.ConstraintSystem.Get target next) /\
        continuation tf st rest
    | R.KAfterSide fr next rest =>
        next = tf (R.frame_owner fr) /\ continuation tf st rest
    | R.KAfterSpawn fr next rest =>
        evaluation tf st (R.frame_owner fr) next /\ continuation tf st rest
    | R.KDead fr direct _ rest =>
        completed tf st (R.frame_owner fr) direct /\ continuation tf st rest
    | R.KDrain _ rest => continuation tf st rest
    end.

  Definition history tf st control : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode _ k | R.RunDrain _ k | R.Return k => continuation tf st k
    | R.RunRhs fr body k =>
        evaluation tf st (R.frame_owner fr) body /\ continuation tf st k
    | R.RunDead fr direct _ k | R.RunCommit fr direct k =>
        completed tf st (R.frame_owner fr) direct /\ continuation tf st k
    end.

  Definition carries_reads before after := forall owner reads,
    B.guarded_reads before owner reads -> B.guarded_reads after owner reads.

  Lemma carries_same before after : B.same_read_view before after ->
    carries_reads before after.
  Proof. intros H owner reads Hr. eapply B.guarded_reads_same_view; eauto. Qed.

  Lemma carries_trans first middle last :
    carries_reads first middle -> carries_reads middle last -> carries_reads first last.
  Proof. intros H1 H2 owner reads H. apply H2, H1, H. Qed.

  Lemma evaluation_carries tf before after owner body :
    (forall reads, B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
    evaluation tf before owner body -> evaluation tf after owner body.
  Proof. intros H [reads [effects [Hcontext Hreads]]]. exists reads, effects. auto. Qed.

  Lemma completed_carries tf before after owner direct :
    (forall reads, B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
    completed tf before owner direct -> completed tf after owner direct.
  Proof. intros H [reads [effects [Htrace Hreads]]]. exists reads, effects. auto. Qed.

  Lemma continuation_carries tf before after k : carries_reads before after ->
    continuation tf before k -> continuation tf after k.
  Proof.
    intros H. induction k; cbn; intro Hk; try exact I; try (now apply IHk).
    all: destruct Hk as [Hhead Htail]; split; try (now apply IHk).
    all: try exact Hhead.
    all: first [eapply evaluation_carries with (before := before)
      |eapply completed_carries with (before := before)];
      [exact (H (R.frame_owner f)) |exact Hhead].
  Qed.

  Lemma initial_evaluation tf st owner : evaluation tf st owner (tf owner).
  Proof.
    exists [], []. split; [apply B.initial_rhs_context |].
    intros target value H. contradiction.
  Qed.

  Lemma evaluation_ret tf st owner direct :
    evaluation tf st owner (R.ConstraintSystem.Ret direct) -> completed tf st owner direct.
  Proof.
    intros [reads [effects [Hcontext Hreads]]]. exists reads, effects. split; [|exact Hreads].
    specialize (Hcontext direct [] [] (B.TraceRet direct)).
    now rewrite !List.app_nil_r in Hcontext.
  Qed.

  Lemma evaluation_side tf st owner target value next :
    evaluation tf st owner (R.ConstraintSystem.Side target value next) ->
    evaluation tf st owner next.
  Proof.
    intros [reads [effects [Hcontext Hreads]]].
    exists reads, (effects ++ [(target,value)]). split; [|exact Hreads].
    eapply B.rhs_context_side; exact Hcontext.
  Qed.

  Lemma evaluation_spawn tf st owner target next :
    evaluation tf st owner (R.ConstraintSystem.Spawn target next) -> evaluation tf st owner next.
  Proof.
    intros [reads [effects [Hcontext Hreads]]]. exists reads, effects. split; [|exact Hreads].
    eapply B.rhs_context_spawn; exact Hcontext.
  Qed.

  Lemma carries_materialize st target : carries_reads st (R.materialize st target).
  Proof. intros owner reads H. now apply B.guarded_reads_materialize. Qed.

  Lemma carries_enqueue st target : carries_reads st (R.enqueue st target).
  Proof. intros owner reads H. now apply B.guarded_reads_enqueue. Qed.

  Lemma carries_observe st target : carries_reads st (R.observe st target).
  Proof. apply carries_same, B.same_read_view_observe. Qed.

  Lemma carries_get st fr target after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) -> carries_reads st after.
  Proof.
    intro Hget. unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in Hget.
    fold B.add_reader in Hget. inversion Hget; subst after next_fr value.
    intros owner reads H. apply B.guarded_reads_materialize, B.guarded_reads_add_reader.
    subst base. destruct (R.rank_lt st (R.frame_owner fr) target); [exact H |].
    eapply B.guarded_reads_same_view;
      [exact (proj1 (B.promote_controlled_same_solver_view st target)) |exact H].
  Qed.

  Lemma get_owner st fr target after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) ->
    R.frame_owner next_fr = R.frame_owner fr.
  Proof.
    unfold R.complete_get. destruct (R.rank_lt st (R.frame_owner fr) target);
      intro H; inversion H; reflexivity.
  Qed.

  Lemma get_new_read st fr target after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) ->
    B.guarded_reads after (R.frame_owner fr) [(target,value)].
  Proof.
    intro H. unfold R.complete_get in H.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in H.
    fold B.add_reader in H. inversion H; subst after next_fr value.
    intros observed seen [Heq|Hnil]; [inversion Heq; subst |contradiction].
    split; [apply B.materialize_solved_correctness |].
    split; left; [apply B.add_reader_registered_after_materialize |reflexivity].
  Qed.

  Lemma evaluation_get tf st fr target next after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) ->
    evaluation tf st (R.frame_owner fr) (R.ConstraintSystem.Get target next) ->
    evaluation tf after (R.frame_owner next_fr) (next value).
  Proof.
    intros Hget [reads [effects [Hcontext Hreads]]]. rewrite (get_owner Hget).
    exists (reads ++ [(target,value)]), effects. split.
    - eapply B.rhs_context_get; exact Hcontext.
    - intros observed seen Hin. apply List.in_app_or in Hin. destruct Hin as [Hin|Hin].
      + exact (carries_get Hget Hreads observed seen Hin).
      + eapply (get_new_read Hget); exact Hin.
  Qed.

  Lemma publication_carries targets st fr :
    carries_reads st (P.publish_accumulated targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st;
      cbn -[R.write_side_contribution]; [intros owner reads H; exact H |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    eapply carries_trans; [|apply IH].
    eapply carries_trans; [apply carries_same; eapply B.write_side_contribution_same_read_view; exact Hwrite |].
    destruct changed; [apply carries_enqueue |intros owner reads H; exact H].
  Qed.

  Lemma lt_extended before after x y : B.rank_extends before after ->
    R.rank_lt before x y = true -> R.rank_lt after x y = true.
  Proof.
    intros Hext Hlt. unfold R.rank_lt, R.ranking_lt in *.
    destruct (R.Ranking.lookup (R.ranking before) x) as [rx|] eqn:Hx;
      [|discriminate].
    destruct (R.Ranking.lookup (R.ranking before) y) as [ry|] eqn:Hy;
      [|discriminate].
    rewrite (Hext _ _ Hx), (Hext _ _ Hy). exact Hlt.
  Qed.

  Lemma below_extended before after upper k : B.rank_extends before after ->
    T.continuation_below before upper k -> T.continuation_below after upper k.
  Proof.
    intro Hext. revert upper. induction k; cbn; intros upper H; try exact I.
    all: destruct H as [Hlt Hk]; split; [eapply lt_extended; eauto |now apply IHk].
  Qed.

  Lemma ordered_extended before after control : B.rank_extends before after ->
    T.control_ordered before control -> T.control_ordered after control.
  Proof.
    intros Hext. destruct control; cbn; try (eapply below_extended; exact Hext).
    all: try (intro H; exact I).
    destruct c; cbn; try (intro H; exact I); eapply below_extended; exact Hext.
  Qed.

  Lemma continuation_other tf before after upper k :
    T.continuation_below before upper k ->
    (forall owner reads, R.rank_lt before owner upper = true ->
      B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
    continuation tf before k -> continuation tf after k.
  Proof.
    revert upper. induction k; cbn; intros upper Hbelow Hcarry Hhistory; try exact I.
    all: destruct Hbelow as [Hlt Hbelow].
    all: try (destruct Hhistory as [Hhead Htail]; split).
    all: try solve [eapply evaluation_carries; [intros; eapply Hcarry; eauto |exact Hhead]
      |eapply completed_carries; [intros; eapply Hcarry; eauto |exact Hhead]
      |exact Hhead].
    all: eapply IHk; [exact Hbelow | |eassumption].
    all: intros owner reads Howner Hreads; apply Hcarry; [|exact Hreads];
      eapply T.rank_lt_trans_true; eauto.
  Qed.

  Lemma continuation_clear tf st owner k : T.continuation_below st owner k ->
    continuation tf st k -> continuation tf (P.clear_owner st owner) k.
  Proof.
    intro Hbelow. eapply continuation_other; [exact Hbelow |].
    intros reader reads Hlt Hreads. apply P.clear_other_guarded_reads; [|exact Hreads].
    now apply B.rank_lt_true_neq_correctness in Hlt.
  Qed.

  Lemma continuation_pop tf st upper popped rest k :
    R.queue_pop (R.queue st) = Some (popped,rest) ->
    T.continuation_below st upper k ->
    (popped = upper \/ R.rank_lt st upper popped = true) ->
    continuation tf st k -> continuation tf (R.with_queue st rest) k.
  Proof.
    intros Hpop Hbelow Habove. eapply continuation_other; [exact Hbelow |].
    intros owner reads Hlt Hreads. eapply B.guarded_reads_pop_other; [exact Hpop | |exact Hreads].
    apply (@B.rank_lt_true_neq_correctness st).
    destruct Habove as [->|Hhigher]; [exact Hlt |eapply T.rank_lt_trans_true; eauto].
  Qed.
  Definition valid tf (c : R.config) :=
    T.control_ordered (R.cfg_state c) (R.cfg_control c) /\
    history tf (R.cfg_state c) (R.cfg_control c).

  Lemma history_carries tf before after control : carries_reads before after ->
    history tf before control -> history tf after control.
  Proof.
    intro Hcarry. destruct control; cbn; intro H; try exact I;
      try solve [eapply continuation_carries; eauto].
    all: destruct H as [Hhead Htail]; split;
      try solve [eapply continuation_carries; eauto].
    all: first [eapply evaluation_carries with (before := before)
      |eapply completed_carries with (before := before)];
      [exact (Hcarry (R.frame_owner f)) |exact Hhead].
  Qed.

  Lemma valid_carries tf before after control :
    B.rank_extends before after -> carries_reads before after ->
    valid tf {| R.cfg_state := before; R.cfg_control := control |} ->
    valid tf {| R.cfg_state := after; R.cfg_control := control |}.
  Proof.
    intros Hrank Hcarry [Horder Hhistory]. split.
    - eapply ordered_extended; eauto.
    - eapply history_carries; eauto.
  Qed.

  Lemma carries_write st fr target input after changed :
    R.write_side_contribution st fr target input = (after,changed) -> carries_reads st after.
  Proof. intro H. apply carries_same. eapply B.write_side_contribution_same_read_view; eauto. Qed.

  Lemma carries_set st fr direct after next_fr :
    R.set_value st fr direct = (after,next_fr) -> carries_reads st after.
  Proof. intros H owner reads Hr. eapply B.guarded_reads_set_value; eauto. Qed.

  Lemma carries_requeue before after owner :
    carries_reads after (R.requeue_changed_controlled_owner before after owner).
  Proof.
    unfold R.requeue_changed_controlled_owner.
    destruct (_ && _)%bool; [apply carries_enqueue |intros x reads H; exact H].
  Qed.

  Lemma requeue_extends before after owner :
    B.rank_extends after (R.requeue_changed_controlled_owner before after owner).
  Proof.
    unfold R.requeue_changed_controlled_owner. apply B.rank_extends_with_queue.
  Qed.

  Lemma get_config tf st fr target next k after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) ->
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
    valid tf {| R.cfg_state := after; R.cfg_control := R.RunRhs next_fr (next value) k |}.
  Proof.
    intros Hget [Horder [Heval Hk]]. split; cbn.
    - rewrite (get_owner Hget). eapply below_extended;
        [eapply B.rank_extends_complete_get; exact Hget |exact Horder].
    - split; [eapply evaluation_get; eauto |].
      eapply continuation_carries; [exact (carries_get Hget) |exact Hk].
  Qed.

  Lemma base_get tf st fr target next k after :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
    R.next_config tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} = Some after ->
    valid tf after.
  Proof.
    intros Hvalid Hstep.
    assert (Hobs : valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |}).
    { eapply valid_carries; [eapply B.rank_extends_observe; reflexivity |apply carries_observe |exact Hvalid]. }
    cbn -[R.observe R.complete_get R.enqueue] in Hstep.
    destruct (negb (R.is_materialized (R.observe st target) target) &&
      R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool eqn:Hguard.
    - apply Bool.andb_true_iff in Hguard. inversion Hstep; subst. destruct Hobs as [Ho [He Hk]].
      split; cbn; [split; [exact (proj2 Hguard) |exact Ho] |now split].
    - set (current := if R.is_materialized (R.observe st target) target
        then R.observe st target else R.enqueue (R.observe st target) target) in *.
      destruct (R.complete_get current fr target) as [[next_st next_fr] value] eqn:Hget.
      inversion Hstep; subst. eapply get_config; [exact Hget |].
      subst current. destruct (R.is_materialized (R.observe st target) target); [exact Hobs |].
      eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hobs].
  Qed.

  Lemma base_spawn tf st fr target next k after :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} ->
    R.next_config tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} = Some after ->
    valid tf after.
  Proof.
    intros Hvalid Hstep.
    assert (Hobs : valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs fr next k |}).
    { destruct Hvalid as [Ho [He Hk]]. eapply valid_carries;
        [eapply B.rank_extends_observe; reflexivity |apply carries_observe |].
      split; [exact Ho |]. split; [eapply evaluation_spawn; exact He |exact Hk]. }
    cbn -[R.observe R.materialize R.enqueue] in Hstep.
    destruct (R.is_materialized (R.observe st target) target);
      [inversion Hstep; subst; exact Hobs |].
    destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target) eqn:Hlt.
    - inversion Hstep; subst. destruct Hobs as [Ho [He Hk]].
      split; cbn; [split; assumption |now split].
    - inversion Hstep; subst. eapply valid_carries;
        [apply B.rank_extends_materialize |apply carries_materialize |].
      eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hobs].
  Qed.

  Lemma base_dead tf st fr direct pending k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct pending k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep. destruct pending as [|target rest];
      cbn -[R.write_side_contribution R.continue_dead R.publish_targets] in Hstep.
    - inversion Hstep; subst. eapply valid_carries;
        [apply B.rank_extends_with_last_targets |apply carries_same;
          exact (proj1 (B.publish_targets_same_solver_view st fr)) |].
      split; [exact Ho |now split].
    - destruct (S.mem target (R.frame_current_targets fr));
        [inversion Hstep; subst; split; [exact Ho |now split] |].
      destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
      assert (Hnext : valid tf {| R.cfg_state := next; R.cfg_control := R.RunDead fr direct rest k |}).
      { eapply valid_carries; [eapply B.rank_extends_write_side_contribution; exact Hwrite
          |exact (carries_write Hwrite) |]. split; [exact Ho |now split]. }
      inversion Hstep; subst. unfold R.continue_dead. destruct changed; [|exact Hnext].
      destruct (R.rank_lt next (R.frame_owner fr) target && negb (R.is_materialized next target))%bool eqn:Hguard.
      + apply Bool.andb_true_iff in Hguard. destruct Hnext as [Ho' [Hc' Hk']].
        split; cbn; [split; [exact (proj1 Hguard) |exact Ho'] |now split].
      + eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hnext].
  Qed.

  Lemma base_commit tf st fr direct k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep. cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
    destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
    inversion Hstep; subst. eapply valid_carries;
      [apply requeue_extends |apply carries_requeue |].
    split; cbn.
    - rewrite (@B.set_value_frame_owner st fr direct next next_fr Hset). eapply below_extended;
        [eapply B.rank_extends_set_value; exact Hset |exact Ho].
    - eapply continuation_carries; [eapply carries_set; exact Hset |exact Hk].
  Qed.

  Lemma base_drain tf st fr k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho Hk] Hstep. destruct (R.queue st) as [|target rest] eqn:Hqueue;
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hqueue in Hstep; cbn in Hstep.
    - inversion Hstep; subst. split.
      + apply ordered_extended with st; [apply B.rank_extends_reset_registered_cells |].
        destruct k; cbn in *; tauto.
      + eapply continuation_carries; [apply carries_same;
          exact (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr))) |exact Hk].
    - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
      + inversion Hstep; subst. split; cbn;
          [eapply below_extended; [apply B.rank_extends_with_queue |exact Ho] |].
        split; [apply initial_evaluation |]. eapply continuation_pop;
          [unfold R.queue_pop; rewrite Hqueue; reflexivity |exact Ho |now left |exact Hk].
      + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
        * inversion Hstep; subst. split; cbn.
          -- split; [exact Hlt |]. eapply below_extended;
               [apply B.rank_extends_with_queue |exact Ho].
          --
          eapply continuation_pop; [unfold R.queue_pop; rewrite Hqueue; reflexivity
            |exact Ho |now right |exact Hk].
        * inversion Hstep; subst. split.
          -- apply ordered_extended with st; [apply B.rank_extends_reset_registered_cells |].
             destruct k; cbn in *; tauto.
          -- eapply continuation_carries; [apply carries_same;
               exact (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr))) |exact Hk].
  Qed.

  Lemma base_return tf st k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.Return k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho Hk] Hstep. destruct k; cbn -[R.complete_get] in Hstep;
      cbn in Ho,Hk.
    all: try solve [inversion Hstep; subst; split; cbn; tauto].
    - destruct Hk as [He Hk]. destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hget.
      inversion Hstep; subst. eapply get_config; [exact Hget |]. split; [exact Ho |now split].
    - destruct Hk as [Heq Hk]. inversion Hstep; subst. split; [exact Ho |].
      split; [apply initial_evaluation |exact Hk].
  Qed.

  Definition not_side control :=
    match control with R.RunRhs _ (R.ConstraintSystem.Side _ _ _) _ => False | _ => True end.

  Lemma base_step tf before after : not_side (R.cfg_control before) ->
    valid tf before -> R.next_config tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hnot Hvalid Hstep. destruct control.
    - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
        [inversion Hstep; subst; split; exact I |discriminate].
    - destruct l; cbn -[R.observe] in Hstep;
        try destruct (R.is_materialized (R.observe st t) t);
        inversion Hstep; subst; split; exact I.
    - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
        inversion Hstep; subst; split; exact I.
    - destruct Hvalid as [Ho Hk]. inversion Hstep; subst. split; cbn.
      + eapply below_extended; [apply B.rank_extends_materialize |exact Ho].
      + split; [apply initial_evaluation |].
        eapply continuation_carries; [apply carries_materialize |exact Hk].
    - destruct r.
      + inversion Hstep; subst. destruct Hvalid as [Ho [He Hk]].
        split; [exact Ho |]. split; [now apply evaluation_ret |exact Hk].
      + eapply base_get; eauto.
      + contradiction.
      + eapply base_spawn; eauto.
    - eapply base_dead; eauto.
    - eapply base_commit; eauto.
    - eapply base_drain; eauto.
    - eapply base_return; eauto.
  Qed.
  Lemma suspend_valid tf st fr direct k target rest :
    P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    valid tf (P.suspend_commit tf st fr k target rest).
  Proof.
    intros Hpending [Ho [Hc Hk]].
    destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hpending) as [_ [Hpop Hlt]].
    split; cbn.
    - split; [exact Hlt |]. eapply below_extended;
        [apply B.rank_extends_with_queue |exact Ho].
    - split; [reflexivity |]. eapply continuation_pop;
        [exact Hpop |exact Ho |now right |exact Hk].
  Qed.

  Lemma precommit_step tf before after : not_side (R.cfg_control before) ->
    valid tf before -> P.next_config tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hnot Hvalid Hstep.
    destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep.
    all: try solve [eapply base_step; eauto].
    destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hpending.
    - inversion Hstep; subst. eapply suspend_valid; eauto.
    - eapply base_step; eauto.
  Qed.

  Lemma batched_side tf st fr target raw body k :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Side target raw body) k |} ->
    valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs (fst (R.record_side_input fr target raw)) body k |}.
  Proof.
    intros [Ho [He Hk]]. eapply valid_carries;
      [eapply B.rank_extends_observe; reflexivity |apply carries_observe |].
    split; [exact Ho |]. split; [eapply evaluation_side; exact He |exact Hk].
  Qed.

  Lemma publication_extends targets st fr : B.rank_extends st (P.publish_accumulated targets st fr).
  Proof. apply P.publication_extends_ranks. Qed.

  Lemma batched_done tf st fr direct k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} ->
    valid tf {| R.cfg_state := R.publish_targets
      (P.publish_accumulated (S.elements (R.frame_current_targets fr)) st fr) fr;
      R.cfg_control := R.RunCommit fr direct k |}.
  Proof.
    intro Hvalid. eapply valid_carries;
      [apply B.rank_extends_with_last_targets |apply carries_same;
        apply (proj1 (B.publish_targets_same_solver_view _ _)) |].
    eapply valid_carries; [apply publication_extends |apply publication_carries |exact Hvalid].
  Qed.

  Lemma batched_step tf before after :
    valid tf before -> P.next_batched tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep. destruct control;
      cbn -[P.next_config R.record_side_input R.observe P.publish_accumulated R.publish_targets] in Hstep.
    all: try solve [eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I].
    - destruct r;
        try solve [eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I].
      inversion Hstep; subst. apply batched_side; exact Hvalid.
    - destruct l.
      + inversion Hstep; subst. apply batched_done; exact Hvalid.
      + eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I.
  Qed.

  Lemma clear_start tf st owner k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |} ->
    valid tf {| R.cfg_state := P.clear_owner st owner; R.cfg_control := R.StartEpisode owner k |}.
  Proof.
    intros [Ho Hk]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - eapply continuation_clear; eauto.
  Qed.

  Lemma clear_resume tf st fr body k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.Return (R.KAfterSide fr body k) |} ->
    valid tf {| R.cfg_state := P.clear_owner st (R.frame_owner fr);
      R.cfg_control := R.Return (R.KAfterSide fr body k) |}.
  Proof.
    intros [Ho [Hbody Hk]]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - split; [exact Hbody |]. eapply continuation_clear; eauto.
  Qed.

  Lemma retry_valid tf st fr direct k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    valid tf (P.retry_current tf st fr k).
  Proof.
    intros [Ho [Hc Hk]]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - split; [apply initial_evaluation |]. eapply continuation_clear; eauto.
  Qed.

  Theorem fresh_step tf before after :
    valid tf before -> P.next_fresh tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep. destruct control;
      cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
    all: try solve [eapply batched_step; eauto].
    - eapply batched_step; [eapply clear_start; exact Hvalid |exact Hstep].
    - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hpending.
      + inversion Hstep; subst. eapply suspend_valid; eauto.
      + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
        * inversion Hstep; subst. eapply retry_valid; exact Hvalid.
        * eapply batched_step; eauto.
    - destruct c; cbn -[P.next_batched] in Hstep;
        try solve [eapply batched_step; eauto].
      eapply batched_step; [eapply clear_resume; exact Hvalid |exact Hstep].
  Qed.

  Lemma guarded_reads_clean st owner reads :
    ~ B.queued st owner -> B.guarded_reads st owner reads -> B.reads_agree st reads.
  Proof.
    intros Hclean Hguard target value Hin.
    destruct (Hguard target value Hin) as [[current Hlookup] [_ [Heq|Hqueued]]];
      [|contradiction].
    unfold R.sigma_value in Heq. rewrite Hlookup in Heq. cbn in Heq. now subst.
  Qed.

End Make.
End ReadHistory.

Module CellRepair.
(** Local successor: individual contribution changes invalidate the source,
    including changes hidden by another contribution to the same target. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module H := ReadHistory.Make V D U S M Features DL UL SL ML.
  Module P := H.P.
  Import H.
  Module R := H.R.

  Definition cell_changed before after source target :=
    negb (R.equivalent (R.stored_contribution before source target)
      (R.stored_contribution after source target)).

  Definition requeue_source before after source target :=
    if cell_changed before after source target then R.enqueue after source else after.

  Definition finish_write before after fr target (aggregate_changed : bool) :=
    let next := requeue_source before after (R.frame_owner fr) target in
    if aggregate_changed then R.enqueue next target else next.

  Fixpoint publish (targets : list V.t) (st : R.state) (fr : R.frame) :=
    match targets with
    | [] => st
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        publish rest (finish_write st next fr target changed) fr
    end.

  Definition next_config tf (c : R.config) :=
    let st := R.cfg_state c in
    match R.cfg_control c with
    | R.RunDead fr direct [] k =>
        Some {| R.cfg_state := R.publish_targets
          (publish (S.elements (R.frame_current_targets fr)) st fr) fr;
          R.cfg_control := R.RunCommit fr direct k |}
    | R.RunDead fr direct (target :: rest) k =>
        if S.mem target (R.frame_current_targets fr) then
          Some {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct rest k |}
        else let '(next, changed) := R.write_side_contribution st fr target D.bottom in
          Some (R.continue_dead (requeue_source st next (R.frame_owner fr) target)
            fr direct target rest k changed)
    | _ => P.next_fresh tf c
    end.

  Fixpoint run_fuel fuel tf c :=
    match fuel with
    | 0 => c
    | S fuel => match next_config tf c with
        Some next => run_fuel fuel tf next | None => c end
    end.
  Definition solve_fuel fuel tf roots := R.terminal_state (run_fuel fuel tf (R.initial_config roots)).

  Inductive steps tf : R.config -> R.config -> Prop :=
  | steps_refl : forall c, steps tf c c
  | steps_next : forall first next last,
      next_config tf first = Some next -> steps tf next last -> steps tf first last.

  Lemma requeue_extends before after source target :
    B.rank_extends after (requeue_source before after source target).
  Proof. unfold requeue_source. destruct cell_changed;
    [apply B.rank_extends_enqueue |apply B.rank_extends_refl]. Qed.

  Lemma requeue_carries before after source target :
    H.carries_reads after (requeue_source before after source target).
  Proof. unfold requeue_source. destruct cell_changed;
    [apply H.carries_enqueue |intros owner reads Hreads; exact Hreads]. Qed.

  Lemma finish_extends before after fr target changed :
    B.rank_extends after (finish_write before after fr target changed).
  Proof.
    unfold finish_write. destruct changed; [|apply requeue_extends].
    eapply B.rank_extends_trans; [apply requeue_extends |apply B.rank_extends_enqueue].
  Qed.

  Lemma finish_carries before after fr target changed :
    H.carries_reads after (finish_write before after fr target changed).
  Proof.
    unfold finish_write. destruct changed; [|apply requeue_carries].
    eapply H.carries_trans; [apply requeue_carries |apply H.carries_enqueue].
  Qed.

  Lemma publish_extends targets st fr : B.rank_extends st (publish targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st;
      cbn -[R.write_side_contribution finish_write]; [apply B.rank_extends_refl |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    eapply B.rank_extends_trans; [|apply IH].
    eapply B.rank_extends_trans;
      [eapply B.rank_extends_write_side_contribution; exact Hwrite |apply finish_extends].
  Qed.

  Lemma publish_carries targets st fr : H.carries_reads st (publish targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st;
      cbn -[R.write_side_contribution finish_write]; [intros owner reads Hreads; exact Hreads |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    eapply H.carries_trans; [|apply IH].
    eapply H.carries_trans; [eapply H.carries_write; exact Hwrite |apply finish_carries].
  Qed.

  Lemma dead_done_valid tf st fr direct k :
    H.valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} ->
    H.valid tf {| R.cfg_state := R.publish_targets
      (publish (S.elements (R.frame_current_targets fr)) st fr) fr;
      R.cfg_control := R.RunCommit fr direct k |}.
  Proof.
    intro Hvalid. eapply H.valid_carries;
      [apply B.rank_extends_with_last_targets |apply H.carries_same;
        exact (proj1 (B.publish_targets_same_solver_view _ _)) |].
    eapply H.valid_carries; [apply publish_extends |apply publish_carries |exact Hvalid].
  Qed.

  Lemma dead_pending_valid tf st fr direct target rest k after :
    H.valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} ->
    next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} = Some after ->
    H.valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep.
    cbn -[R.write_side_contribution requeue_source R.continue_dead] in Hstep.
    destruct (S.mem target (R.frame_current_targets fr));
      [inversion Hstep; subst; split; [exact Ho |now split] |].
    destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
    set (queued := requeue_source st next (R.frame_owner fr) target) in *.
    assert (Hnext : H.valid tf {| R.cfg_state := queued; R.cfg_control := R.RunDead fr direct rest k |}).
    { unfold queued. eapply H.valid_carries; [apply requeue_extends |apply requeue_carries |].
      eapply H.valid_carries; [eapply B.rank_extends_write_side_contribution; exact Hwrite
        |eapply H.carries_write; exact Hwrite |]. split; [exact Ho |now split]. }
    inversion Hstep; subst. unfold R.continue_dead. destruct changed; [|exact Hnext].
    destruct (R.rank_lt queued (R.frame_owner fr) target && negb (R.is_materialized queued target))%bool eqn:Hguard.
    - apply Bool.andb_true_iff in Hguard. destruct Hnext as [Ho' [Hc' Hk']].
      split; cbn; [split; [exact (proj1 Hguard) |exact Ho'] |now split].
    - eapply H.valid_carries; [apply B.rank_extends_enqueue |apply H.carries_enqueue |exact Hnext].
  Qed.

  Theorem next_history tf before after :
    H.valid tf before -> next_config tf before = Some after -> H.valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep. destruct control;
      cbn -[P.next_fresh publish R.publish_targets R.write_side_contribution
        requeue_source R.continue_dead] in Hstep.
    all: try solve [eapply H.fresh_step; eauto].
    destruct l.
    - inversion Hstep; subst. apply dead_done_valid; exact Hvalid.
    - eapply dead_pending_valid; eauto.
  Qed.

  Theorem reachable_history tf roots c : steps tf (R.initial_config roots) c -> H.valid tf c.
  Proof.
    assert (Hpreserve : forall first last, steps tf first last -> H.valid tf first -> H.valid tf last).
    { intros first last Hsteps. induction Hsteps; intro Hvalid; [exact Hvalid |].
      apply IHHsteps. eapply next_history; eauto. }
    intro Hsteps. eapply Hpreserve; [exact Hsteps |]. split; exact I.
  Qed.

  Lemma fuel_steps fuel tf c : steps tf c (run_fuel fuel tf c).
  Proof.
    revert c. induction fuel as [|fuel IH]; intro c; cbn; [constructor |].
    destruct (next_config tf c) as [next|] eqn:Hstep;
      [econstructor; [exact Hstep |apply IH] |constructor].
  Qed.

  Theorem actual_commit_replay tf roots st fr direct k after next_fr next_k :
    steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
      Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
    exists reads effects, B.Sem.rhs_eval st (tf (R.frame_owner fr)) direct reads effects.
  Proof.
    intros Hreach Hstep.
    destruct (reachable_history Hreach) as [_ [[reads [effects [Htrace Hguard]]] _]].
    destruct (@P.fresh_commit_ready tf st fr direct k after next_fr next_k Hstep) as [_ Hclean].
    exists reads, effects. apply B.rhs_trace_replay; [exact Htrace |].
    eapply H.guarded_reads_clean; eauto.
  Qed.
  Lemma requeue_members before after source target owner :
    B.queued (requeue_source before after source target) owner <->
    B.queued after owner \/ (owner = source /\ cell_changed before after source target = true).
  Proof.
    unfold requeue_source. destruct (cell_changed before after source target) eqn:Hchanged.
    - unfold B.queued, R.enqueue. cbn. rewrite B.queue_insert_members. tauto.
    - split; [now left |intros [H|[_ H]]; [exact H |discriminate]].
  Qed.

  Lemma finish_keeps_queued before after fr target changed owner :
    B.queued after owner -> B.queued (finish_write before after fr target changed) owner.
  Proof.
    intro Hq. unfold finish_write. destruct changed.
    - unfold B.queued, R.enqueue. cbn. apply B.queue_insert_members. right.
      apply requeue_members. now left.
    - apply requeue_members. now left.
  Qed.

  Lemma finish_queues_changed before after fr target changed :
    cell_changed before after (R.frame_owner fr) target = true ->
    B.queued (finish_write before after fr target changed) (R.frame_owner fr).
  Proof.
    intro Hchange. unfold finish_write. destruct changed.
    - unfold B.queued, R.enqueue. cbn. apply B.queue_insert_members. right.
      apply requeue_members. right. now split.
    - apply requeue_members. right. now split.
  Qed.

  Lemma publish_keeps_queued targets st fr owner :
    B.queued st owner -> B.queued (publish targets st fr) owner.
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hq;
      cbn -[R.write_side_contribution finish_write]; [exact Hq |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    apply IH, finish_keeps_queued. unfold B.queued in *.
    rewrite (proj2 (proj2 (B.write_side_contribution_same_read_view Hwrite))). exact Hq.
  Qed.

  Fixpoint publication_changes targets st fr : Prop :=
    match targets with
    | [] => False
    | target :: rest =>
        let input := match M.lookup (R.frame_local_side fr) target with
          Some value => value | None => D.bottom end in
        let '(next, changed) := R.write_side_contribution st fr target input in
        cell_changed st next (R.frame_owner fr) target = true \/
        publication_changes rest (finish_write st next fr target changed) fr
    end.

  Theorem changed_publication_queues_source targets st fr :
    publication_changes targets st fr -> B.queued (publish targets st fr) (R.frame_owner fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hchange;
      cbn -[R.write_side_contribution finish_write] in Hchange |- *; [contradiction |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    destruct Hchange as [Hhead|Htail]; [|now apply IH].
    apply publish_keeps_queued, finish_queues_changed, Hhead.
  Qed.

  Corollary clean_publication_unchanged targets st fr :
    ~ B.queued (publish targets st fr) (R.frame_owner fr) -> ~ publication_changes targets st fr.
  Proof. intros Hclean Hchange. apply Hclean, changed_publication_queues_source, Hchange. Qed.

  Lemma stored_after_update st source target scope phase value :
    R.stored_contribution
      (R.register_reset (R.with_contributions st
        (R.update_map (R.contributions st) target source value)) source target scope phase)
      source target = value.
  Proof.
    unfold R.stored_contribution. rewrite B.contributions_register_reset. cbn.
    now rewrite B.lookup_update_map_same.
  Qed.

  Lemma changed_cell_consumes_credit st fr target input next changed :
    R.write_side_contribution st fr target input = (next,changed) ->
    cell_changed st next (R.frame_owner fr) target = true ->
    B.Credits.side_cell_credit next (R.frame_owner fr) target <
    B.Credits.side_cell_credit st (R.frame_owner fr) target.
  Proof.
    intros Hwrite Hchange. unfold R.write_side_contribution in Hwrite.
    set (base := R.promote_side_target st fr target) in *.
    set (cell := R.stored_side_cell base (R.frame_owner fr) target) in *.
    set (old := R.stored_contribution base (R.frame_owner fr) target) in *.
    destruct (U.update true target (R.side_phase cell) old input) as [phase value] eqn:Hupdate.
    cbn in Hwrite. inversion Hwrite; subst next changed.
    unfold cell_changed in Hchange. rewrite stored_after_update in Hchange.
    assert (Hold : R.stored_contribution st (R.frame_owner fr) target = old).
    { subst old base. unfold R.promote_side_target.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
    rewrite Hold in Hchange.
    assert (Hneq : ~ UL.equivalent value old).
    { intros [Hvo Hov]. unfold R.equivalent in Hchange. rewrite Hvo, Hov in Hchange. discriminate. }
    rewrite B.Credits.side_cell_credit_after_update.
    rewrite <- (B.Credits.side_cell_credit_promote_side_target st fr (R.frame_owner fr) target).
    change (UL.remaining_changes phase value < UL.remaining_changes (R.side_phase cell) old).
    pose proof (@UL.update_change_consumes true target (R.side_phase cell) old input) as Hcredit.
    rewrite Hupdate in Hcredit. apply Hcredit, Hneq.
  Qed.

  Lemma changed_source_consumes_credit support st fr target input next changed :
    List.In target support -> R.write_side_contribution st fr target input = (next,changed) ->
    cell_changed st next (R.frame_owner fr) target = true ->
    B.Credits.source_side_credit support next (R.frame_owner fr) <
    B.Credits.source_side_credit support st (R.frame_owner fr).
  Proof.
    intros Hin Hwrite Hchange. induction support as [|head rest IH]; [contradiction |].
    cbn. destruct Hin as [->|Hin].
    - pose proof (changed_cell_consumes_credit Hwrite Hchange).
      pose proof (B.Credits.source_side_credit_write_nonincreasing rest Hwrite). lia.
    - destruct (V.eq_dec head target) as [->|Hneq].
      + pose proof (changed_cell_consumes_credit Hwrite Hchange).
        pose proof (B.Credits.source_side_credit_write_nonincreasing rest Hwrite). lia.
      + rewrite (B.Credits.side_cell_credit_write_other Hwrite)
          by (intro Heq; inversion Heq; contradiction).
        specialize (IH Hin). lia.
  Qed.

  Lemma finish_credit support before after fr target changed source :
    B.Credits.source_side_credit support (finish_write before after fr target changed) source =
    B.Credits.source_side_credit support after source.
  Proof.
    unfold finish_write, requeue_source. destruct changed, cell_changed;
      repeat rewrite P.source_credit_enqueue; reflexivity.
  Qed.

  Lemma publish_credit_nonincreasing targets support st fr :
    B.Credits.source_side_credit support (publish targets st fr) (R.frame_owner fr) <=
    B.Credits.source_side_credit support st (R.frame_owner fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intro st;
      cbn -[R.write_side_contribution finish_write]; [reflexivity |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    eapply Nat.le_trans; [apply IH |]. rewrite finish_credit.
    eapply B.Credits.source_side_credit_write_nonincreasing; exact Hwrite.
  Qed.

  Theorem changed_publication_consumes_credit targets support st fr :
    List.incl targets support -> publication_changes targets st fr ->
    B.Credits.source_side_credit support (publish targets st fr) (R.frame_owner fr) <
    B.Credits.source_side_credit support st (R.frame_owner fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hin Hchange;
      cbn -[R.write_side_contribution finish_write] in Hchange |- *; [contradiction |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    destruct Hchange as [Hhead|Htail].
    - eapply Nat.le_lt_trans; [apply publish_credit_nonincreasing |]. rewrite finish_credit.
      eapply changed_source_consumes_credit;
        [apply Hin; now left |exact Hwrite |exact Hhead].
    - eapply Nat.lt_le_trans; [apply IH; [intros x Hx; apply Hin; now right |exact Htail] |].
      rewrite finish_credit. eapply B.Credits.source_side_credit_write_nonincreasing; exact Hwrite.
  Qed.
  Theorem committing_publication_unchanged tf st fr direct k after next_fr next_k :
    next_config tf
      {| R.cfg_state := R.publish_targets
          (publish (S.elements (R.frame_current_targets fr)) st fr) fr;
         R.cfg_control := R.RunCommit fr direct k |} =
      Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
    ~ publication_changes (S.elements (R.frame_current_targets fr)) st fr.
  Proof.
    intro Hstep. apply clean_publication_unchanged.
    exact (proj2 (@P.fresh_commit_ready tf _ fr direct k after next_fr next_k Hstep)).
  Qed.

  Lemma requeue_reset_bounded before after source target :
    B.ScopeBounds.reset_sources_bounded after ->
    B.ScopeBounds.reset_sources_bounded (requeue_source before after source target).
  Proof. unfold requeue_source. destruct cell_changed; intro Hbounded;
    [now apply B.ScopeBounds.reset_sources_bounded_enqueue |exact Hbounded]. Qed.

  Lemma finish_reset_bounded before after fr target changed :
    B.ScopeBounds.reset_sources_bounded after ->
    B.ScopeBounds.reset_sources_bounded (finish_write before after fr target changed).
  Proof.
    intro Hbounded. unfold finish_write. destruct changed;
      [apply B.ScopeBounds.reset_sources_bounded_enqueue |]; now apply requeue_reset_bounded.
  Qed.

  Lemma publish_scopes targets st fr : B.ScopeBounds.reset_sources_bounded st ->
    B.ScopeBounds.frame_scope_bounded st fr -> B.ScopeBounds.reset_sources_bounded (publish targets st fr).
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Hreset Hframe;
      cbn -[R.write_side_contribution finish_write]; [exact Hreset |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end))
      as [next changed] eqn:Hwrite.
    destruct (B.ScopeBounds.write_side_scopes Hreset Hframe Hwrite) as [Hr Hf].
    apply IH; [now apply finish_reset_bounded |].
    eapply B.ScopeBounds.frame_scope_bounded_extended; [apply finish_extends |exact Hf].
  Qed.

  Lemma continue_dead_scopes st fr direct target rest k changed :
    B.ScopeBounds.scopes_bounded {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct rest k |} ->
    B.ScopeBounds.scopes_bounded (R.continue_dead st fr direct target rest k changed).
  Proof.
    intro Hbounded. unfold R.continue_dead. destruct changed; [|exact Hbounded].
    destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))%bool.
    - exact Hbounded.
    - apply P.queue_view_scopes; exact Hbounded.
  Qed.

  Lemma dead_pending_scopes tf st fr direct target rest k after :
    B.ScopeBounds.scopes_bounded
      {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} ->
    next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} = Some after ->
    B.ScopeBounds.scopes_bounded after.
  Proof.
    intros [Hreset [Hframe Hk]] Hstep.
    cbn -[R.write_side_contribution requeue_source R.continue_dead] in Hstep.
    destruct (S.mem target (R.frame_current_targets fr));
      [inversion Hstep; subst; split; [exact Hreset |now split] |].
    destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
    inversion Hstep; subst. apply continue_dead_scopes.
    destruct (B.ScopeBounds.write_side_scopes Hreset Hframe Hwrite) as [Hr Hf]. split.
    - now apply requeue_reset_bounded.
    - apply B.ScopeBounds.control_scopes_bounded_extended with next;
        [apply requeue_extends |]. split; [exact Hf |].
      eapply B.ScopeBounds.continuation_scopes_bounded_extended;
        [eapply B.rank_extends_write_side_contribution; exact Hwrite |exact Hk].
  Qed.

  Theorem next_scopes tf before after :
    B.ScopeBounds.scopes_bounded before -> next_config tf before = Some after ->
    B.ScopeBounds.scopes_bounded after.
  Proof.
    destruct before as [st control]. intros Hbounded Hstep. destruct control;
      cbn -[P.next_fresh publish R.publish_targets R.write_side_contribution
        requeue_source R.continue_dead] in Hstep.
    all: try solve [eapply P.fresh_step_scopes; eauto].
    destruct l.
    - inversion Hstep; subst. destruct Hbounded as [Hreset [Hframe Hk]]. split.
      + apply B.ScopeBounds.reset_sources_bounded_publish_targets. now apply publish_scopes.
      + apply B.ScopeBounds.control_scopes_bounded_extended with st; [|now split].
        eapply B.rank_extends_trans; [apply publish_extends |apply B.rank_extends_with_last_targets].
    - eapply dead_pending_scopes with (tf := tf); eauto.
  Qed.

  Theorem reachable_scopes tf roots c : steps tf (R.initial_config roots) c ->
    B.ScopeBounds.scopes_bounded c.
  Proof.
    assert (Hpreserve : forall first last, steps tf first last ->
      B.ScopeBounds.scopes_bounded first -> B.ScopeBounds.scopes_bounded last).
    { intros first last Hsteps. induction Hsteps; intro Hbounded; [exact Hbounded |].
      apply IHHsteps. eapply next_scopes; eauto. }
    intro Hsteps. eapply Hpreserve; [exact Hsteps |].
    apply B.ScopeBounds.reachable_scopes_bounded with tf roots. constructor.
  Qed.

  Theorem higher_reset_preserves_credit tf roots c support source scope :
    steps tf (R.initial_config roots) c -> R.rank_lt (R.cfg_state c) source scope = true ->
    B.Credits.source_side_credit support
      (R.reset_registered_cells (R.cfg_state c) scope) source =
    B.Credits.source_side_credit support (R.cfg_state c) source.
  Proof.
    intros Hsteps Hrank. apply B.reset_above_preserves_source_credit;
      [exact (proj1 (reachable_scopes Hsteps)) |exact Hrank].
  Qed.
End Make.
End CellRepair.

Module PublicationStability.
(** Facts derived from the executable source-invalidation guard. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module C := CellRepair.Make V D U S M Features DL UL SL ML.
  Import C C.H.

  Lemma phase_after_update st source target scope phase value :
    R.side_phase (R.stored_side_cell
      (R.register_reset (R.with_contributions st
        (R.update_map (R.contributions st) target source value))
        source target scope phase) source target) = phase.
  Proof.
    unfold R.stored_side_cell, R.register_reset. cbn.
    rewrite B.lookup_update_map_same. reflexivity.
  Qed.

  Definition cell_stable st source target input :=
    UL.equivalent
      (snd (U.update true target (R.side_phase (R.stored_side_cell st source target))
        (R.stored_contribution st source target) input))
      (R.stored_contribution st source target).

  Lemma unchanged_write_stable st fr target input next changed :
    R.write_side_contribution st fr target input = (next,changed) ->
    cell_changed st next (R.frame_owner fr) target = false ->
    cell_stable next (R.frame_owner fr) target input.
  Proof.
    intros Hwrite Hsame. unfold R.write_side_contribution in Hwrite.
    set (base := R.promote_side_target st fr target) in *.
    set (cell := R.stored_side_cell base (R.frame_owner fr) target) in *.
    set (old := R.stored_contribution base (R.frame_owner fr) target) in *.
    destruct (U.update true target (R.side_phase cell) old input)
      as [phase value] eqn:Hupdate.
    cbn in Hwrite. inversion Hwrite; subst next changed.
    unfold cell_changed in Hsame. rewrite stored_after_update in Hsame.
    assert (Hold : R.stored_contribution st (R.frame_owner fr) target = old).
    { subst old base. unfold R.promote_side_target.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
    rewrite Hold in Hsame. apply Bool.negb_false_iff, Bool.andb_true_iff in Hsame.
    assert (Heq : UL.equivalent value old) by (split; tauto).
    unfold cell_stable. rewrite phase_after_update, stored_after_update.
    pose proof (@UL.update_stutter_closed true target (R.side_phase cell) old input) as Hclosed.
    rewrite Hupdate in Hclosed. apply Hclosed;
      [exact Heq |exact Heq |split; apply DL.leq_refl].
  Qed.

  Lemma finish_stable before after fr target changed source observed input :
    cell_stable (finish_write before after fr target changed) source observed input <->
    cell_stable after source observed input.
  Proof.
    unfold finish_write, requeue_source, cell_stable.
    destruct changed, cell_changed; reflexivity.
  Qed.

  Lemma write_other_stable st fr target input next changed source observed raw :
    R.write_side_contribution st fr target input = (next,changed) ->
    (source,observed) <> (R.frame_owner fr,target) ->
    cell_stable next source observed raw <-> cell_stable st source observed raw.
  Proof.
    intros Hw Hneq. unfold cell_stable.
    rewrite (B.Credits.stored_side_cell_write_other Hw Hneq),
      (B.Credits.stored_contribution_write_other Hw Hneq). reflexivity.
  Qed.

  Lemma publish_other_stable targets st fr observed raw :
    ~ List.In observed targets ->
    cell_stable (publish targets st fr) (R.frame_owner fr) observed raw <->
    cell_stable st (R.frame_owner fr) observed raw.
  Proof.
    revert st. induction targets as [|target rest IH]; intros st Houtside;
      cbn -[R.write_side_contribution finish_write]; [reflexivity |].
    destruct (R.write_side_contribution st fr target
      (match M.lookup (R.frame_local_side fr) target with
        Some value => value | None => D.bottom end)) as [next changed] eqn:Hw.
    rewrite IH by (intro H; apply Houtside; now right).
    rewrite finish_stable. eapply write_other_stable; [exact Hw |].
    intro Heq. inversion Heq. apply Houtside. now left.
  Qed.

  Theorem unchanged_publication_stable targets st fr target :
    List.In target targets -> ~ publication_changes targets st fr ->
    cell_stable (publish targets st fr) (R.frame_owner fr) target
      (match M.lookup (R.frame_local_side fr) target with
        Some value => value | None => D.bottom end).
  Proof.
    revert st. induction targets as [|head rest IH]; intros st Hin Hclean;
      [contradiction |].
    cbn -[R.write_side_contribution finish_write] in Hclean |- *.
    destruct (R.write_side_contribution st fr head
      (match M.lookup (R.frame_local_side fr) head with
        Some value => value | None => D.bottom end)) as [next changed] eqn:Hw.
    destruct (List.in_dec V.eq_dec target rest) as [Hrest|Houtside].
    - apply IH; [exact Hrest |tauto].
    - destruct Hin as [->|Hin]; [|contradiction].
      apply publish_other_stable; [exact Houtside |].
      apply finish_stable. eapply unchanged_write_stable; [exact Hw |].
      destruct cell_changed eqn:Hchange;
        [exfalso; apply Hclean; now left |reflexivity].
  Qed.

  Theorem committing_publication_stable tf st fr direct k after next_fr next_k target :
    next_config tf {| R.cfg_state := R.publish_targets
      (publish (S.elements (R.frame_current_targets fr)) st fr) fr;
      R.cfg_control := R.RunCommit fr direct k |} =
      Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
    S.mem target (R.frame_current_targets fr) = true ->
    cell_stable (R.publish_targets
      (publish (S.elements (R.frame_current_targets fr)) st fr) fr)
      (R.frame_owner fr) target
      (match M.lookup (R.frame_local_side fr) target with
        Some value => value | None => D.bottom end).
  Proof.
    intros Hstep Hin. change (cell_stable
      (publish (S.elements (R.frame_current_targets fr)) st fr)
      (R.frame_owner fr) target
      (match M.lookup (R.frame_local_side fr) target with
        Some value => value | None => D.bottom end)).
    apply unchanged_publication_stable; [now apply SL.mem_spec |].
    eapply committing_publication_unchanged; exact Hstep.
  Qed.

  Lemma stable_covers_input st source target input :
    cell_stable st source target input ->
    D.leq input (R.stored_contribution st source target) = true.
  Proof.
    intros [Hle _]. eapply DL.leq_trans; [apply UL.update_sound |exact Hle].
  Qed.
End Make.
End PublicationStability.
