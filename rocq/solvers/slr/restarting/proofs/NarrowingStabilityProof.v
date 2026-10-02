From Stdlib Require Import List Lia Arith.PeanoNat Sorting.Permutation.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrder
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting.proofs.Correctness.
From TcSolvers Require Import
  common.BoxUpdate.

Import ListNotations.
Set Implicit Arguments.

(** Internal ordinary narrowing-stability proof for the Restarting solver.

    No ordinary frame ever reaches the fallback [Widen] phase.  Together with
    correctness and termination, this says that the returned solution was
    obtained using the widening/narrowing box without falling back to widening
    again.  It does not claim a least fixpoint among all solutions.

    The generic theorem below makes the key semantic obligation explicit:
    when a reachable ordinary commit first enters [BoxN], its queue must
    contain only lower-ranked work.  Commits which stay in [BoxW] need no
    such restriction.  This entry-frontier is sufficient, but arbitrary
    fixed ranks do not follow it from transfer monotonicity alone; see
    [NarrowingStabilityCounterexample].  For the append-only
    first-discovery
    ranking, [first_discovery_ordinary_avoids_fallback] proves the frontier
    operationally and discharges the obligation. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (WN : WIDEN_NARROW D).

  Module U := OneBoxUpdate V D WN.

  Module WithLaws
    (S : SET V)
    (M : MAP V)
    (Rk : DISCOVERY_ORDER V)
    (Features : Restarting.FEATURES)
    (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
    (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
    (DL : DOMAIN_LAWS D)
    (WNL : WIDEN_NARROW_LAWS D WN)
    (UL : UPDATE_LAWS V D U)
    (SL : SET_LAWS V S)
    (ML : MAP_LAWS V M).

  Module Total := Correctness.Make
    V D U S M Rk Features RankLaws RankFinite DL UL SL ML.
  Module Inv := Total.
  Module Support := Total.
  Module Sem := Total.Sem.
  Module R := Total.R.

  Lemma reachable_invariant :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      Total.invariant tf roots c.
  Proof.
    intros tf roots c Hsteps.
    eapply Total.invariant_steps.
    - apply Total.initial_invariant.
    - exact Hsteps.
  Qed.

  (** Append-only discovery assigns every fresh variable a rank above every
      variable already present in the ranking. *)
  Definition fresh_ranks_above : Prop :=
    forall order target next target_rank owner owner_rank,
      RankLaws.valid order ->
      Rk.lookup order target = None ->
      Rk.lookup order owner = Some owner_rank ->
      Rk.observe order target = (next, target_rank) ->
      owner_rank < target_rank.

  Lemma fresh_observe_rank_lt :
    forall st owner target,
      fresh_ranks_above ->
      Total.rank_valid st ->
      Total.ranked st owner ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.rank_lt (R.observe st target) owner target = true.
  Proof.
    intros st owner target Habove Hvalid [owner_rank Howner] Hfresh.
    unfold R.observe.
    destruct (R.Ranking.observe (R.ranking st) target)
      as [next target_rank] eqn:Hobserve.
    unfold R.rank_lt, R.ranking_lt. cbn.
    rewrite (RankLaws.observe_preserves Hobserve Howner).
    rewrite (RankLaws.observe_lookup Hobserve).
    apply Nat.ltb_lt.
    eapply Habove; eassumption.
  Qed.

  Lemma fresh_observe_queue_below :
    forall st target,
      fresh_ranks_above ->
      Total.rank_valid st ->
      Total.queue_ranked st ->
      R.Ranking.lookup (R.ranking st) target = None ->
      Total.Termination.queue_strictly_below target (R.observe st target).
  Proof.
    intros st target Habove Hvalid Hqueue Hfresh queued Hin.
    rewrite Total.Termination.observe_queue in Hin.
    eapply fresh_observe_rank_lt.
    - exact Habove.
    - exact Hvalid.
    - exact (Hqueue queued Hin).
    - exact Hfresh.
  Qed.

  Lemma reachable_fresh_observe_queue_below :
    forall tf roots c target,
      fresh_ranks_above ->
      Sem.steps tf (R.initial_config roots) c ->
      R.Ranking.lookup (R.ranking (R.cfg_state c)) target = None ->
      Total.Termination.queue_strictly_below target
        (R.observe (R.cfg_state c) target).
  Proof.
    intros tf roots c target Habove Hreachable Hfresh.
    pose proof (Total.reachable_configuration_ranked Hreachable) as Hranked.
    eapply fresh_observe_queue_below.
    - exact Habove.
    - exact (Total.configuration_rank_valid Hranked).
    - exact (Total.data_queue_ranked
        (Total.configuration_state_data Hranked)).
    - exact Hfresh.
  Qed.

  Lemma continuation_active_ranked :
    forall st k owner,
      Total.continuation_ranked st k ->
      Inv.continuation_active_correctness owner k ->
      Total.ranked st owner.
  Proof.
    intros st k. induction k; intros owner Hranked Hactive;
      cbn in Hranked, Hactive; try contradiction.
    - destruct Hranked as [Hframe [_ Hrest]].
      destruct Hframe as [Howner _].
      destruct Hactive as [-> | Hactive]; [exact Howner |].
      now apply IHk.
    - destruct Hranked as [Hframe Hrest].
      destruct Hframe as [Howner _].
      destruct Hactive as [-> | Hactive]; [exact Howner |].
      now apply IHk.
    - destruct Hranked as [Hframe Hrest].
      destruct Hframe as [Howner _].
      destruct Hactive as [-> | Hactive]; [exact Howner |].
      now apply IHk.
    - destruct Hranked as [Hframe [_ Hrest]].
      destruct Hframe as [Howner _].
      destruct Hactive as [-> | Hactive]; [exact Howner |].
      now apply IHk.
    - destruct Hranked as [_ Hrest].
      now apply IHk.
  Qed.

  Lemma control_active_ranked :
    forall st control owner,
      Total.control_ranked st control ->
      Inv.control_active owner control ->
      Total.ranked st owner.
  Proof.
    intros st control owner Hranked Hactive.
    destruct control; cbn in Hranked, Hactive; try contradiction.
    - destruct Hranked as [Hcurrent Hrest].
      destruct Hactive as [-> | Hactive]; [exact Hcurrent |].
      eapply continuation_active_ranked; eassumption.
    - destruct Hranked as [Hframe Hrest].
      destruct Hframe as [Hcurrent _].
      destruct Hactive as [-> | Hactive]; [exact Hcurrent |].
      eapply continuation_active_ranked; eassumption.
    - destruct Hranked as [Hframe [_ Hrest]].
      destruct Hframe as [Hcurrent _].
      destruct Hactive as [-> | Hactive]; [exact Hcurrent |].
      eapply continuation_active_ranked; eassumption.
    - destruct Hranked as [Hframe Hrest].
      destruct Hframe as [Hcurrent _].
      destruct Hactive as [-> | Hactive]; [exact Hcurrent |].
      eapply continuation_active_ranked; eassumption.
    - destruct Hranked as [_ Hrest].
      eapply continuation_active_ranked; eassumption.
    - eapply continuation_active_ranked; eassumption.
  Qed.

  Definition solved_ranked (st : R.state) : Prop :=
    forall owner, Sem.solved st owner -> Total.ranked st owner.

  Lemma next_config_solved_ranked :
    forall tf roots before after,
      Total.invariant tf roots before ->
      Total.configuration_ranked before ->
      solved_ranked (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      solved_ranked (R.cfg_state after).
  Proof.
    intros tf roots before after Hinv Hranked Hsolved_ranked Hstep
      owner Hsolved.
    pose proof (@Total.next_config_configuration_ranked
      tf before after Hranked Hstep) as Hranked_after.
    destruct (@Total.next_config_solved_origin_guarded
      tf before after owner
      (Total.invariant_get_consistent Hinv)
      (Total.invariant_history Hinv) Hsolved Hstep)
      as [Hbefore | [Hqueued | Hactive]].
    - eapply Total.ranked_extended.
      + eapply Total.next_config_rank_extends. exact Hstep.
      + now apply Hsolved_ranked.
    - apply (Total.data_queue_ranked
        (Total.configuration_state_data Hranked_after)).
      exact Hqueued.
    - eapply control_active_ranked.
      + exact (Total.configuration_control_ranked Hranked_after).
      + exact Hactive.
  Qed.

  Lemma reachable_solved_ranked :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      solved_ranked (R.cfg_state c).
  Proof.
    intros tf roots c Hsteps.
    assert (Hpreserve : forall first last,
      Total.invariant tf roots first ->
      Total.configuration_ranked first ->
      solved_ranked (R.cfg_state first) ->
      Sem.steps tf first last ->
      solved_ranked (R.cfg_state last)).
    { intros first last Hinv Hranked Hsolved Hrun.
      induction Hrun.
      - exact Hsolved.
      - apply IHHrun.
        + eapply Total.invariant_step; eassumption.
        + eapply Total.next_config_configuration_ranked; eassumption.
        + eapply next_config_solved_ranked; eassumption. }
    eapply Hpreserve.
    - apply Total.initial_invariant.
    - apply Total.initial_configuration_ranked.
    - intros owner [value Hlookup]. cbn in Hlookup.
      rewrite ML.lookup_empty in Hlookup. discriminate.
    - exact Hsteps.
  Qed.

  Lemma reachable_unranked_is_unmaterialized :
    forall tf roots c target,
      Sem.steps tf (R.initial_config roots) c ->
      R.Ranking.lookup (R.ranking (R.cfg_state c)) target = None ->
      R.is_materialized (R.cfg_state c) target = false.
  Proof.
    intros tf roots c target Hreachable Hunranked.
    destruct (R.is_materialized (R.cfg_state c) target)
      eqn:Hmaterialized; [|reflexivity].
    unfold R.is_materialized in Hmaterialized.
    destruct (M.lookup (R.sigma (R.cfg_state c)) target)
      as [value |] eqn:Hvalue; try discriminate.
    pose proof (@reachable_solved_ranked tf roots c Hreachable target
      (ex_intro _ value Hvalue)) as [rank Hranked].
    rewrite Hunranked in Hranked. discriminate.
  Qed.

  Lemma append_only_unranked_get_starts_episode :
    forall tf roots st fr target next k,
      fresh_ranks_above ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.next_config tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) k |} =
      Some
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterGet fr target next k) |}.
  Proof.
    intros tf roots st fr target next k Habove Hreachable Hunranked.
    pose proof (Total.reachable_configuration_ranked Hreachable) as Hranked.
    pose proof (Total.configuration_control_ranked Hranked) as Hcontrol.
    cbn in Hcontrol. destruct Hcontrol as [Hframe _].
    assert (Hfresh : R.is_materialized st target = false).
    { eapply reachable_unranked_is_unmaterialized
        with (c := {| R.cfg_state := st;
          R.cfg_control :=
            R.RunRhs fr (R.ConstraintSystem.Get target next) k |});
        eassumption. }
    assert (Hobserved_fresh :
      R.is_materialized (R.observe st target) target = false).
    { unfold R.is_materialized, R.observe in *.
      destruct (R.Ranking.observe (R.ranking st) target). exact Hfresh. }
    assert (Hhigher :
      R.rank_lt (R.observe st target) (R.frame_owner fr) target = true).
    { eapply fresh_observe_rank_lt.
      - exact Habove.
      - exact (Total.configuration_rank_valid Hranked).
      - exact (proj1 Hframe).
      - exact Hunranked. }
    unfold R.next_config. cbn -[R.observe].
    now rewrite Hobserved_fresh, Hhigher.
  Qed.

  Lemma append_only_unranked_spawn_starts_episode :
    forall tf roots st fr target next k,
      fresh_ranks_above ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.next_config tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} =
      Some
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterSpawn fr next k) |}.
  Proof.
    intros tf roots st fr target next k Habove Hreachable Hunranked.
    pose proof (Total.reachable_configuration_ranked Hreachable) as Hranked.
    pose proof (Total.configuration_control_ranked Hranked) as Hcontrol.
    cbn in Hcontrol. destruct Hcontrol as [Hframe _].
    assert (Hfresh : R.is_materialized st target = false).
    { eapply reachable_unranked_is_unmaterialized
        with (c := {| R.cfg_state := st;
          R.cfg_control :=
            R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |});
        eassumption. }
    assert (Hobserved_fresh :
      R.is_materialized (R.observe st target) target = false).
    { unfold R.is_materialized, R.observe in *.
      destruct (R.Ranking.observe (R.ranking st) target). exact Hfresh. }
    assert (Hhigher :
      R.rank_lt (R.observe st target) (R.frame_owner fr) target = true).
    { eapply fresh_observe_rank_lt.
      - exact Habove.
      - exact (Total.configuration_rank_valid Hranked).
      - exact (proj1 Hframe).
      - exact Hunranked. }
    unfold R.next_config. cbn -[R.observe].
    now rewrite Hobserved_fresh, Hhigher.
  Qed.

  Lemma observe_ranked_state :
    forall st owner,
      Total.ranked st owner -> R.observe st owner = st.
  Proof.
    intros st owner [rank Hlookup].
    unfold R.observe.
    rewrite (RankLaws.observe_existing Hlookup).
    now destruct st.
  Qed.

  Lemma complete_get_same_ranking :
    forall st fr target next next_fr value,
      R.complete_get st fr target = (next, next_fr, value) ->
      R.ranking next = R.ranking st.
  Proof.
    intros st fr target next next_fr value Hget.
    unfold R.complete_get, R.promote_controlled, R.materialize in Hget.
    repeat match type of Hget with
    | context [if ?condition then _ else _] => destruct condition eqn:?
    | context [match ?subject with _ => _ end] => destruct subject eqn:?
    end; inversion Hget; reflexivity.
  Qed.

  Lemma set_value_same_ranking :
    forall st fr direct next next_fr,
      R.set_value st fr direct = (next, next_fr) ->
      R.ranking next = R.ranking st.
  Proof.
    intros st fr direct next next_fr Hset.
    unfold R.set_value in Hset.
    repeat match type of Hset with
    | context [if ?condition then _ else _] => destruct condition eqn:?
    end; inversion Hset; reflexivity.
  Qed.

  Record observation : Type := {
    observed_direct : D.t;
    observed_reads : list (V.t * D.t);
    observed_sides : list (V.t * D.t);
    observed_spawns : list V.t;
  }.

  (** A trace records the value returned by every individual [Get].
      This deliberately permits different occurrences to observe different
      stores when an evaluation suspends for a nested episode. *)
  Inductive trace_observes : R.ConstraintSystem.rhs -> observation -> Prop :=
  | TraceRet :
      forall direct,
        trace_observes (R.ConstraintSystem.Ret direct)
          {| observed_direct := direct;
             observed_reads := [];
             observed_sides := [];
             observed_spawns := [] |}
  | TraceGet :
      forall target value next result,
        trace_observes (next value) result ->
        trace_observes (R.ConstraintSystem.Get target next)
          {| observed_direct := observed_direct result;
             observed_reads :=
               (target, value) :: observed_reads result;
             observed_sides := observed_sides result;
             observed_spawns := observed_spawns result |}
  | TraceSide :
      forall target payload next result,
        trace_observes next result ->
        trace_observes (R.ConstraintSystem.Side target payload next)
          {| observed_direct := observed_direct result;
             observed_reads := observed_reads result;
             observed_sides :=
               (target, payload) :: observed_sides result;
             observed_spawns := observed_spawns result |}
  | TraceSpawn :
      forall target next result,
        trace_observes next result ->
        trace_observes (R.ConstraintSystem.Spawn target next)
          {| observed_direct := observed_direct result;
             observed_reads := observed_reads result;
             observed_sides := observed_sides result;
             observed_spawns :=
               target :: observed_spawns result |}.

  Definition full_rhs_context
    (root current : R.ConstraintSystem.rhs)
    (prefix_reads prefix_sides : list (V.t * D.t))
    (prefix_spawns : list V.t) : Prop :=
    forall suffix,
      trace_observes current suffix ->
      exists result,
        trace_observes root result /\
        observed_direct result =
          observed_direct suffix /\
        observed_reads result =
          prefix_reads ++ observed_reads suffix /\
        observed_sides result =
          prefix_sides ++ observed_sides suffix /\
        observed_spawns result =
          prefix_spawns ++ observed_spawns suffix.

  Lemma initial_full_rhs_context :
    forall body,
      full_rhs_context body body [] [] [].
  Proof.
    intros body result Hresult.
    exists result.
    repeat split; try assumption; reflexivity.
  Qed.

  Lemma full_rhs_context_get :
    forall root target next prefix_reads
      prefix_sides prefix_spawns value,
      full_rhs_context root (R.ConstraintSystem.Get target next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root (next value)
        (prefix_reads ++ [(target, value)])
        prefix_sides prefix_spawns.
  Proof.
    unfold full_rhs_context.
    intros root target next prefix_reads
      prefix_sides prefix_spawns value
      Hcontext result Hresult.
    destruct
      (Hcontext
        {| observed_direct := observed_direct result;
           observed_reads :=
             (target, value) :: observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns := observed_spawns result |})
      as [root_result
        [Hroot [Hdirect [Hreads [Hsides Hspawns]]]]].
    - constructor. exact Hresult.
    - exists root_result.
      cbn in Hdirect, Hreads, Hsides, Hspawns.
      repeat split; try assumption.
      rewrite Hreads.
      rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma full_rhs_context_side :
    forall root target value next prefix_reads
      prefix_sides prefix_spawns,
      full_rhs_context root (R.ConstraintSystem.Side target value next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root next prefix_reads
        (prefix_sides ++ [(target, value)])
        prefix_spawns.
  Proof.
    unfold full_rhs_context.
    intros root target value next prefix_reads
      prefix_sides prefix_spawns Hcontext result Hresult.
    destruct
      (Hcontext
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides :=
             (target, value) :: observed_sides result;
           observed_spawns := observed_spawns result |})
      as [root_result
        [Hroot [Hdirect [Hreads [Hsides Hspawns]]]]].
    - constructor. exact Hresult.
    - exists root_result.
      cbn in Hdirect, Hreads, Hsides, Hspawns.
      repeat split; try assumption.
      rewrite Hsides.
      rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma full_rhs_context_spawn :
    forall root target next prefix_reads
      prefix_sides prefix_spawns,
      full_rhs_context root (R.ConstraintSystem.Spawn target next)
        prefix_reads prefix_sides prefix_spawns ->
      full_rhs_context root next prefix_reads prefix_sides
        (prefix_spawns ++ [target]).
  Proof.
    unfold full_rhs_context.
    intros root target next prefix_reads
      prefix_sides prefix_spawns Hcontext result Hresult.
    destruct
      (Hcontext
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns :=
             target :: observed_spawns result |})
      as [root_result
        [Hroot [Hdirect [Hreads [Hsides Hspawns]]]]].
    - constructor. exact Hresult.
    - exists root_result.
      cbn in Hdirect, Hreads, Hsides, Hspawns.
      repeat split; try assumption.
      rewrite Hspawns.
      rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma invariant_trace_observes :
    forall st body direct reads sides,
      Inv.rhs_trace st body direct reads sides ->
      exists result,
        trace_observes body result /\
        observed_direct result = direct /\
        observed_reads result = reads /\
        observed_sides result = sides.
  Proof.
    intros st body direct reads sides Htrace.
    induction Htrace.
    - exists
        {| observed_direct := direct;
           observed_reads := [];
           observed_sides := [];
           observed_spawns := [] |}.
      split; [constructor | cbn; repeat split].
    - destruct IHHtrace as
        [result [Hresult [Hdirect [Hreads Hsides]]]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads :=
             (target, value) :: observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns := observed_spawns result |}.
      split.
      + constructor. exact Hresult.
      + cbn. rewrite Hdirect, Hreads, Hsides.
        repeat split.
    - destruct IHHtrace as
        [result [Hresult [Hdirect [Hreads Hsides]]]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides :=
             (target, value) :: observed_sides result;
           observed_spawns := observed_spawns result |}.
      split.
      + constructor. exact Hresult.
      + cbn. rewrite Hdirect, Hreads, Hsides.
        repeat split.
    - destruct IHHtrace as
        [result [Hresult [Hdirect [Hreads Hsides]]]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns :=
             target :: observed_spawns result |}.
      split.
      + constructor. exact Hresult.
      + cbn. rewrite Hdirect, Hreads, Hsides.
        repeat split.
  Qed.

  Lemma supported_trace_observes :
    forall supported body,
      Sem.rhs_supported supported body ->
      exists result, trace_observes body result.
  Proof.
    intros supported body Hsupported.
    induction Hsupported.
    - eexists. constructor.
    - destruct (H1 D.bottom) as [result Hresult].
      eexists. constructor. exact Hresult.
    - destruct IHHsupported as [result Hresult].
      eexists. constructor. exact Hresult.
    - destruct IHHsupported as [result Hresult].
      eexists. constructor. exact Hresult.
  Qed.

  Definition reads_are_bottom
    (result : observation) : Prop :=
    forall target value,
      List.In (target, value) (observed_reads result) ->
      value = D.bottom.

  Lemma supported_bottom_trace_observes :
    forall supported body,
      Sem.rhs_supported supported body ->
      exists result,
        trace_observes body result /\
        reads_are_bottom result.
  Proof.
    intros supported body Hsupported.
    induction Hsupported.
    - exists
        {| observed_direct := value;
           observed_reads := [];
           observed_sides := [];
           observed_spawns := [] |}.
      split; [constructor |].
      intros target read Hread. contradiction.
    - destruct (H1 D.bottom) as
        [result [Hresult Hbottom]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads :=
             (target, D.bottom) ::
             observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns := observed_spawns result |}.
      split.
      + constructor. exact Hresult.
      + intros observed value Hread.
        cbn in Hread.
        destruct Hread as [Hequal | Hread].
        * now inversion Hequal.
        * unfold reads_are_bottom in Hbottom.
          exact (Hbottom observed value Hread).
    - destruct IHHsupported as
        [result [Hresult Hbottom]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides :=
             (target, value) :: observed_sides result;
           observed_spawns := observed_spawns result |}.
      split;
        [constructor; exact Hresult | exact Hbottom].
    - destruct IHHsupported as
        [result [Hresult Hbottom]].
      exists
        {| observed_direct := observed_direct result;
           observed_reads := observed_reads result;
           observed_sides := observed_sides result;
           observed_spawns :=
             target :: observed_spawns result |}.
      split;
        [constructor; exact Hresult | exact Hbottom].
  Qed.



  Lemma full_rhs_context_bottom_completion :
    forall root current prefix_reads prefix_sides
      prefix_spawns supported,
      full_rhs_context root current
        prefix_reads prefix_sides prefix_spawns ->
      Sem.rhs_supported supported current ->
      exists suffix result,
        trace_observes current suffix /\
        reads_are_bottom suffix /\
        trace_observes root result /\
        observed_direct result =
          observed_direct suffix /\
        observed_reads result =
          prefix_reads ++ observed_reads suffix /\
        observed_sides result =
          prefix_sides ++ observed_sides suffix /\
        observed_spawns result =
          prefix_spawns ++ observed_spawns suffix.
  Proof.
    intros root current prefix_reads prefix_sides
      prefix_spawns supported Hcontext Hsupported.
    destruct
      (supported_bottom_trace_observes Hsupported)
      as [suffix [Hsuffix Hbottom]].
    destruct (Hcontext suffix Hsuffix) as
      [result
        [Hresult
          [Hdirect [Hreads [Hsides Hspawns]]]]].
    exists suffix, result.
    repeat split; assumption.
  Qed.

  Definition list_included {A : Type}
    (lower upper : list A) : Prop :=
    forall value,
      List.In value lower ->
      List.In value upper.

  Definition valued_events_le
    (lower upper : list (V.t * D.t)) : Prop :=
    forall target lower_value,
      List.In (target, lower_value) lower ->
      exists upper_value,
        List.In (target, upper_value) upper /\
        D.leq lower_value upper_value = true.

  (** Values of reads common to two traces are ordered.  Dependency
      monotonicity below separately requires every lower-trace dependency
      to occur in the upper trace. *)
  Definition common_read_values_le
    (lower upper : observation) : Prop :=
    forall target lower_value upper_value,
      List.In (target, lower_value) (observed_reads lower) ->
      List.In (target, upper_value) (observed_reads upper) ->
      D.leq lower_value upper_value = true.

  Definition read_values_below
    (reads : list (V.t * D.t))
    (upper : observation) : Prop :=
    forall target lower_value upper_value,
      List.In (target, lower_value) reads ->
      List.In (target, upper_value)
        (observed_reads upper) ->
      D.leq lower_value upper_value = true.

  Lemma bottom_completion_common_reads :
    forall prefix suffix lower upper,
      observed_reads lower =
        prefix ++ observed_reads suffix ->
      reads_are_bottom suffix ->
      read_values_below prefix upper ->
      common_read_values_le lower upper.
  Proof.
    intros prefix suffix lower upper
      Hreads Hbottom Hprefix
      target lower_value upper_value Hlower Hupper.
    rewrite Hreads in Hlower.
    apply List.in_app_or in Hlower.
    destruct Hlower as [Hlower | Hlower].
    - eapply Hprefix; eassumption.
    - unfold reads_are_bottom in Hbottom.
      rewrite (Hbottom target lower_value Hlower).
      apply DL.bottom_least.
  Qed.

  Record effects_le (lower upper : observation) : Prop := {
    direct_effect_le :
      D.leq
        (observed_direct lower)
        (observed_direct upper) = true;
    side_effects_le :
      valued_events_le
        (observed_sides lower)
        (observed_sides upper);
    spawn_effects_le :
      list_included
        (observed_spawns lower)
        (observed_spawns upper);
  }.

  Definition rhs_dependencies_monotone (body : R.ConstraintSystem.rhs) : Prop :=
    forall lower upper,
      trace_observes body lower ->
      trace_observes body upper ->
      common_read_values_le lower upper ->
      list_included
        (List.map fst (observed_reads lower))
        (List.map fst (observed_reads upper)).

  Definition rhs_effects_monotone (body : R.ConstraintSystem.rhs) : Prop :=
    forall lower upper,
      trace_observes body lower ->
      trace_observes body upper ->
      valued_events_le
        (observed_reads lower)
        (observed_reads upper) ->
      effects_le lower upper.

  Definition rhs_has_unique_side_targets (body : R.ConstraintSystem.rhs) : Prop :=
    forall result,
      trace_observes body result ->
      NoDup (List.map fst (observed_sides result)).

  Record monotonic_system (tf : R.ConstraintSystem.system) : Prop := {
    system_dependencies_monotone :
      forall owner, rhs_dependencies_monotone (tf owner);
    system_effects_monotone :
      forall owner, rhs_effects_monotone (tf owner);
    system_unique_side_targets :
      forall owner, rhs_has_unique_side_targets (tf owner);
  }.

  Record ordinary_monotonic_system (tf : R.ConstraintSystem.system) : Prop := {
    ordinary_dependencies_monotone :
      forall owner, rhs_dependencies_monotone (tf owner);
    ordinary_effects_monotone :
      forall owner, rhs_effects_monotone (tf owner);
    ordinary_has_no_side_effects :
      forall owner result,
        trace_observes (tf owner) result ->
        observed_sides result = [];
  }.

  Lemma ordinary_system_is_monotonic :
    forall tf,
      ordinary_monotonic_system tf ->
      monotonic_system tf.
  Proof.
    intros tf Hordinary.
    constructor.
    - exact (ordinary_dependencies_monotone Hordinary).
    - exact (ordinary_effects_monotone Hordinary).
    - intros owner result Htrace.
      rewrite (@ordinary_has_no_side_effects
        tf Hordinary owner result Htrace).
      constructor.
  Qed.

  Lemma dependency_order_gives_read_order :
    forall body lower upper,
      rhs_dependencies_monotone body ->
      trace_observes body lower ->
      trace_observes body upper ->
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
    destruct Hincluded as [[upper_target upper_value]
      [Hequal Hupper_read]].
    cbn in Hequal. subst upper_target.
    exists upper_value. split; [exact Hupper_read |].
    eapply Hvalues; eassumption.
  Qed.

  Lemma monotone_observations :
    forall body lower upper,
      rhs_dependencies_monotone body ->
      rhs_effects_monotone body ->
      trace_observes body lower ->
      trace_observes body upper ->
      common_read_values_le lower upper ->
      effects_le lower upper.
  Proof.
    intros body lower upper Hdependencies Heffects
      Hlower Hupper Hvalues.
    eapply Heffects; [exact Hlower |exact Hupper |].
    eapply dependency_order_gives_read_order; eassumption.
  Qed.

  Lemma current_get_in_upper_reads :
    forall root target next prefix_reads prefix_sides prefix_spawns supported upper,
      full_rhs_context root (R.ConstraintSystem.Get target next)
        prefix_reads prefix_sides prefix_spawns ->
      Sem.rhs_supported supported (R.ConstraintSystem.Get target next) ->
      rhs_dependencies_monotone root ->
      trace_observes root upper ->
      read_values_below prefix_reads upper ->
      exists upper_value,
        List.In (target, upper_value) (observed_reads upper).
  Proof.
    intros root target next prefix_reads prefix_sides prefix_spawns supported upper
      Hcontext Hsupported Hdependencies Hupper Hprefix.
    destruct (@full_rhs_context_bottom_completion
      root (R.ConstraintSystem.Get target next)
      prefix_reads prefix_sides prefix_spawns supported Hcontext Hsupported)
      as [suffix [lower
        [Hsuffix [Hbottom [Hlower [Hdirect [Hreads [Hsides Hspawns]]]]]]]].
    assert (Hcommon : common_read_values_le lower upper).
    { eapply bottom_completion_common_reads; eassumption. }
    pose proof (Hdependencies lower upper Hlower Hupper Hcommon)
      as Hincluded.
    assert (Htarget :
      List.In target (List.map fst (observed_reads lower))).
    { apply in_map_iff. inversion Hsuffix; subst.
      exists (target, value). split; [reflexivity |].
      rewrite Hreads. apply in_or_app. right. now left. }
    specialize (Hincluded target Htarget).
    apply in_map_iff in Hincluded.
    destruct Hincluded as [[observed upper_value] [Hequal Hin]].
    cbn in Hequal. subst observed. now exists upper_value.
  Qed.

  Lemma current_spawn_in_upper_spawns :
    forall root target next prefix_reads prefix_sides prefix_spawns
      supported upper,
      full_rhs_context root (R.ConstraintSystem.Spawn target next)
        prefix_reads prefix_sides prefix_spawns ->
      Sem.rhs_supported supported (R.ConstraintSystem.Spawn target next) ->
      rhs_dependencies_monotone root ->
      rhs_effects_monotone root ->
      trace_observes root upper ->
      read_values_below prefix_reads upper ->
      List.In target (observed_spawns upper).
  Proof.
    intros root target next prefix_reads prefix_sides prefix_spawns
      supported upper Hcontext Hsupported Hdependencies Heffects
      Hupper Hprefix.
    destruct (@full_rhs_context_bottom_completion
      root (R.ConstraintSystem.Spawn target next)
      prefix_reads prefix_sides prefix_spawns supported
      Hcontext Hsupported)
      as [suffix [lower
        [Hsuffix [Hbottom [Hlower
          [Hdirect [Hreads [Hsides Hspawns]]]]]]]].
    assert (Hcommon : common_read_values_le lower upper).
    { eapply bottom_completion_common_reads; eassumption. }
    pose proof (monotone_observations Hdependencies Heffects
      Hlower Hupper Hcommon) as Horder.
    apply (spawn_effects_le Horder).
    rewrite Hspawns. apply in_or_app. right.
    inversion Hsuffix; subst. now left.
  Qed.

  Lemma reachable_control_history :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      Total.control_history tf (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots c Hsteps.
    pose proof (@Total.invariant_steps tf roots
      (R.initial_config roots) c
      (@Total.initial_invariant tf roots) Hsteps) as Hinv.
    exact (Total.invariant_history Hinv).
  Qed.

  Lemma invariant_prefix_observes : forall st root current reads sides,
    Inv.rhs_context st root current reads sides ->
    forall suffix, trace_observes current suffix ->
    exists result, trace_observes root result /\
      observed_sides result = sides ++ observed_sides suffix.
  Proof.
    intros st root current reads sides Hprefix. induction Hprefix;
      intros suffix Hsuffix.
    - exists suffix. split; [exact Hsuffix |reflexivity].
    - destruct (IHHprefix suffix Hsuffix) as [result [Hresult Hsides]].
      exists {| observed_direct := observed_direct result;
                observed_reads := (target, value) :: observed_reads result;
                observed_sides := observed_sides result;
                observed_spawns := observed_spawns result |}.
      split; [constructor; exact Hresult |exact Hsides].
    - destruct (IHHprefix suffix Hsuffix) as [result [Hresult Hsides]].
      exists {| observed_direct := observed_direct result;
                observed_reads := observed_reads result;
                observed_sides := (target, raw) :: observed_sides result;
                observed_spawns := observed_spawns result |}.
      split; [constructor; exact Hresult |cbn; now rewrite Hsides].
    - destruct (IHHprefix suffix Hsuffix) as [result [Hresult Hsides]].
      exists {| observed_direct := observed_direct result;
                observed_reads := observed_reads result;
                observed_sides := observed_sides result;
                observed_spawns := target :: observed_spawns result |}.
      split; [constructor; exact Hresult |exact Hsides].
  Qed.

  Lemma ordinary_reachable_side_impossible :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr target raw next k,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Side target raw next) k |} ->
      False.
  Proof.
    intros tf roots finite st fr target raw next k Hordinary Hsteps.
    pose proof (@Total.reachable_config_supported tf roots finite
      {| R.cfg_state := st;
         R.cfg_control :=
           R.RunRhs fr (R.ConstraintSystem.Side target raw next) k |}
      Hsteps) as Hsupported.
    destruct Hsupported as [_ Hcontrol_supported].
    cbn in Hcontrol_supported.
    destruct Hcontrol_supported as [_ [Hbody_supported _]].
    destruct (supported_trace_observes Hbody_supported)
      as [suffix Hsuffix].
    pose proof (reachable_control_history Hsteps) as Hhistory.
    cbn in Hhistory.
    destruct Hhistory as
      [[_ [prefix_reads [prefix_effects
        [Hcontext [Hreads [Heffects Hframe]]]]]] Hcontinuation].
    destruct (invariant_prefix_observes Hcontext Hsuffix)
      as [result [Hresult Hsides]].
    pose proof (@ordinary_has_no_side_effects
      tf Hordinary (R.frame_owner fr) result Hresult) as Hnone.
    cbn in Hsides.
    rewrite Hnone in Hsides.
    inversion Hsuffix; subst. cbn in Hsides.
    destruct prefix_effects; discriminate.
  Qed.

  Definition set_has_no_members (set : S.t) : Prop :=
    forall variable, S.mem variable set = false.

  Definition state_has_no_side_data (st : R.state) : Prop :=
    R.contributions st = M.empty (M.t D.t) /\
    forall owner target,
      S.mem target (R.lookup_set (R.last_targets st) owner) = false.

  Definition frame_has_no_side_data (fr : R.frame) : Prop :=
    set_has_no_members (R.frame_previous_targets fr) /\
    set_has_no_members (R.frame_current_targets fr).

  Fixpoint continuation_has_no_side_data (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr _ _ rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDrain fr rest =>
        frame_has_no_side_data fr /\
        continuation_has_no_side_data rest
    | R.KDead fr _ pending rest =>
        frame_has_no_side_data fr /\
        pending = [] /\
        continuation_has_no_side_data rest
    end.

  Definition control_has_no_side_data (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode _ k | R.Return k =>
        continuation_has_no_side_data k
    | R.RunRhs fr _ k
    | R.RunCommit fr _ k
    | R.RunDrain fr k =>
        frame_has_no_side_data fr /\
        continuation_has_no_side_data k
    | R.RunDead fr _ pending k =>
        frame_has_no_side_data fr /\
        pending = [] /\
        continuation_has_no_side_data k
    end.

  Definition config_has_no_side_data (c : R.config) : Prop :=
    state_has_no_side_data (R.cfg_state c) /\
    control_has_no_side_data (R.cfg_control c).

  Lemma no_member_set_elements_nil :
    forall set,
      set_has_no_members set ->
      S.elements set = [].
  Proof.
    intros set Hempty.
    destruct (S.elements set) as [|head rest] eqn:Helements;
      [reflexivity |].
    assert (Hmem : S.mem head set = true).
    { apply SL.mem_spec. rewrite Helements. now left. }
    rewrite (Hempty head) in Hmem. discriminate.
  Qed.

  Lemma state_no_side_data_view :
    forall before after,
      R.contributions after = R.contributions before ->
      R.last_targets after = R.last_targets before ->
      state_has_no_side_data before ->
      state_has_no_side_data after.
  Proof.
    intros before after Hcontributions Htargets [Hempty Hlast].
    split.
    - now rewrite Hcontributions.
    - intros owner target. unfold R.lookup_set in *.
      now rewrite Htargets.
  Qed.

  Lemma fresh_frame_has_no_side_data :
    forall st owner phase,
      state_has_no_side_data st ->
      frame_has_no_side_data (R.fresh_frame st owner phase).
  Proof.
    intros st owner phase [_ Hlast]. split; cbn.
    - exact (Hlast owner).
    - intros variable. apply SL.empty_spec.
  Qed.

  Lemma materialize_has_no_side_data :
    forall st target,
      state_has_no_side_data st ->
      state_has_no_side_data (R.materialize st target).
  Proof.
    intros st target Hstate. unfold R.materialize.
    destruct (M.lookup (R.sigma st) target); [exact Hstate |].
    eapply state_no_side_data_view;
      [reflexivity |reflexivity |exact Hstate].
  Qed.

  Lemma with_readers_has_no_side_data :
    forall st readers,
      state_has_no_side_data st ->
      state_has_no_side_data (R.with_readers st readers).
  Proof.
    intros st readers Hstate.
    eapply state_no_side_data_view;
      [reflexivity |reflexivity |exact Hstate].
  Qed.

  Lemma promote_controlled_has_no_side_data :
    forall st target,
      state_has_no_side_data st ->
      state_has_no_side_data (R.promote_controlled st target).
  Proof.
    intros st target Hstate.
    eapply state_no_side_data_view;
      [reflexivity |reflexivity |exact Hstate].
  Qed.

  Lemma with_frame_read_has_no_side_data :
    forall fr minimum maximum,
      frame_has_no_side_data fr ->
      frame_has_no_side_data (R.with_frame_read fr minimum maximum).
  Proof.
    intros fr minimum maximum Hframe. exact Hframe.
  Qed.

  Lemma complete_get_has_no_side_data :
    forall st fr target next next_fr value,
      state_has_no_side_data st ->
      frame_has_no_side_data fr ->
      R.complete_get st fr target = (next, next_fr, value) ->
      state_has_no_side_data next /\
      frame_has_no_side_data next_fr.
  Proof.
    intros st fr target next next_fr value Hstate Hframe Hget.
    unfold R.complete_get in Hget.
    repeat match type of Hget with
    | context [if ?condition then _ else _] => destruct condition
    | context [match ?subject with _ => _ end] => destruct subject
    end; inversion Hget; subst; split.
    all: try now apply with_frame_read_has_no_side_data.
    all: apply materialize_has_no_side_data.
    all: apply with_readers_has_no_side_data.
    all: try apply promote_controlled_has_no_side_data.
    all: exact Hstate.
  Qed.

  Lemma set_value_has_no_side_data :
    forall st fr direct next next_fr,
      state_has_no_side_data st ->
      frame_has_no_side_data fr ->
      R.set_value st fr direct = (next, next_fr) ->
      state_has_no_side_data next /\
      frame_has_no_side_data next_fr.
  Proof.
    intros st fr direct next next_fr Hstate Hframe Hset.
    unfold R.set_value in Hset.
    repeat match type of Hset with
    | context [if ?condition then _ else _] => destruct condition
    | context [match ?subject with _ => _ end] => destruct subject
    end; inversion Hset; subst; split; try exact Hframe.
    all: eapply state_no_side_data_view; [reflexivity |reflexivity |exact Hstate].
  Qed.

  Lemma publish_targets_has_no_side_data :
    forall st fr,
      state_has_no_side_data st ->
      frame_has_no_side_data fr ->
      state_has_no_side_data (R.publish_targets st fr).
  Proof.
    intros st fr [Hempty Hlast] [_ Hcurrent]. split; cbn.
    - exact Hempty.
    - intros owner target. unfold R.lookup_set.
      destruct (V.eq_dec owner (R.frame_owner fr)) as [-> |Hneq].
      + rewrite ML.lookup_update_same. exact (Hcurrent target).
      + rewrite ML.lookup_update_other by exact Hneq.
        exact (Hlast owner target).
  Qed.

  Lemma ordinary_clean_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      config_has_no_side_data before ->
      Sem.step tf before after ->
      config_has_no_side_data after.
  Proof.
    intros tf roots finite [st control] after Hordinary Hreachable
      [Hstate Hcontrol] Hstep.
    unfold Sem.step in Hstep.
    destruct control as
      [|seeded |remaining |owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k].
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[head tail] |];
        try discriminate.
      inversion Hstep; subst. split; [exact Hstate |exact I].
    - destruct seeded as [|root rest]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst. now split.
      + assert (Hobserved : state_has_no_side_data (R.observe st root)).
        { cbn in Hstate, Hcontrol.
          unfold R.observe.
          destruct (R.Ranking.observe (R.ranking st) root).
          exact Hstate. }
        destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; subst; split; assumption.
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[head tail] |].
      + inversion Hstep; subst. now split.
      + inversion Hstep; subst. now split.
    - cbn -[R.materialize] in Hstep.
      inversion Hstep; subst. split.
      + unfold R.materialize.
        destruct (M.lookup (R.sigma st) owner); exact Hstate.
      + cbn. split.
        * apply fresh_frame_has_no_side_data.
          unfold R.materialize.
          destruct (M.lookup (R.sigma st) owner); exact Hstate.
        * exact Hcontrol.
    - destruct Hcontrol as [Hfr Hk]. destruct body.
      + cbn in Hstep. inversion Hstep; subst. split.
        * exact Hstate.
        * cbn. split; [exact Hfr |].
          split.
          -- destruct Features.eliminate_dead_sides.
             ++ apply no_member_set_elements_nil. exact (proj1 Hfr).
             ++ reflexivity.
          -- exact Hk.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st t) in *.
        assert (Hobserved : state_has_no_side_data observed).
        { subst observed. unfold R.observe.
          destruct (R.Ranking.observe (R.ranking st) t). exact Hstate. }
        destruct (andb (negb (R.is_materialized observed t))
          (R.rank_lt observed (R.frame_owner fr) t)).
        * inversion Hstep; subst. split; [exact Hobserved |].
          cbn. split; [exact Hfr |exact Hk].
        * set (base := if R.is_materialized observed t
            then observed else R.enqueue observed t) in *.
          assert (Hbase : state_has_no_side_data base).
          { subst base. destruct (R.is_materialized observed t);
              exact Hobserved. }
          destruct (R.complete_get base fr t)
            as [[next_st next_fr] value] eqn:Hget.
          inversion Hstep; subst.
          destruct (@complete_get_has_no_side_data
            base fr t next_st next_fr value Hbase Hfr Hget)
            as [Hnext Hnext_fr].
          split; [exact Hnext |]. cbn. now split.
      + exfalso. eapply ordinary_reachable_side_impossible; eauto.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st t) in *.
        assert (Hobserved : state_has_no_side_data observed).
        { subst observed. unfold R.observe.
          destruct (R.Ranking.observe (R.ranking st) t). exact Hstate. }
        destruct (R.is_materialized observed t).
        * inversion Hstep; subst. split; [exact Hobserved |].
          cbn. now split.
        * destruct (R.rank_lt observed (R.frame_owner fr) t).
          -- inversion Hstep; subst. split; [exact Hobserved |].
             cbn. now split.
          -- inversion Hstep; subst. split.
             ++ unfold R.materialize.
                destruct (M.lookup (R.sigma (R.enqueue observed t)) t);
                  exact Hobserved.
             ++ cbn. now split.
    - destruct Hcontrol as [Hfr [Hpending Hk]]. subst pending.
      cbn in Hstep. inversion Hstep; subst. split.
      + now apply publish_targets_has_no_side_data.
      + cbn. now split.
    - destruct Hcontrol as [Hfr Hk].
      cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
      inversion Hstep; subst.
      destruct (@set_value_has_no_side_data st fr direct next next_fr
        Hstate Hfr Hset) as [Hnext Hnext_fr].
      split; [exact Hnext |]. cbn. now split.
    - destruct Hcontrol as [Hfr Hk].
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      + destruct (V.eq_dec next (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
            try discriminate.
          inversion Hstep; subst. split; [exact Hstate |].
          cbn. split.
          -- apply fresh_frame_has_no_side_data. exact Hstate.
          -- exact Hk.
        * destruct (R.rank_lt st (R.frame_owner fr) next).
          -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
               try discriminate.
             inversion Hstep; subst. split; [exact Hstate |].
             cbn. now split.
          -- inversion Hstep; subst. split.
             ++ unfold R.reset_registered_cells.
                destruct Features.restart_side_phases; exact Hstate.
             ++ exact Hk.
      + inversion Hstep; subst. split.
        * unfold R.reset_registered_cells.
          destruct Features.restart_side_phases; exact Hstate.
        * exact Hk.
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hcontrol, Hstep.
      + inversion Hstep; subst. now split.
      + inversion Hstep; subst. now split.
      + destruct Hcontrol as [Hfr Hrest].
        destruct (R.complete_get st fr target)
          as [[next_st next_fr] value] eqn:Hget.
        inversion Hstep; subst.
        destruct (@complete_get_has_no_side_data
          st fr target next_st next_fr value Hstate Hfr Hget)
          as [Hnext Hnext_fr].
        split; [exact Hnext |]. cbn. now split.
      + destruct Hcontrol as [Hfr Hrest].
        inversion Hstep; subst. split; [exact Hstate |].
        cbn. now split.
      + destruct Hcontrol as [Hfr Hrest].
        inversion Hstep; subst. split; [exact Hstate |].
        cbn. now split.
      + destruct Hcontrol as [Hfr [Hpending Hrest]]. subst pending.
        inversion Hstep; subst. split; [exact Hstate |].
        cbn. split; [exact Hfr |].
        split; [reflexivity |exact Hrest].
      + destruct Hcontrol as [Hfr Hrest].
        inversion Hstep; subst. split; [exact Hstate |].
        cbn. now split.
  Qed.

  Theorem ordinary_reachable_clean :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      forall c,
        Sem.steps tf (R.initial_config roots) c ->
        config_has_no_side_data c.
  Proof.
    intros tf roots finite Hordinary final Hsteps.
    assert (Hpreserve : forall first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      config_has_no_side_data first ->
      config_has_no_side_data last).
    {
      intros first last Hreachable Hrun.
      revert Hreachable.
      induction Hrun as [c | first next last Hstep Hrun IH].
      - intros _ Hclean. exact Hclean.
      - intros Hreachable Hclean. apply IH.
        + eapply Total.Termination.steps_transitive.
          * exact Hreachable.
          * econstructor; [exact Hstep |constructor].
        + eapply ordinary_clean_step; eauto.
    }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - split; cbn.
      + split; [reflexivity |].
        intros owner target. unfold R.lookup_set.
        rewrite ML.lookup_empty. apply SL.empty_spec.
      + exact I.
  Qed.

  Lemma ordinary_reachable_aggregate_bottom :
    forall tf roots (finite : Sem.finite_system tf roots) c target,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) c ->
      R.aggregate (R.cfg_state c) target = D.bottom.
  Proof.
    intros tf roots finite c target Hordinary Hreachable.
    pose proof (@ordinary_reachable_clean tf roots finite Hordinary c
      Hreachable) as [[Hempty _] _].
    unfold R.aggregate, R.lookup_map.
    rewrite Hempty, ML.lookup_empty, ML.values_empty. reflexivity.
  Qed.

  Definition observation_reads_cover_state
    (st : R.state) (result : observation) : Prop :=
    forall target value,
      List.In (target, value) (observed_reads result) ->
      Sem.solved st target /\
      D.leq (R.sigma_value st target) value = true.

  Definition observation_spawns_cover_state
    (st : R.state) (result : observation) : Prop :=
    forall target,
      List.In target (observed_spawns result) ->
      Sem.solved st target.

  Definition state_values_le (lower upper : R.state) : Prop :=
    forall variable,
      Sem.solved upper variable ->
      Sem.solved lower variable /\
      D.leq (R.sigma_value lower variable)
        (R.sigma_value upper variable) = true.

  Lemma observation_reads_cover_decrease :
    forall lower upper result,
      state_values_le lower upper ->
      observation_reads_cover_state upper result ->
      observation_reads_cover_state lower result.
  Proof.
    intros lower upper result Hstates Hcover target value Hin.
    destruct (Hcover target value Hin) as [Hsolved Hvalue].
    destruct (Hstates target Hsolved) as [Hsolved' Hdecrease].
    split; [exact Hsolved' |]. eapply DL.leq_trans; eassumption.
  Qed.

  Lemma observation_spawns_cover_decrease :
    forall lower upper result,
      state_values_le lower upper ->
      observation_spawns_cover_state upper result ->
      observation_spawns_cover_state lower result.
  Proof.
    intros lower upper result Hstates Hcover target Hin.
    exact (proj1 (Hstates target (Hcover target Hin))).
  Qed.

  Definition upper_observation
    (tf : R.ConstraintSystem.system) (st : R.state)
    (owner : V.t) (upper : observation) : Prop :=
    trace_observes (tf owner) upper /\
    D.leq (observed_direct upper) (R.sigma_value st owner) = true /\
    observation_reads_cover_state st upper /\
    observation_spawns_cover_state st upper.

  Definition reads_cover_state
    (st : R.state) (reads : list (V.t * D.t)) : Prop :=
    forall target value,
      List.In (target, value) reads ->
      Sem.solved st target /\
      D.leq (R.sigma_value st target) value = true.

  Definition spawns_cover_state
    (st : R.state) (spawns : list V.t) : Prop :=
    forall target, List.In target spawns -> Sem.solved st target.

  Definition wave_evaluation
    (tf : R.ConstraintSystem.system) (st : R.state)
    (fr : R.frame) (current : R.ConstraintSystem.rhs) : Prop :=
    exists upper prefix_reads prefix_sides prefix_spawns,
      trace_observes (tf (R.frame_owner fr)) upper /\
      full_rhs_context (tf (R.frame_owner fr)) current
        prefix_reads prefix_sides prefix_spawns /\
      read_values_below prefix_reads upper /\
      D.leq (observed_direct upper)
        (R.sigma_value st (R.frame_owner fr)) = true /\
      observation_reads_cover_state st upper /\
      observation_spawns_cover_state st upper /\
      reads_cover_state st prefix_reads /\
      spawns_cover_state st prefix_spawns.

  Definition wave_completed
    (tf : R.ConstraintSystem.system) (st : R.state)
    (fr : R.frame) (direct : D.t) : Prop :=
    exists current upper,
      trace_observes (tf (R.frame_owner fr)) current /\
      trace_observes (tf (R.frame_owner fr)) upper /\
      observed_direct current = direct /\
      common_read_values_le current upper /\
      D.leq (observed_direct upper)
        (R.sigma_value st (R.frame_owner fr)) = true /\
      observation_reads_cover_state st current /\
      observation_spawns_cover_state st current.

  Lemma initial_wave_evaluation :
    forall tf st fr upper,
      upper_observation tf st (R.frame_owner fr) upper ->
      wave_evaluation tf st fr (tf (R.frame_owner fr)).
  Proof.
    intros tf st fr upper [Hupper [Hdirect [Hreads Hspawns]]].
    exists upper, [], [], []. split; [exact Hupper |].
    split; [apply initial_full_rhs_context |].
    split.
    - intros target lower upper_value Hin. contradiction.
    - split; [exact Hdirect |]. split; [exact Hreads |].
      split; [exact Hspawns |]. split.
      + intros target value Hin. contradiction.
      + intros target Hin. contradiction.
  Qed.

  Lemma complete_get_solved_view :
    forall st fr target st' fr' value,
      Sem.solved st target ->
      R.complete_get st fr target = (st', fr', value) ->
      R.sigma st' = R.sigma st /\
      R.frame_owner fr' = R.frame_owner fr /\
      value = R.sigma_value st target.
  Proof.
    intros st fr target st' fr' value [found Hfound] Hget.
    unfold R.complete_get in Hget.
    repeat match type of Hget with
    | context [if ?condition then _ else _] => destruct condition eqn:?
    | context [match ?choice with Some _ => _ | None => _ end] =>
        destruct choice eqn:?
    end.
    all: unfold R.materialize in Hget; cbn in Hget.
    all: rewrite Hfound in Hget; inversion Hget; subst; cbn.
    all: repeat split; reflexivity.
  Qed.


  Lemma wave_evaluation_get :
    forall tf supported st fr target next st' fr' value,
      rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
      Sem.rhs_supported supported (R.ConstraintSystem.Get target next) ->
      wave_evaluation tf st fr (R.ConstraintSystem.Get target next) ->
      R.complete_get st fr target = (st', fr', value) ->
      wave_evaluation tf st' fr' (next value).
  Proof.
    intros tf supported st fr target next st' fr' value
      Hdependencies Hsupported
      [upper [prefix_reads [prefix_sides [prefix_spawns
        [Hupper [Hcontext [Hprefix [Hdirect
          [Hupper_reads [Hupper_spawns [Hreads Hspawns]]]]]]]]]]]
      Hget.
    destruct (@current_get_in_upper_reads
      (tf (R.frame_owner fr)) target next prefix_reads prefix_sides prefix_spawns
      supported upper Hcontext Hsupported Hdependencies Hupper Hprefix)
      as [upper_value Hupper_read].
    destruct (Hupper_reads target upper_value Hupper_read)
      as [Htarget_solved Htarget_below].
    destruct (@complete_get_solved_view st fr target st' fr' value
      Htarget_solved Hget) as [Hsigma [Howner Hvalue]].
    exists upper, (prefix_reads ++ [(target, value)]),
      prefix_sides, prefix_spawns. split.
    - now rewrite Howner.
    - split; [rewrite Howner; now apply full_rhs_context_get |].
      split.
      + intros observed lower_value observed_upper Hlower Hupper_observed.
        apply List.in_app_or in Hlower. destruct Hlower as [Hlower |Hlower].
        * eapply Hprefix; eassumption.
        * cbn in Hlower. destruct Hlower as [Hequal |Hfalse];
            [|contradiction]. inversion Hequal; subst.
          exact (proj2 (Hupper_reads observed observed_upper Hupper_observed)).
      + split.
        * unfold R.sigma_value in *. now rewrite Hsigma, Howner.
        * split.
          -- intros observed observed_value Hin.
             destruct (Hupper_reads observed observed_value Hin)
               as [[found Hfound] Hbelow]. split.
             ++ exists found. unfold Sem.solved in *; now rewrite Hsigma.
             ++ unfold R.sigma_value in *; now rewrite Hsigma.
          -- split.
             ++ intros observed Hin.
                destruct (Hupper_spawns observed Hin) as [found Hfound].
                exists found. unfold Sem.solved in *; now rewrite Hsigma.
             ++ split.
                ** intros observed observed_value Hin.
                   apply List.in_app_or in Hin. destruct Hin as [Hin |Hin].
                   --- destruct (Hreads _ _ Hin) as [[found Hfound] Hbelow].
                       split.
                       +++ exists found. unfold Sem.solved in *;
                             now rewrite Hsigma.
                       +++ unfold R.sigma_value in *; now rewrite Hsigma.
                   --- cbn in Hin. destruct Hin as [Hequal |Hfalse];
                         [|contradiction]. inversion Hequal; subst. split.
                       +++ destruct Htarget_solved as [found Hfound].
                           exists found. unfold Sem.solved in *;
                             now rewrite Hsigma.
                       +++ unfold R.sigma_value. rewrite Hsigma.
                           apply DL.leq_refl.
                ** intros observed Hin.
                   destruct (Hspawns observed Hin) as [found Hfound].
                   exists found. unfold Sem.solved in *; now rewrite Hsigma.
  Qed.

  Lemma wave_evaluation_get_target_solved :
    forall tf supported st fr target next,
      rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
      Sem.rhs_supported supported (R.ConstraintSystem.Get target next) ->
      wave_evaluation tf st fr (R.ConstraintSystem.Get target next) ->
      Sem.solved st target.
  Proof.
    intros tf supported st fr target next Hdependencies Hsupported
      [upper [prefix_reads [prefix_sides [prefix_spawns
        [Hupper [Hcontext [Hprefix [Hdirect
          [Hupper_reads [Hupper_spawns [Hreads Hspawns]]]]]]]]]]].
    destruct (@current_get_in_upper_reads
      (tf (R.frame_owner fr)) target next prefix_reads prefix_sides prefix_spawns
      supported upper Hcontext Hsupported Hdependencies Hupper Hprefix)
      as [upper_value Hupper_read].
    exact (proj1 (Hupper_reads target upper_value Hupper_read)).
  Qed.

  Lemma wave_evaluation_spawn_target_solved :
    forall tf supported st fr target next,
      rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
      rhs_effects_monotone (tf (R.frame_owner fr)) ->
      Sem.rhs_supported supported (R.ConstraintSystem.Spawn target next) ->
      wave_evaluation tf st fr (R.ConstraintSystem.Spawn target next) ->
      Sem.solved st target.
  Proof.
    intros tf supported st fr target next Hdependencies Heffects Hsupported
      [upper [prefix_reads [prefix_sides [prefix_spawns
        [Hupper [Hcontext [Hprefix [Hdirect
          [Hupper_reads [Hupper_spawns [Hreads Hspawns]]]]]]]]]]].
    apply Hupper_spawns.
    eapply current_spawn_in_upper_spawns; eassumption.
  Qed.

  Lemma wave_evaluation_spawn :
    forall tf st fr target next,
      wave_evaluation tf st fr (R.ConstraintSystem.Spawn target next) ->
      Sem.solved st target ->
      wave_evaluation tf st fr next.
  Proof.
    intros tf st fr target next
      [upper [prefix_reads [prefix_sides [prefix_spawns
        [Hupper [Hcontext [Hprefix [Hdirect
          [Hreads [Hspawns [Hprefix_reads Hprefix_spawns]]]]]]]]]]]
      Htarget.
    exists upper, prefix_reads, prefix_sides, (prefix_spawns ++ [target]).
    split; [exact Hupper |].
    split; [now apply full_rhs_context_spawn |].
    split; [exact Hprefix |]. split; [exact Hdirect |].
    split; [exact Hreads |]. split; [exact Hspawns |].
    split; [exact Hprefix_reads |].
    intros observed Hin. apply List.in_app_or in Hin.
    destruct Hin as [Hin |Hin]; [now apply Hprefix_spawns |].
    cbn in Hin. destruct Hin as [-> |Hfalse];
      [exact Htarget |contradiction].
  Qed.

  Lemma wave_evaluation_completed :
    forall tf st fr direct,
      wave_evaluation tf st fr (R.ConstraintSystem.Ret direct) ->
      wave_completed tf st fr direct.
  Proof.
    intros tf st fr direct
      [upper [prefix_reads [prefix_sides [prefix_spawns
        [Hupper [Hcontext [Hprefix [Hdirect
          [Hupper_reads [Hupper_spawns [Hreads Hspawns]]]]]]]]]]].
    destruct (Hcontext
      {| observed_direct := direct; observed_reads := [];
         observed_sides := []; observed_spawns := [] |}) as
      [current [Hcurrent [Hcurrent_direct
        [Hcurrent_reads [Hcurrent_sides Hcurrent_spawns]]]]];
      [constructor |].
    exists current, upper. split; [exact Hcurrent |].
    split; [exact Hupper |]. split; [exact Hcurrent_direct |].
    split.
    - intros target lower_value upper_value Hlower Hupper_read.
      rewrite Hcurrent_reads in Hlower. apply List.in_app_or in Hlower.
      destruct Hlower as [Hlower |Hlower];
        [eapply Hprefix; eassumption |contradiction].
    - split; [exact Hdirect |]. split.
      + intros target value Hin. rewrite Hcurrent_reads in Hin.
        apply List.in_app_or in Hin. destruct Hin as [Hin |Hin];
          [now apply Hreads |contradiction].
      + intros target Hin. rewrite Hcurrent_spawns in Hin.
        apply List.in_app_or in Hin. destruct Hin as [Hin |Hin];
          [now apply Hspawns |contradiction].
  Qed.

  Lemma ordinary_wave_completed_decreases :
    forall tf st fr direct,
      ordinary_monotonic_system tf ->
      wave_completed tf st fr direct ->
      R.aggregate st (R.frame_owner fr) = D.bottom ->
      D.leq (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr)) = true.
  Proof.
    intros tf st fr direct Hordinary
      [current [upper [Hcurrent [Hupper [Hcurrent_direct
        [Hreads [Hupper_direct [Hcover Hspawns]]]]]]]] Haggregate.
    pose proof (monotone_observations
      (ordinary_dependencies_monotone Hordinary (R.frame_owner fr))
      (ordinary_effects_monotone Hordinary (R.frame_owner fr))
      Hcurrent Hupper Hreads) as Heffects.
    rewrite Haggregate. apply DL.join_least.
    - rewrite <- Hcurrent_direct. eapply DL.leq_trans.
      + exact (direct_effect_le Heffects).
      + exact Hupper_direct.
    - apply DL.bottom_least.
  Qed.

  Lemma upper_observation_decrease_other :
    forall tf lower upper owner result,
      state_values_le lower upper ->
      R.sigma_value lower owner = R.sigma_value upper owner ->
      upper_observation tf upper owner result ->
      upper_observation tf lower owner result.
  Proof.
    intros tf lower upper owner result Hstates Howner
      [Htrace [Hdirect [Hreads Hspawns]]].
    split; [exact Htrace |]. split; [now rewrite Howner |]. split.
    - eapply observation_reads_cover_decrease; eassumption.
    - eapply observation_spawns_cover_decrease; eassumption.
  Qed.

  Lemma set_value_state_values_le :
    forall st fr direct st' fr',
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      state_values_le st' st.
  Proof.
    intros st fr direct st' fr' Hset Howner variable Hsolved.
    split.
    - eapply Inv.set_value_solved; eassumption.
    - destruct (V.eq_dec variable (R.frame_owner fr)) as [-> |Hneq].
      + exact Howner.
      + rewrite (@Total.set_value_sigma_value_other_correctness
          st fr direct st' fr' variable Hset Hneq).
        apply DL.leq_refl.
  Qed.

  Lemma safe_set_value_owner_decreases :
    forall st fr direct st' fr',
      U.avoids_fallback (R.frame_phase fr) ->
      D.leq (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true.
  Proof.
    intros st fr direct st' fr' Hsafe Hcandidate Hset.
    unfold R.set_value in Hset.
    set (owner := R.frame_owner fr) in *.
    set (candidate := D.join direct (R.aggregate st owner)) in *.
    set (old := R.sigma_value st owner) in *.
    destruct (R.equivalent candidate old) eqn:Hequivalent.
    - inversion Hset; subst. apply DL.leq_refl.
    - destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
      + destruct (R.frame_phase fr) eqn:Hphase.
        * unfold U.update in Hset. rewrite Hcandidate in Hset. cbn in Hset.
          destruct (R.equivalent (WN.narrow old candidate) old);
            inversion Hset; subst.
          -- apply DL.leq_refl.
          -- rewrite Inv.sigma_value_with_readers.
             rewrite Inv.sigma_value_enqueue_all.
             rewrite Inv.sigma_value_update_same.
             now apply WNL.narrow_upper.
        * unfold U.update in Hset. rewrite Hcandidate in Hset. cbn in Hset.
          destruct (R.equivalent (WN.narrow old candidate) old);
            inversion Hset; subst.
          -- apply DL.leq_refl.
          -- rewrite Inv.sigma_value_with_readers.
             rewrite Inv.sigma_value_enqueue_all.
             rewrite Inv.sigma_value_update_same.
             now apply WNL.narrow_upper.
        * exfalso. apply Hsafe. reflexivity.
      + cbn in Hset. rewrite Hequivalent in Hset.
        inversion Hset; subst.
        rewrite Inv.sigma_value_with_readers.
        rewrite Inv.sigma_value_enqueue_all.
        rewrite Inv.sigma_value_update_same.
        exact Hcandidate.
  Qed.

  Lemma wave_completed_set_value_upper :
    forall tf st fr direct st' fr',
      wave_completed tf st fr direct ->
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      exists current,
        upper_observation tf st' (R.frame_owner fr) current.
  Proof.
    intros tf st fr direct st' fr'
      [current [upper [Hcurrent [Hupper [Hcurrent_direct
        [Hreads [Hupper_direct
          [Hcurrent_reads Hcurrent_spawns]]]]]]]] Hset Hdecrease.
    pose proof (@set_value_state_values_le
      st fr direct st' fr' Hset Hdecrease) as Hstates.
    exists current. split; [exact Hcurrent |]. split.
    - rewrite Hcurrent_direct.
      eapply Inv.set_value_direct_sound; eassumption.
    - split.
      + eapply observation_reads_cover_decrease; eassumption.
      + eapply observation_spawns_cover_decrease; eassumption.
  Qed.

  Lemma active_solved_or_start_from_history :
    forall tf st control variable,
      Inv.control_history tf st control ->
      Inv.control_active variable control ->
      Sem.solved st variable \/
      exists owner k,
        control = R.StartEpisode owner k /\
        variable = owner.
  Proof.
    intros tf st control variable Hhistory Hactive.
    destruct control; cbn in Hactive, Hhistory.
    - contradiction.
    - contradiction.
    - contradiction.
    - destruct Hactive as [-> | Hactive].
      + right. exists t, c. now split.
      + pose proof (@Inv.continuation_history_active_solved tf
          (R.materialize st t) c variable Hhistory Hactive) as Hsolved.
        destruct (@Inv.materialize_solved_origin_correctness st t variable Hsolved)
          as [Hsolved0 | ->].
        * now left.
        * right. exists t, c. now split.
    - destruct Hhistory as [Hframe Hk].
      destruct Hactive as [-> | Hactive].
      + left. exact (proj1 Hframe).
      + left. eapply Inv.continuation_history_active_solved; eassumption.
    - destruct Hhistory as [Hframe Hk].
      destruct Hactive as [-> | Hactive].
      + left. exact (proj1 Hframe).
      + left. eapply Inv.continuation_history_active_solved; eassumption.
    - destruct Hhistory as [Hframe Hk].
      destruct Hactive as [-> | Hactive].
      + left. exact (proj1 Hframe).
      + left. eapply Inv.continuation_history_active_solved; eassumption.
    - destruct Hhistory as [Hsummary Hhistory].
      left. eapply Inv.continuation_history_active_solved; eassumption.
    - left. eapply Inv.continuation_history_active_solved; eassumption.
  Qed.

  Lemma active_step_solved_from_history :
    forall tf before after variable,
      Inv.control_history tf
        (R.cfg_state before) (R.cfg_control before) ->
      Inv.control_active variable (R.cfg_control before) ->
      Sem.step tf before after ->
      Sem.solved (R.cfg_state after) variable.
  Proof.
    intros tf [st control] after variable Hhistory Hactive Hstep.
    destruct (@active_solved_or_start_from_history
      tf st control variable Hhistory Hactive)
      as [Hsolved | [owner [k [Hcontrol Hvariable]]]].
    - unfold Sem.step in Hstep.
      exact (@Inv.next_config_preserves_solved tf
        {| R.cfg_state := st; R.cfg_control := control |}
        after variable Hsolved Hstep).
    - subst control variable. unfold Sem.step in Hstep.
      cbn in Hstep. inversion Hstep; subst. cbn.
      apply Inv.materialize_solved_correctness.
  Qed.

  Definition spawn_live
    (st : R.state) (control : R.control) (target : V.t) : Prop :=
    Sem.solved st target \/ Inv.control_active target control.

  Definition aligned_evaluation_history
    (tf : R.ConstraintSystem.system) (st : R.state) (control : R.control)
    (fr : R.frame) (current : R.ConstraintSystem.rhs) : Prop :=
    Sem.solved st (R.frame_owner fr) /\
    exists prefix_reads prefix_sides prefix_spawns,
      full_rhs_context (tf (R.frame_owner fr)) current
        prefix_reads prefix_sides prefix_spawns /\
      Inv.guarded_reads st (R.frame_owner fr) prefix_reads /\
      (forall target,
        List.In target prefix_spawns -> spawn_live st control target).

  Definition aligned_completed_history
    (tf : R.ConstraintSystem.system) (st : R.state) (control : R.control)
    (fr : R.frame) (direct : D.t) : Prop :=
    Sem.solved st (R.frame_owner fr) /\
    exists result,
      trace_observes (tf (R.frame_owner fr)) result /\
      observed_direct result = direct /\
      Inv.guarded_reads st (R.frame_owner fr) (observed_reads result) /\
      (forall target,
        List.In target (observed_spawns result) ->
        spawn_live st control target).

  Definition aligned_summary_history
    (tf : R.ConstraintSystem.system) (st : R.state) (control : R.control)
    (fr : R.frame) : Prop :=
    Sem.solved st (R.frame_owner fr) /\
    exists result,
      trace_observes (tf (R.frame_owner fr)) result /\
      Inv.guarded_reads st (R.frame_owner fr) (observed_reads result) /\
      D.leq (observed_direct result)
        (R.sigma_value st (R.frame_owner fr)) = true /\
      (forall target,
        List.In target (observed_spawns result) ->
        spawn_live st control target).

  Fixpoint aligned_continuation_history
    (tf : R.ConstraintSystem.system) (st : R.state) (control : R.control)
    (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr target next rest =>
        aligned_evaluation_history tf st control fr
          (R.ConstraintSystem.Get target next) /\
        aligned_continuation_history tf st control rest
    | R.KAfterSide fr next rest
    | R.KAfterSpawn fr next rest =>
        aligned_evaluation_history tf st control fr next /\
        aligned_continuation_history tf st control rest
    | R.KDead fr direct _ rest =>
        aligned_completed_history tf st control fr direct /\
        aligned_continuation_history tf st control rest
    | R.KDrain fr rest =>
        aligned_summary_history tf st control fr /\
        aligned_continuation_history tf st control rest
    end.

  Definition aligned_control_history
    (tf : R.ConstraintSystem.system) (st : R.state)
    (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode _ k | R.Return k =>
        aligned_continuation_history tf st control k
    | R.RunRhs fr current k =>
        aligned_evaluation_history tf st control fr current /\
        aligned_continuation_history tf st control k
    | R.RunDead fr direct _ k | R.RunCommit fr direct k =>
        aligned_completed_history tf st control fr direct /\
        aligned_continuation_history tf st control k
    | R.RunDrain fr k =>
        aligned_summary_history tf st control fr /\
        aligned_continuation_history tf st control k
    end.

  Lemma spawn_live_after_step_from_history :
    forall tf before after target,
      Inv.control_history tf
        (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      spawn_live (R.cfg_state before) (R.cfg_control before) target ->
      Sem.solved (R.cfg_state after) target.
  Proof.
    intros tf before after target Hhistory Hstep [Hsolved | Hactive].
    - unfold Sem.step in Hstep.
      eapply Inv.next_config_preserves_solved; eassumption.
    - eapply active_step_solved_from_history; eassumption.
  Qed.

  Lemma is_materialized_solved :
    forall st target,
      R.is_materialized st target = true -> Sem.solved st target.
  Proof.
    intros st target Hmaterialized.
    unfold R.is_materialized in Hmaterialized.
    destruct (M.lookup (R.sigma st) target) as [value |] eqn:Hlookup.
    - now exists value.
    - discriminate.
  Qed.

  Lemma solved_is_materialized :
    forall st target,
      Sem.solved st target ->
      R.is_materialized st target = true.
  Proof.
    intros st target [value Hlookup].
    unfold R.is_materialized. now rewrite Hlookup.
  Qed.

  Lemma aligned_initial_evaluation :
    forall tf st control fr,
      Sem.solved st (R.frame_owner fr) ->
      aligned_evaluation_history tf st control fr
        (tf (R.frame_owner fr)).
  Proof.
    intros tf st control fr Hsolved. split; [exact Hsolved |].
    exists [], [], []. split; [apply initial_full_rhs_context |].
    split.
    - intros target value Hin. contradiction.
    - intros target Hin. contradiction.
  Qed.

  Lemma aligned_evaluation_completed :
    forall tf st control fr direct,
      aligned_evaluation_history tf st control fr
        (R.ConstraintSystem.Ret direct) ->
      aligned_completed_history tf st control fr direct.
  Proof.
    intros tf st control fr direct
      [Hsolved [reads [sides [spawns [Hcontext [Hreads Hspawns]]]]]].
    split; [exact Hsolved |].
    destruct (Hcontext
      {| observed_direct := direct; observed_reads := [];
         observed_sides := []; observed_spawns := [] |})
      as [result [Hresult [Hdirect [Hresult_reads
        [Hresult_sides Hresult_spawns]]]]]; [constructor |].
    exists result. split; [exact Hresult |]. split; [exact Hdirect |].
    split.
    - intros target value Hin. rewrite Hresult_reads in Hin.
      apply List.in_app_or in Hin. destruct Hin; [now apply Hreads |contradiction].
    - intros target Hin. rewrite Hresult_spawns in Hin.
      apply List.in_app_or in Hin. destruct Hin; [now apply Hspawns |contradiction].
  Qed.

  Lemma aligned_evaluation_spawn :
    forall tf st control fr target next,
      aligned_evaluation_history tf st control fr
        (R.ConstraintSystem.Spawn target next) ->
      spawn_live st control target ->
      aligned_evaluation_history tf st control fr next.
  Proof.
    intros tf st control fr target next
      [Hsolved [reads [sides [spawns [Hcontext [Hreads Hspawns]]]]]]
      Htarget. split; [exact Hsolved |].
    exists reads, sides, (spawns ++ [target]).
    split; [now apply full_rhs_context_spawn |]. split; [exact Hreads |].
    intros observed Hin. apply List.in_app_or in Hin.
    destruct Hin as [Hin | [-> | Hfalse]].
    - now apply Hspawns.
    - exact Htarget.
    - contradiction.
  Qed.

  Lemma aligned_evaluation_get :
    forall tf st control fr target next st' fr' value control',
      R.complete_get st fr target = (st', fr', value) ->
      Sem.solved st' (R.frame_owner fr') ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_evaluation_history tf st control fr
        (R.ConstraintSystem.Get target next) ->
      aligned_evaluation_history tf st' control' fr' (next value).
  Proof.
    intros tf st control fr target next st' fr' value control'
      Hget Hsolved Hlive
      [_ [reads [sides [spawns [Hcontext [Hreads Hspawns]]]]]].
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    set (read_state := Inv.add_reader base target (R.frame_owner fr)) in *.
    fold Inv.add_reader in Hget.
    inversion Hget; subst st' fr' value; clear Hget.
    assert (Hbase : Inv.guarded_reads base (R.frame_owner fr) reads).
    { subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
      - exact Hreads.
      - eapply Inv.guarded_reads_same_view.
        + apply Inv.promote_controlled_same_solver_view.
        + exact Hreads. }
    assert (Hread : Inv.guarded_reads read_state
      (R.frame_owner fr) reads).
    { subst read_state. now apply Inv.guarded_reads_add_reader. }
    assert (Hfinal : Inv.guarded_reads (R.materialize read_state target)
      (R.frame_owner fr) reads).
    { now apply Inv.guarded_reads_materialize. }
    split; [exact Hsolved |].
    exists (reads ++ [(target,
      R.sigma_value (R.materialize read_state target) target)]), sides, spawns.
    split; [now apply full_rhs_context_get |]. split.
    - intros observed seen Hin. apply List.in_app_or in Hin.
      destruct Hin as [Hin | [Hequal | Hfalse]].
      + now apply Hfinal.
      + inversion Hequal; subst. split.
        * apply Inv.materialize_solved_correctness.
        * split.
          -- left. apply Inv.add_reader_registered_after_materialize.
          -- left. reflexivity.
      + contradiction.
    - intros observed Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_completed_set_value_summary :
    forall tf st before_control st' after_control fr fr' direct,
      R.set_value st fr direct = (st', fr') ->
      (forall observed,
        spawn_live st before_control observed ->
        spawn_live st' after_control observed) ->
      aligned_completed_history tf st before_control fr direct ->
      aligned_summary_history tf st' after_control fr'.
  Proof.
    intros tf st before_control st' after_control fr fr' direct
      Hset Hlive
      [Hsolved [result [Hresult [Hdirect [Hreads Hspawns]]]]].
    assert (Howner : R.frame_owner fr' = R.frame_owner fr).
    { eapply Inv.set_value_frame_owner; eassumption. }
    split.
    - rewrite Howner. eapply Inv.set_value_solved; eassumption.
    - exists result. rewrite Howner.
      split; [exact Hresult |].
      split; [eapply Inv.guarded_reads_set_value; eassumption |].
      split.
      + rewrite Hdirect. eapply Inv.set_value_direct_sound; eassumption.
      + intros target Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_evaluation_transport :
    forall tf st control st' control' fr current,
      (forall owner, Sem.solved st owner -> Sem.solved st' owner) ->
      (forall owner reads,
        Inv.guarded_reads st owner reads ->
        Inv.guarded_reads st' owner reads) ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_evaluation_history tf st control fr current ->
      aligned_evaluation_history tf st' control' fr current.
  Proof.
    intros tf st control st' control' fr current
      Hsolved_map Hguard_map Hlive_map
      [Hsolved [reads [sides [spawns [Hcontext [Hreads Hspawns]]]]]].
    split; [now apply Hsolved_map |]. exists reads, sides, spawns.
    split; [exact Hcontext |]. split; [now apply Hguard_map |].
    intros target Hin. apply Hlive_map. now apply Hspawns.
  Qed.

  Lemma aligned_completed_transport :
    forall tf st control st' control' fr direct,
      (forall owner, Sem.solved st owner -> Sem.solved st' owner) ->
      (forall owner reads,
        Inv.guarded_reads st owner reads ->
        Inv.guarded_reads st' owner reads) ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_completed_history tf st control fr direct ->
      aligned_completed_history tf st' control' fr direct.
  Proof.
    intros tf st control st' control' fr direct
      Hsolved_map Hguard_map Hlive_map
      [Hsolved [result [Hresult [Hdirect [Hreads Hspawns]]]]].
    split; [now apply Hsolved_map |]. exists result.
    split; [exact Hresult |]. split; [exact Hdirect |].
    split; [now apply Hguard_map |].
    intros target Hin. apply Hlive_map. now apply Hspawns.
  Qed.

  Lemma aligned_summary_transport :
    forall tf st control st' control' fr,
      (forall owner, Sem.solved st owner -> Sem.solved st' owner) ->
      (forall owner reads,
        Inv.guarded_reads st owner reads ->
        Inv.guarded_reads st' owner reads) ->
      (forall owner value,
        Sem.solved st owner ->
        D.leq value (R.sigma_value st owner) = true ->
        D.leq value (R.sigma_value st' owner) = true) ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_summary_history tf st control fr ->
      aligned_summary_history tf st' control' fr.
  Proof.
    intros tf st control st' control' fr
      Hsolved_map Hguard_map Hdirect_map Hlive_map
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [now apply Hsolved_map |]. exists result.
    split; [exact Hresult |]. split; [now apply Hguard_map |]. split.
    - eapply Hdirect_map; eassumption.
    - intros target Hin. apply Hlive_map. now apply Hspawns.
  Qed.

  Lemma aligned_continuation_transport :
    forall tf st control st' control' k,
      (forall owner, Sem.solved st owner -> Sem.solved st' owner) ->
      (forall owner reads,
        Inv.guarded_reads st owner reads ->
        Inv.guarded_reads st' owner reads) ->
      (forall owner value,
        Sem.solved st owner ->
        D.leq value (R.sigma_value st owner) = true ->
        D.leq value (R.sigma_value st' owner) = true) ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_continuation_history tf st control k ->
      aligned_continuation_history tf st' control' k.
  Proof.
    intros tf st control st' control' k Hsolved Hguards Hdirect Hlive.
    induction k; cbn; intros Hhistory; try exact I.
    all: destruct Hhistory as [Hhead Hrest]; split.
    all: try (eapply aligned_evaluation_transport;
      [exact Hsolved | exact Hguards | exact Hlive | exact Hhead]).
    all: try (eapply aligned_completed_transport;
      [exact Hsolved | exact Hguards | exact Hlive | exact Hhead]).
    all: try (eapply aligned_summary_transport;
      [exact Hsolved | exact Hguards | exact Hdirect |
       exact Hlive | exact Hhead]).
    all: now apply IHk.
  Qed.

  Lemma complete_get_guarded_reads :
    forall st fr target st' fr' value owner reads,
      R.complete_get st fr target = (st', fr', value) ->
      Inv.guarded_reads st owner reads ->
      Inv.guarded_reads st' owner reads.
  Proof.
    intros st fr target st' fr' value owner reads Hget Hreads.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    inversion Hget; subst.
    apply Inv.guarded_reads_materialize.
    apply Inv.guarded_reads_add_reader.
    subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
    - exact Hreads.
    - eapply Inv.guarded_reads_same_view.
      + apply Inv.promote_controlled_same_solver_view.
      + exact Hreads.
  Qed.

  Lemma complete_get_preserves_solved :
    forall st fr target st' fr' value x,
      R.complete_get st fr target = (st', fr', value) ->
      Sem.solved st x -> Sem.solved st' x.
  Proof.
    intros st fr target st' fr' value x Hget Hsolved.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    inversion Hget; subst. apply Inv.materialize_preserves_solved.
    subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
      exact Hsolved.
  Qed.

  Lemma solved_enqueue :
    forall st inserted x,
      Sem.solved st x -> Sem.solved (R.enqueue st inserted) x.
  Proof.
    intros st inserted x [value Hlookup]. exists value.
    rewrite Total.Termination.enqueue_sigma. exact Hlookup.
  Qed.

  Lemma solved_enqueue_back :
    forall st inserted x,
      Sem.solved (R.enqueue st inserted) x -> Sem.solved st x.
  Proof.
    intros st inserted x [value Hlookup]. exists value.
    rewrite Total.Termination.enqueue_sigma in Hlookup. exact Hlookup.
  Qed.

  Lemma complete_get_sigma_value_solved :
    forall st fr target st' fr' value owner,
      R.complete_get st fr target = (st', fr', value) ->
      Sem.solved st owner ->
      R.sigma_value st' owner = R.sigma_value st owner.
  Proof.
    intros st fr target st' fr' value owner Hget Hsolved.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    inversion Hget; subst. rewrite Inv.materialize_sigma_value_solved.
    - subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
        reflexivity.
    - subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
        exact Hsolved.
  Qed.

  Lemma ordinary_aligned_run_rhs_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr current k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |} ->
      aligned_control_history tf st (R.RunRhs fr current k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |}
        after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st fr current k after
      Hordinary Hreachable [Hcurrent Hk] Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hcontrol_history.
    assert (Hsolved_map : forall owner,
      Sem.solved st owner -> Sem.solved (R.cfg_state after) owner).
    { intros owner Hsolved. unfold Sem.step in Hsemantic.
      exact (@Inv.next_config_preserves_solved tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |}
        after owner Hsolved Hsemantic). }
    assert (Hlive_map : forall observed,
      spawn_live st (R.RunRhs fr current k) observed ->
      spawn_live (R.cfg_state after) (R.cfg_control after) observed).
    { intros observed Hlive. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |}
        after observed); eassumption. }
    unfold Sem.step, R.next_config in Hstep.
    destruct current; cbn -[R.complete_get R.observe] in Hstep.
    - inversion Hstep; subst; cbn. split.
      + apply aligned_evaluation_completed.
        eapply aligned_evaluation_transport.
        * exact Hsolved_map.
        * intros; assumption.
        * exact Hlive_map.
        * exact Hcurrent.
      + eapply aligned_continuation_transport.
        * exact Hsolved_map.
        * intros; assumption.
        * intros; assumption.
        * exact Hlive_map.
        * exact Hk.
    - set (observed := R.observe st t) in *.
      destruct (negb (R.is_materialized observed t) &&
        R.rank_lt observed (R.frame_owner fr) t)%bool eqn:Hdemand.
      + inversion Hstep; subst; cbn. split.
        * eapply aligned_evaluation_transport.
          -- exact Hsolved_map.
          -- intros. now apply Inv.guarded_reads_observe.
          -- exact Hlive_map.
          -- exact Hcurrent.
        * eapply aligned_continuation_transport.
          -- exact Hsolved_map.
          -- intros. now apply Inv.guarded_reads_observe.
          -- intros owner direct Hsolved Hdirect.
             subst observed. unfold R.sigma_value.
             rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
          -- exact Hlive_map.
          -- exact Hk.
      + set (st0 := if R.is_materialized observed t
          then observed else R.enqueue observed t) in *.
        destruct (R.complete_get st0 fr t)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst; cbn.
        assert (Hget_solved : forall owner,
          Sem.solved st owner -> Sem.solved st1 owner).
        { intros owner Hsolved. eapply complete_get_preserves_solved;
            [exact Hget |]. subst st0.
          destruct (R.is_materialized observed t).
          - subst observed. now apply Inv.solved_observe.
          - apply solved_enqueue. subst observed.
            now apply Inv.solved_observe. }
        assert (Hget_guards : forall owner reads,
          Inv.guarded_reads st owner reads ->
          Inv.guarded_reads st1 owner reads).
        { intros owner reads Hreads.
          eapply complete_get_guarded_reads; [exact Hget |]. subst st0.
          destruct (R.is_materialized observed t).
          - subst observed. now apply Inv.guarded_reads_observe.
          - apply Inv.guarded_reads_enqueue. subst observed.
            now apply Inv.guarded_reads_observe. }
        assert (Hget_direct : forall owner direct,
          Sem.solved st owner ->
          D.leq direct (R.sigma_value st owner) = true ->
          D.leq direct (R.sigma_value st1 owner) = true).
        { intros owner direct Hsolved Hdirect.
          rewrite (@complete_get_sigma_value_solved
            st0 fr t st1 fr1 value owner Hget).
          - subst st0. destruct (R.is_materialized observed t).
            + subst observed. unfold R.sigma_value.
              rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
            + unfold R.sigma_value. rewrite Total.Termination.enqueue_sigma.
              subst observed.
              rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
          - subst st0. destruct (R.is_materialized observed t).
            + subst observed. now apply Inv.solved_observe.
            + apply solved_enqueue. subst observed.
              now apply Inv.solved_observe. }
        assert (Howner : R.frame_owner fr1 = R.frame_owner fr).
        { pose proof (f_equal
            (fun result : (R.state * R.frame) * D.t =>
              R.frame_owner (snd (fst result))) Hget) as H.
          cbn in H. symmetry. exact H. }
        assert (Hcurrent0 : aligned_evaluation_history tf st0
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
          fr (R.ConstraintSystem.Get t r)).
        { eapply (@aligned_evaluation_transport tf st
            (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
            st0 (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
            fr (R.ConstraintSystem.Get t r)).
          - intros owner Hsolved. subst st0.
            destruct (R.is_materialized observed t).
            + subst observed. now apply Inv.solved_observe.
            + apply solved_enqueue. subst observed.
              now apply Inv.solved_observe.
          - intros owner reads Hreads. subst st0.
            destruct (R.is_materialized observed t).
            + subst observed. now apply Inv.guarded_reads_observe.
            + apply Inv.guarded_reads_enqueue. subst observed.
              now apply Inv.guarded_reads_observe.
          - intros spawned [Hsolved | Hactive].
            + left. subst st0. destruct (R.is_materialized observed t).
              * subst observed. now apply Inv.solved_observe.
              * apply solved_enqueue. subst observed.
                now apply Inv.solved_observe.
            + now right.
          - exact Hcurrent. }
        assert (Hget_live : forall spawned,
          spawn_live st0 (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
            spawned ->
          spawn_live st1 (R.RunRhs fr1 (r value) k) spawned).
        { intros spawned [Hsolved | Hactive].
          - apply Hlive_map. left. subst st0.
            destruct (R.is_materialized observed t).
            + subst observed. now apply Inv.solved_observe_back in Hsolved.
            + apply solved_enqueue_back in Hsolved. subst observed.
              now apply Inv.solved_observe_back in Hsolved.
          - apply Hlive_map. now right. }
        split.
        * eapply aligned_evaluation_get.
          -- exact Hget.
          -- rewrite Howner. apply Hget_solved. exact (proj1 Hcurrent).
          -- exact Hget_live.
          -- exact Hcurrent0.
        * eapply aligned_continuation_transport.
          -- exact Hget_solved.
          -- exact Hget_guards.
          -- exact Hget_direct.
          -- exact Hlive_map.
          -- exact Hk.
    - exfalso. eapply ordinary_reachable_side_impossible; eauto.
    - set (observed := R.observe st t) in *.
      destruct (R.is_materialized observed t) eqn:Hmaterialized.
      + inversion Hstep; subst; cbn. split.
        * eapply aligned_evaluation_spawn.
          -- eapply aligned_evaluation_transport.
             ++ exact Hsolved_map.
             ++ intros. subst observed. now apply Inv.guarded_reads_observe.
             ++ exact Hlive_map.
             ++ exact Hcurrent.
          -- left. now apply is_materialized_solved.
        * eapply aligned_continuation_transport.
          -- exact Hsolved_map.
          -- intros. subst observed. now apply Inv.guarded_reads_observe.
          -- intros owner direct Hsolved Hdirect.
             subst observed. unfold R.sigma_value.
             rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
          -- exact Hlive_map.
          -- exact Hk.
      + destruct (R.rank_lt observed (R.frame_owner fr) t) eqn:Hhigher.
        * inversion Hstep; subst; cbn. split.
          -- eapply aligned_evaluation_spawn.
             ++ eapply aligned_evaluation_transport.
                ** exact Hsolved_map.
                ** intros. subst observed. now apply Inv.guarded_reads_observe.
                ** exact Hlive_map.
                ** exact Hcurrent.
             ++ right. cbn. now left.
          -- eapply aligned_continuation_transport.
             ++ exact Hsolved_map.
             ++ intros. subst observed. now apply Inv.guarded_reads_observe.
             ++ intros owner direct Hsolved Hdirect.
                subst observed. unfold R.sigma_value.
                rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
             ++ exact Hlive_map.
             ++ exact Hk.
        * inversion Hstep; subst; cbn.
          assert (Hguards : forall owner reads,
            Inv.guarded_reads st owner reads ->
            Inv.guarded_reads (R.materialize (R.enqueue observed t) t)
              owner reads).
          { intros owner reads Hreads. apply Inv.guarded_reads_materialize.
            apply Inv.guarded_reads_enqueue. subst observed.
            now apply Inv.guarded_reads_observe. }
          assert (Hdirect : forall owner direct,
            Sem.solved st owner ->
            D.leq direct (R.sigma_value st owner) = true ->
            D.leq direct
              (R.sigma_value (R.materialize (R.enqueue observed t) t) owner)
              = true).
          { intros owner direct Hsolved Hdirect.
            rewrite Inv.materialize_sigma_value_solved.
            - unfold R.sigma_value. rewrite Total.Termination.enqueue_sigma.
              subst observed.
              rewrite (proj1 (Inv.observe_solver_view st t)). exact Hdirect.
            - apply solved_enqueue. subst observed.
              now apply Inv.solved_observe. }
          split.
          -- eapply aligned_evaluation_spawn.
             ++ eapply aligned_evaluation_transport.
                ** exact Hsolved_map.
                ** exact Hguards.
                ** exact Hlive_map.
                ** exact Hcurrent.
             ++ left. apply Inv.materialize_solved_correctness.
          -- eapply aligned_continuation_transport.
             ++ exact Hsolved_map.
             ++ exact Hguards.
             ++ exact Hdirect.
             ++ exact Hlive_map.
             ++ exact Hk.
  Qed.

  Lemma aligned_start_episode_step :
    forall tf roots st owner k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |} ->
      aligned_control_history tf st (R.StartEpisode owner k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |}
        after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st owner k after Hreachable Hk Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hhistory.
    assert (Hlive : forall observed,
      spawn_live st (R.StartEpisode owner k) observed ->
      spawn_live (R.cfg_state after) (R.cfg_control after) observed).
    { intros observed Hspawn. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |}
        after observed); eassumption. }
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst; cbn. split.
    - apply aligned_initial_evaluation.
      apply Inv.materialize_solved_correctness.
    - eapply (@aligned_continuation_transport tf st
        (R.StartEpisode owner k) (R.materialize st owner)
        (R.RunRhs
          (R.fresh_frame (R.materialize st owner) owner
            (U.initial_phase false owner))
          (tf owner) k) k).
      + intros solved Hsolved. now apply Inv.materialize_preserves_solved.
      + intros solved reads Hreads.
        now apply Inv.guarded_reads_materialize.
      + intros solved direct Hsolved Hdirect.
        rewrite Inv.materialize_sigma_value_solved; assumption.
      + exact Hlive.
      + exact Hk.
  Qed.

  Lemma aligned_return_step :
    forall tf roots st k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.Return k |} ->
      aligned_control_history tf st (R.Return k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st k after Hreachable Hhistory Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hcontrol_history.
    assert (Hlive : forall observed,
      spawn_live st (R.Return k) observed ->
      spawn_live (R.cfg_state after) (R.cfg_control after) observed).
    { intros observed Hspawn. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |}
        after observed); eassumption. }
    unfold Sem.step, R.next_config in Hstep.
    destruct k; cbn -[R.complete_get] in Hstep.
    - inversion Hstep; subst; exact I.
    - inversion Hstep; subst; exact I.
    - destruct Hhistory as [Hcurrent Hrest].
      destruct (R.complete_get st f t)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst; cbn. split.
      + eapply aligned_evaluation_get.
        * exact Hget.
        * erewrite Inv.complete_get_frame_owner; [|exact Hget].
          eapply complete_get_preserves_solved; [exact Hget |].
          exact (proj1 Hcurrent).
        * exact Hlive.
        * exact Hcurrent.
      + eapply aligned_continuation_transport.
        * intros owner Hsolved.
          eapply complete_get_preserves_solved; eassumption.
        * intros owner reads Hreads.
          eapply complete_get_guarded_reads; eassumption.
        * intros owner direct Hsolved Hdirect.
          rewrite (@complete_get_sigma_value_solved
            st f t st1 fr1 value owner Hget Hsolved). exact Hdirect.
        * exact Hlive.
        * exact Hrest.
    - destruct Hhistory as [Hcurrent Hrest].
      inversion Hstep; subst; cbn; split.
      + eapply (@aligned_evaluation_transport tf st
          (R.Return (R.KAfterSide f r k)) st (R.RunRhs f r k) f r);
          [intros; assumption | intros; assumption |
           exact Hlive | exact Hcurrent].
      + eapply (@aligned_continuation_transport tf st
          (R.Return (R.KAfterSide f r k)) st (R.RunRhs f r k) k);
          [intros; assumption | intros; assumption | intros; assumption |
           exact Hlive | exact Hrest].
    - destruct Hhistory as [Hcurrent Hrest].
      inversion Hstep; subst; cbn; split.
      + eapply (@aligned_evaluation_transport tf st
          (R.Return (R.KAfterSpawn f r k)) st (R.RunRhs f r k) f r);
          [intros; assumption | intros; assumption |
           exact Hlive | exact Hcurrent].
      + eapply (@aligned_continuation_transport tf st
          (R.Return (R.KAfterSpawn f r k)) st (R.RunRhs f r k) k);
          [intros; assumption | intros; assumption | intros; assumption |
           exact Hlive | exact Hrest].
    - destruct Hhistory as [Hcompleted Hrest].
      inversion Hstep; subst; cbn; split.
      + eapply (@aligned_completed_transport tf st
          (R.Return (R.KDead f t l k)) st (R.RunDead f t l k) f t);
          [intros; assumption | intros; assumption |
           exact Hlive | exact Hcompleted].
      + eapply (@aligned_continuation_transport tf st
          (R.Return (R.KDead f t l k)) st (R.RunDead f t l k) k);
          [intros; assumption | intros; assumption | intros; assumption |
           exact Hlive | exact Hrest].
    - destruct Hhistory as [Hsummary Hrest].
      inversion Hstep; subst; cbn; split.
      + eapply (@aligned_summary_transport tf st
          (R.Return (R.KDrain f k)) st (R.RunDrain f k) f);
          [intros; assumption | intros; assumption | intros; assumption |
           exact Hlive | exact Hsummary].
      + eapply (@aligned_continuation_transport tf st
          (R.Return (R.KDrain f k)) st (R.RunDrain f k) k);
          [intros; assumption | intros; assumption | intros; assumption |
           exact Hlive | exact Hrest].
  Qed.

  Lemma ordinary_aligned_run_dead_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct pending k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} ->
      aligned_control_history tf st (R.RunDead fr direct pending k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st fr direct pending k after
      Hordinary Hreachable [Hcompleted Hk] Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hhistory.
    pose proof (@ordinary_reachable_clean tf roots finite
      Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunDead fr direct pending k |}
      Hreachable) as [_ Hcontrol].
    cbn in Hcontrol. destruct Hcontrol as [_ [-> _]].
    assert (Hlive : forall observed,
      spawn_live st (R.RunDead fr direct [] k) observed ->
      spawn_live (R.cfg_state after) (R.cfg_control after) observed).
    { intros observed Hspawn. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |}
        after observed); eassumption. }
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst; cbn. split.
    - eapply (@aligned_completed_transport tf st
        (R.RunDead fr direct [] k) (R.publish_targets st fr)
        (R.RunCommit fr direct k) fr direct).
      + intros owner Hsolved. exact Hsolved.
      + intros owner reads Hreads. eapply Inv.guarded_reads_same_view.
        * apply Inv.publish_targets_same_solver_view.
        * exact Hreads.
      + exact Hlive.
      + exact Hcompleted.
    - eapply (@aligned_continuation_transport tf st
        (R.RunDead fr direct [] k) (R.publish_targets st fr)
        (R.RunCommit fr direct k) k).
      + intros owner Hsolved. exact Hsolved.
      + intros owner reads Hreads. eapply Inv.guarded_reads_same_view.
        * apply Inv.publish_targets_same_solver_view.
        * exact Hreads.
      + intros owner value Hsolved Hvalue. exact Hvalue.
      + exact Hlive.
      + exact Hk.
  Qed.

  Lemma aligned_summary_set_value_other :
    forall tf st control st' control' fr direct fr' summary,
      R.set_value st fr direct = (st', fr') ->
      R.frame_owner summary <> R.frame_owner fr ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_summary_history tf st control summary ->
      aligned_summary_history tf st' control' summary.
  Proof.
    intros tf st control st' control' fr direct fr' summary
      Hset Hneq Hlive
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [eapply Inv.set_value_solved; eassumption |].
    exists result. split; [exact Hresult |].
    split; [eapply Inv.guarded_reads_set_value; eassumption |]. split.
    - rewrite (@Total.set_value_sigma_value_other_correctness
        st fr direct st' fr' (R.frame_owner summary) Hset Hneq).
      exact Hdirect.
    - intros target Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_continuation_set_value :
    forall tf st control st' control' fr direct fr' k,
      R.set_value st fr direct = (st', fr') ->
      Total.Termination.continuation_below st (R.frame_owner fr) k ->
      (forall observed,
        spawn_live st control observed -> spawn_live st' control' observed) ->
      aligned_continuation_history tf st control k ->
      aligned_continuation_history tf st' control' k.
  Proof.
    intros tf st control st' control' fr direct fr' k
      Hset Hbelow Hlive.
    induction k; cbn in *; intros Hhistory; try exact I.
    all: destruct Hbelow as [Hlt Hbelow].
    all: destruct Hhistory as [Hhead Hrest].
    all: assert (Hneq : R.frame_owner f <> R.frame_owner fr)
      by (eapply Total.rank_lt_true_neq_correctness; exact Hlt).
    all: split.
    all: try (eapply aligned_evaluation_transport;
      [intros; eapply Inv.set_value_solved; eassumption |
       intros; eapply Inv.guarded_reads_set_value; eassumption |
       exact Hlive | exact Hhead]).
    all: try (eapply aligned_completed_transport;
      [intros; eapply Inv.set_value_solved; eassumption |
       intros; eapply Inv.guarded_reads_set_value; eassumption |
       exact Hlive | exact Hhead]).
    all: try (eapply aligned_summary_set_value_other;
      [exact Hset | exact Hneq | exact Hlive | exact Hhead]).
    all: eapply IHk.
    all: try (eapply Total.continuation_below_raise_correctness;
      eassumption).
    all: exact Hrest.
  Qed.

  Lemma aligned_run_commit_step :
    forall tf roots st fr direct k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
      aligned_control_history tf st (R.RunCommit fr direct k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |}
        after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st fr direct k after
      Hreachable [Hcompleted Hk] Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hhistory.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hbelow. cbn in Hbelow.
    unfold Sem.step, R.next_config in Hstep. cbn -[R.set_value] in Hstep.
    destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
    inversion Hstep; subst; cbn.
    assert (Hlive : forall observed,
      spawn_live st (R.RunCommit fr direct k) observed ->
      spawn_live st1 (R.RunDrain fr1 k) observed).
    { intros observed Hspawn. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |}
        {| R.cfg_state := st1; R.cfg_control := R.RunDrain fr1 k |}
        observed); eassumption. }
    split.
    - eapply aligned_completed_set_value_summary; eassumption.
    - eapply aligned_continuation_set_value; eassumption.
  Qed.

  Lemma aligned_evaluation_pop_other :
    forall tf st control control' popped rest fr current,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      R.frame_owner fr <> popped ->
      (forall observed,
        spawn_live st control observed ->
        spawn_live (R.with_queue st rest) control' observed) ->
      aligned_evaluation_history tf st control fr current ->
      aligned_evaluation_history tf (R.with_queue st rest) control' fr current.
  Proof.
    intros tf st control control' popped rest fr current Hpop Hneq Hlive
      [Hsolved [reads [sides [spawns [Hcontext [Hreads Hspawns]]]]]].
    split; [exact Hsolved |]. exists reads, sides, spawns.
    split; [exact Hcontext |].
    split; [eapply Inv.guarded_reads_pop_other; eassumption |].
    intros target Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_completed_pop_other :
    forall tf st control control' popped rest fr direct,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      R.frame_owner fr <> popped ->
      (forall observed,
        spawn_live st control observed ->
        spawn_live (R.with_queue st rest) control' observed) ->
      aligned_completed_history tf st control fr direct ->
      aligned_completed_history tf (R.with_queue st rest) control' fr direct.
  Proof.
    intros tf st control control' popped rest fr direct Hpop Hneq Hlive
      [Hsolved [result [Hresult [Hdirect [Hreads Hspawns]]]]].
    split; [exact Hsolved |]. exists result.
    split; [exact Hresult |]. split; [exact Hdirect |].
    split; [eapply Inv.guarded_reads_pop_other; eassumption |].
    intros target Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_summary_pop_other :
    forall tf st control control' popped rest fr,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      R.frame_owner fr <> popped ->
      (forall observed,
        spawn_live st control observed ->
        spawn_live (R.with_queue st rest) control' observed) ->
      aligned_summary_history tf st control fr ->
      aligned_summary_history tf (R.with_queue st rest) control' fr.
  Proof.
    intros tf st control control' popped rest fr Hpop Hneq Hlive
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [exact Hsolved |]. exists result.
    split; [exact Hresult |].
    split; [eapply Inv.guarded_reads_pop_other; eassumption |]. split.
    - exact Hdirect.
    - intros target Hin. apply Hlive. now apply Hspawns.
  Qed.

  Lemma aligned_continuation_pop_above :
    forall tf st control control' popped rest upper k,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      Total.Termination.continuation_below st upper k ->
      (popped = upper \/ R.rank_lt st upper popped = true) ->
      (forall observed,
        spawn_live st control observed ->
        spawn_live (R.with_queue st rest) control' observed) ->
      aligned_continuation_history tf st control k ->
      aligned_continuation_history tf (R.with_queue st rest) control' k.
  Proof.
    intros tf st control control' popped rest upper k Hpop.
    induction k; intros Hbelow Habove Hlive Hhistory;
      cbn in *; try exact I.
    all: destruct Hbelow as [Hlt Hbelow].
    all: destruct Hhistory as [Hhead Hhistory].
    all: assert (Hneq : R.frame_owner f <> popped) by (
      apply (@Total.rank_lt_true_neq_correctness st
        (R.frame_owner f) popped);
      destruct Habove as [-> | Habove];
      [exact Hlt | eapply Total.Termination.rank_lt_trans_true; eauto]).
    all: split.
    all: try (eapply aligned_evaluation_pop_other; eauto).
    all: try (eapply aligned_completed_pop_other; eauto).
    all: try (eapply aligned_summary_pop_other; eauto).
    all: eapply IHk.
    all: try (eapply Total.continuation_below_raise_correctness; eauto).
    all: try exact Habove.
    all: try exact Hlive.
    all: exact Hhistory.
  Qed.

  Lemma aligned_run_drain_step :
    forall tf roots st fr k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      aligned_control_history tf st (R.RunDrain fr k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st fr k after Hreachable [Hsummary Hk] Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hhistory.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hbelow. cbn in Hbelow.
    assert (Hlive : forall observed,
      spawn_live st (R.RunDrain fr k) observed ->
      spawn_live (R.cfg_state after) (R.cfg_control after) observed).
    { intros observed Hspawn. left.
      eapply (@spawn_live_after_step_from_history tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
        after observed); eassumption. }
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
    destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
    - destruct (V.eq_dec next (R.frame_owner fr)) as [Hequal | Hdifferent].
      + destruct (R.queue_pop (R.queue st))
          as [[popped rest] |] eqn:Hpop; try discriminate.
        inversion Hstep; subst; cbn. split.
        * eapply (@aligned_initial_evaluation tf (R.with_queue st rest)
            (R.RunRhs
              (R.fresh_frame (R.with_queue st rest)
                (R.frame_owner fr) (R.frame_phase fr))
              (tf (R.frame_owner fr)) k)
            (R.fresh_frame (R.with_queue st rest)
              (R.frame_owner fr) (R.frame_phase fr))).
          change (Sem.solved st (R.frame_owner fr)). exact (proj1 Hsummary).
        * eapply aligned_continuation_pop_above.
          -- exact Hpop.
          -- exact Hbelow.
          -- left. pose proof (@Total.queue_peek_pop_same
               (R.queue st) (R.frame_owner fr) popped rest Hpeek Hpop).
             congruence.
          -- intros observed Hspawn. now apply Hlive in Hspawn.
          -- exact Hk.
      + destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
        * destruct (R.queue_pop (R.queue st))
            as [[popped rest] |] eqn:Hpop; try discriminate.
          inversion Hstep; subst; cbn. split.
          -- eapply aligned_summary_pop_other.
             ++ exact Hpop.
             ++ intro Heq. subst. apply Hdifferent.
                pose proof (@Total.queue_peek_pop_same
                  (R.queue st) next (R.frame_owner fr) rest Hpeek Hpop).
                congruence.
             ++ intros observed Hspawn. now apply Hlive in Hspawn.
             ++ exact Hsummary.
          -- eapply aligned_continuation_pop_above.
             ++ exact Hpop.
             ++ exact Hbelow.
             ++ right. pose proof (@Total.queue_peek_pop_same
                  (R.queue st) next popped rest Hpeek Hpop). congruence.
             ++ intros observed Hspawn. now apply Hlive in Hspawn.
             ++ exact Hk.
        * inversion Hstep; subst; cbn.
          eapply (@aligned_continuation_transport tf st
            (R.RunDrain fr k)
            (R.reset_registered_cells st (R.frame_owner fr))
            (R.Return k) k).
          -- intros owner Hsolved. eapply Inv.solved_same_solver_view.
             ++ apply Inv.reset_registered_cells_same_solver_view.
             ++ exact Hsolved.
          -- intros. eapply Inv.guarded_reads_same_view.
             ++ apply Inv.reset_registered_cells_same_solver_view.
             ++ assumption.
          -- intros owner value Hsolved Hvalue. unfold R.sigma_value in *.
             rewrite (proj1 (proj1
               (Inv.reset_registered_cells_same_solver_view
                 st (R.frame_owner fr)))). exact Hvalue.
          -- exact Hlive.
          -- exact Hk.
    - inversion Hstep; subst; cbn.
      eapply (@aligned_continuation_transport tf st
        (R.RunDrain fr k)
        (R.reset_registered_cells st (R.frame_owner fr))
        (R.Return k) k).
      + intros owner Hsolved. eapply Inv.solved_same_solver_view.
        * apply Inv.reset_registered_cells_same_solver_view.
        * exact Hsolved.
      + intros. eapply Inv.guarded_reads_same_view.
        * apply Inv.reset_registered_cells_same_solver_view.
        * assumption.
      + intros owner value Hsolved Hvalue. unfold R.sigma_value in *.
        rewrite (proj1 (proj1
          (Inv.reset_registered_cells_same_solver_view
            st (R.frame_owner fr)))). exact Hvalue.
      + exact Hlive.
      + exact Hk.
  Qed.

  Lemma ordinary_aligned_history_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      aligned_control_history tf
        (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      aligned_control_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite [st control] after
      Hordinary Hreachable Haligned Hstep.
    destruct control.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        inversion Hstep; subst; exact I.
    - unfold Sem.step, R.next_config in Hstep.
      destruct l as [|root remaining]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst; exact I.
      + destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; subst; exact I.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        inversion Hstep; subst; exact I.
    - eapply aligned_start_episode_step; eassumption.
    - eapply ordinary_aligned_run_rhs_step; eassumption.
    - eapply ordinary_aligned_run_dead_step; eassumption.
    - eapply aligned_run_commit_step; eassumption.
    - eapply aligned_run_drain_step; eassumption.
    - eapply aligned_return_step; eassumption.
  Qed.

  Theorem ordinary_reachable_aligned_history :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      forall c,
        Sem.steps tf (R.initial_config roots) c ->
        aligned_control_history tf
          (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots finite Hordinary final Hsteps.
    assert (Hpreserve : forall first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      aligned_control_history tf
        (R.cfg_state first) (R.cfg_control first) ->
      aligned_control_history tf
        (R.cfg_state last) (R.cfg_control last)).
    { intros first last Hreachable Hrun. revert Hreachable.
      induction Hrun as [c | first next last Hstep Hrun IH].
      - intros Hreachable Haligned. exact Haligned.
      - intros Hreachable Haligned. apply IH.
        + eapply Total.Termination.steps_transitive; [exact Hreachable |].
          econstructor; [exact Hstep |constructor].
        + eapply ordinary_aligned_history_step; eauto. }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - exact I.
  Qed.

  Lemma aligned_completed_self_wave :
    forall tf roots st fr direct k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      aligned_completed_history tf st
        (R.RunCommit fr direct k) fr direct ->
      ~ Inv.queued st (R.frame_owner fr) ->
      D.leq direct (R.sigma_value st (R.frame_owner fr)) = true ->
      wave_completed tf st fr direct.
  Proof.
    intros tf roots st fr direct k Hreachable
      [Howner [result
        [Hresult [Hdirect [Hreads Hspawns]]]]]
      Hnot_queued Hdirect_le.
    exists result, result.
    split; [exact Hresult |]. split; [exact Hresult |].
    split; [exact Hdirect |]. split.
    - intros target lower upper Hlower Hupper.
      destruct (Hreads target lower Hlower)
        as [_ [_ [Hlower_eq | Hqueued]]];
        [| contradiction].
      destruct (Hreads target upper Hupper)
        as [_ [_ [Hupper_eq | Hqueued]]];
        [| contradiction].
      rewrite Hlower_eq, Hupper_eq. apply DL.leq_refl.
    - split.
      + now rewrite Hdirect.
      + split.
        * intros target value Hin.
          destruct (Hreads target value Hin)
            as [Htarget [_ [Hvalue | Hqueued]]];
            [| contradiction].
          split; [exact Htarget |].
          rewrite Hvalue. apply DL.leq_refl.
        * intros target Hin.
          destruct (Hspawns target Hin) as [Hsolved | Hactive].
          -- exact Hsolved.
          -- destruct (@active_solved_or_start_from_history
              tf st (R.RunCommit fr direct k) target
              (reachable_control_history Hreachable) Hactive)
              as [Hsolved | [owner [rest [Heq _]]]].
             ++ exact Hsolved.
             ++ discriminate.
  Qed.

  Definition full_summary_history
    (tf : R.ConstraintSystem.system) (st : R.state) (owner : V.t) : Prop :=
    Sem.solved st owner /\
    exists result,
      trace_observes (tf owner) result /\
      Inv.guarded_reads st owner (observed_reads result) /\
      D.leq (observed_direct result) (R.sigma_value st owner) = true /\
      observation_spawns_cover_state st result.

  Definition full_state_history
    (tf : R.ConstraintSystem.system) (st : R.state)
    (control : R.control) : Prop :=
    forall owner,
      Sem.solved st owner ->
      Inv.queued st owner \/
      Inv.control_active owner control \/
      full_summary_history tf st owner.

  Lemma full_summary_transport :
    forall tf st st' owner,
      (forall variable, Sem.solved st variable -> Sem.solved st' variable) ->
      (forall reads,
        Inv.guarded_reads st owner reads ->
        Inv.guarded_reads st' owner reads) ->
      R.sigma_value st' owner = R.sigma_value st owner ->
      full_summary_history tf st owner ->
      full_summary_history tf st' owner.
  Proof.
    intros tf st st' owner Hsolved_map Hguard_map Hsigma
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [now apply Hsolved_map |]. exists result.
    split; [exact Hresult |]. split; [now apply Hguard_map |]. split.
    - now rewrite Hsigma.
    - intros target Hin. apply Hsolved_map. now apply Hspawns.
  Qed.

  Lemma aligned_summary_to_full_core :
    forall tf st control fr,
      Inv.control_history tf st control ->
      (forall owner rest, control <> R.StartEpisode owner rest) ->
      aligned_summary_history tf st control fr ->
      full_summary_history tf st (R.frame_owner fr).
  Proof.
    intros tf st control fr Hhistory Hnot_start
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [exact Hsolved |]. exists result.
    split; [exact Hresult |]. split; [exact Hreads |]. split.
    - exact Hdirect.
    - intros target Hin. destruct (Hspawns target Hin)
        as [Htarget | Hactive]; [exact Htarget |].
      destruct (@active_solved_or_start_from_history
        tf st control target Hhistory Hactive)
        as [Htarget | [owner [rest [Heq _]]]].
      + exact Htarget.
      + exfalso. now apply (Hnot_start owner rest).
  Qed.

  Lemma aligned_summary_to_full :
    forall tf roots st control fr,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := control |} ->
      (forall owner rest, control <> R.StartEpisode owner rest) ->
      aligned_summary_history tf st control fr ->
      full_summary_history tf st (R.frame_owner fr).
  Proof.
    intros tf roots st control fr Hreachable Hnot_start Hsummary.
    eapply aligned_summary_to_full_core.
    - exact (reachable_control_history Hreachable).
    - exact Hnot_start.
    - exact Hsummary.
  Qed.

  Lemma full_summary_set_value_other :
    forall tf st fr direct st' fr' owner,
      R.set_value st fr direct = (st', fr') ->
      owner <> R.frame_owner fr ->
      full_summary_history tf st owner ->
      full_summary_history tf st' owner.
  Proof.
    intros tf st fr direct st' fr' owner Hset Hneq
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [eapply Inv.set_value_solved; eassumption |]. exists result.
    split; [exact Hresult |].
    split; [eapply Inv.guarded_reads_set_value; eassumption |]. split.
    - rewrite (@Total.set_value_sigma_value_other_correctness
        st fr direct st' fr' owner Hset Hneq). exact Hdirect.
    - intros target Hin. eapply Inv.set_value_solved; [exact Hset |].
      now apply Hspawns.
  Qed.

  Lemma full_summary_complete_get :
    forall tf st fr target st' fr' value owner,
      R.complete_get st fr target = (st', fr', value) ->
      full_summary_history tf st owner ->
      full_summary_history tf st' owner.
  Proof.
    intros tf st fr target st' fr' value owner Hget
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split; [eapply complete_get_preserves_solved; eassumption |].
    exists result. split; [exact Hresult |].
    split; [eapply complete_get_guarded_reads; eassumption |]. split.
    - rewrite (@complete_get_sigma_value_solved
        st fr target st' fr' value owner Hget Hsolved). exact Hdirect.
    - intros observed Hin. eapply complete_get_preserves_solved;
        [exact Hget |]. now apply Hspawns.
  Qed.

  Lemma full_summary_enqueue :
    forall tf st inserted owner,
      full_summary_history tf st owner ->
      full_summary_history tf (R.enqueue st inserted) owner.
  Proof.
    intros tf st inserted owner Hsummary.
    eapply (@full_summary_transport tf st (R.enqueue st inserted) owner).
    - intros; assumption.
    - intros. now apply Inv.guarded_reads_enqueue.
    - reflexivity.
    - exact Hsummary.
  Qed.

  Lemma full_summary_materialize :
    forall tf st inserted owner,
      full_summary_history tf st owner ->
      full_summary_history tf (R.materialize st inserted) owner.
  Proof.
    intros tf st inserted owner Hsummary.
    eapply (@full_summary_transport tf st (R.materialize st inserted) owner).
    - intros. now apply Inv.materialize_preserves_solved.
    - intros. now apply Inv.guarded_reads_materialize.
    - apply Inv.materialize_sigma_value_solved. exact (proj1 Hsummary).
    - exact Hsummary.
  Qed.

  Lemma full_summary_pop_other :
    forall tf st popped rest owner,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      owner <> popped ->
      full_summary_history tf st owner ->
      full_summary_history tf (R.with_queue st rest) owner.
  Proof.
    intros tf st popped rest owner Hpop Hneq Hsummary.
    eapply (@full_summary_transport tf st (R.with_queue st rest) owner).
    - intros; assumption.
    - intros. eapply Inv.guarded_reads_pop_other; eauto.
    - reflexivity.
    - exact Hsummary.
  Qed.

  Lemma full_summary_same_solver_view :
    forall tf st st' owner,
      Inv.same_solver_view st st' ->
      full_summary_history tf st owner ->
      full_summary_history tf st' owner.
  Proof.
    intros tf st st' owner [[Hsigma [Hreaders Hqueue]] Hcontributions]
      Hsummary.
    eapply (@full_summary_transport tf st st' owner).
    - intros variable [value Hlookup]. exists value. now rewrite Hsigma.
    - intros reads Hreads. eapply (@Inv.guarded_reads_same_view
        st st' owner reads).
      + repeat split; eassumption.
      + exact Hreads.
    - unfold R.sigma_value. now rewrite Hsigma.
    - exact Hsummary.
  Qed.

  Lemma full_summary_same_read_view :
    forall tf st st' owner,
      Inv.same_read_view st st' ->
      full_summary_history tf st owner ->
      full_summary_history tf st' owner.
  Proof.
    intros tf st st' owner [Hsigma [Hreaders Hqueue]]
      [Hsolved [result [Hresult [Hreads [Hdirect Hspawns]]]]].
    split.
    - destruct Hsolved as [value Hvalue]. exists value. now rewrite Hsigma.
    - exists result. split; [exact Hresult |]. split.
      + eapply (@Inv.guarded_reads_same_view
          st st' owner (observed_reads result)).
        * repeat split; eassumption.
        * exact Hreads.
      + split.
        * unfold R.sigma_value in *. now rewrite Hsigma.
        * intros target Hin. destruct (Hspawns target Hin) as [value Hvalue].
          exists value. now rewrite Hsigma.
  Qed.

  Lemma full_state_history_transport :
    forall tf st control st' control',
      (forall owner,
        Sem.solved st' owner ->
        Sem.solved st owner \/ Inv.queued st' owner \/
        Inv.control_active owner control') ->
      (forall owner,
        Inv.queued st owner ->
        Inv.queued st' owner \/ Inv.control_active owner control') ->
      (forall owner,
        Inv.control_active owner control ->
        Inv.queued st' owner \/ Inv.control_active owner control' \/
        full_summary_history tf st' owner) ->
      (forall owner,
        full_summary_history tf st owner ->
        Inv.queued st' owner \/ Inv.control_active owner control' \/
        full_summary_history tf st' owner) ->
      full_state_history tf st control ->
      full_state_history tf st' control'.
  Proof.
    intros tf st control st' control' Horigin Hqueued Hactive Hsummary Hfull
      owner Hsolved.
    destruct (Horigin owner Hsolved)
      as [Hsolved0 | [Hqueued' | Hactive']].
    - destruct (Hfull owner Hsolved0)
        as [Hqueued0 | [Hactive0 | Hsummary0]].
      + destruct (Hqueued owner Hqueued0); [now left |now right; left].
      + now apply Hactive.
      + now apply Hsummary.
    - now left.
    - now right; left.
  Qed.

  Lemma full_state_history_same_solver_view :
    forall tf st control st' control',
      Inv.same_solver_view st st' ->
      (forall owner,
        Inv.control_active owner control ->
        Inv.control_active owner control' \/
        full_summary_history tf st' owner) ->
      full_state_history tf st control ->
      full_state_history tf st' control'.
  Proof.
    intros tf st control st' control'
      [[Hsigma [Hreaders Hqueue]] Hcontributions] Hactive Hfull.
    eapply (@full_state_history_transport tf st control st' control').
    - intros owner [value Hlookup]. left. exists value.
      now rewrite Hsigma in Hlookup.
    - intros owner Hqueued. left. unfold Inv.queued in *.
      now rewrite Hqueue.
    - intros owner Hactive0. destruct (Hactive owner Hactive0)
        as [Hactive' | Hsummary].
      + now right; left.
      + now right; right.
    - intros owner Hsummary. right; right.
      eapply (@full_summary_same_solver_view tf st st' owner).
      + repeat split; eassumption.
      + exact Hsummary.
    - exact Hfull.
  Qed.

  Lemma initial_full_state_history :
    forall tf roots,
      full_state_history tf
        (R.cfg_state (R.initial_config roots))
        (R.cfg_control (R.initial_config roots)).
  Proof.
    intros tf roots owner [value Hlookup]. cbn in Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma full_state_history_run_commit_step :
    forall tf roots st fr direct k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
      aligned_control_history tf st (R.RunCommit fr direct k) ->
      full_state_history tf st (R.RunCommit fr direct k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |}
        after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st fr direct k after Hreachable Haligned Hfull Hstep.
    pose proof (@aligned_run_commit_step tf roots st fr direct k after
      Hreachable Haligned Hstep) as Haligned_after.
    pose proof (Total.Termination.steps_append_one Hreachable Hstep)
      as Hreachable_after.
    pose proof (reachable_control_history Hreachable_after) as Hhistory_after.
    unfold Sem.step, R.next_config in Hstep. cbn -[R.set_value] in Hstep.
    destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
    inversion Hstep; subst; cbn in Haligned_after |- *.
    destruct Haligned_after as [Hsummary Hk].
    assert (Hnew : full_summary_history tf st1 (R.frame_owner fr)).
    { rewrite <- (@Inv.set_value_frame_owner st fr direct st1 fr1 Hset).
      eapply aligned_summary_to_full_core.
      - exact Hhistory_after.
      - intros; discriminate.
      - exact Hsummary. }
    eapply (@full_state_history_transport tf st
      (R.RunCommit fr direct k) st1 (R.RunDrain fr1 k)).
    - intros owner Hsolved.
      destruct (@Inv.set_value_solved_origin
        st fr direct st1 fr1 owner Hset Hsolved) as [Hsolved0 | ->].
      + now left.
      + left. exact (proj1 (proj1 Haligned)).
    - intros owner Hqueued. left. eapply Inv.queued_set_value; eassumption.
    - intros owner Hactive. cbn in Hactive |- *.
      destruct Hactive as [-> | Hactive].
      + now right; right.
      + now right; left.
    - intros owner Hsummary0.
      destruct (V.eq_dec owner (R.frame_owner fr)) as [-> | Hneq].
      + now right; right.
      + right; right. eapply full_summary_set_value_other; eassumption.
    - exact Hfull.
  Qed.

  Lemma full_state_history_pop_to_active :
    forall tf st control popped rest control',
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      Inv.control_active popped control' ->
      (forall owner,
        Inv.control_active owner control -> Inv.control_active owner control') ->
      full_state_history tf st control ->
      full_state_history tf (R.with_queue st rest) control'.
  Proof.
    intros tf st control popped rest control' Hpop Hpopped Hactive Hfull.
    eapply (@full_state_history_transport tf st control
      (R.with_queue st rest) control').
    - intros owner Hsolved. now left.
    - intros owner Hqueued. unfold Inv.queued in Hqueued |- *.
      destruct (R.queue st) as [|head tail] eqn:Hqueue;
        cbn in Hpop; try discriminate.
      inversion Hpop; subst. cbn in Hqueued.
      destruct Hqueued as [-> | Hqueued']; [now right |now left].
    - intros owner Hactive0. right; left. now apply Hactive.
    - intros owner Hsummary.
      destruct (V.eq_dec owner popped) as [-> | Hneq].
      + now right; left.
      + right; right. eapply full_summary_pop_other; eassumption.
    - exact Hfull.
  Qed.

  Lemma full_state_history_run_drain_step :
    forall tf roots st fr k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      full_state_history tf st (R.RunDrain fr k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st fr k after Hreachable Hfull Hstep.
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
    destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
    - destruct (V.eq_dec next (R.frame_owner fr)) as [Hequal | Hdifferent].
      + destruct (R.queue_pop (R.queue st))
          as [[popped rest] |] eqn:Hpop; try discriminate.
        inversion Hstep; subst; cbn.
        assert (Hpopped : popped = R.frame_owner fr).
        { pose proof (@Total.queue_peek_pop_same
            (R.queue st) (R.frame_owner fr) popped rest Hpeek Hpop).
          congruence. }
        subst popped.
        eapply (@full_state_history_pop_to_active tf st
          (R.RunDrain fr k) (R.frame_owner fr) rest
          (R.RunRhs
            (R.fresh_frame (R.with_queue st rest)
              (R.frame_owner fr) (R.frame_phase fr))
            (tf (R.frame_owner fr)) k)).
        * exact Hpop.
        * cbn. now left.
        * intros owner Hactive. cbn in Hactive |- *. now right.
        * exact Hfull.
      + destruct (R.rank_lt st (R.frame_owner fr) next).
        * destruct (R.queue_pop (R.queue st))
            as [[popped rest] |] eqn:Hpop; try discriminate.
          inversion Hstep; subst; cbn.
          assert (Hpopped : popped = next).
          { pose proof (@Total.queue_peek_pop_same
              (R.queue st) next popped rest Hpeek Hpop). congruence. }
          subst popped.
          eapply (@full_state_history_pop_to_active tf st
            (R.RunDrain fr k) next rest
            (R.StartEpisode next (R.KDrain fr k))).
          -- exact Hpop.
          -- cbn. now left.
          -- intros owner Hactive. cbn in Hactive |- *. now right.
          -- exact Hfull.
        * inversion Hstep; subst; cbn.
          eapply (@full_state_history_same_solver_view tf st
            (R.RunDrain fr k)
            (R.reset_registered_cells st (R.frame_owner fr))
            (R.Return k)).
          -- apply Inv.reset_registered_cells_same_solver_view.
          -- intros owner Hactive. exact (or_introl Hactive).
          -- exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.RunDrain fr k)
        (R.reset_registered_cells st (R.frame_owner fr))
        (R.Return k)).
      + apply Inv.reset_registered_cells_same_solver_view.
      + intros owner Hactive. exact (or_introl Hactive).
      + exact Hfull.
  Qed.

  Lemma reachable_get_consistent :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      Inv.control_get_consistent (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots c Hsteps.
    pose proof (@Total.invariant_steps tf roots
      (R.initial_config roots) c (@Total.initial_invariant tf roots) Hsteps)
      as Hinv.
    exact (Total.invariant_get_consistent Hinv).
  Qed.

  Lemma full_state_history_return_step :
    forall tf roots st k after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.Return k |} ->
      full_state_history tf st (R.Return k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots st k after Hreachable Hfull Hstep.
    pose proof (reachable_get_consistent Hreachable) as Hconsistent.
    unfold Sem.step, R.next_config in Hstep.
    destruct k; cbn -[R.complete_get] in Hstep.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return R.KLoop) st R.RunLoop).
      + repeat split; reflexivity.
      + intros owner Hactive. contradiction.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return (R.KSeedLoop l)) st (R.RunSeedLoop l)).
      + repeat split; reflexivity.
      + intros owner Hactive. contradiction.
      + exact Hfull.
    - cbn in Hconsistent. destruct Hconsistent as [Htarget Hconsistent].
      destruct (R.complete_get st f t)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst; cbn.
      assert (Howner : R.frame_owner fr1 = R.frame_owner f).
      { pose proof (f_equal
          (fun result : (R.state * R.frame) * D.t =>
            R.frame_owner (snd (fst result))) Hget) as H.
        cbn in H. symmetry. exact H. }
      eapply (@full_state_history_transport tf st
        (R.Return (R.KAfterGet f t r k))
        st1 (R.RunRhs fr1 (r value) k)).
      + intros owner Hsolved.
        destruct (@Inv.complete_get_solved_origin
          st f t st1 fr1 value owner Hget Hsolved) as [Hsolved0 | ->].
        * now left.
        * now left.
      + intros owner Hqueued. left.
        eapply Inv.queued_complete_get; eassumption.
      + intros owner Hactive. cbn in Hactive |- *.
        destruct Hactive as [-> | Hactive].
        * right; left; left. symmetry. exact Howner.
        * now right; left; right.
      + intros owner Hsummary. right; right.
        eapply full_summary_complete_get; eassumption.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return (R.KAfterSide f r k)) st (R.RunRhs f r k)).
      + repeat split; reflexivity.
      + intros owner Hactive. now left.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return (R.KAfterSpawn f r k)) st (R.RunRhs f r k)).
      + repeat split; reflexivity.
      + intros owner Hactive. now left.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return (R.KDead f t l k)) st (R.RunDead f t l k)).
      + repeat split; reflexivity.
      + intros owner Hactive. now left.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_same_solver_view tf st
        (R.Return (R.KDrain f k)) st (R.RunDrain f k)).
      + repeat split; reflexivity.
      + intros owner Hactive. now left.
      + exact Hfull.
  Qed.

  Lemma full_state_history_start_episode_step :
    forall tf st owner k,
      full_state_history tf st (R.StartEpisode owner k) ->
      full_state_history tf (R.materialize st owner)
        (R.RunRhs
          (R.fresh_frame (R.materialize st owner) owner
            (U.initial_phase false owner))
          (tf owner) k).
  Proof.
    intros tf st owner k Hfull.
    eapply (@full_state_history_transport tf st (R.StartEpisode owner k)
      (R.materialize st owner)
      (R.RunRhs
        (R.fresh_frame (R.materialize st owner) owner
          (U.initial_phase false owner))
        (tf owner) k)).
    - intros variable Hsolved.
      destruct (@Inv.materialize_solved_origin_correctness
        st owner variable Hsolved)
        as [Hsolved0 | ->].
      + now left.
      + right; right. cbn. now left.
    - intros variable Hqueued. left. unfold Inv.queued in *.
      unfold R.materialize. destruct (M.lookup (R.sigma st) owner);
        exact Hqueued.
    - intros variable Hactive. cbn in Hactive |- *.
      destruct Hactive as [-> | Hactive].
      + now right; left; left.
      + now right; left; right.
    - intros variable Hsummary. right; right.
      now apply full_summary_materialize.
    - exact Hfull.
  Qed.

  Lemma full_state_history_enqueue :
    forall tf st control inserted,
      full_state_history tf st control ->
      full_state_history tf (R.enqueue st inserted) control.
  Proof.
    intros tf st control inserted Hfull.
    eapply (@full_state_history_transport
      tf st control (R.enqueue st inserted) control).
    - intros owner Hsolved. now left.
    - intros owner Hqueued. left. unfold Inv.queued in *.
      cbn. apply (proj2 (@Total.queue_insert_members
        (R.ranking st) inserted (R.queue st) owner)). now right.
    - intros owner Hactive. now right; left.
    - intros owner Hsummary. right; right.
      now apply full_summary_enqueue.
    - exact Hfull.
  Qed.

  Lemma full_state_history_control_active_equiv :
    forall tf st before after,
      (forall owner,
        Inv.control_active owner before <->
        Inv.control_active owner after) ->
      full_state_history tf st before ->
      full_state_history tf st after.
  Proof.
    intros tf st before after Hactive Hfull owner Hsolved.
    destruct (Hfull owner Hsolved)
      as [Hqueued | [Hbefore | Hsummary]].
    - now left.
    - right; left. now apply (proj1 (Hactive owner)).
    - now right; right.
  Qed.

  Lemma ordinary_full_state_history_run_dead_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct pending k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} ->
      full_state_history tf st (R.RunDead fr direct pending k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st fr direct pending k after
      Hordinary Hreachable Hfull Hstep.
    pose proof (@ordinary_reachable_clean tf roots finite Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunDead fr direct pending k |}
      Hreachable) as [_ Hcontrol].
    cbn in Hcontrol. destruct Hcontrol as [_ [-> _]].
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst; cbn.
    eapply (@full_state_history_same_solver_view tf st
      (R.RunDead fr direct [] k)
      (R.publish_targets st fr) (R.RunCommit fr direct k)).
    - apply Inv.publish_targets_same_solver_view.
    - intros owner Hactive. now left.
    - exact Hfull.
  Qed.

  Lemma ordinary_full_state_history_run_rhs_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr current k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} ->
      full_state_history tf st (R.RunRhs fr current k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st fr current k after
      Hordinary Hreachable Hfull Hstep.
    unfold Sem.step, R.next_config in Hstep.
    destruct current; cbn -[R.complete_get R.observe] in Hstep.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_control_active_equiv tf st
        (R.RunRhs fr (R.ConstraintSystem.Ret t) k)
        (R.RunDead fr t (S.elements (R.frame_previous_targets fr)) k)).
      + intros owner. cbn. tauto.
      + exact Hfull.
    - set (observed := R.observe st t) in *.
      assert (Hfull_observed : full_state_history tf observed
        (R.RunRhs fr (R.ConstraintSystem.Get t r) k)).
      { subst observed.
        eapply (@full_state_history_same_solver_view tf st
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
          (R.observe st t)
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)).
        - apply Inv.observe_same_solver_view.
        - intros owner Hactive. now left.
        - exact Hfull. }
      destruct (negb (R.is_materialized observed t) &&
        R.rank_lt observed (R.frame_owner fr) t)%bool eqn:Hdemand.
      + inversion Hstep; subst; cbn.
        eapply (@full_state_history_same_solver_view tf observed
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
          observed
          (R.StartEpisode t (R.KAfterGet fr t r k))).
        * repeat split; reflexivity.
        * intros owner Hactive. cbn in Hactive |- *.
          left. now right.
        * exact Hfull_observed.
      + set (st0 := if R.is_materialized observed t
          then observed else R.enqueue observed t) in *.
        assert (Hfull0 : full_state_history tf st0
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)).
        { subst st0. destruct (R.is_materialized observed t).
          - exact Hfull_observed.
          - now apply full_state_history_enqueue. }
        destruct (R.complete_get st0 fr t)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst; cbn.
        assert (Howner : R.frame_owner fr1 = R.frame_owner fr).
        { pose proof (f_equal
            (fun result : (R.state * R.frame) * D.t =>
              R.frame_owner (snd (fst result))) Hget) as H.
          cbn in H. symmetry. exact H. }
        eapply (@full_state_history_transport tf st0
          (R.RunRhs fr (R.ConstraintSystem.Get t r) k)
          st1 (R.RunRhs fr1 (r value) k)).
        * intros owner Hsolved.
          destruct (@Inv.complete_get_solved_origin
            st0 fr t st1 fr1 value owner Hget Hsolved)
            as [Hsolved0 | ->].
          -- now left.
          -- subst st0. destruct (R.is_materialized observed t)
               eqn:Hmaterialized.
             ++ left. now apply is_materialized_solved.
             ++ right; left. eapply Inv.queued_complete_get.
                ** exact Hget.
                ** unfold Inv.queued. cbn.
                   apply (proj2 (@Total.queue_insert_members
                     (R.ranking observed) t (R.queue observed) t)).
                   now left.
        * intros owner Hqueued. left.
          eapply Inv.queued_complete_get; eassumption.
        * intros owner Hactive. cbn in Hactive |- *.
          destruct Hactive as [-> | Hactive].
          -- right; left; left. symmetry. exact Howner.
          -- now right; left; right.
        * intros owner Hsummary. right; right.
          eapply full_summary_complete_get; eassumption.
        * exact Hfull0.
    - exfalso. eapply ordinary_reachable_side_impossible; eauto.
    - set (observed := R.observe st t) in *.
      assert (Hfull_observed : full_state_history tf observed
        (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)).
      { subst observed.
        eapply (@full_state_history_same_solver_view tf st
          (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)
          (R.observe st t)
          (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)).
        - apply Inv.observe_same_solver_view.
        - intros owner Hactive. now left.
        - exact Hfull. }
      destruct (R.is_materialized observed t) eqn:Hmaterialized.
      + inversion Hstep; subst; cbn.
        eapply (@full_state_history_control_active_equiv tf observed
          (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)
          (R.RunRhs fr current k)).
        * intros owner. cbn. tauto.
        * exact Hfull_observed.
      + destruct (R.rank_lt observed (R.frame_owner fr) t)
          eqn:Hhigher.
        * inversion Hstep; subst; cbn.
          eapply (@full_state_history_same_solver_view tf observed
            (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)
            observed
            (R.StartEpisode t (R.KAfterSpawn fr current k))).
          -- repeat split; reflexivity.
          -- intros owner Hactive. cbn in Hactive |- *.
             left. now right.
          -- exact Hfull_observed.
        * inversion Hstep; subst; cbn.
          assert (Hfull0 : full_state_history tf (R.enqueue observed t)
            (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)).
          { now apply full_state_history_enqueue. }
          eapply (@full_state_history_transport tf
            (R.enqueue observed t)
            (R.RunRhs fr (R.ConstraintSystem.Spawn t current) k)
            (R.materialize (R.enqueue observed t) t)
            (R.RunRhs fr current k)).
          -- intros owner Hsolved.
             destruct (@Inv.materialize_solved_origin_correctness
               (R.enqueue observed t) t owner Hsolved)
               as [Hsolved0 | ->].
             ++ now left.
             ++ right; left. unfold Inv.queued, R.materialize.
                destruct (M.lookup (R.sigma (R.enqueue observed t)) t);
                  cbn; apply (proj2 (@Total.queue_insert_members
                    (R.ranking observed) t (R.queue observed) t));
                  now left.
          -- intros owner Hqueued. left. unfold Inv.queued in *.
             unfold R.materialize.
             destruct (M.lookup (R.sigma (R.enqueue observed t)) t);
               exact Hqueued.
          -- intros owner Hactive. now right; left.
          -- intros owner Hsummary. right; right.
             now apply full_summary_materialize.
          -- exact Hfull0.
  Qed.

  Lemma full_state_history_run_loop_step :
    forall tf st after,
      full_state_history tf st R.RunLoop ->
      Sem.step tf {| R.cfg_state := st; R.cfg_control := R.RunLoop |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf st after Hfull Hstep.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    destruct (R.queue_pop (R.queue st))
      as [[owner rest] |] eqn:Hpop; try discriminate.
    inversion Hstep; subst; cbn.
    eapply (@full_state_history_pop_to_active tf st R.RunLoop
      owner rest (R.StartEpisode owner R.KLoop)).
    - exact Hpop.
    - cbn. now left.
    - intros variable Hactive. contradiction.
    - exact Hfull.
  Qed.

  Lemma full_state_history_run_seeds_step :
    forall tf st seeds after,
      full_state_history tf st (R.RunSeeds seeds) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds seeds |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf st seeds after Hfull Hstep.
    unfold Sem.step, R.next_config in Hstep.
    destruct seeds as [|root remaining]; cbn -[R.observe] in Hstep.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_control_active_equiv tf st
        (R.RunSeeds []) R.RunLoop).
      + intros owner. cbn. tauto.
      + exact Hfull.
    - destruct (R.is_materialized (R.observe st root) root).
      + inversion Hstep; subst; cbn.
        eapply (@full_state_history_same_solver_view tf st
          (R.RunSeeds (root :: remaining)) (R.observe st root)
          (R.RunSeeds remaining)).
        * apply Inv.observe_same_solver_view.
        * intros owner Hactive. contradiction.
        * exact Hfull.
      + inversion Hstep; subst; cbn.
        eapply (@full_state_history_same_solver_view tf st
          (R.RunSeeds (root :: remaining)) (R.observe st root)
          (R.StartEpisode root (R.KSeedLoop remaining))).
        * apply Inv.observe_same_solver_view.
        * intros owner Hactive. contradiction.
        * exact Hfull.
  Qed.

  Lemma full_state_history_run_seed_loop_step :
    forall tf st seeds after,
      full_state_history tf st (R.RunSeedLoop seeds) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop seeds |} after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf st seeds after Hfull Hstep.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    destruct (R.queue_pop (R.queue st))
      as [[owner rest] |] eqn:Hpop.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_pop_to_active tf st
        (R.RunSeedLoop seeds) owner rest
        (R.StartEpisode owner (R.KSeedLoop seeds))).
      + exact Hpop.
      + cbn. now left.
      + intros variable Hactive. contradiction.
      + exact Hfull.
    - inversion Hstep; subst; cbn.
      eapply (@full_state_history_control_active_equiv tf st
        (R.RunSeedLoop seeds) (R.RunSeeds seeds)).
      + intros owner. cbn. tauto.
      + exact Hfull.
  Qed.

  Lemma ordinary_full_state_history_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      full_state_history tf
        (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      full_state_history tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite [st control] after
      Hordinary Hreachable Hfull Hstep.
    destruct control.
    - eapply full_state_history_run_loop_step; eassumption.
    - eapply full_state_history_run_seeds_step; eassumption.
    - eapply full_state_history_run_seed_loop_step; eassumption.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      inversion Hstep; subst; cbn.
      now apply full_state_history_start_episode_step.
    - eapply ordinary_full_state_history_run_rhs_step; eassumption.
    - eapply ordinary_full_state_history_run_dead_step; eassumption.
    - eapply full_state_history_run_commit_step.
      + exact Hreachable.
      + pose proof (@ordinary_reachable_aligned_history
          tf roots finite Hordinary
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit f t c |}
          Hreachable) as Haligned.
        exact Haligned.
      + exact Hfull.
      + exact Hstep.
    - eapply full_state_history_run_drain_step; eassumption.
    - eapply full_state_history_return_step; eassumption.
  Qed.

  Theorem ordinary_reachable_full_state_history :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      forall c,
        Sem.steps tf (R.initial_config roots) c ->
        full_state_history tf
          (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots finite Hordinary final Hsteps.
    assert (Hpreserve : forall first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      full_state_history tf
        (R.cfg_state first) (R.cfg_control first) ->
      full_state_history tf
        (R.cfg_state last) (R.cfg_control last)).
    { intros first last Hreachable Hrun. revert Hreachable.
      induction Hrun as [c | first next last Hstep Hrun IH].
      - intros Hreachable Hhistory. exact Hhistory.
      - intros Hreachable Hhistory. apply IH.
        + eapply Total.Termination.steps_transitive; [exact Hreachable |].
          econstructor; [exact Hstep | constructor].
        + eapply ordinary_full_state_history_step; eauto. }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - apply initial_full_state_history.
  Qed.

  Lemma continuation_below_active :
    forall st upper k owner,
      Total.Termination.continuation_below st upper k ->
      Inv.continuation_active_correctness owner k ->
      R.rank_lt st owner upper = true.
  Proof.
    intros st upper k. revert upper.
    induction k; cbn; intros upper owner Hbelow Hactive;
      try contradiction.
    all: destruct Hbelow as [Htop Hbelow].
    - destruct Hactive as [-> | Hactive]; [exact Htop |].
      eapply Total.Termination.rank_lt_trans_true;
        [eapply IHk; eauto | exact Htop].
    - destruct Hactive as [-> | Hactive]; [exact Htop |].
      eapply Total.Termination.rank_lt_trans_true;
        [eapply IHk; eauto | exact Htop].
    - destruct Hactive as [-> | Hactive]; [exact Htop |].
      eapply Total.Termination.rank_lt_trans_true;
        [eapply IHk; eauto | exact Htop].
    - destruct Hactive as [-> | Hactive]; [exact Htop |].
      eapply Total.Termination.rank_lt_trans_true;
        [eapply IHk; eauto | exact Htop].
    - eapply Total.Termination.rank_lt_trans_true;
        [eapply IHk; eauto | exact Htop].
  Qed.

  Lemma reachable_run_drain_higher_inactive :
    forall tf roots st fr k variable,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      R.rank_lt st (R.frame_owner fr) variable = true ->
      ~ Inv.control_active variable (R.RunDrain fr k).
  Proof.
    intros tf roots st fr k variable Hreachable Hhigher Hactive.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hordered.
    cbn in Hordered, Hactive.
    pose proof (@continuation_below_active st (R.frame_owner fr)
      k variable Hordered Hactive) as Hlower.
    pose proof (@Total.rank_lt_true_ranked
      st (R.frame_owner fr) variable Hhigher) as [Hfr Hvariable].
    rewrite (@Total.rank_lt_asymmetric st
      (R.frame_owner fr) variable Hfr Hvariable Hhigher) in Hlower.
    discriminate.
  Qed.

  Lemma peek_maximal :
    forall st top variable,
      Total.queue_ordered st ->
      R.queue_peek (R.queue st) = Some top ->
      List.In variable (R.queue st) ->
      R.rank_lt st top variable = false.
  Proof.
    intros st top variable Hordered Hpeek Hin.
    unfold Total.queue_ordered, Total.queue_ordered_at in Hordered.
    destruct (R.queue st) as [|head tail] eqn:Hqueue;
      cbn in Hpeek; try discriminate.
    inversion Hpeek; subst head. inversion Hordered; subst.
    cbn in Hin. destruct Hin as [-> | Hin].
    - unfold R.rank_lt, R.ranking_lt.
      destruct (R.Ranking.lookup (R.ranking st) variable);
        cbn; [apply Nat.ltb_ge; lia | reflexivity].
    - apply Forall_forall with (x := variable) in H2; [|exact Hin].
      unfold Total.rank_above in H2.
      pose proof (@Total.rank_lt_true_ranked st variable top H2)
        as [Hvariable Htop].
      exact (@Total.rank_lt_asymmetric st variable top
        Hvariable Htop H2).
  Qed.

  Lemma clean_queue_excludes_higher :
    forall st owner variable,
      Total.rank_valid st ->
      Total.queue_ranked st ->
      Total.queue_ordered st ->
      R.rank_lt st owner variable = true ->
      (R.queue_peek (R.queue st) = None \/
       exists top,
         R.queue_peek (R.queue st) = Some top /\
         R.rank_lt st owner top = false) ->
      ~ Inv.queued st variable.
  Proof.
    intros st owner variable Hvalid Hranked Hordered
      Hhigher Hclean Hqueued.
    destruct Hclean as [Hnone | [top [Hpeek Hnot_higher]]].
    - unfold Inv.queued in Hqueued.
      destruct (R.queue st); cbn in Hnone; [contradiction | discriminate].
    - pose proof (@peek_maximal st top variable Hordered Hpeek Hqueued)
        as Hmaximal.
      assert (Htop : Total.ranked st top).
      { apply Hranked. destruct (R.queue st) as [|head tail] eqn:Hqueue;
          cbn in Hpeek; try discriminate.
        inversion Hpeek; subst. now left. }
      destruct (@Total.rank_lt_true_ranked st owner variable Hhigher)
        as [Howner Hvariable].
      destruct (V.eq_dec top variable) as [-> | Hdifferent].
      + rewrite Hhigher in Hnot_higher. discriminate.
      + destruct (@Total.rank_lt_total st top variable
          Hvalid Htop Hvariable Hdifferent) as [Htop_lower | Hvariable_lower].
        * rewrite Htop_lower in Hmaximal. discriminate.
        * pose proof (@Total.Termination.rank_lt_trans_true
            st owner variable top Hhigher Hvariable_lower) as Howner_top.
          rewrite Howner_top in Hnot_higher. discriminate.
  Qed.

  Lemma clean_drain_higher_upper_from_full :
    forall tf roots st fr k variable,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      full_state_history tf st (R.RunDrain fr k) ->
      (R.queue_peek (R.queue st) = None \/
       exists top,
         R.queue_peek (R.queue st) = Some top /\
         R.rank_lt st (R.frame_owner fr) top = false) ->
      R.rank_lt st (R.frame_owner fr) variable = true ->
      Sem.solved st variable ->
      exists upper, upper_observation tf st variable upper.
  Proof.
    intros tf roots st fr k variable
      Hreachable Hfull Hclean Hhigher Hsolved.
    pose proof (Total.reachable_configuration_ranked Hreachable) as Hranked.
    assert (Hnot_queued : ~ Inv.queued st variable).
    { eapply clean_queue_excludes_higher.
      - exact (Total.configuration_rank_valid Hranked).
      - exact (Total.data_queue_ranked
          (Total.configuration_state_data Hranked)).
      - exact (Total.configuration_queue_ordered Hranked).
      - exact Hhigher.
      - exact Hclean. }
    assert (Hnot_active :
      ~ Inv.control_active variable (R.RunDrain fr k)).
    { eapply reachable_run_drain_higher_inactive; eassumption. }
    destruct (Hfull variable Hsolved)
      as [Hqueued | [Hactive | Hsummary]];
      try contradiction.
    destruct Hsummary as
      [_ [upper [Hupper [Hreads [Hdirect Hspawns]]]]].
    exists upper. split; [exact Hupper |]. split; [exact Hdirect |].
    split.
    - intros target value Hin.
      destruct (Hreads target value Hin)
        as [Htarget [_ [Hvalue | Hqueued]]].
      + split; [exact Htarget |]. rewrite Hvalue. apply DL.leq_refl.
      + contradiction.
    - exact Hspawns.
  Qed.

  Definition wave_summary
    (tf : R.ConstraintSystem.system) (st : R.state) (fr : R.frame) : Prop :=
    exists upper,
      upper_observation tf st (R.frame_owner fr) upper.

  Inductive wave_stack
    (tf : R.ConstraintSystem.system) (root : V.t) (st : R.state)
    (base : R.continuation) : R.continuation -> Prop :=
  | WaveStackBase : wave_stack tf root st base base
  | WaveStackDrain :
      forall fr rest,
        (R.frame_owner fr = root \/
         R.rank_lt st root (R.frame_owner fr) = true) ->
        wave_summary tf st fr ->
        wave_stack tf root st base rest ->
        wave_stack tf root st base (R.KDrain fr rest).

  Fixpoint continuation_boxn_free (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr _ _ rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDead fr _ _ rest
    | R.KDrain fr rest =>
        R.frame_phase fr <> U.BoxN /\
        continuation_boxn_free rest
    end.

  Fixpoint continuation_has_boxn (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => False
    | R.KAfterGet fr _ _ rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDead fr _ _ rest
    | R.KDrain fr rest =>
        R.frame_phase fr = U.BoxN \/ continuation_has_boxn rest
    end.

  Definition control_has_boxn (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
    | R.StartEpisode _ k | R.Return k => continuation_has_boxn k
    | R.RunRhs fr _ k
    | R.RunDead fr _ _ k
    | R.RunCommit fr _ k
    | R.RunDrain fr k =>
        R.frame_phase fr = U.BoxN \/ continuation_has_boxn k
    end.

  Lemma continuation_boxn_free_excludes :
    forall k,
      continuation_boxn_free k -> continuation_has_boxn k -> False.
  Proof.
    induction k; cbn; try tauto.
  Qed.

  Lemma wave_stack_boxn_decompose :
    forall tf root st base k,
      continuation_boxn_free base ->
      wave_stack tf root st base k ->
      continuation_has_boxn k ->
      exists fr rest,
        k = R.KDrain fr rest /\
        (R.frame_owner fr = root \/
         R.rank_lt st root (R.frame_owner fr) = true) /\
        wave_summary tf st fr /\
        wave_stack tf root st base rest.
  Proof.
    intros tf root st base k Hbase Hstack Hboxn.
    destruct Hstack.
    - exfalso. eapply continuation_boxn_free_excludes; eassumption.
    - exists fr, rest. now repeat split.
  Qed.

  Definition higher_upper_history
    (tf : R.ConstraintSystem.system) (root : V.t) (st : R.state) : Prop :=
    forall owner,
      R.rank_lt st root owner = true ->
      Sem.solved st owner ->
      exists upper, upper_observation tf st owner upper.

  Definition higher_queue_solved (root : V.t) (st : R.state) : Prop :=
    forall owner,
      R.rank_lt st root owner = true ->
      Inv.queued st owner ->
      Sem.solved st owner.

  Definition readers_solved (st : R.state) : Prop :=
    forall target reader,
      S.mem reader (R.lookup_set (R.readers st) target) = true ->
      Sem.solved st reader.

  Lemma lookup_set_update_same :
    forall (table : M.t S.t) target readers,
      R.lookup_set (M.update table target readers) target = readers.
  Proof.
    intros table target readers. unfold R.lookup_set.
    rewrite ML.lookup_update_same. reflexivity.
  Qed.

  Lemma lookup_set_update_other :
    forall (table : M.t S.t) target readers observed,
      observed <> target ->
      R.lookup_set (M.update table target readers) observed =
      R.lookup_set table observed.
  Proof.
    intros table target readers observed Hneq.
    unfold R.lookup_set.
    now rewrite ML.lookup_update_other by exact Hneq.
  Qed.

  Lemma higher_queue_solved_enqueue :
    forall root st inserted,
      Sem.solved st inserted ->
      higher_queue_solved root st ->
      higher_queue_solved root (R.enqueue st inserted).
  Proof.
    intros root st inserted Hinserted Hqueue owner Hhigher Hqueued.
    unfold Inv.queued in Hqueued. cbn in Hqueued.
    apply (proj1 (@Total.queue_insert_members
      (R.ranking st) inserted (R.queue st) owner)) in Hqueued.
    destruct Hqueued as [-> | Hqueued].
    - exact Hinserted.
    - now apply Hqueue.
  Qed.

  Lemma clean_drain_higher_upper_history :
    forall tf roots (finite : Sem.finite_system tf roots) st fr k,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      (R.queue_peek (R.queue st) = None \/
       exists top,
         R.queue_peek (R.queue st) = Some top /\
         R.rank_lt st (R.frame_owner fr) top = false) ->
      higher_upper_history tf (R.frame_owner fr) st.
  Proof.
    intros tf roots finite st fr k Hordinary Hreachable Hclean
      owner Hhigher Hsolved.
    eapply clean_drain_higher_upper_from_full.
    - exact Hreachable.
    - exact (@ordinary_reachable_full_state_history
        tf roots finite Hordinary
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
        Hreachable).
    - exact Hclean.
    - exact Hhigher.
    - exact Hsolved.
  Qed.

  Lemma clean_drain_higher_queue_solved :
    forall st owner,
      Total.rank_valid st ->
      Total.queue_ranked st ->
      Total.queue_ordered st ->
      (R.queue_peek (R.queue st) = None \/
       exists top,
         R.queue_peek (R.queue st) = Some top /\
         R.rank_lt st owner top = false) ->
      higher_queue_solved owner st.
  Proof.
    intros st owner Hvalid Hranked Hordered Hclean
      variable Hhigher Hqueued.
    exfalso. eapply clean_queue_excludes_higher; eassumption.
  Qed.

  Lemma set_value_state_cases :
    forall st fr direct st' fr',
      R.set_value st fr direct = (st', fr') ->
      st' = st \/
      exists value,
        st' = Inv.commit_value st (R.frame_owner fr) value.
  Proof.
    intros st fr direct st' fr' Hset.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))).
    - inversion Hset; now left.
    - destruct (if S.mem (R.frame_owner fr) (R.controlled st)
        then U.update false (R.frame_owner fr) (R.frame_phase fr)
          (R.sigma_value st (R.frame_owner fr))
          (D.join direct (R.aggregate st (R.frame_owner fr)))
        else (R.frame_phase fr,
          D.join direct (R.aggregate st (R.frame_owner fr))))
        as [phase value] eqn:Hupdate.
      cbn in Hset.
      destruct (R.equivalent value
        (R.sigma_value st (R.frame_owner fr))).
      + inversion Hset; now left.
      + inversion Hset; subst. right. exists value. reflexivity.
  Qed.

  Lemma readers_solved_set_value :
    forall st fr direct st' fr',
      readers_solved st ->
      R.set_value st fr direct = (st', fr') ->
      readers_solved st'.
  Proof.
    intros st fr direct st' fr' Hreaders Hset.
    destruct (@set_value_state_cases
      st fr direct st' fr' Hset) as [-> | [value ->]];
      [exact Hreaders |].
    intros target reader Hmem.
    unfold Inv.commit_value in Hmem |- *.
    cbn in Hmem |- *.
    destruct (V.eq_dec target (R.frame_owner fr)) as [-> | Hneq].
    - rewrite lookup_set_update_same in Hmem.
      rewrite SL.empty_spec in Hmem. discriminate.
    - rewrite lookup_set_update_other in Hmem by exact Hneq.
      eapply Inv.set_value_solved.
      + exact Hset.
      + now apply Hreaders with target.
  Qed.

  Lemma readers_solved_complete_get :
    forall st fr target st' fr' value,
      readers_solved st ->
      Sem.solved st (R.frame_owner fr) ->
      R.complete_get st fr target = (st', fr', value) ->
      readers_solved st'.
  Proof.
    intros st fr target st' fr' value
      Hreaders Howner Hget observed reader Hmem.
    assert (Hreader : Sem.solved st reader).
    { pose proof Hget as Hshape.
      unfold R.complete_get in Hshape.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      inversion Hshape; subst st' fr' value; clear Hshape.
      unfold R.materialize in Hmem.
      destruct (M.lookup
        (R.sigma
          (R.with_readers base
            (M.update (R.readers base) target
              (S.add (R.frame_owner fr)
                (R.lookup_set (R.readers base) target))))) target);
        cbn in Hmem.
      all: destruct (V.eq_dec observed target) as [-> | Hneq].
      all: try rewrite lookup_set_update_same in Hmem.
      all: try rewrite lookup_set_update_other in Hmem by exact Hneq.
      all: try (apply SL.add_spec in Hmem;
        destruct Hmem as [-> | Hmem]; [exact Howner |]).
      all: subst base.
      all: destruct (R.rank_lt st (R.frame_owner fr) target);
        cbn in Hmem.
      all: eapply Hreaders; exact Hmem. }
    eapply complete_get_preserves_solved; eassumption.
  Qed.

  Lemma readers_solved_transport :
    forall st st',
      R.readers st' = R.readers st ->
      (forall owner,
        Sem.solved st owner -> Sem.solved st' owner) ->
      readers_solved st ->
      readers_solved st'.
  Proof.
    intros st st' Hreaders Hsolved Hsound
      target reader Hmem.
    rewrite Hreaders in Hmem.
    now apply Hsolved, Hsound with target.
  Qed.

  Lemma ordinary_readers_solved_run_rhs_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr current k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |} ->
      Inv.control_history tf st (R.RunRhs fr current k) ->
      readers_solved st ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr current k |}
        after ->
      readers_solved (R.cfg_state after).
  Proof.
    intros tf roots finite st fr current k after
      Hordinary Hreachable [Hcurrent Hk] Hreaders Hstep.
    pose proof Hstep as Hsemantic.
    assert (Hsolved_map : forall owner,
      Sem.solved st owner -> Sem.solved (R.cfg_state after) owner).
    { intros owner Hsolved. unfold Sem.step in Hsemantic.
      exact (@Inv.next_config_preserves_solved tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |}
        after owner Hsolved Hsemantic). }
    unfold Sem.step, R.next_config in Hstep.
    destruct current; cbn -[R.complete_get R.observe] in Hstep.
    - inversion Hstep; subst. exact Hreaders.
    - destruct (Inv.observe_same_solver_view st t)
        as [[Hsigma [Hreader_view Hqueue_view]] Hcontributions].
      assert (Hreaders_observed : readers_solved (R.observe st t)).
      { eapply (@readers_solved_transport st (R.observe st t)).
        - exact Hreader_view.
        - intros owner [value Hvalue]. exists value.
          now rewrite Hsigma.
        - exact Hreaders. }
      assert (Howner_observed :
        Sem.solved (R.observe st t) (R.frame_owner fr)).
      { destruct (proj1 Hcurrent) as [value Hvalue].
        exists value. now rewrite Hsigma. }
      destruct (negb (R.is_materialized (R.observe st t) t) &&
        R.rank_lt (R.observe st t) (R.frame_owner fr) t)%bool.
      + inversion Hstep; subst. exact Hreaders_observed.
      + set (st0 := if R.is_materialized (R.observe st t) t
          then R.observe st t else R.enqueue (R.observe st t) t) in *.
        assert (Hreaders0 : readers_solved st0).
        { subst st0. destruct (R.is_materialized (R.observe st t) t);
            exact Hreaders_observed. }
        assert (Howner0 : Sem.solved st0 (R.frame_owner fr)).
        { subst st0. destruct (R.is_materialized (R.observe st t) t);
            exact Howner_observed. }
        destruct (R.complete_get st0 fr t)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst; cbn.
        eapply readers_solved_complete_get; eassumption.
    - exfalso. eapply ordinary_reachable_side_impossible; eassumption.
    - destruct (Inv.observe_same_solver_view st t)
        as [[Hsigma [Hreader_view Hqueue_view]] Hcontributions].
      assert (Hreaders_observed : readers_solved (R.observe st t)).
      { eapply (@readers_solved_transport st (R.observe st t)).
        - exact Hreader_view.
        - intros owner [value Hvalue]. exists value.
          now rewrite Hsigma.
        - exact Hreaders. }
      destruct (R.is_materialized (R.observe st t) t).
      + inversion Hstep; subst. exact Hreaders_observed.
      + destruct (R.rank_lt (R.observe st t) (R.frame_owner fr) t).
        * inversion Hstep; subst. exact Hreaders_observed.
        * inversion Hstep; subst; cbn.
          eapply (@readers_solved_transport
            (R.observe st t)
            (R.materialize (R.enqueue (R.observe st t) t) t)).
          -- unfold R.materialize.
             destruct (M.lookup
               (R.sigma (R.enqueue (R.observe st t) t)) t);
               reflexivity.
          -- intros owner Hsolved.
             apply Inv.materialize_preserves_solved. exact Hsolved.
          -- exact Hreaders_observed.
  Qed.

  Lemma readers_solved_return_step :
    forall tf st k after,
      Inv.control_history tf st (R.Return k) ->
      readers_solved st ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after ->
      readers_solved (R.cfg_state after).
  Proof.
    intros tf st k after Hhistory Hreaders Hstep.
    unfold Sem.step, R.next_config in Hstep.
    destruct k; cbn -[R.complete_get] in Hstep;
      try (inversion Hstep; subst; exact Hreaders).
    cbn in Hhistory. destruct Hhistory as [Hcurrent Hrest].
    destruct (R.complete_get st f t)
      as [[st1 fr1] value] eqn:Hget.
    inversion Hstep; subst; cbn.
    eapply readers_solved_complete_get.
    - exact Hreaders.
    - exact (proj1 Hcurrent).
    - exact Hget.
  Qed.

  Lemma ordinary_readers_solved_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      readers_solved (R.cfg_state before) ->
      Sem.step tf before after ->
      readers_solved (R.cfg_state after).
  Proof.
    intros tf roots finite [st control] after
      Hordinary Hreachable Hreaders Hstep.
    pose proof Hstep as Hsemantic.
    pose proof (reachable_control_history Hreachable) as Hhistory.
    assert (Hsolved_map : forall owner,
      Sem.solved st owner -> Sem.solved (R.cfg_state after) owner).
    { intros owner Hsolved. unfold Sem.step in Hsemantic.
      exact (@Inv.next_config_preserves_solved tf
        {| R.cfg_state := st; R.cfg_control := control |}
        after owner Hsolved Hsemantic). }
    destruct control.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        try discriminate.
      inversion Hstep; subst. exact Hreaders.
    - unfold Sem.step, R.next_config in Hstep.
      destruct l as [|root remaining]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst. exact Hreaders.
      + destruct (Inv.observe_same_solver_view st root)
          as [[Hsigma [Hreader_view Hqueue_view]] Hcontributions].
        destruct (R.is_materialized (R.observe st root) root).
        * inversion Hstep; subst.
          eapply (@readers_solved_transport st (R.observe st root)).
          -- exact Hreader_view.
          -- exact Hsolved_map.
          -- exact Hreaders.
        * inversion Hstep; subst.
          eapply (@readers_solved_transport st (R.observe st root)).
          -- exact Hreader_view.
          -- exact Hsolved_map.
          -- exact Hreaders.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        inversion Hstep; subst; exact Hreaders.
    - unfold Sem.step, R.next_config in Hstep.
      cbn -[R.materialize] in Hstep.
      inversion Hstep; subst; cbn.
      eapply (@readers_solved_transport st (R.materialize st t)).
      + unfold R.materialize.
        destruct (M.lookup (R.sigma st) t); reflexivity.
      + intros owner Hsolved.
        now apply Inv.materialize_preserves_solved.
      + exact Hreaders.
    - eapply ordinary_readers_solved_run_rhs_step; eassumption.
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := st; R.cfg_control := R.RunDead f t l c |}
        Hreachable) as [_ Hcontrol].
      cbn in Hcontrol. destruct Hcontrol as [_ [-> _]].
      unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      inversion Hstep; subst. exact Hreaders.
    - unfold Sem.step, R.next_config in Hstep.
      cbn -[R.set_value] in Hstep.
      destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst; cbn.
      eapply readers_solved_set_value; eassumption.
    - unfold Sem.step, R.next_config in Hstep.
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      + destruct (V.eq_dec next (R.frame_owner f)).
        * destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
            try discriminate.
          inversion Hstep; subst. exact Hreaders.
        * destruct (R.rank_lt st (R.frame_owner f) next).
          -- destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
               try discriminate.
             inversion Hstep; subst. exact Hreaders.
          -- inversion Hstep; subst.
             eapply (@readers_solved_transport st
               (R.reset_registered_cells st (R.frame_owner f))).
             ++ exact (proj1 (proj2 (proj1
                  (Inv.reset_registered_cells_same_solver_view
                    st (R.frame_owner f))))).
             ++ exact Hsolved_map.
             ++ exact Hreaders.
      + inversion Hstep; subst.
        eapply (@readers_solved_transport st
          (R.reset_registered_cells st (R.frame_owner f))).
        * exact (proj1 (proj2 (proj1
             (Inv.reset_registered_cells_same_solver_view
               st (R.frame_owner f))))).
        * exact Hsolved_map.
        * exact Hreaders.
    - eapply readers_solved_return_step; eassumption.
  Qed.

  Theorem ordinary_reachable_readers_solved :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      forall c,
        Sem.steps tf (R.initial_config roots) c ->
        readers_solved (R.cfg_state c).
  Proof.
    intros tf roots finite Hordinary final Hsteps.
    assert (Hpreserve : forall first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      readers_solved (R.cfg_state first) ->
      readers_solved (R.cfg_state last)).
    { intros first last Hreachable Hrun. revert Hreachable.
      induction Hrun as [c | first next last Hstep Hrun IH].
      - intros Hreachable Hsound. exact Hsound.
      - intros Hreachable Hsound. apply IH.
        + eapply Total.Termination.steps_transitive; [exact Hreachable |].
          econstructor; [exact Hstep | constructor].
        + eapply ordinary_readers_solved_step; eauto. }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - intros target reader Hmem. cbn in Hmem.
      unfold R.lookup_set in Hmem.
      rewrite ML.lookup_empty, SL.empty_spec in Hmem.
      discriminate.
  Qed.

  Lemma higher_queue_solved_set_value :
    forall root st fr direct st' fr',
      higher_queue_solved root st ->
      readers_solved st ->
      R.set_value st fr direct = (st', fr') ->
      higher_queue_solved root st'.
  Proof.
    intros root st fr direct st' fr'
      Hqueue Hreaders Hset owner Hhigher Hqueued.
    destruct (@set_value_state_cases
      st fr direct st' fr' Hset) as [-> | [value ->]].
    - now apply Hqueue.
    - unfold Inv.commit_value in Hqueued.
      unfold Inv.queued in Hqueued. cbn in Hqueued.
      apply (proj1 (@Total.queue_insert_all_members
        (R.ranking st)
        (S.elements
          (R.lookup_set (R.readers st) (R.frame_owner fr)))
        (R.queue st) owner)) in Hqueued.
      destruct Hqueued as [Hinvalidated | Hqueued0].
      + eapply (@Inv.set_value_solved st fr direct
          (Inv.commit_value st (R.frame_owner fr) value)
          fr' owner Hset).
        eapply Hreaders with (target := R.frame_owner fr).
        apply SL.mem_spec. exact Hinvalidated.
      + eapply (@Inv.set_value_solved st fr direct
          (Inv.commit_value st (R.frame_owner fr) value)
          fr' owner Hset).
        eapply Hqueue; eassumption.
  Qed.

  Lemma higher_upper_history_set_value :
    forall tf root st fr direct st' fr' current,
      higher_upper_history tf root st ->
      R.rank_lt st root (R.frame_owner fr) = true ->
      upper_observation tf st' (R.frame_owner fr) current ->
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      higher_upper_history tf root st'.
  Proof.
    intros tf root st fr direct st' fr' current
      Hhistory Howner_higher Hcurrent Hset Hdecrease
      owner Hhigher Hsolved.
    pose proof (@set_value_same_ranking
      st fr direct st' fr' Hset) as Hranking.
    unfold R.rank_lt, R.ranking_lt in Hhigher.
    rewrite Hranking in Hhigher.
    destruct (V.eq_dec owner (R.frame_owner fr)) as [-> | Hneq].
    - now exists current.
    - destruct (@Inv.set_value_solved_origin
        st fr direct st' fr' owner Hset Hsolved)
        as [Hsolved0 | Heq]; [| contradiction].
      destruct (Hhistory owner Hhigher Hsolved0) as [upper Hupper].
      exists upper. eapply upper_observation_decrease_other.
      + eapply set_value_state_values_le; eassumption.
      + eapply Total.set_value_sigma_value_other_correctness; eassumption.
      + exact Hupper.
  Qed.

  Lemma higher_upper_history_set_value_root :
    forall tf root st fr direct st' fr',
      higher_upper_history tf root st ->
      R.frame_owner fr = root ->
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      higher_upper_history tf root st'.
  Proof.
    intros tf root st fr direct st' fr'
      Hhistory Hroot Hset Hdecrease owner Hhigher Hsolved.
    pose proof (@set_value_same_ranking
      st fr direct st' fr' Hset) as Hranking.
    assert (Hhigher0 : R.rank_lt st root owner = true).
    { unfold R.rank_lt, R.ranking_lt in Hhigher |- *.
      now rewrite Hranking in Hhigher. }
    assert (Hneq : owner <> R.frame_owner fr).
    { intro Heq. subst owner.
      eapply Total.rank_lt_true_neq_correctness in Hhigher0.
      apply Hhigher0. symmetry. exact Hroot. }
    destruct (@Inv.set_value_solved_origin
      st fr direct st' fr' owner Hset Hsolved)
      as [Hsolved0 | Heq]; [| contradiction].
    destruct (Hhistory owner Hhigher0 Hsolved0) as [upper Hupper].
    exists upper. eapply upper_observation_decrease_other.
    - eapply set_value_state_values_le; eassumption.
    - eapply Total.set_value_sigma_value_other_correctness; eassumption.
    - exact Hupper.
  Qed.

  Lemma upper_observation_sigma_view :
    forall tf st st' owner upper,
      R.sigma st' = R.sigma st ->
      upper_observation tf st owner upper ->
      upper_observation tf st' owner upper.
  Proof.
    intros tf st st' owner upper Hsigma
      [Hupper [Hdirect [Hreads Hspawns]]].
    split; [exact Hupper |]. split.
    - unfold R.sigma_value in *. now rewrite Hsigma.
    - split.
      + intros target value Hin.
        destruct (Hreads target value Hin)
          as [[found Hfound] Hbelow].
        split.
        * exists found. now rewrite Hsigma.
        * unfold R.sigma_value in *. now rewrite Hsigma.
      + intros target Hin.
        destruct (Hspawns target Hin) as [found Hfound].
        exists found. now rewrite Hsigma.
  Qed.

  Lemma higher_upper_history_sigma_view :
    forall tf root st st',
      R.ranking st' = R.ranking st ->
      R.sigma st' = R.sigma st ->
      higher_upper_history tf root st ->
      higher_upper_history tf root st'.
  Proof.
    intros tf root st st' Hranking Hsigma Hhistory
      owner Hhigher [value Hlookup].
    unfold R.rank_lt, R.ranking_lt in Hhigher.
    rewrite Hranking in Hhigher.
    assert (Hsolved : Sem.solved st owner).
    { exists value. now rewrite Hsigma in Hlookup. }
    destruct (Hhistory owner Hhigher Hsolved) as [upper Hupper].
    exists upper. eapply upper_observation_sigma_view; eassumption.
  Qed.

  Lemma higher_queue_solved_sigma_queue_view :
    forall root st st',
      R.ranking st' = R.ranking st ->
      R.sigma st' = R.sigma st ->
      R.queue st' = R.queue st ->
      higher_queue_solved root st ->
      higher_queue_solved root st'.
  Proof.
    intros root st st' Hranking Hsigma Hqueue Hhistory
      owner Hhigher Hqueued.
    unfold R.rank_lt, R.ranking_lt in Hhigher.
    rewrite Hranking in Hhigher.
    assert (Hqueued0 : Inv.queued st owner).
    { unfold Inv.queued in *. now rewrite Hqueue in Hqueued. }
    destruct (Hhistory owner Hhigher Hqueued0) as [value Hvalue].
    exists value. unfold Sem.solved in *. now rewrite Hsigma.
  Qed.

  Lemma wave_completed_sigma_view :
    forall tf st st' fr direct,
      R.sigma st' = R.sigma st ->
      wave_completed tf st fr direct ->
      wave_completed tf st' fr direct.
  Proof.
    intros tf st st' fr direct Hsigma
      [current [upper
        [Hcurrent [Hupper [Hcurrent_direct
          [Hreads [Hupper_direct
            [Hcurrent_reads Hcurrent_spawns]]]]]]]].
    exists current, upper.
    split; [exact Hcurrent |]. split; [exact Hupper |].
    split; [exact Hcurrent_direct |]. split; [exact Hreads |].
    split.
    - unfold R.sigma_value in *. now rewrite Hsigma.
    - split.
      + intros target value Hin.
        destruct (Hcurrent_reads target value Hin)
          as [[found Hfound] Hbelow].
        split.
        * exists found. now rewrite Hsigma.
        * unfold R.sigma_value in *. now rewrite Hsigma.
      + intros target Hin.
        destruct (Hcurrent_spawns target Hin) as [found Hfound].
        exists found. now rewrite Hsigma.
  Qed.

  Lemma wave_stack_sigma_view :
    forall tf root st st' base k,
      R.ranking st' = R.ranking st ->
      R.sigma st' = R.sigma st ->
      wave_stack tf root st base k ->
      wave_stack tf root st' base k.
  Proof.
    intros tf root st st' base k Hranking Hsigma Hstack.
    induction Hstack.
    - constructor.
    - constructor.
      + destruct H as [Hroot | Hroot].
        * now left.
        * right. unfold R.rank_lt, R.ranking_lt in *.
          now rewrite Hranking.
      + destruct H0 as [upper Hupper]. exists upper.
        eapply upper_observation_sigma_view; eassumption.
      + exact IHHstack.
  Qed.

  Lemma wave_summary_set_value_other :
    forall tf st fr direct st' fr' summary,
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      R.frame_owner summary <> R.frame_owner fr ->
      wave_summary tf st summary ->
      wave_summary tf st' summary.
  Proof.
    intros tf st fr direct st' fr' summary
      Hset Hdecrease Hneq [upper Hupper].
    exists upper. eapply upper_observation_decrease_other.
    - eapply set_value_state_values_le; eassumption.
    - eapply Total.set_value_sigma_value_other_correctness; eassumption.
    - exact Hupper.
  Qed.

  Lemma wave_stack_set_value :
    forall tf root st fr direct st' fr' base k,
      R.set_value st fr direct = (st', fr') ->
      D.leq (R.sigma_value st' (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = true ->
      Total.Termination.continuation_below
        st (R.frame_owner fr) k ->
      wave_stack tf root st base k ->
      wave_stack tf root st' base k.
  Proof.
    intros tf root st fr direct st' fr' base k
      Hset Hdecrease Hbelow Hstack.
    pose proof (@set_value_same_ranking
      st fr direct st' fr' Hset) as Hranking.
    induction Hstack.
    - constructor.
    - cbn in Hbelow. destruct Hbelow as [Hlt Hbelow].
      constructor.
      + destruct H as [Hroot | Hroot].
        * now left.
        * right. unfold R.rank_lt, R.ranking_lt in *.
          now rewrite Hranking.
      + eapply wave_summary_set_value_other.
        * exact Hset.
        * exact Hdecrease.
        * eapply Total.rank_lt_true_neq_correctness. exact Hlt.
        * exact H0.
      + apply IHHstack.
        eapply Total.continuation_below_raise_correctness;
          eassumption.
  Qed.

  Lemma work_queue_pop_members :
    forall queue head tail owner,
      R.queue_pop queue = Some (head, tail) ->
      (List.In owner queue <->
       owner = head \/ List.In owner tail).
  Proof.
    intros [|first rest] head tail owner Hpop;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. cbn. split.
    - intros [Heq | Hin].
      + now left; symmetry.
      + now right.
    - intros [Heq | Hin].
      + now left; symmetry.
      + now right.
  Qed.

  Lemma higher_queue_solved_pop :
    forall root st popped rest,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      higher_queue_solved root st ->
      higher_queue_solved root (R.with_queue st rest).
  Proof.
    intros root st popped rest Hpop Hqueue owner Hhigher Hqueued.
    apply Hqueue with (owner := owner).
    - exact Hhigher.
    - unfold Inv.queued in *. cbn in Hqueued.
      apply (proj2 (@work_queue_pop_members
        (R.queue st) popped rest owner Hpop)).
      now right.
  Qed.

  Lemma materialize_solved_state :
    forall st owner,
      Sem.solved st owner ->
      R.materialize st owner = st.
  Proof.
    intros st owner [value Hvalue].
    unfold R.materialize. now rewrite Hvalue.
  Qed.

  Definition wave_control
    (tf : R.ConstraintSystem.system) (root : V.t)
    (st : R.state) (control : R.control) : Prop :=
    exists base,
      continuation_boxn_free base /\
      higher_upper_history tf root st /\
      higher_queue_solved root st /\
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
      | R.StartEpisode owner k =>
          R.rank_lt st root owner = true /\
          Sem.solved st owner /\
          wave_summary tf st
            (R.fresh_frame (R.materialize st owner) owner
              (U.initial_phase false owner)) /\
          wave_stack tf root st base k
      | R.RunRhs fr current k =>
          (R.frame_owner fr = root \/
           R.rank_lt st root (R.frame_owner fr) = true) /\
          wave_evaluation tf st fr current /\
          wave_stack tf root st base k
      | R.RunDead fr direct _ k
      | R.RunCommit fr direct k =>
          (R.frame_owner fr = root \/
           R.rank_lt st root (R.frame_owner fr) = true) /\
          wave_completed tf st fr direct /\
          wave_stack tf root st base k
      | R.RunDrain fr k =>
          (R.frame_owner fr = root \/
           R.rank_lt st root (R.frame_owner fr) = true) /\
          wave_summary tf st fr /\
          wave_stack tf root st base k
      | R.Return k => wave_stack tf root st base k
      end.

  Lemma ordinary_wave_run_rhs_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      root st fr current k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} ->
      wave_control tf root st (R.RunRhs fr current k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} after ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite root st fr current k after
      Hordinary Hreachable
      [base [Hbase [Hhigher [Hqueue
        [Howner [Hwave Hstack]]]]]] Hstep.
    pose proof (@Total.reachable_config_supported
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control := R.RunRhs fr current k |}
      Hreachable) as Hsupported.
    destruct Hsupported as [_ Hcontrol_supported].
    cbn in Hcontrol_supported.
    destruct Hcontrol_supported as
      [Hframe_supported [Hbody_supported Hk_supported]].
    pose proof (@reachable_solved_ranked tf roots
      {| R.cfg_state := st;
         R.cfg_control := R.RunRhs fr current k |}
      Hreachable) as Hsolved_ranked.
    cbn in Hsolved_ranked.
    unfold Sem.step, R.next_config in Hstep.
    destruct current; cbn -[R.complete_get R.observe] in Hstep.
    - inversion Hstep; subst; cbn.
      exists base. repeat split; try assumption.
      now apply wave_evaluation_completed.
    - assert (Htarget : Sem.solved st t).
      { eapply wave_evaluation_get_target_solved.
        - exact (ordinary_dependencies_monotone
            Hordinary (R.frame_owner fr)).
        - exact Hbody_supported.
        - exact Hwave. }
      rewrite (observe_ranked_state (Hsolved_ranked t Htarget)) in Hstep.
      rewrite (solved_is_materialized Htarget) in Hstep.
      cbn -[R.complete_get] in Hstep.
      destruct (R.complete_get st fr t)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst; cbn.
      destruct (@complete_get_solved_view
        st fr t st1 fr1 value Htarget Hget)
        as [Hsigma [Hframe_owner Hvalue]].
      pose proof (@complete_get_same_ranking
        st fr t st1 fr1 value Hget) as Hranking.
      exists base. split; [exact Hbase |]. split.
      + eapply higher_upper_history_sigma_view; eassumption.
      + split.
        * eapply higher_queue_solved_sigma_queue_view.
          -- exact Hranking.
          -- exact Hsigma.
          -- eapply Total.Termination.complete_get_queue. exact Hget.
          -- exact Hqueue.
        * split.
          -- rewrite Hframe_owner.
             destruct Howner as [Howner | Howner].
             ++ now left.
             ++ right. unfold R.rank_lt, R.ranking_lt in *.
                now rewrite Hranking.
          -- split.
             ++ eapply wave_evaluation_get.
                ** exact (ordinary_dependencies_monotone
                     Hordinary (R.frame_owner fr)).
                ** exact Hbody_supported.
                ** exact Hwave.
                ** exact Hget.
             ++ eapply wave_stack_sigma_view; eassumption.
    - exfalso. eapply ordinary_reachable_side_impossible; eassumption.
    - assert (Htarget : Sem.solved st t).
      { eapply wave_evaluation_spawn_target_solved.
        - exact (ordinary_dependencies_monotone
            Hordinary (R.frame_owner fr)).
        - exact (ordinary_effects_monotone
            Hordinary (R.frame_owner fr)).
        - exact Hbody_supported.
        - exact Hwave. }
      rewrite (observe_ranked_state (Hsolved_ranked t Htarget)) in Hstep.
      rewrite (solved_is_materialized Htarget) in Hstep.
      inversion Hstep; subst; cbn.
      exists base. repeat split; try assumption.
      eapply wave_evaluation_spawn; eassumption.
  Qed.

  Lemma ordinary_wave_run_dead_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      root st fr direct pending k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} ->
      wave_control tf root st
        (R.RunDead fr direct pending k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} after ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite root st fr direct pending k after
      Hordinary Hreachable
      [base [Hbase [Hhigher [Hqueue
        [Howner [Hwave Hstack]]]]]] Hstep.
    pose proof (@ordinary_reachable_clean tf roots finite Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunDead fr direct pending k |}
      Hreachable) as [_ Hcontrol].
    cbn in Hcontrol. destruct Hcontrol as [_ [-> _]].
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst; cbn.
    exists base. split; [exact Hbase |].
    split; [exact Hhigher |]. split; [exact Hqueue |].
    split; [exact Howner |]. split.
    - eapply (@wave_completed_sigma_view tf st
        (R.publish_targets st fr) fr direct).
      + reflexivity.
      + exact Hwave.
    - eapply (@wave_stack_sigma_view tf root st
        (R.publish_targets st fr) base k).
      + reflexivity.
      + reflexivity.
      + exact Hstack.
  Qed.

  Lemma ordinary_wave_run_drain_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      root st fr k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
      wave_control tf root st (R.RunDrain fr k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} after ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite root st fr k after
      Hordinary Hreachable
      [base [Hbase [Hhigher [Hqueue
        [Howner [Hwave Hstack]]]]]] Hstep.
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
    destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
    - destruct (V.eq_dec next (R.frame_owner fr))
        as [Heq | Hnext_neq].
      + subst next.
        destruct (R.queue_pop (R.queue st))
          as [[popped rest] |] eqn:Hpop; try discriminate.
        assert (Hpopped : popped = R.frame_owner fr).
        { pose proof (@Total.queue_peek_pop_same
            (R.queue st) (R.frame_owner fr) popped rest Hpeek Hpop).
          congruence. }
        subst popped. inversion Hstep; subst; cbn.
        exists base. split; [exact Hbase |].
        split.
        * eapply higher_upper_history_sigma_view;
            [reflexivity | reflexivity | exact Hhigher].
        * split.
          -- eapply higher_queue_solved_pop; eassumption.
          -- split; [exact Howner |]. split.
             ++ destruct Hwave as [upper Hupper].
                eapply (@initial_wave_evaluation tf
                  (R.with_queue st rest)
                  (R.fresh_frame (R.with_queue st rest)
                    (R.frame_owner fr) (R.frame_phase fr)) upper).
                cbn. change (upper_observation tf
                  (R.with_queue st rest) (R.frame_owner fr) upper).
                eapply upper_observation_sigma_view;
                  [reflexivity | exact Hupper].
             ++ eapply (@wave_stack_sigma_view tf root st
                  (R.with_queue st rest) base k);
                  [reflexivity | reflexivity | exact Hstack].
      + destruct (R.rank_lt st (R.frame_owner fr) next)
          eqn:Hnext_higher.
        * destruct (R.queue_pop (R.queue st))
            as [[popped rest] |] eqn:Hpop; try discriminate.
          assert (Hpopped : popped = next).
          { pose proof (@Total.queue_peek_pop_same
              (R.queue st) next popped rest Hpeek Hpop).
            congruence. }
          subst popped. inversion Hstep; subst; cbn.
          assert (Hnext_queued : Inv.queued st next).
          { unfold Inv.queued.
            apply (proj2 (@work_queue_pop_members
              (R.queue st) next rest next Hpop)).
            now left. }
          assert (Hnext_root : R.rank_lt st root next = true).
          { destruct Howner as [Hroot | Howner_higher].
            - now rewrite <- Hroot.
            - eapply Total.Termination.rank_lt_trans_true; eassumption. }
          assert (Hnext_solved : Sem.solved st next).
          { eapply Hqueue; eassumption. }
          destruct (Hhigher next Hnext_root Hnext_solved)
            as [upper Hupper].
          exists base. split; [exact Hbase |].
          split.
          -- eapply higher_upper_history_sigma_view;
               [reflexivity | reflexivity | exact Hhigher].
          -- split.
             ++ eapply higher_queue_solved_pop; eassumption.
             ++ split; [exact Hnext_root |].
                split.
                ** change (Sem.solved (R.with_queue st rest) next).
                   exact Hnext_solved.
                ** split.
                   --- exists upper.
                       change (upper_observation tf
                         (R.with_queue st rest) next upper).
                       eapply upper_observation_sigma_view;
                         [reflexivity | exact Hupper].
                   --- constructor.
                       +++ exact Howner.
                       +++ destruct Hwave as [owner_upper Howner_upper].
                           exists owner_upper.
                           eapply upper_observation_sigma_view;
                             [reflexivity | exact Howner_upper].
                       +++ eapply (@wave_stack_sigma_view tf root st
                            (R.with_queue st rest) base k);
                            [reflexivity | reflexivity | exact Hstack].
        * inversion Hstep; subst; cbn.
          exists base. split; [exact Hbase |].
          split.
          -- eapply higher_upper_history_sigma_view.
             ++ apply Total.Termination.reset_registered_cells_ranking.
             ++ exact (proj1 (proj1
                  (Inv.reset_registered_cells_same_solver_view
                    st (R.frame_owner fr)))).
             ++ exact Hhigher.
          -- split.
             ++ eapply higher_queue_solved_sigma_queue_view.
                ** apply Total.Termination.reset_registered_cells_ranking.
                ** exact (proj1 (proj1
                     (Inv.reset_registered_cells_same_solver_view
                       st (R.frame_owner fr)))).
                ** exact (proj2 (proj2 (proj1
                     (Inv.reset_registered_cells_same_solver_view
                       st (R.frame_owner fr))))).
                ** exact Hqueue.
             ++ eapply wave_stack_sigma_view.
                ** apply Total.Termination.reset_registered_cells_ranking.
                ** exact (proj1 (proj1
                     (Inv.reset_registered_cells_same_solver_view
                       st (R.frame_owner fr)))).
                ** exact Hstack.
    - inversion Hstep; subst; cbn.
      exists base. split; [exact Hbase |].
      split.
      + eapply higher_upper_history_sigma_view.
        * apply Total.Termination.reset_registered_cells_ranking.
        * exact (proj1 (proj1
            (Inv.reset_registered_cells_same_solver_view
              st (R.frame_owner fr)))).
        * exact Hhigher.
      + split.
        * eapply higher_queue_solved_sigma_queue_view.
          -- apply Total.Termination.reset_registered_cells_ranking.
          -- exact (proj1 (proj1
               (Inv.reset_registered_cells_same_solver_view
                 st (R.frame_owner fr)))).
          -- exact (proj2 (proj2 (proj1
               (Inv.reset_registered_cells_same_solver_view
                 st (R.frame_owner fr))))).
          -- exact Hqueue.
        * eapply wave_stack_sigma_view.
          -- apply Total.Termination.reset_registered_cells_ranking.
          -- exact (proj1 (proj1
               (Inv.reset_registered_cells_same_solver_view
                 st (R.frame_owner fr)))).
          -- exact Hstack.
  Qed.

  Lemma ordinary_wave_start_episode_step :
    forall tf root st owner k after,
      wave_control tf root st (R.StartEpisode owner k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner k |} after ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf root st owner k after
      [base [Hbase [Hhigher [Hqueue
        [Howner [Hsolved [Hwave Hstack]]]]]]] Hstep.
    pose proof (materialize_solved_state Hsolved) as Hmaterialize.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    rewrite Hmaterialize in Hstep.
    inversion Hstep; subst; cbn.
    rewrite Hmaterialize in Hwave.
    exists base. split; [exact Hbase |].
    split; [exact Hhigher |]. split; [exact Hqueue |].
    split; [now right |]. split.
    - destruct Hwave as [upper Hupper].
      eapply initial_wave_evaluation. exact Hupper.
    - exact Hstack.
  Qed.

  Lemma complete_get_frame_phase :
    forall st fr target st' fr' value,
      R.complete_get st fr target = (st', fr', value) ->
      R.frame_phase fr' = R.frame_phase fr.
  Proof.
    intros st fr target st' fr' value Hget.
    unfold R.complete_get in Hget.
    inversion Hget. reflexivity.
  Qed.

  Lemma return_boxn_origin :
    forall tf st k after,
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after ->
      control_has_boxn (R.cfg_control after) ->
      continuation_has_boxn k.
  Proof.
    intros tf st k after Hstep Hboxn.
    unfold Sem.step, R.next_config in Hstep.
    destruct k; cbn -[R.complete_get] in Hstep.
    - inversion Hstep; subst. exact Hboxn.
    - inversion Hstep; subst. exact Hboxn.
    - destruct (R.complete_get st f t)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst. cbn in Hboxn |- *.
      destruct Hboxn as [Hphase | Hrest].
      + left. rewrite <- (@complete_get_frame_phase
          st f t st1 fr1 value Hget). exact Hphase.
      + now right.
    - inversion Hstep; subst. exact Hboxn.
    - inversion Hstep; subst. exact Hboxn.
    - inversion Hstep; subst. exact Hboxn.
    - inversion Hstep; subst. exact Hboxn.
  Qed.

  Lemma ordinary_wave_return_step :
    forall tf root st k after,
      wave_control tf root st (R.Return k) ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after ->
      control_has_boxn (R.cfg_control after) ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf root st k after
      [base [Hbase [Hhigher [Hqueue Hstack]]]]
      Hstep Hafter.
    pose proof (@return_boxn_origin tf st k after Hstep Hafter)
      as Hboxn.
    destruct (@wave_stack_boxn_decompose
      tf root st base k Hbase Hstack Hboxn)
      as [fr [rest [-> [Howner [Hsummary Hrest]]]]].
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst; cbn.
    exists base. split; [exact Hbase |].
    split; [exact Hhigher |]. split; [exact Hqueue |].
    split; [exact Howner |]. now split.
  Qed.

  Lemma ordinary_wave_run_commit_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      root st fr direct k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      U.avoids_fallback (R.frame_phase fr) ->
      wave_control tf root st (R.RunCommit fr direct k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} after ->
      wave_control tf root
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite root st fr direct k after
      Hordinary Hreachable Hsafe
      [base [Hbase [Hhigher [Hqueue
        [Howner [Hwave Hstack]]]]]] Hstep.
    pose proof (@ordinary_reachable_aggregate_bottom
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct k |}
      (R.frame_owner fr) Hordinary Hreachable) as Haggregate.
    cbn in Haggregate.
    pose proof (@ordinary_wave_completed_decreases
      tf st fr direct Hordinary Hwave Haggregate) as Hcandidate.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hbelow.
    cbn in Hbelow.
    pose proof (@ordinary_reachable_readers_solved
      tf roots finite Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct k |}
      Hreachable) as Hreaders.
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.set_value] in Hstep.
    destruct (R.set_value st fr direct)
      as [st1 fr1] eqn:Hset.
    inversion Hstep; subst; cbn.
    pose proof (@safe_set_value_owner_decreases
      st fr direct st1 fr1 Hsafe Hcandidate Hset) as Hdecrease.
    destruct (@wave_completed_set_value_upper
      tf st fr direct st1 fr1 Hwave Hset Hdecrease)
      as [current Hcurrent].
    assert (Hhigher' : higher_upper_history tf root st1).
    { destruct Howner as [Hroot | Howner_higher].
      - eapply higher_upper_history_set_value_root; eassumption.
      - eapply higher_upper_history_set_value; eassumption. }
    assert (Hstack' : wave_stack tf root st1 base k).
    { eapply (@wave_stack_set_value
        tf root st fr direct st1 fr1 base k); eassumption. }
    assert (Hqueue' : higher_queue_solved root st1).
    { eapply higher_queue_solved_set_value; eassumption. }
    pose proof (@set_value_same_ranking
      st fr direct st1 fr1 Hset) as Hranking.
    pose proof (@Inv.set_value_frame_owner
      st fr direct st1 fr1 Hset) as Hframe_owner.
    exists base. split; [exact Hbase |].
    split; [exact Hhigher' |]. split; [exact Hqueue' |].
    split.
    - rewrite Hframe_owner.
      destruct Howner as [Hroot | Howner_higher].
      + now left.
      + right. unfold R.rank_lt, R.ranking_lt in *.
        now rewrite Hranking.
    - split.
      + exists current. now rewrite Hframe_owner.
      + exact Hstack'.
  Qed.

  Lemma boxw_set_value_candidate_decreases :
    forall st fr direct st' fr',
      R.frame_phase fr = U.BoxW ->
      R.set_value st fr direct = (st', fr') ->
      R.frame_phase fr' = U.BoxN ->
      D.leq
        (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr)) = true.
  Proof.
    intros st fr direct st' fr' Hphase Hset Hnext.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))) eqn:Hequivalent.
    - inversion Hset; subst. rewrite Hphase in Hnext. discriminate.
    - destruct (S.mem (R.frame_owner fr) (R.controlled st))
        eqn:Hcontrolled.
      + unfold U.update in Hset. rewrite Hphase in Hset.
        destruct (D.leq
          (D.join direct (R.aggregate st (R.frame_owner fr)))
          (R.sigma_value st (R.frame_owner fr))) eqn:Hle.
        * reflexivity.
        * cbn in Hset.
          destruct (R.equivalent
            (WN.widen
              (R.sigma_value st (R.frame_owner fr))
              (D.join direct (R.aggregate st (R.frame_owner fr))))
            (R.sigma_value st (R.frame_owner fr)));
            inversion Hset; subst; cbn in Hnext;
            discriminate Hnext.
      + cbn in Hset. rewrite Hequivalent in Hset.
        inversion Hset; subst. rewrite Hphase in Hnext. discriminate.
  Qed.

  Lemma queue_strictly_below_not_self :
    forall st owner,
      Total.Termination.queue_strictly_below owner st ->
      ~ Inv.queued st owner.
  Proof.
    intros st owner Hbelow Hqueued.
    pose proof (Hbelow owner Hqueued) as Hfalse.
    pose proof (proj1 (@Total.rank_lt_true_ranked
      st owner owner Hfalse)) as Hranked.
    rewrite (@Total.rank_lt_irrefl st owner Hranked) in Hfalse.
    discriminate.
  Qed.

  Lemma reachable_run_commit_higher_inactive :
    forall tf roots st fr direct k variable,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      R.rank_lt st (R.frame_owner fr) variable = true ->
      ~ Inv.control_active variable (R.RunCommit fr direct k).
  Proof.
    intros tf roots st fr direct k variable
      Hreachable Hhigher Hactive.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hordered.
    cbn in Hordered, Hactive.
    destruct Hactive as [Heq | Hactive].
    - subst variable.
      pose proof (proj1 (@Total.rank_lt_true_ranked st
        (R.frame_owner fr) (R.frame_owner fr) Hhigher)) as Hranked.
      rewrite (@Total.rank_lt_irrefl st (R.frame_owner fr) Hranked)
        in Hhigher. discriminate.
    - pose proof (@continuation_below_active st (R.frame_owner fr)
        k variable Hordered Hactive) as Hlower.
      destruct (@Total.rank_lt_true_ranked st
        (R.frame_owner fr) variable Hhigher) as [Howner Hvariable].
      rewrite (@Total.rank_lt_asymmetric st
        (R.frame_owner fr) variable Howner Hvariable Hhigher) in Hlower.
      discriminate.
  Qed.

  Lemma run_commit_higher_upper_from_full :
    forall tf roots st fr direct k variable,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      full_state_history tf st (R.RunCommit fr direct k) ->
      Total.Termination.queue_strictly_below
        (R.frame_owner fr) st ->
      R.rank_lt st (R.frame_owner fr) variable = true ->
      Sem.solved st variable ->
      exists upper, upper_observation tf st variable upper.
  Proof.
    intros tf roots st fr direct k variable Hreachable Hfull
      Hbelow Hhigher Hsolved.
    assert (Hnot_queued : ~ Inv.queued st variable).
    { intro Hqueued.
      pose proof (Hbelow variable Hqueued) as Hlower.
      destruct (@Total.rank_lt_true_ranked st
        (R.frame_owner fr) variable Hhigher) as [Howner Hvariable].
      rewrite (@Total.rank_lt_asymmetric st
        (R.frame_owner fr) variable Howner Hvariable Hhigher) in Hlower.
      discriminate. }
    assert (Hnot_active :
      ~ Inv.control_active variable (R.RunCommit fr direct k)).
    { eapply reachable_run_commit_higher_inactive; eassumption. }
    destruct (Hfull variable Hsolved)
      as [Hqueued | [Hactive | Hsummary]]; try contradiction.
    destruct Hsummary as
      [_ [upper [Hupper [Hreads [Hdirect Hspawns]]]]].
    exists upper. split; [exact Hupper |]. split; [exact Hdirect |].
    split.
    - intros target value Hin.
      destruct (Hreads target value Hin)
        as [Htarget [_ [Hvalue | Hqueued]]].
      + split; [exact Htarget |]. rewrite Hvalue. apply DL.leq_refl.
      + contradiction.
    - exact Hspawns.
  Qed.

  Lemma ordinary_reachable_commit_higher_upper_history :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct k,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      Total.Termination.queue_strictly_below
        (R.frame_owner fr) st ->
      higher_upper_history tf (R.frame_owner fr) st.
  Proof.
    intros tf roots finite st fr direct k Hordinary Hreachable
      Hbelow variable Hhigher Hsolved.
    eapply run_commit_higher_upper_from_full.
    - exact Hreachable.
    - exact (@ordinary_reachable_full_state_history
        tf roots finite Hordinary
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |}
        Hreachable).
    - exact Hbelow.
    - exact Hhigher.
    - exact Hsolved.
  Qed.

  (** Only the commit which first enters the narrowing phase needs a clean
      frontier.  Requiring this at every commit is too strong: a suspended
      lower-ranked owner may legitimately retain unrelated work discovered
      by a higher-ranked child. *)
  Definition ordinary_boxn_entry_frontier
    (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
    forall st fr direct k next next_fr,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      R.frame_phase fr = U.BoxW ->
      R.set_value st fr direct = (next, next_fr) ->
      R.frame_phase next_fr = U.BoxN ->
      Total.Termination.queue_strictly_below
        (R.frame_owner fr) st.

  Lemma ordinary_clean_boxw_commit_starts_wave :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct st' fr' k,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      Total.Termination.queue_strictly_below
        (R.frame_owner fr) st ->
      continuation_boxn_free k ->
      R.frame_phase fr = U.BoxW ->
      R.set_value st fr direct = (st', fr') ->
      R.frame_phase fr' = U.BoxN ->
      wave_control tf (R.frame_owner fr) st'
        (R.RunDrain fr' k).
  Proof.
    intros tf roots finite st fr direct st' fr' k
      Hordinary Hreachable Hbelow Hfree Hphase Hset Hnext.
    pose proof (@boxw_set_value_candidate_decreases
      st fr direct st' fr' Hphase Hset Hnext) as Hcandidate.
    assert (Hdirect :
      D.leq direct (R.sigma_value st (R.frame_owner fr)) = true).
    { eapply DL.leq_trans; [apply DL.join_upper_left |exact Hcandidate]. }
    pose proof (@ordinary_reachable_aligned_history
      tf roots finite Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct k |}
      Hreachable) as Haligned.
    cbn in Haligned.
    assert (Hwave : wave_completed tf st fr direct).
    { eapply aligned_completed_self_wave.
      - exact Hreachable.
      - exact (proj1 Haligned).
      - eapply queue_strictly_below_not_self. exact Hbelow.
      - exact Hdirect. }
    assert (Hqueue : higher_queue_solved (R.frame_owner fr) st).
    { intros variable Hhigher Hqueued.
      exfalso.
      pose proof (Hbelow variable Hqueued) as Hlower.
      destruct (@Total.rank_lt_true_ranked st
        (R.frame_owner fr) variable Hhigher) as [Howner Hvariable].
      rewrite (@Total.rank_lt_asymmetric st
        (R.frame_owner fr) variable Howner Hvariable Hhigher) in Hlower.
      discriminate. }
    assert (Hcontrol : wave_control tf (R.frame_owner fr) st
      (R.RunCommit fr direct k)).
    { exists k. split; [exact Hfree |].
      split.
      - eapply ordinary_reachable_commit_higher_upper_history;
          eassumption.
      - split; [exact Hqueue |]. split; [now left |].
        split; [exact Hwave |constructor]. }
    eapply (@ordinary_wave_run_commit_step
      tf roots finite (R.frame_owner fr) st fr direct k
      {| R.cfg_state := st'; R.cfg_control := R.RunDrain fr' k |}).
    - exact Hordinary.
    - exact Hreachable.
    - unfold U.avoids_fallback. rewrite Hphase. discriminate.
    - exact Hcontrol.
    - unfold Sem.step. cbn -[R.set_value]. now rewrite Hset.
  Qed.

  Lemma continuation_not_boxn_is_free :
    forall k,
      ~ continuation_has_boxn k -> continuation_boxn_free k.
  Proof.
    induction k; cbn; intros Hnone; try exact I.
    all: split.
    all: try (intro Hphase; apply Hnone; now left).
    all: apply IHk; intro Hrest; apply Hnone; now right.
  Qed.

  Lemma ordinary_clean_first_boxn_commit_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      ordinary_boxn_entry_frontier tf roots ->
      U.avoids_fallback (R.frame_phase fr) ->
      ~ control_has_boxn (R.RunCommit fr direct k) ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} after ->
      control_has_boxn (R.cfg_control after) ->
      exists root,
        wave_control tf root
          (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st fr direct k after Hordinary Hreachable
      Hfrontier Hsafe Hnone Hstep Hafter.
    assert (Hphase : R.frame_phase fr = U.BoxW).
    { destruct (R.frame_phase fr) eqn:Hphase; [reflexivity | |].
      - exfalso. apply Hnone. cbn. now left.
      - exfalso. apply Hsafe. reflexivity. }
    assert (Hrest_none : ~ continuation_has_boxn k).
    { intro Hrest. apply Hnone. cbn. now right. }
    pose proof (@continuation_not_boxn_is_free k Hrest_none) as Hfree.
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.set_value] in Hstep.
    destruct (R.set_value st fr direct)
      as [st' fr'] eqn:Hset.
    inversion Hstep; subst; cbn in Hafter |- *.
    assert (Hnext : R.frame_phase fr' = U.BoxN).
    { destruct Hafter as [Hnext | Hrest]; [exact Hnext |contradiction]. }
    assert (Hbelow : Total.Termination.queue_strictly_below
      (R.frame_owner fr) st).
    { eapply Hfrontier; eassumption. }
    exists (R.frame_owner fr).
    eapply ordinary_clean_boxw_commit_starts_wave; eassumption.
  Qed.

  Definition wave_safe
    (tf : R.ConstraintSystem.system) (st : R.state)
    (control : R.control) : Prop :=
    control_has_boxn control ->
    exists root, wave_control tf root st control.

  Lemma start_episode_boxn_origin :
    forall tf st owner k after,
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner k |} after ->
      control_has_boxn (R.cfg_control after) ->
      control_has_boxn (R.StartEpisode owner k).
  Proof.
    intros tf st owner k after Hstep Hafter.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst. cbn in Hafter |- *.
    destruct Hafter as [Hphase | Hrest]; [discriminate |exact Hrest].
  Qed.

  Lemma ordinary_run_rhs_boxn_origin :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr current k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr current k |} after ->
      control_has_boxn (R.cfg_control after) ->
      control_has_boxn (R.RunRhs fr current k).
  Proof.
    intros tf roots finite st fr current k after
      Hordinary Hreachable Hstep Hafter.
    unfold Sem.step, R.next_config in Hstep.
    destruct current; cbn -[R.complete_get R.observe] in Hstep.
    - inversion Hstep; subst. exact Hafter.
    - destruct (andb
        (negb (R.is_materialized (R.observe st t) t))
        (R.rank_lt (R.observe st t) (R.frame_owner fr) t)).
      + inversion Hstep; subst. exact Hafter.
      + set (base := if R.is_materialized (R.observe st t) t
          then R.observe st t else R.enqueue (R.observe st t) t) in *.
        destruct (R.complete_get base fr t)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst. cbn in Hafter |- *.
        destruct Hafter as [Hphase | Hrest].
        * left. rewrite <- (@complete_get_frame_phase
            base fr t st1 fr1 value Hget). exact Hphase.
        * now right.
    - exfalso. eapply ordinary_reachable_side_impossible; eassumption.
    - destruct (R.is_materialized (R.observe st t) t).
      + inversion Hstep; subst. exact Hafter.
      + destruct (R.rank_lt (R.observe st t) (R.frame_owner fr) t);
          inversion Hstep; subst; exact Hafter.
  Qed.

  Lemma ordinary_run_dead_boxn_origin :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct pending k after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} after ->
      control_has_boxn (R.cfg_control after) ->
      control_has_boxn (R.RunDead fr direct pending k).
  Proof.
    intros tf roots finite st fr direct pending k after
      Hordinary Hreachable Hstep Hafter.
    pose proof (@ordinary_reachable_clean tf roots finite Hordinary
      {| R.cfg_state := st;
         R.cfg_control := R.RunDead fr direct pending k |}
      Hreachable) as [_ Hcontrol].
    cbn in Hcontrol. destruct Hcontrol as [_ [-> _]].
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    inversion Hstep; subst. exact Hafter.
  Qed.

  Lemma run_drain_boxn_origin :
    forall tf st fr k after,
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} after ->
      control_has_boxn (R.cfg_control after) ->
      control_has_boxn (R.RunDrain fr k).
  Proof.
    intros tf st fr k after Hstep Hafter.
    unfold Sem.step, R.next_config in Hstep.
    cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
    destruct (R.queue_peek (R.queue st)) as [next |].
    - destruct (V.eq_dec next (R.frame_owner fr)).
      + destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
          try discriminate. inversion Hstep; subst. exact Hafter.
      + destruct (R.rank_lt st (R.frame_owner fr) next).
        * destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
            try discriminate. inversion Hstep; subst. cbn in Hafter |- *.
          exact Hafter.
        * inversion Hstep; subst. now right.
    - inversion Hstep; subst. now right.
  Qed.

  Definition frame_avoids_fallback (fr : R.frame) : Prop :=
    U.avoids_fallback (R.frame_phase fr).

  Fixpoint continuation_avoids_fallback
    (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr _ _ rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDead fr _ _ rest
    | R.KDrain fr rest =>
        frame_avoids_fallback fr /\
        continuation_avoids_fallback rest
    end.

  Definition control_avoids_fallback (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode _ k | R.Return k =>
        continuation_avoids_fallback k
    | R.RunRhs fr _ k
    | R.RunDead fr _ _ k
    | R.RunCommit fr _ k
    | R.RunDrain fr k =>
        frame_avoids_fallback fr /\
        continuation_avoids_fallback k
    end.

  Definition ordinary_avoids_fallback
    (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
    forall c,
      Sem.steps tf (R.initial_config roots) c ->
      control_avoids_fallback (R.cfg_control c).

  Definition commit_input_admissible
    (st : R.state) (fr : R.frame) (direct : D.t) : Prop :=
    U.admissible_input (R.frame_phase fr)
      (R.sigma_value st (R.frame_owner fr))
      (D.join direct (R.aggregate st (R.frame_owner fr))).

  Definition ordinary_commit_inputs_admissible
    (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
    forall st fr direct k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      commit_input_admissible st fr direct.

  Definition unmaterialized_readers_empty (st : R.state) : Prop :=
    forall target reader,
      R.is_materialized st target = false ->
      S.mem reader (R.lookup_set (R.readers st) target) = false.

  Lemma unmaterialized_readers_empty_view :
    forall before after,
      R.sigma after = R.sigma before ->
      R.readers after = R.readers before ->
      unmaterialized_readers_empty before ->
      unmaterialized_readers_empty after.
  Proof.
    intros before after Hsigma Hreaders Hempty target reader Hfresh.
    rewrite Hreaders. apply Hempty. unfold R.is_materialized in *.
    now rewrite Hsigma in Hfresh.
  Qed.

  Lemma unmaterialized_readers_empty_materialize :
    forall st inserted,
      unmaterialized_readers_empty st ->
      unmaterialized_readers_empty (R.materialize st inserted).
  Proof.
    intros st inserted Hempty target reader Hfresh.
    unfold R.materialize in Hfresh |- *.
    destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted.
    - now apply Hempty.
    - destruct (V.eq_dec target inserted) as [-> |Hneq].
      + unfold R.is_materialized in Hfresh. cbn in Hfresh.
        rewrite ML.lookup_update_same in Hfresh. discriminate.
      + apply Hempty. unfold R.is_materialized in Hfresh |- *.
        cbn in Hfresh. rewrite ML.lookup_update_other in Hfresh by exact Hneq.
        exact Hfresh.
  Qed.

  Lemma unmaterialized_readers_empty_add_reader :
    forall st target owner,
      unmaterialized_readers_empty st ->
      unmaterialized_readers_empty
        (R.materialize
          (R.with_readers st
            (M.update (R.readers st) target
              (S.add owner (R.lookup_set (R.readers st) target))))
          target).
  Proof.
    intros st target owner Hempty variable reader Hfresh.
    set (read_state :=
      R.with_readers st
        (M.update (R.readers st) target
          (S.add owner (R.lookup_set (R.readers st) target)))) in *.
    assert (Hneq : variable <> target).
    { intro Heq. subst variable.
      pose proof (Inv.materialize_solved_correctness read_state target)
        as Hsolved.
      pose proof (solved_is_materialized Hsolved) as Hmaterialized.
      rewrite Hmaterialized in Hfresh. discriminate. }
    assert (Hsigma : R.sigma read_state = R.sigma st) by reflexivity.
    assert (Hreaders :
      R.lookup_set (R.readers read_state) variable =
      R.lookup_set (R.readers st) variable).
    { subst read_state. cbn. now apply lookup_set_update_other. }
    unfold R.materialize in Hfresh |- *.
    destruct (M.lookup (R.sigma read_state) target) eqn:Htarget.
    - rewrite Hreaders. apply Hempty.
      unfold R.is_materialized in Hfresh |- *. now rewrite Hsigma in Hfresh.
    - cbn in Hfresh |- *.
      rewrite lookup_set_update_other by exact Hneq. apply Hempty.
      unfold R.is_materialized in Hfresh |- *. cbn in Hfresh.
      rewrite ML.lookup_update_other in Hfresh by exact Hneq.
      exact Hfresh.
  Qed.

  Lemma unmaterialized_readers_empty_complete_get :
    forall st fr target next next_fr value,
      unmaterialized_readers_empty st ->
      R.complete_get st fr target = (next, next_fr, value) ->
      unmaterialized_readers_empty next.
  Proof.
    intros st fr target next next_fr value Hempty Hget.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    set (minimum := if R.rank_lt st target (R.frame_min_scope fr)
      then target else R.frame_min_scope fr) in *.
    set (maximum := match R.frame_max_read fr with
      | None => Some target
      | Some previous =>
          if R.rank_lt st previous target then Some target else Some previous
      end) in *.
    inversion Hget; subst next next_fr value; clear Hget.
    apply unmaterialized_readers_empty_add_reader.
    subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
    - exact Hempty.
    - eapply unmaterialized_readers_empty_view.
      + reflexivity.
      + reflexivity.
      + exact Hempty.
  Qed.

  Lemma unmaterialized_readers_empty_set_value :
    forall st fr direct next next_fr,
      unmaterialized_readers_empty st ->
      R.set_value st fr direct = (next, next_fr) ->
      unmaterialized_readers_empty next.
  Proof.
    intros st fr direct next next_fr Hempty Hset.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))) eqn:Hcandidate.
    { inversion Hset; subst; exact Hempty. }
    clear Hcandidate.
    destruct (if S.mem (R.frame_owner fr) (R.controlled st)
      then U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr)))
      else (R.frame_phase fr,
        D.join direct (R.aggregate st (R.frame_owner fr))))
      as [phase value] eqn:Hupdate.
    cbn in Hset.
    destruct (R.equivalent value
      (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue.
    { inversion Hset; subst; exact Hempty. }
    clear Hvalue.
    inversion Hset; subst; clear Hset.
    intros target reader Hfresh.
    unfold Inv.commit_value in Hfresh.
    unfold Inv.commit_value. cbn in Hfresh |- *.
    destruct (V.eq_dec target (R.frame_owner fr)) as [-> |Hneq].
    - rewrite lookup_set_update_same, SL.empty_spec. reflexivity.
    - rewrite lookup_set_update_other by exact Hneq.
      apply Hempty. unfold R.is_materialized in Hfresh |- *.
      cbn in Hfresh. rewrite ML.lookup_update_other in Hfresh by exact Hneq.
      exact Hfresh.
  Qed.

  Lemma unmaterialized_readers_empty_step :
    forall tf before after,
      unmaterialized_readers_empty (R.cfg_state before) ->
      Sem.step tf before after ->
      unmaterialized_readers_empty (R.cfg_state after).
  Proof.
    intros tf [st control] after Hempty Hstep.
    unfold Sem.step, R.next_config in Hstep.
    destruct control as
      [|roots |remaining |owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k].
    - cbn in Hstep. destruct (R.queue_pop (R.queue st));
        try discriminate. destruct p. inversion Hstep; subst; cbn; exact Hempty.
    - destruct roots as [|root roots]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst; exact Hempty.
      + assert (Hobserved :
          unmaterialized_readers_empty (R.observe st root)).
        { eapply unmaterialized_readers_empty_view.
          - exact (proj1 (Inv.observe_solver_view st root)).
          - exact (proj1 (proj2 (proj2
              (Inv.observe_solver_view st root)))).
          - exact Hempty. }
        destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; subst; exact Hobserved.
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[head tail] |];
        inversion Hstep; subst; cbn; exact Hempty.
    - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
      now apply unmaterialized_readers_empty_materialize.
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. inversion Hstep; subst; exact Hempty.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        assert (Hobserved : unmaterialized_readers_empty observed).
        { subst observed. eapply unmaterialized_readers_empty_view.
          - exact (proj1 (Inv.observe_solver_view st target)).
          - exact (proj1 (proj2 (proj2
              (Inv.observe_solver_view st target)))).
          - exact Hempty. }
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst; exact Hobserved.
        * set (base := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          assert (Hbase : unmaterialized_readers_empty base).
          { subst base. destruct (R.is_materialized observed target);
              exact Hobserved. }
          destruct (R.complete_get base fr target)
            as [[st1 fr1] read] eqn:Hget.
          inversion Hstep; subst.
          eapply unmaterialized_readers_empty_complete_get; eassumption.
      + cbn -[R.observe R.record_side_input
          R.write_side_contribution R.continue_side] in Hstep.
        destruct (R.record_side_input fr target raw) as [fr1 input].
        destruct (R.write_side_contribution (R.observe st target)
          fr1 target input) as [st1 changed] eqn:Hwrite.
        assert (Hst1 : unmaterialized_readers_empty st1).
        { destruct (Inv.write_side_contribution_same_read_view Hwrite)
            as [Hsigma [Hreaders _]].
          eapply unmaterialized_readers_empty_view.
          - rewrite Hsigma. exact (proj1 (Inv.observe_solver_view st target)).
          - rewrite Hreaders. exact (proj1 (proj2 (proj2
              (Inv.observe_solver_view st target)))).
          - exact Hempty. }
        unfold R.continue_side in Hstep. destruct changed;
          try destruct (_ && _)%bool;
          inversion Hstep; subst; exact Hst1.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        assert (Hobserved : unmaterialized_readers_empty (R.observe st target)).
        { eapply unmaterialized_readers_empty_view.
          - exact (proj1 (Inv.observe_solver_view st target)).
          - exact (proj1 (proj2 (proj2
              (Inv.observe_solver_view st target)))).
          - exact Hempty. }
        destruct (R.is_materialized (R.observe st target) target).
        * inversion Hstep; subst; exact Hobserved.
        * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
          -- inversion Hstep; subst; exact Hobserved.
          -- inversion Hstep; subst.
             now apply unmaterialized_readers_empty_materialize.
    - destruct pending as [|target remaining].
      + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
        exact Hempty.
      + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        * inversion Hstep; subst; exact Hempty.
        * destruct (R.write_side_contribution st fr target D.bottom)
            as [st1 changed] eqn:Hwrite.
          destruct (Inv.write_side_contribution_same_read_view Hwrite)
            as [Hsigma [Hreaders _]].
          assert (Hst1 : unmaterialized_readers_empty st1).
          { eapply unmaterialized_readers_empty_view; eassumption. }
          unfold R.continue_dead in Hstep. destruct changed;
            try destruct (_ && _)%bool;
            inversion Hstep; subst; exact Hst1.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst.
      eapply unmaterialized_readers_empty_set_value; eassumption.
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      + destruct (V.eq_dec next (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)); try discriminate.
          destruct p. inversion Hstep; subst; exact Hempty.
        * destruct (R.rank_lt st (R.frame_owner fr) next).
          -- destruct (R.queue_pop (R.queue st)); try discriminate.
             destruct p. inversion Hstep; subst; exact Hempty.
          -- inversion Hstep; subst.
             destruct (Inv.reset_registered_cells_same_solver_view st
               (R.frame_owner fr)) as [[Hsigma [Hreaders _]] _].
             eapply unmaterialized_readers_empty_view; eassumption.
      + inversion Hstep; subst.
        destruct (Inv.reset_registered_cells_same_solver_view st
          (R.frame_owner fr)) as [[Hsigma [Hreaders _]] _].
        eapply unmaterialized_readers_empty_view; eassumption.
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; exact Hempty).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst.
      eapply unmaterialized_readers_empty_complete_get; eassumption.
  Qed.

  Theorem reachable_unmaterialized_readers_empty :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      unmaterialized_readers_empty (R.cfg_state c).
  Proof.
    intros tf roots c Hsteps.
    assert (Hinitial :
      unmaterialized_readers_empty (R.cfg_state (R.initial_config roots))).
    { intros target reader Hfresh. cbn. unfold R.lookup_set.
      rewrite ML.lookup_empty. apply SL.empty_spec. }
    revert Hinitial. induction Hsteps; intros Hfirst.
    - exact Hfirst.
    - apply IHHsteps. eapply unmaterialized_readers_empty_step; eassumption.
  Qed.

  Lemma reachable_fresh_target_has_no_readers :
    forall tf roots c target,
      Sem.steps tf (R.initial_config roots) c ->
      R.is_materialized (R.cfg_state c) target = false ->
      set_has_no_members
        (R.lookup_set (R.readers (R.cfg_state c)) target).
  Proof.
    intros tf roots c target Hreachable Hfresh reader.
    exact (@reachable_unmaterialized_readers_empty
      tf roots c Hreachable target reader Hfresh).
  Qed.

  Lemma set_value_no_readers_queue :
    forall st fr direct next next_fr,
      set_has_no_members
        (R.lookup_set (R.readers st) (R.frame_owner fr)) ->
      R.set_value st fr direct = (next, next_fr) ->
      R.queue next = R.queue st.
  Proof.
    intros st fr direct next next_fr Hreaders Hset.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))) eqn:Hcandidate.
    { inversion Hset; reflexivity. }
    clear Hcandidate.
    destruct (if S.mem (R.frame_owner fr) (R.controlled st)
      then U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr)))
      else (R.frame_phase fr,
        D.join direct (R.aggregate st (R.frame_owner fr))))
      as [phase value].
    cbn in Hset.
    destruct (R.equivalent value
      (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue.
    { inversion Hset; reflexivity. }
    clear Hvalue.
    assert (Helements :
      S.elements (R.lookup_set (R.readers st) (R.frame_owner fr)) = []).
    { now apply no_member_set_elements_nil. }
    rewrite Helements in Hset. inversion Hset. reflexivity.
  Qed.

  Lemma ordinary_active_source_credit_step :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      Sem.step tf before after ->
      Total.Termination.control_contains owner (R.cfg_control before) ->
      Total.Termination.control_contains owner (R.cfg_control after) ->
      Total.Credits.source_side_credit support
        (R.cfg_state after) owner =
      Total.Credits.source_side_credit support
        (R.cfg_state before) owner.
  Proof.
    intros support tf roots finite owner [st control] after
      Hordinary Hreachable Hstep Hbefore Hafter.
    unfold Sem.step in Hstep.
    destruct control as
      [|seed_roots |remaining |episode_owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k];
      try contradiction.
    - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
      apply Total.Termination.source_credit_materialize.
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. inversion Hstep; subst. reflexivity.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst; cbn. unfold observed.
          apply Total.Termination.source_credit_observe.
        * set (base := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          destruct (R.complete_get base fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst; cbn.
          rewrite (@Total.Termination.source_credit_complete_get
            support base fr target st1 fr1 value owner Hget).
          subst base observed.
          destruct (R.is_materialized (R.observe st target) target).
          -- apply Total.Termination.source_credit_observe.
          -- rewrite Total.Termination.source_credit_enqueue.
             apply Total.Termination.source_credit_observe.
      + exfalso. eapply ordinary_reachable_side_impossible; eassumption.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (R.is_materialized observed target).
        * inversion Hstep; subst; cbn. unfold observed.
          apply Total.Termination.source_credit_observe.
        * destruct (R.rank_lt observed (R.frame_owner fr) target).
          -- inversion Hstep; subst; cbn. unfold observed.
             apply Total.Termination.source_credit_observe.
          -- inversion Hstep; subst; cbn.
             rewrite Total.Termination.source_credit_materialize.
             rewrite Total.Termination.source_credit_enqueue.
             unfold observed.
             apply Total.Termination.source_credit_observe.
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |}
        Hreachable) as [_ Hclean].
      cbn in Hclean. destruct Hclean as [_ [-> _]].
      cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
      apply Total.Termination.source_credit_publish_targets.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst.
      apply Total.Termination.source_credit_set_value with
        (fr := fr) (direct := direct) (next_fr := fr1).
      exact Hset.
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
      + destruct (V.eq_dec next (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
            try discriminate. inversion Hstep; subst.
          apply Total.Termination.source_credit_with_queue.
        * destruct (R.rank_lt st (R.frame_owner fr) next).
          -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
               try discriminate. inversion Hstep; subst.
             apply Total.Termination.source_credit_with_queue.
          -- inversion Hstep; subst.
             pose proof (Total.Termination.reachable_control_ordered
               Hreachable) as Hordered.
             cbn in Hbefore, Hafter, Hordered.
             assert (Habove :
               R.rank_lt st owner (R.frame_owner fr) = true).
             { eapply Total.Termination.continuation_contains_below;
                 eassumption. }
             apply Total.reset_above_preserves_source_credit.
             ++ exact (proj1 (@Total.ScopeBounds.reachable_scopes_bounded
                  tf roots
                  {| R.cfg_state := st;
                     R.cfg_control := R.RunDrain fr k |}
                  Hreachable)).
             ++ exact Habove.
      + inversion Hstep; subst.
        pose proof (Total.Termination.reachable_control_ordered
          Hreachable) as Hordered.
        cbn in Hbefore, Hafter, Hordered.
        assert (Habove :
          R.rank_lt st owner (R.frame_owner fr) = true).
        { eapply Total.Termination.continuation_contains_below;
            eassumption. }
        apply Total.reset_above_preserves_source_credit.
        * exact (proj1 (@Total.ScopeBounds.reachable_scopes_bounded
             tf roots
             {| R.cfg_state := st;
                R.cfg_control := R.RunDrain fr k |}
             Hreachable)).
        * exact Habove.
    - destruct k as
        [|seed_remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; reflexivity).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst.
      eapply Total.Termination.source_credit_complete_get; eassumption.
  Qed.

  Lemma ordinary_active_prefix_source_credit_equal :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner first final,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) first ->
      Total.Termination.active_prefix owner tf first final ->
      Total.Termination.control_contains owner (R.cfg_control final) ->
      Total.Credits.source_side_credit support
        (R.cfg_state final) owner =
      Total.Credits.source_side_credit support
        (R.cfg_state first) owner.
  Proof.
    intros support tf roots finite owner first final
      Hordinary Hreachable Hprefix.
    induction Hprefix; intros Hfinal; [reflexivity |].
    assert (Hnext : Total.Termination.control_contains owner
      (R.cfg_control next)).
    { destruct Hprefix; [exact Hfinal |exact H1]. }
    rewrite (IHHprefix
      (Total.Termination.steps_append_one Hreachable H0) Hfinal).
    eapply ordinary_active_source_credit_step; eassumption.
  Qed.

  Lemma ordinary_evaluation_frontier_without_discovery :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner base first final,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) first ->
      Total.Termination.until_owner_commit owner tf first final ->
      Total.Termination.active_prefix owner tf first final ->
      Total.Termination.evaluation_frontier support owner base first ->
      Total.Termination.queue_strictly_below owner (R.cfg_state first) ->
      Total.Termination.unmaterialized_count support (R.cfg_state final) =
        Total.Termination.unmaterialized_count support (R.cfg_state first) ->
      Total.Termination.queue_strictly_below owner (R.cfg_state final).
  Proof.
    intros support tf roots finite owner base first final Hsupport
      Hordinary Hreachable Huntil Hactive Hfrontier Hbelow Hmaterialized.
    eapply (@Total.Termination.evaluation_frontier_until_queue_below
      support tf roots finite owner Hsupport base first final);
      try eassumption.
    eapply ordinary_active_prefix_source_credit_equal;
      try eassumption.
    apply Total.Termination.owner_commitb_contains.
    exact (Total.Termination.until_owner_commit_final Huntil).
  Qed.

  Lemma ordinary_fresh_episode_commit_without_discovery :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner k st commit_st commit_fr direct,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner k |} ->
      Total.Termination.queue_strictly_below owner st ->
      let started :=
        {| R.cfg_state := R.materialize st owner;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize st owner) owner
                 (U.initial_phase false owner))
               (tf owner) k |} in
      let commit :=
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |} in
      Total.Termination.until_owner_commit owner tf started commit ->
      Total.Termination.active_prefix owner tf started commit ->
      Total.Termination.unmaterialized_count support commit_st =
        Total.Termination.unmaterialized_count support
          (R.materialize st owner) ->
      Total.Termination.queue_strictly_below owner commit_st.
  Proof.
    intros support tf roots finite owner k st commit_st commit_fr direct
      Hsupport Hordinary Hreachable Hbelow started commit Huntil Hactive
      Hmaterialized.
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |}
      started).
    { unfold Sem.step, started. cbn -[R.materialize]. reflexivity. }
    assert (Hstarted : Sem.steps tf (R.initial_config roots) started).
    { eapply Total.Termination.steps_append_one; eassumption. }
    assert (Hbelow_started : Total.Termination.queue_strictly_below owner
      (R.cfg_state started)).
    { unfold started. cbn. intros queued Hin.
      unfold R.materialize in Hin |- *.
      destruct (M.lookup (R.sigma st) owner); exact (Hbelow queued Hin). }
    eapply (@ordinary_evaluation_frontier_without_discovery
      support tf roots finite owner k started commit Hsupport Hordinary
      Hstarted Huntil Hactive).
    - unfold started. cbn. apply Total.Termination.EvaluationRhs.
      reflexivity.
    - exact Hbelow_started.
    - exact Hmaterialized.
  Qed.

  Lemma fresh_episode_measure_decreases :
    forall support tf roots (finite : Sem.finite_system tf roots)
      st owner k,
      support = Sem.support finite ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner k |} ->
      R.is_materialized st owner = false ->
      Total.Termination.unmaterialized_count support
        (R.materialize st owner) <
      Total.Termination.unmaterialized_count support st.
  Proof.
    intros support tf roots finite st owner k Hsupport Hreachable Hfresh.
    subst support.
    pose proof (Total.reachable_config_supported
      finite Hreachable) as [_ Hcontrol].
    cbn in Hcontrol.
    eapply Total.Termination.unmaterialized_count_materialize_decreases.
    - apply Sem.support_nodup.
    - exact (proj1 Hcontrol).
    - exact Hfresh.
  Qed.

  Lemma phase_boxn_cases :
    forall phase : U.phase, phase <> U.BoxN \/ phase = U.BoxN.
  Proof.
    intros phase. unfold U.phase in phase. destruct phase.
    - left. discriminate.
    - right. reflexivity.
    - left. discriminate.
  Qed.

  Lemma continuation_boxn_cases :
    forall k,
      ~ continuation_has_boxn k \/ continuation_has_boxn k.
  Proof.
    induction k; cbn; try tauto.
    all: destruct (@phase_boxn_cases (R.frame_phase f));
      destruct IHk; tauto.
  Qed.

  Lemma control_boxn_cases :
    forall control,
      ~ control_has_boxn control \/ control_has_boxn control.
  Proof.
    intros control. destruct control; cbn; try tauto.
    all: try destruct (@continuation_boxn_cases c).
    all: try destruct (@phase_boxn_cases (R.frame_phase f)).
    all: tauto.
  Qed.

  Lemma ordinary_wave_safe_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      st control after,
      ordinary_monotonic_system tf ->
      ordinary_boxn_entry_frontier tf roots ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := control |} ->
      control_avoids_fallback control ->
      wave_safe tf st control ->
      Sem.step tf
        {| R.cfg_state := st; R.cfg_control := control |} after ->
      wave_safe tf
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite st control after Hordinary Hfrontier
      Hreachable Hsafe Hwave Hstep Hafter.
    destruct control.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        inversion Hstep; subst; cbn in Hafter; contradiction.
    - unfold Sem.step, R.next_config in Hstep.
      destruct l as [|root remaining]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst; cbn in Hafter; contradiction.
      + destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; subst; cbn in Hafter; contradiction.
    - unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        inversion Hstep; subst; cbn in Hafter; contradiction.
    - pose proof (@start_episode_boxn_origin
        tf st t c after Hstep Hafter) as Hbefore.
      destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
      eapply ordinary_wave_start_episode_step; eassumption.
    - pose proof (@ordinary_run_rhs_boxn_origin
        tf roots finite st f r c after Hordinary Hreachable Hstep Hafter)
        as Hbefore.
      destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
      eapply ordinary_wave_run_rhs_step; eassumption.
    - pose proof (@ordinary_run_dead_boxn_origin
        tf roots finite st f t l c after Hordinary Hreachable Hstep Hafter)
        as Hbefore.
      destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
      eapply ordinary_wave_run_dead_step; eassumption.
    - destruct (control_boxn_cases (R.RunCommit f t c))
        as [Hnone | Hbefore].
      + eapply (@ordinary_clean_first_boxn_commit_step
          tf roots finite st f t c after).
        * exact Hordinary.
        * exact Hreachable.
        * exact Hfrontier.
        * exact (proj1 Hsafe).
        * exact Hnone.
        * exact Hstep.
        * exact Hafter.
      + destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
        eapply (@ordinary_wave_run_commit_step
          tf roots finite root st f t c after).
        * exact Hordinary.
        * exact Hreachable.
        * exact (proj1 Hsafe).
        * exact Hcontrol.
        * exact Hstep.
    - pose proof (@run_drain_boxn_origin
        tf st f c after Hstep Hafter) as Hbefore.
      destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
      eapply ordinary_wave_run_drain_step; eassumption.
    - pose proof (@return_boxn_origin tf st c after Hstep Hafter)
        as Hbefore.
      destruct (Hwave Hbefore) as [root Hcontrol]. exists root.
      eapply ordinary_wave_return_step; eassumption.
  Qed.

  Lemma wave_commit_input_admissible :
    forall tf roots (finite : Sem.finite_system tf roots)
      st fr direct k,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} ->
      wave_completed tf st fr direct ->
      commit_input_admissible st fr direct.
  Proof.
    intros tf roots finite st fr direct k Hordinary Hreachable Hwave.
    unfold commit_input_admissible, U.admissible_input.
    intros Hboxn.
    eapply ordinary_wave_completed_decreases.
    - exact Hordinary.
    - exact Hwave.
    - exact (@ordinary_reachable_aggregate_bottom tf roots finite
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |}
        (R.frame_owner fr) Hordinary Hreachable).
  Qed.

  Lemma frame_set_value_avoids_fallback :
    forall st fr direct next next_fr,
      frame_avoids_fallback fr ->
      commit_input_admissible st fr direct ->
      R.set_value st fr direct = (next, next_fr) ->
      frame_avoids_fallback next_fr.
  Proof.
    intros st fr direct next next_fr Hsafe Hadmissible Hset.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))) eqn:Hequivalent.
    - inversion Hset; subst. exact Hsafe.
    - destruct (S.mem (R.frame_owner fr) (R.controlled st))
        eqn:Hcontrolled.
      + destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
          (R.sigma_value st (R.frame_owner fr))
          (D.join direct (R.aggregate st (R.frame_owner fr))))
          as [phase value] eqn:Hupdate.
        assert (Hphase : U.avoids_fallback phase).
        { unfold frame_avoids_fallback in Hsafe.
          unfold commit_input_admissible in Hadmissible.
          pose proof (@U.admissible_update_avoids_fallback false
            (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr)))
            Hsafe Hadmissible) as Hnext.
          rewrite Hupdate in Hnext. exact Hnext. }
        cbn in Hset.
        destruct (R.equivalent value
          (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue;
          inversion Hset; subst; unfold frame_avoids_fallback; cbn;
          exact Hphase.
      + cbn in Hset. rewrite Hequivalent in Hset.
        inversion Hset; subst. exact Hsafe.
  Qed.

  Lemma frame_complete_get_avoids_fallback :
    forall st fr target next next_fr value,
      frame_avoids_fallback fr ->
      R.complete_get st fr target = (next, next_fr, value) ->
      frame_avoids_fallback next_fr.
  Proof.
    intros st fr target next next_fr value Hsafe Hget.
    unfold R.complete_get in Hget.
    inversion Hget; subst. exact Hsafe.
  Qed.

  Definition current_commit_input_admissible (c : R.config) : Prop :=
    match R.cfg_control c with
    | R.RunCommit fr direct _ =>
        commit_input_admissible (R.cfg_state c) fr direct
    | _ => True
    end.

  Lemma ordinary_safe_step_current :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      current_commit_input_admissible before ->
      Sem.steps tf (R.initial_config roots) before ->
      control_avoids_fallback (R.cfg_control before) ->
      Sem.step tf before after ->
      control_avoids_fallback (R.cfg_control after).
  Proof.
    intros tf roots finite [st control] after Hordinary Hadmissible
      Hreachable Hsafe Hstep.
    unfold Sem.step in Hstep.
    destruct control as
      [|seeded |remaining |owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k].
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue st))
        as [[head tail] |]; inversion Hstep; exact I.
    - destruct seeded as [|root rest]; cbn -[R.observe] in Hstep.
      + inversion Hstep; exact I.
      + destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; exact I.
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue st))
        as [[head tail] |]; inversion Hstep; exact I.
    - cbn -[R.materialize] in Hstep.
      inversion Hstep; subst. cbn. split.
      + apply U.initial_avoids_fallback.
      + exact Hsafe.
    - destruct Hsafe as [Hfr Hk]. destruct body.
      + cbn in Hstep. inversion Hstep; subst. cbn. now split.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st t) in *.
        destruct (andb (negb (R.is_materialized observed t))
          (R.rank_lt observed (R.frame_owner fr) t)).
        * inversion Hstep; subst. cbn. now split.
        * set (base := if R.is_materialized observed t
            then observed else R.enqueue observed t) in *.
          destruct (R.complete_get base fr t)
            as [[next_st next_fr] value] eqn:Hget.
          inversion Hstep; subst. cbn. split.
          -- eapply frame_complete_get_avoids_fallback; eassumption.
          -- exact Hk.
      + exfalso. eapply ordinary_reachable_side_impossible; eauto.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st t) in *.
        destruct (R.is_materialized observed t).
        * inversion Hstep; subst. cbn. now split.
        * destruct (R.rank_lt observed (R.frame_owner fr) t).
          -- inversion Hstep; subst. cbn. now split.
          -- inversion Hstep; subst. cbn. now split.
    - destruct Hsafe as [Hfr Hk]. destruct pending as [|target remaining].
      + cbn in Hstep. inversion Hstep; subst. cbn. now split.
      + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        * inversion Hstep; subst. cbn. now split.
        * destruct (R.write_side_contribution st fr target D.bottom)
            as [next_st changed] eqn:Hwrite.
          unfold R.continue_dead in Hstep.
          destruct changed;
            try destruct (andb (R.rank_lt next_st (R.frame_owner fr) target)
              (negb (R.is_materialized next_st target)));
            inversion Hstep; subst; cbn; now split.
    - destruct Hsafe as [Hfr Hk]. cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [next_st next_fr] eqn:Hset.
      inversion Hstep; subst. cbn. split.
      + eapply frame_set_value_avoids_fallback.
        * exact Hfr.
        * exact Hadmissible.
        * exact Hset.
      + exact Hk.
    - destruct Hsafe as [Hfr Hk].
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
      + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
        * destruct (R.queue_pop (R.queue st)) as [[head tail] |]
            eqn:Hpop; try discriminate.
          inversion Hstep; subst. cbn. now split.
        * destruct (R.rank_lt st (R.frame_owner fr) next).
          -- destruct (R.queue_pop (R.queue st)) as [[head tail] |]
              eqn:Hpop; try discriminate.
             inversion Hstep; subst. cbn. now split.
          -- inversion Hstep; subst. exact Hk.
      + inversion Hstep; subst. exact Hk.
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest]; cbn in Hsafe.
      + cbn in Hstep. inversion Hstep; exact I.
      + cbn in Hstep. inversion Hstep; exact I.
      + cbn -[R.complete_get] in Hstep.
        destruct Hsafe as [Hfr Hrest].
        destruct (R.complete_get st fr target)
          as [[next_st next_fr] value] eqn:Hget.
        inversion Hstep; subst. cbn. split.
        * eapply frame_complete_get_avoids_fallback; eassumption.
        * exact Hrest.
      + cbn in Hstep. inversion Hstep; subst. cbn. exact Hsafe.
      + cbn in Hstep. inversion Hstep; subst. cbn. exact Hsafe.
      + cbn in Hstep. inversion Hstep; subst. cbn. exact Hsafe.
      + cbn in Hstep. inversion Hstep; subst. cbn. exact Hsafe.
  Qed.

  Lemma ordinary_safe_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      ordinary_commit_inputs_admissible tf roots ->
      Sem.steps tf (R.initial_config roots) before ->
      control_avoids_fallback (R.cfg_control before) ->
      Sem.step tf before after ->
      control_avoids_fallback (R.cfg_control after).
  Proof.
    intros tf roots finite [st control] after Hordinary Hadmissible
      Hreachable Hsafe Hstep.
    eapply (@ordinary_safe_step_current tf roots finite
      {| R.cfg_state := st; R.cfg_control := control |} after).
    - exact Hordinary.
    - destruct control; cbn; try exact I.
      eapply Hadmissible. exact Hreachable.
    - exact Hreachable.
    - exact Hsafe.
    - exact Hstep.
  Qed.

  Lemma ordinary_wave_current_commit_input_admissible :
    forall tf roots (finite : Sem.finite_system tf roots) c,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) c ->
      wave_safe tf (R.cfg_state c) (R.cfg_control c) ->
      current_commit_input_admissible c.
  Proof.
    intros tf roots finite [st control] Hordinary Hreachable Hwave.
    destruct control; cbn; try exact I.
    destruct (@phase_boxn_cases (R.frame_phase f))
      as [Hnot_boxn | Hboxn].
    - unfold commit_input_admissible, U.admissible_input.
      intros Heq. contradiction.
    - destruct (Hwave (or_introl Hboxn)) as
        [root [base [Hbase [Hhigher [Hqueue
          [Howner [Hcompleted Hstack]]]]]]].
      eapply (@wave_commit_input_admissible
        tf roots finite st f t c); eassumption.
  Qed.

  Theorem ordinary_boxn_entry_frontier_reachable_safe_wave :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      ordinary_boxn_entry_frontier tf roots ->
      forall c,
        Sem.steps tf (R.initial_config roots) c ->
        control_avoids_fallback (R.cfg_control c) /\
        wave_safe tf (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots finite Hordinary Hfrontier final Hsteps.
    assert (Hpreserve : forall first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      control_avoids_fallback (R.cfg_control first) /\
      wave_safe tf (R.cfg_state first) (R.cfg_control first) ->
      control_avoids_fallback (R.cfg_control last) /\
      wave_safe tf (R.cfg_state last) (R.cfg_control last)).
    { intros first last Hreachable Hrun. revert Hreachable.
      induction Hrun as [c | first next last Hstep Hrun IH].
      - intros Hreachable Hjoint. exact Hjoint.
      - intros Hreachable [Hsafe Hwave].
        assert (Hreachable_next :
          Sem.steps tf (R.initial_config roots) next).
        { eapply Total.Termination.steps_transitive.
          - exact Hreachable.
          - econstructor; [exact Hstep |constructor]. }
        apply IH; [exact Hreachable_next |]. split.
        + eapply (@ordinary_safe_step_current
            tf roots finite first next).
          * exact Hordinary.
          * eapply (@ordinary_wave_current_commit_input_admissible
              tf roots finite first); eassumption.
          * exact Hreachable.
          * exact Hsafe.
          * exact Hstep.
        + destruct first as [st control].
          eapply (@ordinary_wave_safe_step
            tf roots finite st control next); eassumption. }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - split.
      + exact I.
      + intros Hboxn. cbn in Hboxn. contradiction.
  Qed.

  Theorem ordinary_boxn_entry_frontier_commit_inputs_admissible :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      ordinary_boxn_entry_frontier tf roots ->
      ordinary_commit_inputs_admissible tf roots.
  Proof.
    intros tf roots finite Hordinary Hfrontier st fr direct k Hreachable.
    pose proof (@ordinary_boxn_entry_frontier_reachable_safe_wave
      tf roots finite Hordinary Hfrontier
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct k |}
      Hreachable) as [_ Hwave].
    exact (@ordinary_wave_current_commit_input_admissible
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct k |}
      Hordinary Hreachable Hwave).
  Qed.

  (** Public conditional narrowing-stability theorem.  For an ordinary monotone
      finite system, it suffices to establish a lower-ranked queue frontier
      exactly when an ordinary frame first enters [BoxN]. *)
  Theorem ordinary_boxn_entry_frontier_avoids_fallback :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      ordinary_boxn_entry_frontier tf roots ->
      ordinary_avoids_fallback tf roots.
  Proof.
    intros tf roots finite Hordinary Hfrontier final Hreachable.
    exact (proj1 (@ordinary_boxn_entry_frontier_reachable_safe_wave
      tf roots finite Hordinary Hfrontier final Hreachable)).
  Qed.

  Theorem admissible_ordinary_system_avoids_fallback :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      ordinary_commit_inputs_admissible tf roots ->
      ordinary_avoids_fallback tf roots.
  Proof.
    intros tf roots finite Hordinary Hadmissible.
    unfold ordinary_avoids_fallback.
    intros final Hrun.
    assert (Hpreserve :
      forall before after,
        Sem.steps tf before after ->
        Sem.steps tf (R.initial_config roots) before ->
        control_avoids_fallback (R.cfg_control before) ->
        control_avoids_fallback (R.cfg_control after)).
    {
      intros before after Hsteps.
      induction Hsteps as [c | first next last Hstep Hsteps IH].
      - intros Hreachable Hsafe. exact Hsafe.
      - intros Hreachable Hsafe.
        apply IH.
        + eapply Total.Termination.steps_transitive.
          * exact Hreachable.
          * econstructor.
            -- exact Hstep.
            -- constructor.
        + eapply ordinary_safe_step; eauto.
    }
    eapply Hpreserve.
    - exact Hrun.
    - constructor.
    - exact I.
  Qed.

End WithLaws.

(** Narrowing-stability specialization for append-only first discovery. *)
Module FirstDiscovery
  (S : SET V)
  (M : MAP V)
  (Features : Restarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (WNL : WIDEN_NARROW_LAWS D WN)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Rk := ListDiscoveryOrder V.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module RankFinite <: FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws :=
    ListFiniteDiscoveryOrderLaws V.
  Module FullRankLaws := ListDiscoveryOrderLaws V.

  Include WithLaws
    S M Rk Features RankLaws RankFinite DL WNL UL SL ML.

  Theorem first_discovery_fresh_ranks_above : fresh_ranks_above.
  Proof.
    intros order target next target_rank owner owner_rank
      Hvalid Hfresh Howner Hobserve.
    destruct (@FullRankLaws.observe_fresh
      order target next target_rank Hfresh Hobserve)
      as [Htarget_rank _].
    subst target_rank.
    eapply (@FullRankLaws.lookup_bound order owner owner_rank); eassumption.
  Qed.

  Definition all_ranked_materialized (st : R.state) : Prop :=
    forall variable,
      Total.ranked st variable ->
      R.is_materialized st variable = true.

  Definition ranked_materialization_control
    (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.StartEpisode owner _ =>
        forall variable,
          Total.ranked st variable ->
          variable = owner \/ R.is_materialized st variable = true
    | _ => all_ranked_materialized st
    end.

  Lemma first_discovery_observe_ranked_cases :
    forall st target variable,
      Total.ranked (R.observe st target) variable ->
      variable = target \/ Total.ranked st variable.
  Proof.
    intros st target variable [rank Hrank].
    unfold R.observe, R.Ranking.observe in Hrank.
    destruct (R.Ranking.lookup (R.ranking st) target)
      as [target_rank |] eqn:Htarget.
    - right. now exists rank.
    - cbn in Hrank. destruct (V.eq_dec variable target) as [Heq |Hneq].
      + now left.
      + right. now exists rank.
  Qed.

  Lemma complete_get_target_materialized :
    forall st fr target next next_fr value,
      R.complete_get st fr target = (next, next_fr, value) ->
      R.is_materialized next target = true.
  Proof.
    intros st fr target next next_fr value Hget.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    inversion Hget; subst next next_fr value.
    apply solved_is_materialized.
    apply Inv.materialize_solved_correctness.
  Qed.

  Lemma materialize_target_materialized :
    forall st target,
      R.is_materialized (R.materialize st target) target = true.
  Proof.
    intros st target. apply solved_is_materialized.
    apply Inv.materialize_solved_correctness.
  Qed.

  Lemma all_ranked_materialized_step_same_ranking :
    forall tf before after,
      Sem.step tf before after ->
      R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before) ->
      all_ranked_materialized (R.cfg_state before) ->
      all_ranked_materialized (R.cfg_state after).
  Proof.
    intros tf before after Hstep Hranking Hall variable [rank Hrank].
    assert (Hbefore_ranked : Total.ranked
      (R.cfg_state before) variable).
    { exists rank. now rewrite Hranking in Hrank. }
    eapply Total.Termination.step_materialized_mono.
    - exact Hstep.
    - now apply Hall.
  Qed.

  Lemma write_side_contribution_same_ranking :
    forall st fr target input next changed,
      R.write_side_contribution st fr target input = (next, changed) ->
      R.ranking next = R.ranking st.
  Proof.
    intros st fr target input next changed Hwrite.
    unfold R.write_side_contribution in Hwrite.
    set (base := R.promote_side_target st fr target) in *.
    destruct (U.update true target
      (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
      (R.stored_contribution base (R.frame_owner fr) target) input).
    inversion Hwrite; subst next changed.
    unfold base, R.promote_side_target, R.promote_controlled.
    destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
  Qed.

  Lemma reset_registered_cells_same_ranking :
    forall st owner,
      R.ranking (R.reset_registered_cells st owner) = R.ranking st.
  Proof.
    intros st owner. unfold R.reset_registered_cells.
    destruct Features.restart_side_phases; reflexivity.
  Qed.

  Lemma first_discovery_ranked_materialization_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      ranked_materialization_control
        (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      ranked_materialization_control
        (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf roots finite [st control] after Hordinary Hreachable
      Hmaterialized Hstep.
    pose proof Hstep as Hstep_semantic.
    unfold Sem.step in Hstep.
    destruct control as
      [|seeded |remaining |owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k].
    - cbn in Hstep. destruct (R.queue_pop (R.queue st))
        as [[head tail] |]; try discriminate.
      inversion Hstep; subst. cbn.
      intros variable Hranked. right.
      apply Hmaterialized. exact Hranked.
    - destruct seeded as [|root rest]; cbn -[R.observe] in Hstep.
      + inversion Hstep; subst. cbn.
        exact Hmaterialized.
      + set (observed := R.observe st root) in *.
        destruct (R.is_materialized observed root) eqn:Hroot.
        * inversion Hstep; subst. cbn.
          intros variable Hranked.
          destruct (@first_discovery_observe_ranked_cases
            st root variable Hranked) as [-> |Hold].
          -- exact Hroot.
          -- exact (@Total.Termination.step_materialized_mono tf
               {| R.cfg_state := st;
                  R.cfg_control := R.RunSeeds (root :: rest) |}
               {| R.cfg_state := observed;
                  R.cfg_control := R.RunSeeds rest |}
               variable Hstep_semantic (Hmaterialized variable Hold)).
        * inversion Hstep; subst. cbn.
          intros variable Hranked.
          destruct (@first_discovery_observe_ranked_cases
            st root variable Hranked) as [-> |Hold].
          -- now left.
          -- right. exact (Total.Termination.step_materialized_mono
               variable Hstep_semantic (Hmaterialized variable Hold)).
    - cbn in Hstep. destruct (R.queue_pop (R.queue st))
        as [[head tail] |].
      + inversion Hstep; subst; cbn.
        intros variable Hranked. right.
        apply Hmaterialized. exact Hranked.
      + inversion Hstep; subst; cbn. exact Hmaterialized.
    - cbn -[R.materialize] in Hstep. inversion Hstep; subst. cbn.
      intros variable Hranked.
      assert (Hranked_before : Total.ranked st variable).
      { destruct Hranked as [rank Hranked]. exists rank.
        unfold R.materialize in Hranked.
        destruct (M.lookup (R.sigma st) owner); exact Hranked. }
      destruct (Hmaterialized variable Hranked_before) as [-> |Hold].
      + apply materialize_target_materialized.
      + exact (Total.Termination.step_materialized_mono
          variable Hstep_semantic Hold).
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. inversion Hstep; subst. cbn.
        exact Hmaterialized.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst. cbn.
          intros variable Hranked.
          destruct (@first_discovery_observe_ranked_cases
            st target variable Hranked) as [-> |Hold].
          -- now left.
          -- right. exact (Total.Termination.step_materialized_mono
               variable Hstep_semantic (Hmaterialized variable Hold)).
        * set (get_base := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          destruct (R.complete_get get_base fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. cbn.
          assert (Hranking : R.ranking st1 = R.ranking observed).
          { rewrite (@complete_get_same_ranking
              get_base fr target st1 fr1 value Hget).
            subst get_base. destruct (R.is_materialized observed target);
              reflexivity. }
          intros variable [rank Hrank].
          assert (Hobserved : Total.ranked observed variable).
          { exists rank. now rewrite Hranking in Hrank. }
          destruct (@first_discovery_observe_ranked_cases
            st target variable Hobserved) as [-> |Hold].
          -- eapply complete_get_target_materialized. exact Hget.
          -- exact (Total.Termination.step_materialized_mono
               variable Hstep_semantic (Hmaterialized variable Hold)).
      + exfalso. eapply (@ordinary_reachable_side_impossible
          tf roots finite); eauto.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (R.is_materialized observed target) eqn:Htarget.
        * inversion Hstep; subst. cbn.
          intros variable Hranked.
          destruct (@first_discovery_observe_ranked_cases
            st target variable Hranked) as [-> |Hold].
          -- exact Htarget.
          -- exact (Total.Termination.step_materialized_mono
               variable Hstep_semantic (Hmaterialized variable Hold)).
        * destruct (R.rank_lt observed (R.frame_owner fr) target).
          -- inversion Hstep; subst. cbn.
             intros variable Hranked.
             destruct (@first_discovery_observe_ranked_cases
               st target variable Hranked) as [-> |Hold].
             ++ now left.
             ++ right. exact (Total.Termination.step_materialized_mono
                  variable Hstep_semantic (Hmaterialized variable Hold)).
          -- inversion Hstep; subst. cbn.
             intros variable Hranked.
             assert (Hobserved : Total.ranked observed variable).
             { destruct Hranked as [rank Hranked]. exists rank.
               unfold R.materialize, R.enqueue in Hranked.
               destruct (M.lookup
                 (R.sigma
                   (R.with_queue observed
                     (R.queue_insert (R.ranking observed) target
                       (R.queue observed)))) target);
                 exact Hranked. }
             destruct (@first_discovery_observe_ranked_cases
               st target variable Hobserved) as [-> |Hold].
             ++ apply materialize_target_materialized.
             ++ exact (Total.Termination.step_materialized_mono
                  variable Hstep_semantic (Hmaterialized variable Hold)).
    - destruct pending as [|target remaining].
      + cbn -[R.publish_targets] in Hstep.
        inversion Hstep; subst. cbn. exact Hmaterialized.
      + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        * inversion Hstep; subst. cbn. exact Hmaterialized.
        * destruct (R.write_side_contribution st fr target D.bottom)
            as [st1 changed] eqn:Hwrite.
          assert (Hst1 : all_ranked_materialized st1).
          { intros variable [rank Hrank].
            assert (Hold : Total.ranked st variable).
            { exists rank. rewrite (write_side_contribution_same_ranking
                Hwrite) in Hrank. exact Hrank. }
            destruct (Inv.write_side_contribution_same_read_view Hwrite)
              as [Hsigma _].
            unfold R.is_materialized. rewrite Hsigma.
            now apply Hmaterialized. }
          unfold R.continue_dead in Hstep. destruct changed.
          -- destruct (_ && _)%bool.
             ++ inversion Hstep; subst; cbn.
                intros variable Hranked. right. now apply Hst1.
             ++ inversion Hstep; subst; cbn. exact Hst1.
          -- inversion Hstep; subst; cbn. exact Hst1.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst. cbn.
      intros variable [rank Hrank].
      assert (Hold : Total.ranked st variable).
      { exists rank. rewrite (@set_value_same_ranking
          st fr direct st1 fr1 Hset) in Hrank.
        exact Hrank. }
      exact (Total.Termination.step_materialized_mono
        variable Hstep_semantic (Hmaterialized variable Hold)).
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [queued |].
      + destruct (V.eq_dec queued (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
            try discriminate.
          inversion Hstep; subst; cbn.
          exact Hmaterialized.
        * destruct (R.rank_lt st (R.frame_owner fr) queued).
          -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
               try discriminate.
             inversion Hstep; subst; cbn.
             intros variable Hranked. right.
             apply Hmaterialized. exact Hranked.
          -- inversion Hstep; subst. cbn.
             intros variable [rank Hrank].
             assert (Hold : Total.ranked st variable).
             { exists rank. rewrite reset_registered_cells_same_ranking
                 in Hrank. exact Hrank. }
             exact (Total.Termination.step_materialized_mono
               variable Hstep_semantic (Hmaterialized variable Hold)).
      + inversion Hstep; subst. cbn.
        intros variable [rank Hrank].
        assert (Hold : Total.ranked st variable).
        { exists rank. rewrite reset_registered_cells_same_ranking
            in Hrank. exact Hrank. }
        exact (Total.Termination.step_materialized_mono
          variable Hstep_semantic (Hmaterialized variable Hold)).
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; cbn; exact Hmaterialized).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst. cbn.
      intros variable [rank Hrank].
      assert (Hold : Total.ranked st variable).
      { exists rank. rewrite (@complete_get_same_ranking
          st fr target st1 fr1 value Hget) in Hrank. exact Hrank. }
      exact (Total.Termination.step_materialized_mono
        variable Hstep_semantic (Hmaterialized variable Hold)).
  Qed.

  Theorem first_discovery_reachable_ranked_materialization :
    forall tf roots (finite : Sem.finite_system tf roots) c,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) c ->
      ranked_materialization_control
        (R.cfg_state c) (R.cfg_control c).
  Proof.
    intros tf roots finite c Hordinary Hsteps.
    assert (Hpreserve : forall before after,
      Sem.steps tf before after ->
      Sem.steps tf (R.initial_config roots) before ->
      ranked_materialization_control
        (R.cfg_state before) (R.cfg_control before) ->
      ranked_materialization_control
        (R.cfg_state after) (R.cfg_control after)).
    { intros before after Hrun Hbefore Hbefore_materialized.
      induction Hrun.
      - exact Hbefore_materialized.
      - apply IHHrun.
        + eapply Total.Termination.steps_append_one; eassumption.
        + eapply (@first_discovery_ranked_materialization_step
            tf roots finite first next); eassumption. }
    eapply Hpreserve.
    - exact Hsteps.
    - constructor.
    - cbn. intros variable [rank Hrank].
      rewrite RankLaws.empty_lookup in Hrank. discriminate.
  Qed.

  Corollary first_discovery_reachable_nonstart_ranked_materialized :
    forall tf roots (finite : Sem.finite_system tf roots) st control variable,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := control |} ->
      (forall k, control <> R.StartEpisode variable k) ->
      Total.ranked st variable ->
      R.is_materialized st variable = true.
  Proof.
    intros tf roots finite st control variable Hordinary Hreachable
      Hnotstart Hranked.
    pose proof (@first_discovery_reachable_ranked_materialization
      tf roots finite
      {| R.cfg_state := st; R.cfg_control := control |}
      Hordinary Hreachable) as Hmaterialized.
    destruct control; cbn in Hmaterialized; try now apply Hmaterialized.
    destruct (Hmaterialized variable Hranked) as [Heq |Hmat];
      [exfalso; eapply (Hnotstart c); now subst |exact Hmat].
  Qed.

  Definition old_queue_members_from
    (entry initial current : R.state) : Prop :=
    forall queued,
      Total.ranked entry queued ->
      List.In queued (R.queue current) ->
      List.In queued (R.queue initial).

  Lemma old_queue_members_from_queue :
    forall entry initial before after,
      R.queue after = R.queue before ->
      old_queue_members_from entry initial before ->
      old_queue_members_from entry initial after.
  Proof.
    intros entry initial before after Hqueue Hold queued Hranked Hin.
    apply Hold; [exact Hranked |]. now rewrite <- Hqueue.
  Qed.

  Lemma old_queue_members_from_enqueue_fresh :
    forall entry initial st target,
      R.Ranking.lookup (R.ranking entry) target = None ->
      old_queue_members_from entry initial st ->
      old_queue_members_from entry initial (R.enqueue st target).
  Proof.
    intros entry initial st target Htarget Hold queued
      [rank Hqueued_rank] Hin.
    unfold R.enqueue in Hin. cbn in Hin.
    apply Total.queue_insert_members in Hin.
    destruct Hin as [-> |Hin].
    - rewrite Htarget in Hqueued_rank. discriminate.
    - eapply Hold; [now exists rank |exact Hin].
  Qed.

  Lemma old_queue_members_from_materialize :
    forall entry initial st target,
      old_queue_members_from entry initial st ->
      old_queue_members_from entry initial (R.materialize st target).
  Proof.
    intros entry initial st target Hold.
    eapply old_queue_members_from_queue; [|exact Hold].
    unfold R.materialize. destruct (M.lookup (R.sigma st) target);
      reflexivity.
  Qed.

  Lemma first_discovery_old_rank_below_fresh :
    forall before target after variable,
      Total.rank_valid before ->
      Total.ranked before variable ->
      R.Ranking.lookup (R.ranking before) target = None ->
      Total.rank_extends (R.observe before target) after ->
      R.rank_lt after variable target = true.
  Proof.
    intros before target after variable Hvalid Hvariable Hfresh Hextends.
    assert (Hobserved : R.rank_lt
      (R.observe before target) variable target = true).
    { eapply fresh_observe_rank_lt.
      - apply first_discovery_fresh_ranks_above.
      - exact Hvalid.
      - exact Hvariable.
      - exact Hfresh. }
    assert (Hvariable_observed :
      Total.ranked (R.observe before target) variable).
    { eapply Total.ranked_extended.
      - eapply Total.rank_extends_observe. reflexivity.
      - exact Hvariable. }
    assert (Htarget_observed :
      Total.ranked (R.observe before target) target).
    { eapply Total.observe_ranks_variable. reflexivity. }
    rewrite <- (@Total.rank_lt_stable
      (R.observe before target) after variable target
      Hextends Hvariable_observed Htarget_observed).
    exact Hobserved.
  Qed.

  Lemma continuation_above_below :
    forall st owner base upper k,
      Total.Termination.continuation_above owner base k ->
      Total.Termination.continuation_below st upper k ->
      R.rank_lt st owner upper = true.
  Proof.
    intros st owner base upper k. revert upper.
    induction k; intros upper Habove Hbelow;
      cbn in *; try contradiction.
    all: destruct Hbelow as [Htop Hbelow].
    all: destruct Habove as [[Howner Hbase] |Habove].
    all: try (now rewrite Howner in Htop).
    all: eapply Total.Termination.rank_lt_trans_true;
      [eapply IHk; eassumption |exact Htop].
  Qed.

  Lemma first_discovery_active_frame_was_fresh :
    forall tf roots before owner base after fr body k,
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start
        {| R.cfg_state := after;
           R.cfg_control := R.RunRhs fr body k |} ->
      Total.Termination.episode_active_control owner base
        (R.RunRhs fr body k) ->
      ~ Total.ranked (R.cfg_state before) (R.frame_owner fr).
  Proof.
    intros tf roots before owner base after fr body k Hbefore Hfresh
      start Hstart Hrun Hactive Hold.
    assert (Hfinal : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := after;
         R.cfg_control := R.RunRhs fr body k |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    pose proof (Total.Termination.reachable_control_ordered Hfinal)
      as Hordered.
    cbn in Hactive, Hordered.
    assert (Hold_lower :
      R.rank_lt after (R.frame_owner fr) owner = true).
    { eapply first_discovery_old_rank_below_fresh.
      - exact (Total.configuration_rank_valid
          (Total.reachable_configuration_ranked Hbefore)).
      - exact Hold.
      - exact Hfresh.
      - exact (Total.Termination.steps_rank_extends Hrun). }
    destruct Hactive as [[Howner Hbase] |Habove].
    - rewrite Howner in Hold_lower.
      pose proof (proj1 (@Total.rank_lt_true_ranked after
        owner owner Hold_lower)) as Hranked.
      rewrite (@Total.rank_lt_irrefl after owner Hranked) in Hold_lower.
      discriminate.
    - pose proof (@continuation_above_below after owner base
        (R.frame_owner fr) k Habove Hordered) as Hhigher.
      destruct (@Total.rank_lt_true_ranked after
        (R.frame_owner fr) owner Hold_lower) as [Hframe Howner_ranked].
      rewrite (@Total.rank_lt_asymmetric after
        (R.frame_owner fr) owner Hframe Howner_ranked Hold_lower) in Hhigher.
      discriminate.
  Qed.

  Lemma first_discovery_active_commit_frame_was_fresh :
    forall tf roots before owner base after fr direct k,
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start
        {| R.cfg_state := after;
           R.cfg_control := R.RunCommit fr direct k |} ->
      Total.Termination.episode_active_control owner base
        (R.RunCommit fr direct k) ->
      ~ Total.ranked (R.cfg_state before) (R.frame_owner fr).
  Proof.
    intros tf roots before owner base after fr direct k Hbefore Hfresh
      start Hstart Hrun Hactive Hold.
    assert (Hfinal : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := after;
         R.cfg_control := R.RunCommit fr direct k |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    pose proof (Total.Termination.reachable_control_ordered Hfinal)
      as Hordered.
    cbn in Hactive, Hordered.
    assert (Hold_lower :
      R.rank_lt after (R.frame_owner fr) owner = true).
    { eapply first_discovery_old_rank_below_fresh.
      - exact (Total.configuration_rank_valid
          (Total.reachable_configuration_ranked Hbefore)).
      - exact Hold.
      - exact Hfresh.
      - exact (Total.Termination.steps_rank_extends Hrun). }
    destruct Hactive as [[Howner Hbase] |Habove].
    - rewrite Howner in Hold_lower.
      pose proof (proj1 (@Total.rank_lt_true_ranked after
        owner owner Hold_lower)) as Hranked.
      rewrite (@Total.rank_lt_irrefl after owner Hranked) in Hold_lower.
      discriminate.
    - pose proof (@continuation_above_below after owner base
        (R.frame_owner fr) k Habove Hordered) as Hhigher.
      destruct (@Total.rank_lt_true_ranked after
        (R.frame_owner fr) owner Hold_lower) as [Hframe Howner_ranked].
      rewrite (@Total.rank_lt_asymmetric after
        (R.frame_owner fr) owner Hframe Howner_ranked Hold_lower) in Hhigher.
      discriminate.
  Qed.

  Lemma first_discovery_active_after_get_frame_was_fresh :
    forall tf roots before owner base after fr target next k,
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start
        {| R.cfg_state := after;
           R.cfg_control := R.Return (R.KAfterGet fr target next k) |} ->
      Total.Termination.episode_active_control owner base
        (R.Return (R.KAfterGet fr target next k)) ->
      ~ Total.ranked (R.cfg_state before) (R.frame_owner fr).
  Proof.
    intros tf roots before owner base after fr target next k
      Hbefore Hfresh start Hstart Hrun Hactive Hold.
    assert (Hfinal : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := after;
         R.cfg_control := R.Return (R.KAfterGet fr target next k) |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    pose proof (Total.Termination.reachable_control_ordered Hfinal)
      as Hordered.
    cbn in Hactive, Hordered.
    assert (Hold_lower :
      R.rank_lt after (R.frame_owner fr) owner = true).
    { eapply first_discovery_old_rank_below_fresh.
      - exact (Total.configuration_rank_valid
          (Total.reachable_configuration_ranked Hbefore)).
      - exact Hold.
      - exact Hfresh.
      - exact (Total.Termination.steps_rank_extends Hrun). }
    destruct Hactive as [[Howner Hbase] |Habove].
    - rewrite Howner in Hold_lower.
      pose proof (proj1 (@Total.rank_lt_true_ranked after
        owner owner Hold_lower)) as Hranked.
      rewrite (@Total.rank_lt_irrefl after owner Hranked) in Hold_lower.
      discriminate.
    - pose proof (@continuation_above_below after owner base
        (R.frame_owner fr) k Habove Hordered) as Hhigher.
      destruct (@Total.rank_lt_true_ranked after
        (R.frame_owner fr) owner Hold_lower) as [Hframe Howner_ranked].
      rewrite (@Total.rank_lt_asymmetric after
        (R.frame_owner fr) owner Hframe Howner_ranked Hold_lower) in Hhigher.
      discriminate.
  Qed.

  Definition fresh_readers_from (entry st : R.state) : Prop :=
    forall target reader,
      R.Ranking.lookup (R.ranking entry) target = None ->
      S.mem reader (R.lookup_set (R.readers st) target) = true ->
      R.Ranking.lookup (R.ranking entry) reader = None.

  Lemma fresh_readers_from_view :
    forall entry before after,
      R.readers after = R.readers before ->
      fresh_readers_from entry before ->
      fresh_readers_from entry after.
  Proof.
    intros entry before after Hreaders Hfresh target reader
      Htarget Hmem.
    apply Hfresh with target; [exact Htarget |].
    now rewrite <- Hreaders.
  Qed.

  Lemma fresh_readers_from_same_read_view :
    forall entry before after,
      Inv.same_read_view before after ->
      fresh_readers_from entry before ->
      fresh_readers_from entry after.
  Proof.
    intros entry before after [_ [Hreaders _]].
    now apply fresh_readers_from_view.
  Qed.

  Lemma first_discovery_fresh_readers_initial :
    forall tf roots c owner,
      Sem.steps tf (R.initial_config roots) c ->
      fresh_readers_from (R.cfg_state c)
        (R.observe (R.cfg_state c) owner).
  Proof.
    intros tf roots c owner Hreachable target reader Htarget Hmem.
    destruct (R.Ranking.lookup
      (R.ranking (R.cfg_state c)) reader) eqn:Hreader;
      [|reflexivity].
    exfalso.
    assert (Hunmaterialized :
      R.is_materialized (R.cfg_state c) target = false).
    { eapply reachable_unranked_is_unmaterialized; eassumption. }
    pose proof (@reachable_unmaterialized_readers_empty
      tf roots c Hreachable target reader Hunmaterialized) as Hempty.
    destruct (Inv.same_read_view_observe (R.cfg_state c) owner)
      as [_ [Hreaders _]].
    rewrite Hreaders in Hmem. rewrite Hempty in Hmem. discriminate.
  Qed.

  Lemma fresh_readers_from_complete_get :
    forall entry st fr target next next_fr value,
      fresh_readers_from entry st ->
      R.Ranking.lookup (R.ranking entry) (R.frame_owner fr) = None ->
      R.complete_get st fr target = (next, next_fr, value) ->
      fresh_readers_from entry next.
  Proof.
    intros entry st fr target next next_fr value
      Hfresh Howner Hget observed reader Hobserved Hmem.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    inversion Hget; subst next next_fr value; clear Hget.
    unfold R.materialize in Hmem.
    destruct (M.lookup
      (R.sigma
        (R.with_readers base
          (M.update (R.readers base) target
            (S.add (R.frame_owner fr)
              (R.lookup_set (R.readers base) target))))) target);
      cbn in Hmem.
    all: destruct (V.eq_dec observed target) as [-> |Hneq].
    all: try rewrite lookup_set_update_same in Hmem.
    all: try rewrite lookup_set_update_other in Hmem by exact Hneq.
    all: try (apply SL.add_spec in Hmem;
      destruct Hmem as [-> |Hmem]; [exact Howner |]).
    all: subst base.
    all: destruct (R.rank_lt st (R.frame_owner fr) target);
      cbn in Hmem.
    all: eapply Hfresh; eassumption.
  Qed.

  Lemma fresh_readers_from_set_value :
    forall entry st fr direct next next_fr,
      fresh_readers_from entry st ->
      R.set_value st fr direct = (next, next_fr) ->
      fresh_readers_from entry next.
  Proof.
    intros entry st fr direct next next_fr Hfresh Hset.
    destruct (@set_value_state_cases st fr direct next next_fr Hset)
      as [-> |[value ->]]; [exact Hfresh |].
    intros target reader Htarget Hmem.
    unfold Inv.commit_value in Hmem. cbn in Hmem.
    destruct (V.eq_dec target (R.frame_owner fr)) as [-> |Hneq].
    - rewrite lookup_set_update_same, SL.empty_spec in Hmem.
      discriminate.
    - rewrite lookup_set_update_other in Hmem by exact Hneq.
      eapply Hfresh; eassumption.
  Qed.

  Lemma first_discovery_fresh_readers_active_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base current after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start current ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control current) ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state current) ->
      Sem.step tf current after ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state after).
  Proof.
    intros tf roots finite before owner base [st control] after Hordinary
      Hbefore Howner_fresh start Hstart Hrun Hactive Hreaders Hstep.
    assert (Hcurrent : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := control |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    unfold Sem.step in Hstep.
    destruct control as
      [|seeded |remaining |current_owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k];
      cbn in Hactive; try contradiction.
    - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
      eapply fresh_readers_from_view; [|exact Hreaders].
      unfold R.materialize. destruct (M.lookup (R.sigma st) current_owner);
        reflexivity.
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. inversion Hstep; subst. exact Hreaders.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        assert (Hobserved : fresh_readers_from
          (R.cfg_state before) observed).
        { subst observed. eapply fresh_readers_from_same_read_view.
          - apply Inv.same_read_view_observe.
          - exact Hreaders. }
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst. exact Hobserved.
        * set (get_base := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          assert (Hbase : fresh_readers_from
            (R.cfg_state before) get_base).
          { subst get_base. destruct (R.is_materialized observed target);
              exact Hobserved. }
          destruct (R.complete_get get_base fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          eapply fresh_readers_from_complete_get;
            [exact Hbase | |exact Hget].
          destruct (R.Ranking.lookup
            (R.ranking (R.cfg_state before)) (R.frame_owner fr))
            eqn:Hold; [|reflexivity].
          exfalso. eapply (@first_discovery_active_frame_was_fresh
            tf roots before owner base st fr
            (R.ConstraintSystem.Get target next) k);
            try eassumption.
          now exists n.
      + exfalso. eapply (@ordinary_reachable_side_impossible
          tf roots finite); eauto.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        assert (Hobserved : fresh_readers_from
          (R.cfg_state before) (R.observe st target)).
        { eapply fresh_readers_from_same_read_view.
          - apply Inv.same_read_view_observe.
          - exact Hreaders. }
        destruct (R.is_materialized (R.observe st target) target).
        * inversion Hstep; subst. exact Hobserved.
        * destruct (R.rank_lt (R.observe st target)
            (R.frame_owner fr) target).
          -- inversion Hstep; subst. exact Hobserved.
          -- inversion Hstep; subst.
             eapply fresh_readers_from_view; [|exact Hobserved].
             unfold R.materialize, R.enqueue.
             destruct (M.lookup
               (R.sigma
                 (R.with_queue (R.observe st target)
                   (R.queue_insert (R.ranking (R.observe st target)) target
                     (R.queue (R.observe st target))))) target);
               reflexivity.
    - destruct pending as [|target remaining].
      + cbn -[R.publish_targets] in Hstep.
        inversion Hstep; subst. exact Hreaders.
      + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        * inversion Hstep; subst. exact Hreaders.
        * destruct (R.write_side_contribution st fr target D.bottom)
            as [st1 changed] eqn:Hwrite.
          assert (Hst1 : fresh_readers_from
            (R.cfg_state before) st1).
          { eapply fresh_readers_from_same_read_view.
            - eapply Inv.write_side_contribution_same_read_view.
              exact Hwrite.
            - exact Hreaders. }
          unfold R.continue_dead in Hstep. destruct changed;
            try destruct (_ && _)%bool;
            inversion Hstep; subst; exact Hst1.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst.
      eapply fresh_readers_from_set_value; eassumption.
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [queued |].
      + destruct (V.eq_dec queued (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)); try discriminate.
          destruct p. inversion Hstep; subst. exact Hreaders.
        * destruct (R.rank_lt st (R.frame_owner fr) queued).
          -- destruct (R.queue_pop (R.queue st)); try discriminate.
             destruct p. inversion Hstep; subst. exact Hreaders.
          -- inversion Hstep; subst.
             eapply fresh_readers_from_same_read_view.
             ++ exact (proj1 (Inv.reset_registered_cells_same_solver_view
                  st (R.frame_owner fr))).
             ++ exact Hreaders.
      + inversion Hstep; subst.
        eapply fresh_readers_from_same_read_view.
        * exact (proj1 (Inv.reset_registered_cells_same_solver_view
            st (R.frame_owner fr))).
        * exact Hreaders.
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; exact Hreaders).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst.
      eapply fresh_readers_from_complete_get;
        [exact Hreaders | |exact Hget].
      destruct (R.Ranking.lookup
        (R.ranking (R.cfg_state before)) (R.frame_owner fr))
        eqn:Hold; [|reflexivity].
      exfalso. eapply (@first_discovery_active_after_get_frame_was_fresh
        tf roots before owner base st fr target next rest);
        try eassumption.
      now exists n.
  Qed.

  Lemma first_discovery_fresh_readers_active_prefix :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base first final,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start first ->
      ~ Total.Termination.continuation_contains owner base ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control first) ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state first) ->
      Total.Termination.active_prefix owner tf first final ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state final).
  Proof.
    intros tf roots finite before owner base first final Hordinary
      Hbefore Howner_fresh start Hstart Hrun Hbase Hactive Hreaders Hprefix.
    revert Hrun Hactive Hreaders.
    induction Hprefix as
      [c |current next final Hcontains Hstep Htail IH];
      intros Hrun Hactive Hreaders; [exact Hreaders |].
    assert (Hnext_readers : fresh_readers_from
      (R.cfg_state before) (R.cfg_state next)).
    { eapply (@first_discovery_fresh_readers_active_step
        tf roots finite before owner base current next);
        eassumption. }
    assert (Hnext_run : Sem.steps tf start next).
    { eapply Total.Termination.steps_append_one; eassumption. }
    destruct (@Total.Termination.episode_active_control_step
      tf current next owner base Hstep Hactive) as [Hnext_active |Hexit].
    - eapply IH; eassumption.
    - inversion Htail as
        [|tail_first tail_next tail_final Htail_contains Htail_step Htail_rest];
        subst.
      + exact Hnext_readers.
      + exfalso. apply Hbase. rewrite Hexit in Htail_contains.
        exact Htail_contains.
  Qed.

  Lemma first_discovery_episode_fresh_readers :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base final,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Total.Termination.active_prefix owner tf start final ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state final).
  Proof.
    intros tf roots finite before owner base final Hordinary Hbefore
      Howner_fresh start Hstart Hprefix.
    assert (Hordered : Total.Termination.continuation_below
      (R.cfg_state start) owner base).
    { exact (Total.Termination.reachable_control_ordered Hstart). }
    assert (Hbase :
      ~ Total.Termination.continuation_contains owner base).
    { intro Hcontains.
      pose proof (@Total.Termination.continuation_contains_below
        (R.cfg_state start) owner base owner Hordered Hcontains) as Hfalse.
      pose proof (proj1 (@Total.rank_lt_true_ranked
        (R.cfg_state start) owner owner Hfalse)) as Hranked.
      rewrite (@Total.rank_lt_irrefl
        (R.cfg_state start) owner Hranked) in Hfalse.
      discriminate. }
    eapply (@first_discovery_fresh_readers_active_prefix
      tf roots finite before owner base start final);
      try eassumption.
    - constructor.
    - cbn. now left.
    - eapply first_discovery_fresh_readers_initial. exact Hbefore.
  Qed.

  Lemma fresh_set_value_does_not_enqueue_old :
    forall entry st fr direct next next_fr queued,
      fresh_readers_from entry st ->
      R.Ranking.lookup (R.ranking entry) (R.frame_owner fr) = None ->
      Total.ranked entry queued ->
      R.set_value st fr direct = (next, next_fr) ->
      ~ List.In queued (R.queue st) ->
      ~ List.In queued (R.queue next).
  Proof.
    intros entry st fr direct next next_fr queued Hreaders Howner
      [rank Hqueued_rank] Hset Hnot_before Hqueued_after.
    destruct (@Total.set_value_new_queue_cause
      st fr direct next next_fr queued Hset Hnot_before Hqueued_after)
      as [_ Hreader].
    pose proof (Hreaders (R.frame_owner fr) queued Howner Hreader)
      as Hqueued_fresh.
    rewrite Hqueued_rank in Hqueued_fresh. discriminate.
  Qed.

  Lemma fresh_set_value_preserves_old_queue_membership :
    forall entry st fr direct next next_fr queued,
      fresh_readers_from entry st ->
      R.Ranking.lookup (R.ranking entry) (R.frame_owner fr) = None ->
      Total.ranked entry queued ->
      R.set_value st fr direct = (next, next_fr) ->
      List.In queued (R.queue next) ->
      List.In queued (R.queue st).
  Proof.
    intros entry st fr direct next next_fr queued Hreaders Howner
      Hqueued Hset Hafter.
    destruct (in_dec V.eq_dec queued (R.queue st)) as [Hbefore |Hnot];
      [exact Hbefore |].
    exfalso. eapply (@fresh_set_value_does_not_enqueue_old
      entry st fr direct next next_fr queued);
      eassumption.
  Qed.

  Lemma first_discovery_old_target_materialized_in_runrhs :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base st fr body k target rank,
      ordinary_monotonic_system tf ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) target = Some rank ->
      R.is_materialized st target = true.
  Proof.
    intros tf roots finite before owner base st fr body k target rank
      Hordinary start Hstart Hrun Htarget.
    assert (Htarget_start : R.Ranking.lookup
      (R.ranking (R.cfg_state start)) target = Some rank).
    { pose proof (@Total.rank_extends_observe
        (R.cfg_state before) owner (R.observe (R.cfg_state before) owner)
        eq_refl) as Hextends.
      exact (Hextends target rank Htarget). }
    assert (Htarget_st : Total.ranked st target).
    { exists rank. exact ((Total.Termination.steps_rank_extends Hrun)
        target rank Htarget_start). }
    eapply (@first_discovery_reachable_nonstart_ranked_materialized
      tf roots finite st (R.RunRhs fr body k) target Hordinary).
    - eapply Total.Termination.steps_transitive; eassumption.
    - intros continuation Hshape. discriminate.
    - exact Htarget_st.
  Qed.

  Lemma first_discovery_old_queue_active_step :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base initial current after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start current ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control current) ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state current) ->
      old_queue_members_from (R.cfg_state before) initial
        (R.cfg_state current) ->
      Sem.step tf current after ->
      old_queue_members_from (R.cfg_state before) initial
        (R.cfg_state after).
  Proof.
    intros tf roots finite before owner base initial [st control] after
      Hordinary Hbefore Howner_fresh start Hstart Hrun Hactive
      Hreaders Hold Hstep.
    assert (Hcurrent : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := control |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    unfold Sem.step in Hstep.
    destruct control as
      [|seeded |remaining |current_owner k |fr body k
       |fr direct pending k |fr direct k |fr k |k];
      cbn in Hactive; try contradiction.
    - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
      now apply old_queue_members_from_materialize.
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. inversion Hstep; subst. exact Hold.
      + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        assert (Hobserved : old_queue_members_from
          (R.cfg_state before) initial observed).
        { eapply old_queue_members_from_queue; [|exact Hold].
          subst observed. apply Total.Termination.observe_queue. }
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst. exact Hobserved.
        * set (get_base := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          assert (Hbase : old_queue_members_from
            (R.cfg_state before) initial get_base).
          { subst get_base.
            destruct (R.is_materialized observed target) eqn:Htarget;
              [exact Hobserved |].
            assert (Htarget_fresh : R.Ranking.lookup
              (R.ranking (R.cfg_state before)) target = None).
            { destruct (R.Ranking.lookup
                (R.ranking (R.cfg_state before)) target)
                as [rank |] eqn:Hold_target; [|reflexivity].
              pose proof (@first_discovery_old_target_materialized_in_runrhs
                tf roots finite before owner base st fr
                (R.ConstraintSystem.Get target next) k target rank
                Hordinary Hstart Hrun Hold_target) as Hmaterialized.
              assert (Hobserved_materialized :
                R.is_materialized observed target = true).
              { subst observed. unfold R.observe, R.is_materialized.
                destruct (R.Ranking.observe (R.ranking st) target).
                exact Hmaterialized. }
              rewrite Hobserved_materialized in Htarget. discriminate. }
            now apply old_queue_members_from_enqueue_fresh. }
          destruct (R.complete_get get_base fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          eapply old_queue_members_from_queue; [|exact Hbase].
          eapply Total.Termination.complete_get_queue. exact Hget.
      + exfalso. eapply (@ordinary_reachable_side_impossible
          tf roots finite); eauto.
      + cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        assert (Hobserved : old_queue_members_from
          (R.cfg_state before) initial observed).
        { eapply old_queue_members_from_queue; [|exact Hold].
          subst observed. apply Total.Termination.observe_queue. }
        destruct (R.is_materialized observed target) eqn:Htarget.
        * inversion Hstep; subst. exact Hobserved.
        * assert (Htarget_fresh : R.Ranking.lookup
            (R.ranking (R.cfg_state before)) target = None).
          { destruct (R.Ranking.lookup
              (R.ranking (R.cfg_state before)) target)
              as [rank |] eqn:Hold_target; [|reflexivity].
            pose proof (@first_discovery_old_target_materialized_in_runrhs
              tf roots finite before owner base st fr
              (R.ConstraintSystem.Spawn target next) k target rank
              Hordinary Hstart Hrun Hold_target) as Hmaterialized.
            assert (Hobserved_materialized :
              R.is_materialized observed target = true).
            { subst observed. unfold R.observe, R.is_materialized.
              destruct (R.Ranking.observe (R.ranking st) target).
              exact Hmaterialized. }
            rewrite Hobserved_materialized in Htarget. discriminate. }
          destruct (R.rank_lt observed (R.frame_owner fr) target).
          -- inversion Hstep; subst. exact Hobserved.
          -- inversion Hstep; subst.
             apply old_queue_members_from_materialize.
             now apply old_queue_members_from_enqueue_fresh.
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |}
        Hcurrent) as [_ Hclean].
      cbn in Hclean. destruct Hclean as [_ [Hpending _]]. subst pending.
      cbn -[R.publish_targets] in Hstep. inversion Hstep; subst. exact Hold.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst.
      assert (Hframe_fresh : R.Ranking.lookup
        (R.ranking (R.cfg_state before)) (R.frame_owner fr) = None).
      { destruct (R.Ranking.lookup
          (R.ranking (R.cfg_state before)) (R.frame_owner fr))
          as [rank |] eqn:Hlookup; [|reflexivity].
        exfalso. eapply (@first_discovery_active_commit_frame_was_fresh
          tf roots before owner base st fr direct k);
          try eassumption. now exists rank. }
      intros queued Hranked Hin.
      apply Hold; [exact Hranked |].
      eapply fresh_set_value_preserves_old_queue_membership;
        eassumption.
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [queued |] eqn:Hpeek.
      + destruct (V.eq_dec queued (R.frame_owner fr)).
        * destruct (R.queue_pop (R.queue st)) as [[head tail] |]
            eqn:Hpop; try discriminate.
          inversion Hstep; subst. intros variable Hranked Hin.
          apply Hold; [exact Hranked |].
          apply (proj2 (@work_queue_pop_members
            (R.queue st) head tail variable Hpop)). now right.
        * destruct (R.rank_lt st (R.frame_owner fr) queued).
          -- destruct (R.queue_pop (R.queue st)) as [[head tail] |]
               eqn:Hpop; try discriminate.
             inversion Hstep; subst. intros variable Hranked Hin.
             apply Hold; [exact Hranked |].
             apply (proj2 (@work_queue_pop_members
               (R.queue st) head tail variable Hpop)). now right.
          -- inversion Hstep; subst.
             eapply old_queue_members_from_queue; [|exact Hold].
             exact (proj2 (proj2 (proj1
               (Inv.reset_registered_cells_same_solver_view
                 st (R.frame_owner fr))))).
      + inversion Hstep; subst.
        eapply old_queue_members_from_queue; [|exact Hold].
        exact (proj2 (proj2 (proj1
          (Inv.reset_registered_cells_same_solver_view
            st (R.frame_owner fr))))).
    - destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; exact Hold).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst.
      eapply old_queue_members_from_queue; [|exact Hold].
      eapply Total.Termination.complete_get_queue. exact Hget.
  Qed.

  Lemma first_discovery_old_queue_active_prefix :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base initial first final,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start first ->
      ~ Total.Termination.continuation_contains owner base ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control first) ->
      fresh_readers_from (R.cfg_state before) (R.cfg_state first) ->
      old_queue_members_from (R.cfg_state before) initial
        (R.cfg_state first) ->
      Total.Termination.active_prefix owner tf first final ->
      old_queue_members_from (R.cfg_state before) initial
        (R.cfg_state final).
  Proof.
    intros tf roots finite before owner base initial first final
      Hordinary Hbefore Howner_fresh start Hstart Hrun Hbase Hactive
      Hreaders Hold Hprefix.
    revert Hrun Hactive Hreaders Hold.
    induction Hprefix as
      [c |current next final Hcontains Hstep Htail IH];
      intros Hrun Hactive Hreaders Hold; [exact Hold |].
    assert (Hnext_readers : fresh_readers_from
      (R.cfg_state before) (R.cfg_state next)).
    { eapply (@first_discovery_fresh_readers_active_step
        tf roots finite before owner base current next);
        eassumption. }
    assert (Hnext_old : old_queue_members_from
      (R.cfg_state before) initial (R.cfg_state next)).
    { eapply (@first_discovery_old_queue_active_step
        tf roots finite before owner base initial current next);
        eassumption. }
    assert (Hnext_run : Sem.steps tf start next).
    { eapply Total.Termination.steps_append_one; eassumption. }
    destruct (@Total.Termination.episode_active_control_step
      tf current next owner base Hstep Hactive) as [Hnext_active |Hexit].
    - eapply IH; eassumption.
    - inversion Htail as
        [|tail_first tail_next tail_final Htail_contains Htail_step Htail_rest];
        subst.
      + exact Hnext_old.
      + exfalso. apply Hbase. rewrite Hexit in Htail_contains.
        exact Htail_contains.
  Qed.

  Theorem first_discovery_episode_preserves_old_queue :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base final,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Total.Termination.active_prefix owner tf start final ->
      old_queue_members_from (R.cfg_state before) (R.cfg_state start)
        (R.cfg_state final).
  Proof.
    intros tf roots finite before owner base final Hordinary Hbefore
      Howner_fresh start Hstart Hprefix.
    assert (Hordered : Total.Termination.continuation_below
      (R.cfg_state start) owner base).
    { exact (Total.Termination.reachable_control_ordered Hstart). }
    assert (Hbase :
      ~ Total.Termination.continuation_contains owner base).
    { intro Hcontains.
      pose proof (@Total.Termination.continuation_contains_below
        (R.cfg_state start) owner base owner Hordered Hcontains) as Hfalse.
      pose proof (proj1 (@Total.rank_lt_true_ranked
        (R.cfg_state start) owner owner Hfalse)) as Hranked.
      rewrite (@Total.rank_lt_irrefl
        (R.cfg_state start) owner Hranked) in Hfalse.
      discriminate. }
    eapply (@first_discovery_old_queue_active_prefix
      tf roots finite before owner base (R.cfg_state start) start final);
      try eassumption.
    - constructor.
    - cbn. now left.
    - eapply first_discovery_fresh_readers_initial. exact Hbefore.
    - intros queued Hranked Hin. exact Hin.
  Qed.

  Lemma first_discovery_fresh_episode_active_completion :
    forall tf roots (finite : Sem.finite_system tf roots)
      before owner base,
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      exists final,
        Total.Termination.active_prefix owner tf start
          {| R.cfg_state := final; R.cfg_control := R.Return base |} /\
        Total.Termination.queue_strictly_below owner final.
  Proof.
    intros tf roots finite before owner base Hbefore Hfresh start Hstart.
    pose proof (Total.reachable_config_supported finite Hstart)
      as [_ Hcontrol_supported].
    cbn in Hcontrol_supported.
    destruct (@Total.Termination.all_episodes_complete
      tf roots finite owner base start (proj1 Hcontrol_supported)
      Hstart eq_refl) as [done [Hdone Hdone_below]].
    assert (Hbase :
      ~ Total.Termination.continuation_contains owner base).
    { pose proof (Total.Termination.reachable_control_ordered Hstart)
        as Hordered. cbn in Hordered.
      intro Hcontains.
      pose proof (@Total.Termination.continuation_contains_below
        (R.cfg_state start) owner base owner Hordered Hcontains) as Hfalse.
      pose proof (proj1 (@Total.rank_lt_true_ranked
        (R.cfg_state start) owner owner Hfalse)) as Hranked.
      rewrite (@Total.rank_lt_irrefl
        (R.cfg_state start) owner Hranked) in Hfalse.
      discriminate. }
    destruct (@Total.Termination.steps_to_episode_boundary
      owner base tf start
      {| R.cfg_state := done; R.cfg_control := R.Return base |}
      Hdone (or_introl (conj eq_refl eq_refl)))
      as [[exit [Hprefix Hexit]] |[Hprefix Hactive]].
    - inversion Hprefix as
        [|first next final Hcontains Hfirst_step Htail]; subst.
      + cbn in Hexit. discriminate.
      + set (started :=
          {| R.cfg_state := R.materialize (R.cfg_state start) owner;
             R.cfg_control :=
               R.RunRhs
                 (R.fresh_frame (R.materialize (R.cfg_state start) owner)
                   owner (U.initial_phase false owner))
                 (tf owner) base |}).
        assert (Hstarted_step : Sem.step tf start started).
        { unfold Sem.step, started. cbn -[R.materialize]. reflexivity. }
        assert (Hnext : next = started).
        { eapply Total.Termination.step_deterministic; eassumption. }
        subst next.
        assert (Hstarted_reachable :
          Sem.steps tf (R.initial_config roots) started).
        { eapply Total.Termination.steps_append_one; eassumption. }
        destruct (@Total.Termination.active_exit_is_boundary
          tf roots owner (R.cfg_state started)
          (R.fresh_frame (R.cfg_state started) owner
            (U.initial_phase false owner))
          (tf owner) base exit eq_refl Hstarted_reachable Htail Hexit)
          as [exit_st [Hexit_shape Hexit_below]].
        subst exit. exists exit_st. split.
        * econstructor; eassumption.
        * exact Hexit_below.
    - exfalso. apply Hbase.
      cbn in Hactive.
      eapply Total.Termination.continuation_above_contains.
      exact Hactive.
  Qed.

  Lemma first_discovery_lower_than_fresh_was_ranked :
    forall st target after variable,
      Total.rank_valid st ->
      Total.rank_valid after ->
      R.Ranking.lookup (R.ranking st) target = None ->
      Total.rank_extends (R.observe st target) after ->
      R.rank_lt after variable target = true ->
      Total.ranked st variable.
  Proof.
    intros st target after variable Hvalid Hvalid_after Hfresh
      Hextends Hlower.
    unfold R.observe in Hextends.
    destruct (R.Ranking.observe (R.ranking st) target)
      as [next target_rank] eqn:Hobserve.
    destruct (@FullRankLaws.observe_fresh
      (R.ranking st) target next target_rank Hfresh Hobserve)
      as [Htarget_rank _].
    assert (Htarget_after :
      R.Ranking.lookup (R.ranking after) target = Some target_rank).
    { apply Hextends. cbn. eapply RankLaws.observe_lookup; eassumption. }
    destruct (proj1 (@Total.rank_lt_true_ranked
      after variable target Hlower)) as [variable_rank Hvariable_after].
    assert (Hrank_lower : variable_rank < target_rank).
    { unfold R.rank_lt, R.ranking_lt in Hlower.
      rewrite Hvariable_after, Htarget_after in Hlower.
      now apply Nat.ltb_lt. }
    rewrite Htarget_rank in Hrank_lower.
    destruct (@FullRankLaws.ranks_dense
      (R.ranking st) variable_rank Hvalid Hrank_lower)
      as [old_variable Hold].
    assert (Hold_after :
      R.Ranking.lookup (R.ranking after) old_variable = Some variable_rank).
    { apply Hextends. cbn.
      eapply RankLaws.observe_preserves; eassumption. }
    assert (Heq : old_variable = variable).
    { eapply RankLaws.lookup_injective;
        [exact Hvalid_after |exact Hold_after |exact Hvariable_after]. }
    subst old_variable. now exists variable_rank.
  Qed.

  Lemma first_discovery_fresh_episode_lower_queue_was_ranked :
    forall tf roots before target k done queued,
      Sem.steps tf (R.initial_config roots) before ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) target = None ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) target;
           R.cfg_control := R.StartEpisode target k |} in
      Sem.steps tf (R.initial_config roots) start ->
      Sem.steps tf start
        {| R.cfg_state := done; R.cfg_control := R.Return k |} ->
      Total.Termination.queue_strictly_below target done ->
      List.In queued (R.queue done) ->
      Total.ranked (R.cfg_state before) queued.
  Proof.
    intros tf roots before target k done queued Hbefore Hfresh start
      Hstart Hrun Hbelow Hqueued.
    assert (Hdone : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := done; R.cfg_control := R.Return k |}).
    { eapply Total.Termination.steps_transitive; eassumption. }
    eapply first_discovery_lower_than_fresh_was_ranked.
    - exact (Total.configuration_rank_valid
        (Total.reachable_configuration_ranked Hbefore)).
    - exact (Total.configuration_rank_valid
        (Total.reachable_configuration_ranked Hdone)).
    - exact Hfresh.
    - exact (Total.Termination.steps_rank_extends Hrun).
    - exact (Hbelow queued Hqueued).
  Qed.

  Theorem first_discovery_fresh_episode_preserves_frontier :
    forall tf roots (finite : Sem.finite_system tf roots)
      before outer owner base,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      Total.ranked (R.cfg_state before) outer ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      Total.Termination.queue_strictly_below outer (R.cfg_state before) ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      exists final,
        Total.Termination.active_prefix owner tf start
          {| R.cfg_state := final; R.cfg_control := R.Return base |} /\
        Total.Termination.queue_strictly_below outer final.
  Proof.
    intros tf roots finite before outer owner base Hordinary Hbefore
      Houter Howner_fresh Hbelow start Hstart.
    destruct (@first_discovery_fresh_episode_active_completion
      tf roots finite before owner base Hbefore Howner_fresh Hstart)
      as [final [Hprefix Hchild_below]].
    exists final. split; [exact Hprefix |].
    pose proof (@first_discovery_episode_preserves_old_queue
      tf roots finite before owner base
      {| R.cfg_state := final; R.cfg_control := R.Return base |}
      Hordinary Hbefore Howner_fresh Hstart Hprefix) as Hold_queue.
    assert (Hextends : Total.rank_extends (R.cfg_state before) final).
    { eapply Total.rank_extends_trans.
      - eapply Total.rank_extends_observe. reflexivity.
      - exact (Total.Termination.steps_rank_extends
          (Total.Termination.active_prefix_steps Hprefix)). }
    intros queued Hin.
    assert (Hqueued_old : Total.ranked (R.cfg_state before) queued).
    { eapply (@first_discovery_fresh_episode_lower_queue_was_ranked
        tf roots before owner base final queued Hbefore Howner_fresh).
      - exact Hstart.
      - exact (Total.Termination.active_prefix_steps Hprefix).
      - exact Hchild_below.
      - exact Hin. }
    assert (Hqueued_start : List.In queued (R.queue (R.cfg_state start))).
    { eapply Hold_queue; eassumption. }
    assert (Hqueued_before : List.In queued (R.queue (R.cfg_state before))).
    { cbn in Hqueued_start. rewrite Total.Termination.observe_queue
        in Hqueued_start. exact Hqueued_start. }
    pose proof (Hbelow queued Hqueued_before) as Hlt.
    rewrite <- (@Total.rank_lt_stable
      (R.cfg_state before) final queued outer Hextends Hqueued_old Houter).
    exact Hlt.
  Qed.

  Lemma lower_active_episode_not_outer_commit :
    forall tf roots c outer owner base,
      Sem.steps tf (R.initial_config roots) c ->
      R.rank_lt (R.cfg_state c) outer owner = true ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control c) ->
      Total.Termination.owner_commitb outer c = false.
  Proof.
    intros tf roots [st control] outer owner base Hreachable Hlower Hactive.
    destruct control; try reflexivity; cbn in Hlower.
    unfold Total.Termination.owner_commitb. cbn.
    destruct (V.eq_dec (R.frame_owner f) outer) as [Hframe |Hframe];
      [|reflexivity].
    cbn in Hactive.
    destruct Hactive as [[Howner _] |Habove].
    - assert (owner = outer) by congruence. subst owner.
      rewrite Hframe in Hlower.
      pose proof (proj1 (@Total.rank_lt_true_ranked
        st outer outer Hlower)) as Hranked.
      rewrite (@Total.rank_lt_irrefl st outer Hranked) in Hlower.
      discriminate.
    - pose proof (Total.Termination.reachable_control_ordered Hreachable)
        as Hordered.
      cbn in Hordered.
      pose proof (@continuation_above_below st owner base
        (R.frame_owner f) c Habove Hordered) as Hhigher.
      rewrite Hframe in Hhigher.
      destruct (@Total.rank_lt_true_ranked st outer owner Hlower)
        as [Houter Howner_ranked].
      rewrite (@Total.rank_lt_asymmetric st outer owner
        Houter Howner_ranked Hlower) in Hhigher.
      discriminate.
  Qed.

  Inductive steps_before_owner_commit
    (owner : V.t) (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | StepsBeforeOwnerCommitRefl :
      forall c, steps_before_owner_commit owner tf c c
  | StepsBeforeOwnerCommitStep :
      forall first next final,
        Total.Termination.owner_commitb owner first = false ->
        Sem.step tf first next ->
        steps_before_owner_commit owner tf next final ->
        steps_before_owner_commit owner tf first final.

  Lemma steps_before_owner_commit_steps :
    forall owner tf first final,
      steps_before_owner_commit owner tf first final ->
      Sem.steps tf first final.
  Proof.
    intros owner tf first final Hsteps. induction Hsteps;
      [constructor |econstructor; eassumption].
  Qed.

  Lemma until_owner_commit_strip_prefix :
    forall owner tf first middle final,
      Total.Termination.until_owner_commit owner tf first final ->
      steps_before_owner_commit owner tf first middle ->
      Total.Termination.until_owner_commit owner tf middle final.
  Proof.
    intros owner tf first middle final Huntil Hprefix.
    revert final Huntil.
    induction Hprefix as
      [c |prefix_first prefix_next prefix_final
        Hnotcommit Hstep Hrest IH];
      intros destination Huntil; [exact Huntil |].
    destruct Huntil as
      [commit Hcommit
      |until_first until_next until_final
        Huntil_notcommit Huntil_step Huntil_rest].
    - rewrite Hnotcommit in Hcommit. discriminate.
    - assert (prefix_next = until_next) by
          (eapply Total.Termination.step_deterministic; eassumption).
      subst until_next. eapply IH. exact Huntil_rest.
  Qed.

  Lemma until_owner_commit_step_suffix :
    forall owner tf first next final,
      Total.Termination.until_owner_commit owner tf first final ->
      Total.Termination.owner_commitb owner first = false ->
      Sem.step tf first next ->
      Total.Termination.until_owner_commit owner tf next final.
  Proof.
    intros owner tf first next final Huntil Hnotcommit Hstep.
    destruct Huntil as
      [commit Hcommit
      |until_first until_next until_final
        Huntil_notcommit Huntil_step Huntil_rest].
    - rewrite Hnotcommit in Hcommit. discriminate.
    - assert (next = until_next) by
          (eapply Total.Termination.step_deterministic; eassumption).
      now subst until_next.
  Qed.

  Lemma active_prefix_from_episode_return_refl :
    forall owner base tf st final,
      ~ Total.Termination.continuation_contains owner base ->
      Total.Termination.active_prefix owner tf
        {| R.cfg_state := st; R.cfg_control := R.Return base |} final ->
      final = {| R.cfg_state := st; R.cfg_control := R.Return base |}.
  Proof.
    intros owner base tf st final Hbase Hprefix.
    inversion Hprefix; [reflexivity |].
    cbn in H. contradiction.
  Qed.

  Lemma lower_active_prefix_before_outer_commit :
    forall tf roots first final outer owner base,
      Sem.steps tf (R.initial_config roots) first ->
      R.rank_lt (R.cfg_state first) outer owner = true ->
      Total.Termination.episode_active_control owner base
        (R.cfg_control first) ->
      ~ Total.Termination.continuation_contains owner base ->
      Total.Termination.active_prefix owner tf first final ->
      R.cfg_control final = R.Return base ->
      steps_before_owner_commit outer tf first final.
  Proof.
    intros tf roots first final outer owner base Hreachable Hlower
      Hactive Hbase Hprefix Hfinal.
    revert Hreachable Hlower Hactive.
    induction Hprefix; intros Hreachable Hlower Hactive; [constructor |].
    econstructor.
    - eapply lower_active_episode_not_outer_commit; eassumption.
    - exact H0.
    - assert (Hnext_reachable : Sem.steps tf (R.initial_config roots) next)
        by (eapply Total.Termination.steps_append_one; eassumption).
      destruct (@Total.rank_lt_true_ranked
        (R.cfg_state first) outer owner Hlower) as [Houter Howner].
      assert (Hextends : Total.rank_extends
        (R.cfg_state first) (R.cfg_state next)).
      { eapply (@Total.Termination.steps_rank_extends tf first next).
        econstructor; [exact H0 |constructor]. }
      assert (Hlower_next :
        R.rank_lt (R.cfg_state next) outer owner = true).
      { rewrite <- (@Total.rank_lt_stable
          (R.cfg_state first) (R.cfg_state next) outer owner
          Hextends Houter Howner). exact Hlower. }
      destruct (@Total.Termination.episode_active_control_step
        tf first next owner base H0 Hactive) as [Hnext_active |Hreturn].
      + eapply IHHprefix; eassumption.
      + assert (Heq : next = final).
        { destruct next as [next_st next_control]. cbn in Hreturn. subst.
          symmetry. eapply active_prefix_from_episode_return_refl;
            eassumption. }
        subst final. constructor.
  Qed.

  Lemma reachable_start_episode_base_excludes :
    forall tf roots st owner base,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner base |} ->
      ~ Total.Termination.continuation_contains owner base.
  Proof.
    intros tf roots st owner base Hreachable Hcontains.
    pose proof (Total.Termination.reachable_control_ordered Hreachable)
      as Hordered.
    cbn in Hordered.
    pose proof (@Total.Termination.continuation_contains_below
      st owner base owner Hordered Hcontains) as Hfalse.
    pose proof (proj1 (@Total.rank_lt_true_ranked
      st owner owner Hfalse)) as Hranked.
    rewrite (@Total.rank_lt_irrefl st owner Hranked) in Hfalse.
    discriminate.
  Qed.

  Theorem first_discovery_fresh_episode_frontier_prefix :
    forall tf roots (finite : Sem.finite_system tf roots)
      before outer owner base,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      Total.ranked (R.cfg_state before) outer ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      Total.Termination.queue_strictly_below outer (R.cfg_state before) ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      exists final,
        Total.Termination.queue_strictly_below outer final /\
        steps_before_owner_commit outer tf start
          {| R.cfg_state := final; R.cfg_control := R.Return base |}.
  Proof.
    intros tf roots finite before outer owner base Hordinary Hbefore
      Houter Hfresh Hbelow start Hstart.
    destruct (@first_discovery_fresh_episode_preserves_frontier
      tf roots finite before outer owner base Hordinary Hbefore Houter
      Hfresh Hbelow Hstart) as [final [Hprefix Hfinal_below]].
    exists final. split; [exact Hfinal_below |].
    assert (Hlower : R.rank_lt (R.cfg_state start) outer owner = true).
    { unfold start. cbn. eapply fresh_observe_rank_lt.
      - apply first_discovery_fresh_ranks_above.
      - exact (Total.configuration_rank_valid
          (Total.reachable_configuration_ranked Hbefore)).
      - exact Houter.
      - exact Hfresh. }
    eapply lower_active_prefix_before_outer_commit.
    - exact Hstart.
    - exact Hlower.
    - unfold start. cbn. now left.
    - eapply reachable_start_episode_base_excludes. exact Hstart.
    - exact Hprefix.
    - reflexivity.
  Qed.

  Corollary first_discovery_fresh_episode_strip_until :
    forall tf roots (finite : Sem.finite_system tf roots)
      before outer owner base commit,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      Total.ranked (R.cfg_state before) outer ->
      R.Ranking.lookup (R.ranking (R.cfg_state before)) owner = None ->
      Total.Termination.queue_strictly_below outer (R.cfg_state before) ->
      let start :=
        {| R.cfg_state := R.observe (R.cfg_state before) owner;
           R.cfg_control := R.StartEpisode owner base |} in
      Sem.steps tf (R.initial_config roots) start ->
      Total.Termination.until_owner_commit outer tf start commit ->
      exists final,
        Total.Termination.queue_strictly_below outer final /\
        Total.Termination.until_owner_commit outer tf
          {| R.cfg_state := final; R.cfg_control := R.Return base |} commit.
  Proof.
    intros tf roots finite before outer owner base commit Hordinary Hbefore
      Houter Hfresh Hbelow start Hstart Huntil.
    destruct (@first_discovery_fresh_episode_frontier_prefix
      tf roots finite before outer owner base Hordinary Hbefore Houter
      Hfresh Hbelow Hstart) as [final [Hfinal_below Hprefix]].
    exists final. split; [exact Hfinal_below |].
    eapply until_owner_commit_strip_prefix; eassumption.
  Qed.

  Lemma return_after_get_restores_evaluation_frontier :
    forall support tf roots st fr target next base after owner,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.Return (R.KAfterGet fr target next base) |} ->
      R.frame_owner fr = owner ->
      Total.Termination.queue_strictly_below owner st ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.Return (R.KAfterGet fr target next base) |}
        after ->
      Total.Termination.evaluation_frontier support owner base after /\
      Total.Termination.queue_strictly_below owner (R.cfg_state after).
  Proof.
    intros support tf roots st fr target next base after owner Hreachable
      Howner Hbelow Hstep.
    pose proof (Total.reachable_configuration_ranked Hreachable) as Hranked.
    destruct Hranked as [_ _ Hcontrol _ _]. cbn in Hcontrol.
    destruct Hcontrol as [Hframe _].
    destruct (R.complete_get st fr target)
      as [[next_st next_fr] value] eqn:Hget.
    unfold Sem.step in Hstep. cbn -[R.complete_get] in Hstep.
    rewrite Hget in Hstep. inversion Hstep; subst. split.
    - apply Total.Termination.EvaluationRhs.
      rewrite (Total.complete_get_owner Hget). reflexivity.
    - eapply Total.Termination.queue_below_extended.
      + eapply Total.rank_extends_complete_get. exact Hget.
      + exact (proj1 Hframe).
      + eapply Total.Termination.complete_get_queue. exact Hget.
      + exact Hbelow.
  Qed.

  Lemma return_after_spawn_restores_evaluation_frontier :
    forall support tf st fr next base after owner,
      R.frame_owner fr = owner ->
      Total.Termination.queue_strictly_below owner st ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.Return (R.KAfterSpawn fr next base) |}
        after ->
      Total.Termination.evaluation_frontier support owner base after /\
      Total.Termination.queue_strictly_below owner (R.cfg_state after).
  Proof.
    intros support tf st fr next base after owner Howner Hbelow Hstep.
    unfold Sem.step in Hstep. cbn in Hstep. inversion Hstep; subst.
    split; [now apply Total.Termination.EvaluationRhs |exact Hbelow].
  Qed.

  Theorem first_discovery_fresh_get_resumes_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      st fr target next base owner commit,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) base |} ->
      R.frame_owner fr = owner ->
      R.Ranking.lookup (R.ranking st) target = None ->
      Total.Termination.queue_strictly_below owner st ->
      let start :=
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterGet fr target next base) |} in
      Sem.steps tf (R.initial_config roots) start ->
      Total.Termination.until_owner_commit owner tf start commit ->
      exists resumed,
        Sem.steps tf start resumed /\
        Sem.steps tf (R.initial_config roots) resumed /\
        Total.Termination.evaluation_frontier support owner base resumed /\
        Total.Termination.queue_strictly_below owner (R.cfg_state resumed) /\
        (forall target k,
          R.cfg_control resumed <> R.StartEpisode target k) /\
        Total.Termination.until_owner_commit owner tf resumed commit.
  Proof.
    intros support tf roots finite st fr target next base owner commit
      Hordinary Hbefore Howner Hfresh Hbelow start Hstart Huntil.
    pose proof (Total.reachable_configuration_ranked Hbefore) as Hranked.
    assert (Howner_ranked : Total.ranked st owner).
    { eapply (@Total.Termination.evaluation_frontier_owner_ranked
        support owner base
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) base |}).
      - exact Hranked.
      - now apply Total.Termination.EvaluationRhs. }
    destruct (@first_discovery_fresh_episode_frontier_prefix
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control :=
           R.RunRhs fr (R.ConstraintSystem.Get target next) base |}
      owner target (R.KAfterGet fr target next base)
      Hordinary Hbefore Howner_ranked Hfresh Hbelow Hstart)
      as [final [Hfinal_below Hprefix]].
    assert (Hreturn_reachable : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := final;
         R.cfg_control := R.Return (R.KAfterGet fr target next base) |}).
    { eapply Total.Termination.steps_transitive; [exact Hstart |].
      now apply steps_before_owner_commit_steps in Hprefix. }
    assert (Hreturn_until : Total.Termination.until_owner_commit owner tf
      {| R.cfg_state := final;
         R.cfg_control := R.Return (R.KAfterGet fr target next base) |}
      commit).
    { eapply until_owner_commit_strip_prefix; eassumption. }
    destruct (R.complete_get final fr target)
      as [[next_st next_fr] value] eqn:Hget.
    set (resumed :=
      {| R.cfg_state := next_st;
         R.cfg_control := R.RunRhs next_fr (next value) base |}).
    assert (Hreturn_step : Sem.step tf
      {| R.cfg_state := final;
         R.cfg_control := R.Return (R.KAfterGet fr target next base) |}
      resumed).
    { unfold Sem.step, resumed. cbn -[R.complete_get]. now rewrite Hget. }
    destruct (@return_after_get_restores_evaluation_frontier support tf roots
      final fr target next base resumed owner Hreturn_reachable Howner
      Hfinal_below Hreturn_step) as [Hfrontier Hresumed_below].
    exists resumed. repeat split.
    - eapply Total.Termination.steps_append_one with (middle :=
        {| R.cfg_state := final;
           R.cfg_control := R.Return (R.KAfterGet fr target next base) |}).
      + unfold start. cbn.
        now apply steps_before_owner_commit_steps in Hprefix.
      + exact Hreturn_step.
    - eapply Total.Termination.steps_append_one; eassumption.
    - exact Hfrontier.
    - exact Hresumed_below.
    - intros resumed_target resumed_base. unfold resumed. discriminate.
    - eapply until_owner_commit_step_suffix; [exact Hreturn_until |reflexivity
        |exact Hreturn_step].
  Qed.

  Theorem first_discovery_fresh_spawn_resumes_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      st fr target next base owner commit,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) base |} ->
      R.frame_owner fr = owner ->
      R.Ranking.lookup (R.ranking st) target = None ->
      Total.Termination.queue_strictly_below owner st ->
      let start :=
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterSpawn fr next base) |} in
      Sem.steps tf (R.initial_config roots) start ->
      Total.Termination.until_owner_commit owner tf start commit ->
      exists resumed,
        Sem.steps tf start resumed /\
        Sem.steps tf (R.initial_config roots) resumed /\
        Total.Termination.evaluation_frontier support owner base resumed /\
        Total.Termination.queue_strictly_below owner (R.cfg_state resumed) /\
        (forall target k,
          R.cfg_control resumed <> R.StartEpisode target k) /\
        Total.Termination.until_owner_commit owner tf resumed commit.
  Proof.
    intros support tf roots finite st fr target next base owner commit
      Hordinary Hbefore Howner Hfresh Hbelow start Hstart Huntil.
    pose proof (Total.reachable_configuration_ranked Hbefore) as Hranked.
    assert (Howner_ranked : Total.ranked st owner).
    { eapply (@Total.Termination.evaluation_frontier_owner_ranked
        support owner base
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) base |}).
      - exact Hranked.
      - now apply Total.Termination.EvaluationRhs. }
    destruct (@first_discovery_fresh_episode_frontier_prefix
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control :=
           R.RunRhs fr (R.ConstraintSystem.Spawn target next) base |}
      owner target (R.KAfterSpawn fr next base)
      Hordinary Hbefore Howner_ranked Hfresh Hbelow Hstart)
      as [final [Hfinal_below Hprefix]].
    set (returned :=
      {| R.cfg_state := final;
         R.cfg_control := R.Return (R.KAfterSpawn fr next base) |}).
    assert (Hreturn_reachable : Sem.steps tf (R.initial_config roots) returned).
    { eapply Total.Termination.steps_transitive; [exact Hstart |].
      unfold returned. now apply steps_before_owner_commit_steps in Hprefix. }
    assert (Hreturn_until :
      Total.Termination.until_owner_commit owner tf returned commit).
    { unfold returned. eapply until_owner_commit_strip_prefix; eassumption. }
    set (resumed :=
      {| R.cfg_state := final; R.cfg_control := R.RunRhs fr next base |}).
    assert (Hreturn_step : Sem.step tf returned resumed).
    { unfold Sem.step, returned, resumed. reflexivity. }
    destruct (@return_after_spawn_restores_evaluation_frontier support tf
      final fr next base resumed owner Howner Hfinal_below Hreturn_step)
      as [Hfrontier Hresumed_below].
    exists resumed. repeat split.
    - eapply Total.Termination.steps_append_one with (middle := returned).
      + unfold returned in Hprefix.
        unfold start. cbn.
        now apply steps_before_owner_commit_steps in Hprefix.
      + exact Hreturn_step.
    - eapply Total.Termination.steps_append_one; eassumption.
    - exact Hfrontier.
    - exact Hresumed_below.
    - intros resumed_target resumed_base. unfold resumed. discriminate.
    - eapply until_owner_commit_step_suffix; [exact Hreturn_until |reflexivity
        |exact Hreturn_step].
  Qed.

  Lemma fresh_episode_resume_decreases :
    forall support tf st target episode_base resumed,
      NoDup support ->
      List.In target support ->
      R.is_materialized (R.observe st target) target = false ->
      Sem.steps tf
        {| R.cfg_state := R.observe st target;
           R.cfg_control := R.StartEpisode target episode_base |}
        resumed ->
      R.cfg_control resumed <> R.StartEpisode target episode_base ->
      Total.Termination.unmaterialized_count support (R.cfg_state resumed) <
        Total.Termination.unmaterialized_count support st.
  Proof.
    intros support tf st target episode_base resumed Hnodup Hin
      Hfresh Hsteps Hresumed.
    inversion Hsteps as
      [|first next final Hstep Htail]; subst.
    - exfalso. apply Hresumed. reflexivity.
    - unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
      inversion Hstep; subst.
      pose proof (@Total.Termination.unmaterialized_count_materialize_decreases
        support (R.observe st target) target Hnodup Hin Hfresh) as Hdecrease.
      pose proof (@Total.Termination.unmaterialized_count_steps_nonincreasing
        support tf
        {| R.cfg_state := R.materialize (R.observe st target) target;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize (R.observe st target) target)
                 target (U.initial_phase false target))
               (tf target) episode_base |}
        resumed Htail) as Hrest.
      pose proof (@Total.Termination.unmaterialized_count_sigma_ext
        support st (R.observe st target)
        (Total.Termination.observe_sigma st target))
        as Hobserve.
      cbn in Hrest. lia.
  Qed.

  Lemma first_discovery_observed_unmaterialized_was_unranked :
    forall tf roots (finite : Sem.finite_system tf roots) st control target,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := control |} ->
      (forall k, control <> R.StartEpisode target k) ->
      R.is_materialized (R.observe st target) target = false ->
      R.Ranking.lookup (R.ranking st) target = None.
  Proof.
    intros tf roots finite st control target Hordinary Hreachable
      Hnotstart Hfresh.
    destruct (R.Ranking.lookup (R.ranking st) target)
      as [rank |] eqn:Hlookup; [|reflexivity].
    assert (Hranked : Total.ranked st target) by (now exists rank).
    pose proof (@first_discovery_reachable_nonstart_ranked_materialized
      tf roots finite st control target Hordinary Hreachable Hnotstart
      Hranked) as Hmaterialized.
    unfold R.observe in Hfresh.
    destruct (R.Ranking.observe (R.ranking st) target).
    unfold R.is_materialized in Hfresh, Hmaterialized.
    cbn in Hfresh. rewrite Hmaterialized in Hfresh. discriminate.
  Qed.

  Inductive running_evaluation
    (owner : V.t) (base : R.continuation) : R.config -> Prop :=
  | RunningEvaluationRhs :
      forall st fr body,
        R.frame_owner fr = owner ->
        running_evaluation owner base
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body base |}
  | RunningEvaluationDead :
      forall st fr direct pending,
        R.frame_owner fr = owner ->
        running_evaluation owner base
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct pending base |}
  | RunningEvaluationCommit :
      forall st fr direct,
        R.frame_owner fr = owner ->
        running_evaluation owner base
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit fr direct base |}.

  Lemma running_evaluation_frontier :
    forall support owner base c,
      running_evaluation owner base c ->
      Total.Termination.evaluation_frontier support owner base c.
  Proof.
    intros support owner base c Hrunning. destruct Hrunning.
    - now apply Total.Termination.EvaluationRhs.
    - now apply Total.Termination.EvaluationDead.
    - now apply Total.Termination.EvaluationCommit.
  Qed.

  Lemma frontier_nonstart_running :
    forall support owner base c,
      Total.Termination.evaluation_frontier support owner base c ->
      (forall target k, R.cfg_control c <> R.StartEpisode target k) ->
      running_evaluation owner base c.
  Proof.
    intros support owner base c Hfrontier Hnonstart.
    destruct Hfrontier.
    - now apply RunningEvaluationRhs.
    - now apply RunningEvaluationDead.
    - now apply RunningEvaluationCommit.
    - exfalso. eapply (Hnonstart target
        (R.KAfterGet fr target next base)). reflexivity.
    - exfalso. eapply (Hnonstart target
        (R.KAfterSide fr next base)). reflexivity.
    - exfalso. eapply (Hnonstart target
        (R.KAfterSpawn fr next base)). reflexivity.
    - exfalso. eapply (Hnonstart target
        (R.KDead fr direct pending base)). reflexivity.
  Qed.

  Theorem first_discovery_running_frontier_queue_below :
    forall support tf roots (finite : Sem.finite_system tf roots) owner base,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      forall first final,
        Sem.steps tf (R.initial_config roots) first ->
        running_evaluation owner base first ->
        Total.Termination.until_owner_commit owner tf first final ->
        Total.Termination.queue_strictly_below owner (R.cfg_state first) ->
        Total.Termination.queue_strictly_below owner (R.cfg_state final).
  Proof.
    intros support tf roots finite owner base Hsupport Hordinary.
    subst support.
    assert (Hall : forall count first final,
      count = Total.Termination.unmaterialized_count (Sem.support finite)
        (R.cfg_state first) ->
      Sem.steps tf (R.initial_config roots) first ->
      running_evaluation owner base first ->
      Total.Termination.until_owner_commit owner tf first final ->
      Total.Termination.queue_strictly_below owner (R.cfg_state first) ->
      Total.Termination.queue_strictly_below owner (R.cfg_state final)).
    { refine (well_founded_induction_type Nat.lt_wf_0
        (fun count => forall first final,
          count = Total.Termination.unmaterialized_count (Sem.support finite)
            (R.cfg_state first) ->
          Sem.steps tf (R.initial_config roots) first ->
          running_evaluation owner base first ->
          Total.Termination.until_owner_commit owner tf first final ->
          Total.Termination.queue_strictly_below owner (R.cfg_state first) ->
          Total.Termination.queue_strictly_below owner (R.cfg_state final)) _).
      intros count IH first final Hcount Hreachable Hrunning Huntil Hbelow.
    revert Hcount Hreachable Hrunning Hbelow.
    induction Huntil as
      [commit Hcommit
      |first next final Hnotcommit Hstep Huntil IHuntil];
      intros Hcount Hreachable Hrunning Hbelow; [exact Hbelow |].
    destruct Hrunning as
      [st fr body Howner |st fr direct pending Howner
      |st fr direct Howner].
    - destruct body as [value |target continuation |target raw continuation
        |target continuation].
      + unfold Sem.step in Hstep. cbn in Hstep. inversion Hstep; subst.
        eapply IHuntil; try eassumption.
        * reflexivity.
        * eapply Total.Termination.steps_append_one; eassumption.
        * now apply RunningEvaluationDead.
      + pose proof Hstep as Hsemantic.
        unfold Sem.step in Hstep.
        cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool
          eqn:Hnested.
        * apply Bool.andb_true_iff in Hnested.
          destruct Hnested as [Hfresh _].
          apply Bool.negb_true_iff in Hfresh.
          assert (Hlookup :
            R.Ranking.lookup (R.ranking st) target = None).
          { eapply (@first_discovery_observed_unmaterialized_was_unranked
              tf roots finite st
              (R.RunRhs fr (R.ConstraintSystem.Get target continuation) base)
              target).
            - exact Hordinary.
            - exact Hreachable.
            - intros k Hfalse. discriminate Hfalse.
            - exact Hfresh. }
          inversion Hstep; subst next.
          assert (Hstart_reachable : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := observed;
               R.cfg_control :=
                 R.StartEpisode target
                   (R.KAfterGet fr target continuation base) |}).
          { eapply Total.Termination.steps_append_one; eassumption. }
          cbn in Hbelow.
          destruct (@first_discovery_fresh_get_resumes_frontier
            (Sem.support finite) tf roots finite st fr target continuation
            base owner final Hordinary Hreachable Howner
            Hlookup Hbelow Hstart_reachable Huntil)
            as [resumed [Hrun [Hresumed_reachable
              [Hfrontier [Hresumed_below [Hnonstart Hresumed_until]]]]]].
          assert (Hresumed_running :
            running_evaluation owner base resumed).
          { eapply frontier_nonstart_running; eassumption. }
          pose proof (Total.reachable_config_supported finite Hreachable)
            as [_ Hsupported].
          cbn in Hsupported.
          pose proof (proj1 (Total.rhs_supported_get_inv
            (proj1 (proj2 Hsupported)))) as Htarget.
          assert (Hdecrease :
            Total.Termination.unmaterialized_count (Sem.support finite)
              (R.cfg_state resumed) <
            Total.Termination.unmaterialized_count (Sem.support finite) st).
          { eapply fresh_episode_resume_decreases.
            - apply Sem.support_nodup.
            - exact Htarget.
            - exact Hfresh.
            - exact Hrun.
            - apply Hnonstart. }
          assert (Hdecrease_count :
            Total.Termination.unmaterialized_count (Sem.support finite)
              (R.cfg_state resumed) < count).
          { rewrite Hcount. exact Hdecrease. }
          eapply (IH _ Hdecrease_count resumed final eq_refl
            Hresumed_reachable Hresumed_running Hresumed_until
            Hresumed_below).
        * assert (Howner_ranked : Total.ranked st owner).
          { eapply (@Total.Termination.evaluation_frontier_owner_ranked
              (Sem.support finite) owner base
              {| R.cfg_state := st;
                 R.cfg_control :=
                   R.RunRhs fr
                     (R.ConstraintSystem.Get target continuation) base |}).
            - exact (Total.reachable_configuration_ranked Hreachable).
            - now apply Total.Termination.EvaluationRhs. }
          assert (Hbelow_observed :
            Total.Termination.queue_strictly_below owner observed).
          { subst observed. eapply Total.Termination.observe_queue_strictly_below;
              [exact Howner_ranked |]. cbn in Hbelow. exact Hbelow. }
          destruct (R.is_materialized observed target)
            eqn:Hmaterialized.
          2: {
            assert (Hlookup :
              R.Ranking.lookup (R.ranking st) target = None).
            { eapply (@first_discovery_observed_unmaterialized_was_unranked
                tf roots finite st
                (R.RunRhs fr
                  (R.ConstraintSystem.Get target continuation) base) target).
              - exact Hordinary.
              - exact Hreachable.
              - intros k Hfalse. discriminate Hfalse.
              - exact Hmaterialized. }
            assert (Hhigher : R.rank_lt observed owner target = true).
            { subst observed. eapply fresh_observe_rank_lt.
              - apply first_discovery_fresh_ranks_above.
              - exact (Total.configuration_rank_valid
                  (Total.reachable_configuration_ranked Hreachable)).
              - exact Howner_ranked.
              - exact Hlookup. }
            rewrite <- Howner in Hhigher.
            rewrite Hhigher in Hnested. discriminate. }
          destruct (R.complete_get observed fr target)
            as [[next_st next_fr] value] eqn:Hget.
          inversion Hstep; subst next.
          assert (Hnext_reachable : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := next_st;
               R.cfg_control :=
                 R.RunRhs next_fr (continuation value) base |}).
          { eapply Total.Termination.steps_append_one; eassumption. }
          assert (Hnext_running : running_evaluation owner base
            {| R.cfg_state := next_st;
               R.cfg_control :=
                 R.RunRhs next_fr (continuation value) base |}).
          { apply RunningEvaluationRhs.
            rewrite (Total.complete_get_owner Hget). exact Howner. }
          assert (Hnext_below :
            Total.Termination.queue_strictly_below owner next_st).
          { eapply Total.Termination.queue_below_extended.
            - eapply Total.rank_extends_complete_get. exact Hget.
            - eapply Total.ranked_extended.
              + eapply Total.rank_extends_observe. reflexivity.
              + exact Howner_ranked.
            - eapply Total.Termination.complete_get_queue. exact Hget.
            - exact Hbelow_observed. }
          destruct (@complete_get_solved_view observed fr target
            next_st next_fr value
            (@Total.materialized_solved observed target Hmaterialized)
            Hget) as [Hsigma _].
          pose proof (@Total.Termination.unmaterialized_count_sigma_ext
            (Sem.support finite) observed next_st Hsigma) as Hget_count.
          pose proof (@Total.Termination.unmaterialized_count_sigma_ext
            (Sem.support finite) st observed
            (Total.Termination.observe_sigma st target)) as Hobserve_count.
          eapply IHuntil.
          -- cbn. rewrite Hget_count, Hobserve_count. exact Hcount.
          -- exact Hnext_reachable.
          -- exact Hnext_running.
          -- exact Hnext_below.
      + exfalso. eapply ordinary_reachable_side_impossible; eassumption.
      + pose proof Hstep as Hsemantic.
        unfold Sem.step in Hstep.
        cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        assert (Howner_ranked : Total.ranked st owner).
        { eapply (@Total.Termination.evaluation_frontier_owner_ranked
            (Sem.support finite) owner base
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.RunRhs fr
                   (R.ConstraintSystem.Spawn target continuation) base |}).
          - exact (Total.reachable_configuration_ranked Hreachable).
          - now apply Total.Termination.EvaluationRhs. }
        assert (Hbelow_observed :
          Total.Termination.queue_strictly_below owner observed).
        { subst observed. eapply Total.Termination.observe_queue_strictly_below;
            [exact Howner_ranked |]. cbn in Hbelow. exact Hbelow. }
        destruct (R.is_materialized observed target)
          eqn:Hmaterialized.
        * inversion Hstep; subst next.
          eapply IHuntil.
          -- pose proof (@Total.Termination.unmaterialized_count_sigma_ext
               (Sem.support finite) st observed
               (Total.Termination.observe_sigma st target)) as Hobserve_count.
             cbn. rewrite Hobserve_count. exact Hcount.
          -- eapply Total.Termination.steps_append_one; eassumption.
          -- now apply RunningEvaluationRhs.
          -- exact Hbelow_observed.
        * assert (Hlookup :
            R.Ranking.lookup (R.ranking st) target = None).
          { eapply (@first_discovery_observed_unmaterialized_was_unranked
              tf roots finite st
              (R.RunRhs fr
                (R.ConstraintSystem.Spawn target continuation) base) target).
            - exact Hordinary.
            - exact Hreachable.
            - intros k Hfalse. discriminate Hfalse.
            - exact Hmaterialized. }
          assert (Hhigher : R.rank_lt observed owner target = true).
          { subst observed. eapply fresh_observe_rank_lt.
            - apply first_discovery_fresh_ranks_above.
            - exact (Total.configuration_rank_valid
                (Total.reachable_configuration_ranked Hreachable)).
            - exact Howner_ranked.
            - exact Hlookup. }
          destruct (R.rank_lt observed (R.frame_owner fr) target)
            eqn:Hrank.
          2: { rewrite <- Howner in Hhigher.
            rewrite Hrank in Hhigher. discriminate. }
          inversion Hstep; subst next.
          assert (Hstart_reachable : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := observed;
               R.cfg_control :=
                 R.StartEpisode target
                   (R.KAfterSpawn fr continuation base) |}).
          { eapply Total.Termination.steps_append_one; eassumption. }
          cbn in Hbelow.
          destruct (@first_discovery_fresh_spawn_resumes_frontier
            (Sem.support finite) tf roots finite st fr target continuation
            base owner final Hordinary Hreachable Howner Hlookup Hbelow
            Hstart_reachable Huntil)
            as [resumed [Hrun [Hresumed_reachable
              [Hfrontier [Hresumed_below [Hnonstart Hresumed_until]]]]]].
          assert (Hresumed_running : running_evaluation owner base resumed).
          { eapply frontier_nonstart_running; eassumption. }
          pose proof (Total.reachable_config_supported finite Hreachable)
            as [_ Hsupported].
          cbn in Hsupported.
          pose proof (proj1 (Total.rhs_supported_spawn_inv
            (proj1 (proj2 Hsupported)))) as Htarget.
          assert (Hdecrease :
            Total.Termination.unmaterialized_count (Sem.support finite)
              (R.cfg_state resumed) <
            Total.Termination.unmaterialized_count (Sem.support finite) st).
          { eapply fresh_episode_resume_decreases.
            - apply Sem.support_nodup.
            - exact Htarget.
            - exact Hmaterialized.
            - exact Hrun.
            - apply Hnonstart. }
          assert (Hdecrease_count :
            Total.Termination.unmaterialized_count (Sem.support finite)
              (R.cfg_state resumed) < count).
          { rewrite Hcount. exact Hdecrease. }
          eapply (IH _ Hdecrease_count resumed final eq_refl
            Hresumed_reachable Hresumed_running Hresumed_until
            Hresumed_below).
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending base |}
        Hreachable) as [_ Hclean].
      cbn in Hclean. destruct Hclean as [_ [-> _]].
      unfold Sem.step in Hstep. cbn -[R.publish_targets] in Hstep.
      inversion Hstep; subst.
      eapply IHuntil; try eassumption.
      + pose proof (@Total.Termination.unmaterialized_count_sigma_ext
          (Sem.support finite) st (R.publish_targets st fr)
          (Total.Termination.publish_targets_sigma st fr)) as Hsame.
        cbn. lia.
      + eapply Total.Termination.steps_append_one; eassumption.
      + now apply RunningEvaluationCommit.
    - unfold Total.Termination.owner_commitb in Hnotcommit.
      cbn in Hnotcommit. rewrite Howner in Hnotcommit.
      destruct (V.eq_dec owner owner); [discriminate |contradiction]. }
    intros first final Hreachable Hrunning Huntil Hbelow.
    eapply (Hall (Total.Termination.unmaterialized_count
      (Sem.support finite) (R.cfg_state first)) first final);
      [reflexivity |eassumption..].
  Qed.

  Theorem first_discovery_episode_first_commit_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner base st commit,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} ->
      Total.Termination.queue_strictly_below owner st ->
      let started :=
        {| R.cfg_state := R.materialize st owner;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize st owner) owner
                 (U.initial_phase false owner))
               (tf owner) base |} in
      Total.Termination.until_owner_commit owner tf started commit ->
      Total.Termination.queue_strictly_below owner (R.cfg_state commit).
  Proof.
    intros support tf roots finite owner base st commit Hsupport Hordinary
      Hstart Hbelow started Huntil.
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner base |}
      started).
    { unfold Sem.step, started. cbn -[R.materialize]. reflexivity. }
    assert (Hstarted : Sem.steps tf (R.initial_config roots) started).
    { eapply Total.Termination.steps_append_one; eassumption. }
    assert (Hrunning : running_evaluation owner base started).
    { unfold started. apply RunningEvaluationRhs. reflexivity. }
    assert (Hbelow_started : Total.Termination.queue_strictly_below owner
      (R.cfg_state started)).
    { unfold started. cbn. intros queued Hin.
      unfold R.materialize in Hin |- *.
      destruct (M.lookup (R.sigma st) owner); exact (Hbelow queued Hin). }
    eapply (@first_discovery_running_frontier_queue_below
      support tf roots finite owner base Hsupport Hordinary started commit);
      eassumption.
  Qed.

  Theorem first_discovery_rerun_first_commit_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner base st fr tail commit,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      R.frame_owner fr = owner ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDrain fr base |} ->
      R.queue_pop (R.queue st) = Some (owner, tail) ->
      let rerun := Total.Termination.executed_rerun
        tf owner base st fr tail in
      Total.Termination.until_owner_commit owner tf rerun commit ->
      Total.Termination.queue_strictly_below owner
        (R.cfg_state commit).
  Proof.
    intros support tf roots finite owner base st fr tail commit
      Hsupport Hordinary Howner Hdrain Hpop rerun Huntil.
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st;
         R.cfg_control := R.RunDrain fr base |} rerun).
    { unfold rerun.
      eapply Total.Termination.executed_rerun_step; eassumption. }
    assert (Hreachable : Sem.steps tf (R.initial_config roots) rerun).
    { eapply Total.Termination.steps_append_one; eassumption. }
    assert (Hrunning : running_evaluation owner base rerun).
    { unfold rerun, Total.Termination.executed_rerun. cbn.
      apply RunningEvaluationRhs. reflexivity. }
    assert (Hbelow : Total.Termination.queue_strictly_below owner
      (R.cfg_state rerun)).
    { unfold rerun, Total.Termination.executed_rerun. cbn.
      eapply Total.Termination.with_queue_strictly_below.
      - exact (Total.configuration_queue_ordered
          (Total.reachable_configuration_ranked Hdrain)).
      - exact Hpop. }
    eapply (@first_discovery_running_frontier_queue_below
      support tf roots finite owner base Hsupport Hordinary rerun commit);
      eassumption.
  Qed.

  Lemma first_discovery_start_episode_step_queue_below :
    forall tf roots (finite : Sem.finite_system tf roots)
      before st owner base,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      Sem.step tf before
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} ->
      Total.Termination.queue_strictly_below owner st.
  Proof.
    intros tf roots finite [before control] st owner base
      Hordinary Hreachable Hstep.
    pose proof (Total.reachable_configuration_ranked Hreachable)
      as Hranked.
    pose proof (Total.configuration_queue_ordered Hranked) as Hordered.
    unfold Sem.step in Hstep. destruct control as
      [|seed_roots |remaining |current k |fr body k
       |fr direct pending k |fr direct k |fr k |k].
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue before))
        as [[head tail] |] eqn:Hpop; try discriminate.
      inversion Hstep; subst.
      now apply Total.Termination.with_queue_strictly_below.
    - destruct seed_roots as [|root remaining_roots]; cbn in Hstep;
        try discriminate.
      set (observed := R.observe before root) in *.
      destruct (R.is_materialized observed root) eqn:Hfresh;
        try discriminate.
      inversion Hstep; subst.
      assert (Hunranked :
        R.Ranking.lookup (R.ranking before) owner = None).
      { eapply (@first_discovery_observed_unmaterialized_was_unranked
          tf roots finite before (R.RunSeeds (owner :: remaining_roots))
          owner Hordinary Hreachable).
        - intros rest Hfalse. discriminate Hfalse.
        - exact Hfresh. }
      subst observed.
      exact (@reachable_fresh_observe_queue_below tf roots
        {| R.cfg_state := before;
           R.cfg_control := R.RunSeeds (owner :: remaining_roots) |}
        owner first_discovery_fresh_ranks_above Hreachable Hunranked).
    - cbn in Hstep.
      destruct (R.queue_pop (R.queue before))
        as [[head tail] |] eqn:Hpop; try discriminate.
      inversion Hstep; subst.
      now apply Total.Termination.with_queue_strictly_below.
    - cbn -[R.materialize] in Hstep. discriminate.
    - destruct body as [value |target next |target raw next |target next].
      + cbn in Hstep. discriminate.
      + cbn -[R.observe R.complete_get] in Hstep.
        set (observed := R.observe before target) in *.
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool
          eqn:Hstarts; try discriminate.
        inversion Hstep; subst.
        apply Bool.andb_true_iff in Hstarts.
        destruct Hstarts as [Hfresh _].
        apply Bool.negb_true_iff in Hfresh.
        assert (Hunranked :
          R.Ranking.lookup (R.ranking before) owner = None).
        { eapply (@first_discovery_observed_unmaterialized_was_unranked
            tf roots finite before
            (R.RunRhs fr (R.ConstraintSystem.Get owner next) k)
            owner Hordinary Hreachable).
          - intros rest Hfalse. discriminate Hfalse.
          - exact Hfresh. }
        subst observed.
        exact (@reachable_fresh_observe_queue_below tf roots
          {| R.cfg_state := before;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Get owner next) k |}
          owner first_discovery_fresh_ranks_above Hreachable Hunranked).
      + exfalso. eapply ordinary_reachable_side_impossible; eassumption.
      + cbn -[R.observe R.materialize] in Hstep.
        set (observed := R.observe before target) in *.
        destruct (R.is_materialized observed target) eqn:Hfresh;
          try discriminate.
        destruct (R.rank_lt observed (R.frame_owner fr) target);
          try discriminate.
        inversion Hstep; subst.
        assert (Hunranked :
          R.Ranking.lookup (R.ranking before) owner = None).
        { eapply (@first_discovery_observed_unmaterialized_was_unranked
            tf roots finite before
            (R.RunRhs fr (R.ConstraintSystem.Spawn owner next) k)
            owner Hordinary Hreachable).
          - intros rest Hfalse. discriminate Hfalse.
          - exact Hfresh. }
        subst observed.
        exact (@reachable_fresh_observe_queue_below tf roots
          {| R.cfg_state := before;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Spawn owner next) k |}
          owner first_discovery_fresh_ranks_above Hreachable Hunranked).
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := before;
           R.cfg_control := R.RunDead fr direct pending k |}
        Hreachable) as [_ Hclean].
      cbn in Hclean. destruct Hclean as [_ [-> _]].
      cbn -[R.publish_targets] in Hstep. discriminate.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value before fr direct). discriminate.
    - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue before)) as [next |] eqn:Hpeek;
        try discriminate.
      destruct (V.eq_dec next (R.frame_owner fr));
        [destruct (R.queue_pop (R.queue before)) as [[head tail] |]
           eqn:Hpop; discriminate |].
      destruct (R.rank_lt before (R.frame_owner fr) next);
        [|discriminate].
      destruct (R.queue_pop (R.queue before))
        as [[head tail] |] eqn:Hpop; try discriminate.
      inversion Hstep; subst.
      assert (Heq : owner = head).
      { eapply Total.queue_peek_pop_same; eassumption. }
      subst head.
      now apply Total.Termination.with_queue_strictly_below.
    - destruct k; cbn -[R.complete_get] in Hstep; discriminate.
  Qed.

  Lemma steps_last :
    forall tf first final,
      Sem.steps tf first final ->
      first = final \/
      exists before,
        Sem.steps tf first before /\
        Sem.step tf before final.
  Proof.
    intros tf first final Hsteps. induction Hsteps.
    - now left.
    - destruct IHHsteps as [-> |[before [Hbefore Hlast]]].
      + right. exists first. split; [constructor |exact H].
      + right. exists before. split.
        * econstructor; eassumption.
        * exact Hlast.
  Qed.

  Theorem first_discovery_reachable_start_episode_queue_below :
    forall tf roots (finite : Sem.finite_system tf roots)
      st owner base,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} ->
      Total.Termination.queue_strictly_below owner st.
  Proof.
    intros tf roots finite st owner base Hordinary Hreachable.
    destruct (@steps_last tf (R.initial_config roots)
      {| R.cfg_state := st;
         R.cfg_control := R.StartEpisode owner base |} Hreachable)
      as [Heq |[before [Hbefore Hstep]]].
    - unfold R.initial_config in Heq. discriminate.
    - eapply (@first_discovery_start_episode_step_queue_below
        tf roots finite before st owner base); eassumption.
  Qed.

  Theorem first_discovery_reachable_episode_first_commit_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner base st commit,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} ->
      let started :=
        {| R.cfg_state := R.materialize st owner;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize st owner) owner
                 (U.initial_phase false owner))
               (tf owner) base |} in
      Total.Termination.until_owner_commit owner tf started commit ->
      Total.Termination.queue_strictly_below owner
        (R.cfg_state commit).
  Proof.
    intros support tf roots finite owner base st commit Hsupport Hordinary
      Hreachable started Huntil.
    eapply (@first_discovery_episode_first_commit_frontier
      support tf roots finite owner base st commit Hsupport Hordinary
      Hreachable).
    - eapply first_discovery_reachable_start_episode_queue_below;
        eassumption.
    - exact Huntil.
  Qed.

  Inductive first_discovery_round_entry
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (owner : V.t) (base : R.continuation) : R.config -> Prop :=
  | RoundEntryEpisode :
      forall st,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.StartEpisode owner base |} ->
        first_discovery_round_entry tf roots owner base
          {| R.cfg_state := R.materialize st owner;
             R.cfg_control :=
               R.RunRhs
                 (R.fresh_frame (R.materialize st owner) owner
                   (U.initial_phase false owner))
                 (tf owner) base |}
  | RoundEntryRerun :
      forall st fr tail,
        R.frame_owner fr = owner ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunDrain fr base |} ->
        R.queue_pop (R.queue st) = Some (owner, tail) ->
        first_discovery_round_entry tf roots owner base
          (Total.Termination.executed_rerun
            tf owner base st fr tail).

  Definition frame_round_origin
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (current : R.config) (fr : R.frame) (base : R.continuation) : Prop :=
    exists entry,
      first_discovery_round_entry tf roots
        (R.frame_owner fr) base entry /\
      steps_before_owner_commit (R.frame_owner fr) tf entry current.

  Fixpoint continuation_round_origins
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (current : R.config) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr _ _ rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDead fr _ _ rest =>
        frame_round_origin tf roots current fr rest /\
        continuation_round_origins tf roots current rest
    | R.KDrain _ rest =>
        continuation_round_origins tf roots current rest
    end.

  Definition control_round_origins
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (current : R.config) : Prop :=
    match R.cfg_control current with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode _ k | R.Return k | R.RunDrain _ k =>
        continuation_round_origins tf roots current k
    | R.RunRhs fr _ k
    | R.RunDead fr _ _ k
    | R.RunCommit fr _ k =>
        frame_round_origin tf roots current fr k /\
        continuation_round_origins tf roots current k
    end.

  Lemma steps_before_owner_commit_snoc :
    forall owner tf first before after,
      steps_before_owner_commit owner tf first before ->
      Total.Termination.owner_commitb owner before = false ->
      Sem.step tf before after ->
      steps_before_owner_commit owner tf first after.
  Proof.
    intros owner tf first before after Hprefix Hnotcommit Hstep.
    induction Hprefix.
    - econstructor; [exact Hnotcommit |exact Hstep |constructor].
    - econstructor; [exact H |exact H0 |].
      now apply IHHprefix.
  Qed.

  Lemma frame_round_origin_step :
    forall tf roots before after fr base,
      frame_round_origin tf roots before fr base ->
      Total.Termination.owner_commitb
        (R.frame_owner fr) before = false ->
      Sem.step tf before after ->
      frame_round_origin tf roots after fr base.
  Proof.
    intros tf roots before after fr base
      [entry [Hentry Hprefix]] Hnotcommit Hstep.
    exists entry. split; [exact Hentry |].
    eapply steps_before_owner_commit_snoc; eassumption.
  Qed.

  Lemma frame_round_origin_owner :
    forall tf roots current before after base,
      R.frame_owner after = R.frame_owner before ->
      frame_round_origin tf roots current before base ->
      frame_round_origin tf roots current after base.
  Proof.
    intros tf roots current before after base Howner Horigin.
    unfold frame_round_origin in *. now rewrite Howner.
  Qed.

  Lemma continuation_round_origins_step_noncommit :
    forall tf roots before after k,
      (forall owner,
        Total.Termination.owner_commitb owner before = false) ->
      Sem.step tf before after ->
      continuation_round_origins tf roots before k ->
      continuation_round_origins tf roots after k.
  Proof.
    intros tf roots before after k Hnotcommit Hstep.
    induction k; cbn; intros Horigins; try exact I.
    all: try (destruct Horigins as [Hframe Hrest]; split;
      [eapply frame_round_origin_step; eauto
      |eapply IHk; exact Hrest]).
    eapply IHk. exact Horigins.
  Qed.

  Lemma lower_owner_not_current_commit :
    forall st fr direct k lower,
      R.rank_lt st lower (R.frame_owner fr) = true ->
      Total.Termination.owner_commitb lower
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} = false.
  Proof.
    intros st fr direct k lower Hlower.
    unfold Total.Termination.owner_commitb. cbn.
    destruct (V.eq_dec (R.frame_owner fr) lower) as [Heq |Hneq];
      [|reflexivity].
    rewrite Heq in Hlower.
    pose proof (proj1 (@Total.rank_lt_true_ranked
      st lower lower Hlower)) as Hranked.
    rewrite (@Total.rank_lt_irrefl st lower Hranked) in Hlower.
    discriminate.
  Qed.

  Lemma continuation_round_origins_commit_step :
    forall tf roots st fr direct k after,
      Total.Termination.continuation_below
        st (R.frame_owner fr) k ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} after ->
      continuation_round_origins tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} k ->
      continuation_round_origins tf roots after k.
  Proof.
    intros tf roots st fr direct k after Hbelow Hstep.
    assert (Hall : forall rest,
      Total.Termination.continuation_below
        st (R.frame_owner fr) rest ->
      continuation_round_origins tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |} rest ->
      continuation_round_origins tf roots after rest).
    { intros rest. induction rest; cbn in *; intros Hrest_below Horigins;
        try exact I.
      all: try (destruct Hrest_below as [Hhead Hrest_below];
        destruct Horigins as [Hframe Hrest]; split;
        [eapply frame_round_origin_step;
         [exact Hframe
         |eapply lower_owner_not_current_commit; exact Hhead
         |exact Hstep]
        |eapply IHrest;
         [eapply Total.continuation_below_raise_correctness; eassumption
         |exact Hrest]]).
      destruct Hrest_below as [Hhead Hrest_below].
      eapply IHrest.
      - eapply Total.continuation_below_raise_correctness; eassumption.
      - exact Horigins. }
    now apply Hall.
  Qed.

  Lemma start_episode_round_origins_step :
    forall tf roots st owner base after,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} ->
      continuation_round_origins tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} base ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |} after ->
      control_round_origins tf roots after.
  Proof.
    intros tf roots st owner base after Hreachable Horigins Hstep.
    pose proof Hstep as Hsemantic.
    unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
    inversion Hstep; subst. cbn. split.
    - exists
        {| R.cfg_state := R.materialize st owner;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize st owner) owner
                 (U.initial_phase false owner))
               (tf owner) base |}.
      split.
      + now apply RoundEntryEpisode.
      + constructor.
    - eapply (@continuation_round_origins_step_noncommit tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner base |}
        {| R.cfg_state := R.materialize st owner;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.materialize st owner) owner
                 (U.initial_phase false owner))
               (tf owner) base |} base).
      + intros current. reflexivity.
      + exact Hsemantic.
      + exact Horigins.
  Qed.

  Lemma rerun_round_origins :
    forall tf roots st fr base tail,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunDrain fr base |} ->
      continuation_round_origins tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.RunDrain fr base |} base ->
      R.queue_pop (R.queue st) = Some (R.frame_owner fr, tail) ->
      control_round_origins tf roots
        (Total.Termination.executed_rerun
          tf (R.frame_owner fr) base st fr tail).
  Proof.
    intros tf roots st fr base tail Hreachable Horigins Hpop.
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st;
         R.cfg_control := R.RunDrain fr base |}
      (Total.Termination.executed_rerun
        tf (R.frame_owner fr) base st fr tail)).
    { eapply Total.Termination.executed_rerun_step;
        [reflexivity |exact Hpop]. }
    unfold Total.Termination.executed_rerun. cbn. split.
    - exists
        {| R.cfg_state := R.with_queue st tail;
           R.cfg_control :=
             R.RunRhs
               (R.fresh_frame (R.with_queue st tail)
                 (R.frame_owner fr) (R.frame_phase fr))
               (tf (R.frame_owner fr)) base |}.
      split.
      + change (first_discovery_round_entry tf roots
          (R.frame_owner fr) base
          (Total.Termination.executed_rerun
            tf (R.frame_owner fr) base st fr tail)).
        eapply (@RoundEntryRerun tf roots (R.frame_owner fr) base
          st fr tail).
        * reflexivity.
        * exact Hreachable.
        * exact Hpop.
      + constructor.
    - eapply (@continuation_round_origins_step_noncommit tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.RunDrain fr base |}
        (Total.Termination.executed_rerun
          tf (R.frame_owner fr) base st fr tail) base).
      + intros owner. reflexivity.
      + exact Hstep.
      + exact Horigins.
  Qed.

  Lemma first_discovery_control_round_origins_step :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) before ->
      control_round_origins tf roots before ->
      Sem.step tf before after ->
      control_round_origins tf roots after.
  Proof.
    intros tf roots finite [st control] after Hordinary Hreachable
      Horigins Hstep.
    pose proof Hstep as Hsemantic.
    destruct control as
      [|seed_roots |remaining |owner base |fr body base
       |fr direct pending base |fr direct base |fr base |base].
    - unfold Sem.step in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)); try discriminate.
      destruct p. inversion Hstep; subst. exact I.
    - unfold Sem.step in Hstep. destruct seed_roots; cbn in Hstep.
      + inversion Hstep; subst. exact I.
      + destruct (R.is_materialized (R.observe st t) t);
          inversion Hstep; subst; exact I.
    - unfold Sem.step in Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st));
        [destruct p |]; inversion Hstep; subst; exact I.
    - eapply start_episode_round_origins_step; eassumption.
    - cbn in Horigins. destruct Horigins as [Hframe Hrest].
      assert (Hframe_after : frame_round_origin tf roots after fr base).
      { eapply frame_round_origin_step.
        - exact Hframe.
        - reflexivity.
        - exact Hsemantic. }
      assert (Hrest_after :
        continuation_round_origins tf roots after base).
      { eapply (@continuation_round_origins_step_noncommit tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr body base |} after base).
        - intros current. reflexivity.
        - exact Hsemantic.
        - exact Hrest. }
      destruct body as [value |target next |target raw next |target next].
      + unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. cbn. now split.
      + unfold Sem.step in Hstep.
        cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (negb (R.is_materialized observed target) &&
          R.rank_lt observed (R.frame_owner fr) target)%bool.
        * inversion Hstep; subst. cbn. now split.
        * set (base_st := if R.is_materialized observed target
            then observed else R.enqueue observed target) in *.
          destruct (R.complete_get base_st fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. cbn. split.
          -- eapply frame_round_origin_owner.
             ++ eapply Total.complete_get_owner. exact Hget.
             ++ exact Hframe_after.
          -- exact Hrest_after.
      + exfalso. eapply ordinary_reachable_side_impossible; eassumption.
      + unfold Sem.step in Hstep.
        cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (observed := R.observe st target) in *.
        destruct (R.is_materialized observed target).
        * inversion Hstep; subst. cbn. now split.
        * destruct (R.rank_lt observed (R.frame_owner fr) target);
            inversion Hstep; subst; cbn; now split.
    - pose proof (@ordinary_reachable_clean tf roots finite Hordinary
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending base |}
        Hreachable) as [_ Hclean].
      cbn in Hclean. destruct Hclean as [_ [-> _]].
      cbn in Horigins. destruct Horigins as [Hframe Hrest].
      unfold Sem.step in Hstep. cbn -[R.publish_targets] in Hstep.
      inversion Hstep; subst. cbn. split.
      + eapply frame_round_origin_step; [exact Hframe |reflexivity |].
        exact Hsemantic.
      + eapply (@continuation_round_origins_step_noncommit tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct [] base |}
          {| R.cfg_state := R.publish_targets st fr;
             R.cfg_control := R.RunCommit fr direct base |} base).
        * intros current. reflexivity.
        * exact Hsemantic.
        * exact Hrest.
    - cbn in Horigins. destruct Horigins as [_ Hrest].
      pose proof (Total.Termination.reachable_control_ordered Hreachable)
        as Hbelow.
      cbn in Hbelow.
      unfold Sem.step in Hstep. cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      inversion Hstep; subst. cbn.
      eapply continuation_round_origins_commit_step.
      + exact Hbelow.
      + exact Hsemantic.
      + exact Hrest.
    - cbn in Horigins.
      unfold Sem.step in Hstep.
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
      + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
        * destruct (R.queue_pop (R.queue st))
            as [[head tail] |] eqn:Hpop; try discriminate.
          inversion Hstep; subst.
          assert (Hhead : head = R.frame_owner fr).
          { pose proof (@Total.queue_peek_pop_same
              (R.queue st) (R.frame_owner fr) head tail Hpeek Hpop)
              as Hsame.
            now symmetry. }
          subst head.
          eapply rerun_round_origins; eassumption.
        * destruct (R.rank_lt st (R.frame_owner fr) next).
          -- destruct (R.queue_pop (R.queue st))
               as [[head tail] |] eqn:Hpop; try discriminate.
             inversion Hstep; subst. cbn.
             eapply (@continuation_round_origins_step_noncommit tf roots
               {| R.cfg_state := st;
                  R.cfg_control := R.RunDrain fr base |}
               {| R.cfg_state := R.with_queue st tail;
                  R.cfg_control := R.StartEpisode next (R.KDrain fr base) |}
               base).
             ++ intros current. reflexivity.
             ++ exact Hsemantic.
             ++ exact Horigins.
          -- inversion Hstep; subst. cbn.
             eapply (@continuation_round_origins_step_noncommit tf roots
               {| R.cfg_state := st;
                  R.cfg_control := R.RunDrain fr base |}
               {| R.cfg_state :=
                    R.reset_registered_cells st (R.frame_owner fr);
                  R.cfg_control := R.Return base |} base).
             ++ intros current. reflexivity.
             ++ exact Hsemantic.
             ++ exact Horigins.
      + inversion Hstep; subst. cbn.
        eapply (@continuation_round_origins_step_noncommit tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunDrain fr base |}
          {| R.cfg_state :=
               R.reset_registered_cells st (R.frame_owner fr);
             R.cfg_control := R.Return base |} base).
        * intros current. reflexivity.
        * exact Hsemantic.
        * exact Horigins.
    - destruct base as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest]; cbn in Horigins.
      + unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. exact I.
      + unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. exact I.
      + destruct Horigins as [Hframe Hrest].
        destruct (R.complete_get st fr target)
          as [[st1 fr1] value] eqn:Hget.
        unfold Sem.step in Hstep. cbn -[R.complete_get] in Hstep.
        rewrite Hget in Hstep. inversion Hstep; subst. cbn. split.
        * eapply frame_round_origin_owner.
          -- eapply Total.complete_get_owner. exact Hget.
          -- eapply frame_round_origin_step;
               [exact Hframe |reflexivity |exact Hsemantic].
        * eapply (@continuation_round_origins_step_noncommit tf roots
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.Return (R.KAfterGet fr target next rest) |}
            {| R.cfg_state := st1;
               R.cfg_control := R.RunRhs fr1 (next value) rest |} rest).
          -- intros current. reflexivity.
          -- exact Hsemantic.
          -- exact Hrest.
      + destruct Horigins as [Hframe Hrest].
        unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. cbn. split.
        * eapply frame_round_origin_step;
            [exact Hframe |reflexivity |exact Hsemantic].
        * eapply (@continuation_round_origins_step_noncommit tf roots
            {| R.cfg_state := st;
               R.cfg_control := R.Return (R.KAfterSide fr next rest) |}
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr next rest |} rest);
            [intros current; reflexivity |exact Hsemantic |exact Hrest].
      + destruct Horigins as [Hframe Hrest].
        unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. cbn. split.
        * eapply frame_round_origin_step;
            [exact Hframe |reflexivity |exact Hsemantic].
        * eapply (@continuation_round_origins_step_noncommit tf roots
            {| R.cfg_state := st;
               R.cfg_control := R.Return (R.KAfterSpawn fr next rest) |}
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr next rest |} rest);
            [intros current; reflexivity |exact Hsemantic |exact Hrest].
      + destruct Horigins as [Hframe Hrest].
        unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. cbn. split.
        * eapply frame_round_origin_step;
            [exact Hframe |reflexivity |exact Hsemantic].
        * eapply (@continuation_round_origins_step_noncommit tf roots
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.Return (R.KDead fr direct pending rest) |}
            {| R.cfg_state := st;
               R.cfg_control := R.RunDead fr direct pending rest |} rest);
            [intros current; reflexivity |exact Hsemantic |exact Hrest].
      + unfold Sem.step in Hstep. cbn in Hstep.
        inversion Hstep; subst. cbn.
        eapply (@continuation_round_origins_step_noncommit tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.Return (R.KDrain fr rest) |}
          {| R.cfg_state := st;
             R.cfg_control := R.RunDrain fr rest |} rest);
          [intros current; reflexivity |exact Hsemantic |exact Horigins].
  Qed.

  Theorem first_discovery_reachable_control_round_origins :
    forall tf roots (finite : Sem.finite_system tf roots) c,
      ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) c ->
      control_round_origins tf roots c.
  Proof.
    intros tf roots finite c Hordinary Hsteps.
    assert (Hpreserve : forall first final,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first final ->
      control_round_origins tf roots first ->
      control_round_origins tf roots final).
    { intros first final Hreachable Hrun Horigins.
      induction Hrun.
      - exact Horigins.
      - apply IHHrun.
        + eapply Total.Termination.steps_append_one; eassumption.
        + eapply (@first_discovery_control_round_origins_step
            tf roots finite first next); eassumption. }
    eapply Hpreserve.
    - constructor.
    - exact Hsteps.
    - exact I.
  Qed.

  Theorem first_discovery_round_entry_first_commit_frontier :
    forall support tf roots (finite : Sem.finite_system tf roots)
      owner base entry commit,
      support = Sem.support finite ->
      ordinary_monotonic_system tf ->
      first_discovery_round_entry tf roots owner base entry ->
      Total.Termination.until_owner_commit owner tf entry commit ->
      Total.Termination.queue_strictly_below owner
        (R.cfg_state commit).
  Proof.
    intros support tf roots finite owner base entry commit
      Hsupport Hordinary Hentry Huntil.
    inversion Hentry; subst.
    - eapply (@first_discovery_reachable_episode_first_commit_frontier
        (Sem.support finite) tf roots finite owner base st commit eq_refl Hordinary
        H); exact Huntil.
    - eapply (@first_discovery_rerun_first_commit_frontier
        (Sem.support finite) tf roots finite (R.frame_owner fr) base
        st fr tail commit eq_refl Hordinary eq_refl H0 H1);
        exact Huntil.
  Qed.

  Lemma steps_before_owner_commit_until :
    forall owner tf first commit,
      steps_before_owner_commit owner tf first commit ->
      Total.Termination.owner_commitb owner commit = true ->
      Total.Termination.until_owner_commit owner tf first commit.
  Proof.
    intros owner tf first commit Hsteps. induction Hsteps;
      intros Hcommit.
    - now apply Total.Termination.UntilOwnerCommitDone.
    - eapply Total.Termination.UntilOwnerCommitStep.
      + exact H.
      + exact H0.
      + now apply IHHsteps.
  Qed.

  Definition first_discovery_commit_round_origin
    (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
    forall st fr direct base,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct base |} ->
      exists entry,
        first_discovery_round_entry tf roots
          (R.frame_owner fr) base entry /\
        steps_before_owner_commit (R.frame_owner fr) tf entry
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit fr direct base |}.

  Theorem first_discovery_round_origin_boxn_entry_frontier :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      first_discovery_commit_round_origin tf roots ->
      ordinary_boxn_entry_frontier tf roots.
  Proof.
    intros tf roots finite Hordinary Horigin
      st fr direct base next next_fr Hreachable _ _ _.
    destruct (Horigin st fr direct base Hreachable)
      as [entry [Hentry Hprefix]].
    assert (Hcommit : Total.Termination.owner_commitb
      (R.frame_owner fr)
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct base |} = true).
    { unfold Total.Termination.owner_commitb. cbn.
      destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));
        [reflexivity |contradiction]. }
    eapply (@first_discovery_round_entry_first_commit_frontier
      (Sem.support finite) tf roots finite (R.frame_owner fr) base entry
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct base |}
      eq_refl Hordinary Hentry).
    now apply steps_before_owner_commit_until.
  Qed.

  Theorem first_discovery_round_origin_avoids_fallback :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      first_discovery_commit_round_origin tf roots ->
      ordinary_avoids_fallback tf roots.
  Proof.
    intros tf roots finite Hordinary Horigin.
    eapply (@ordinary_boxn_entry_frontier_avoids_fallback
      tf roots finite).
    - exact Hordinary.
    - eapply first_discovery_round_origin_boxn_entry_frontier;
        eassumption.
  Qed.

  Theorem first_discovery_reachable_commit_round_origin :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      first_discovery_commit_round_origin tf roots.
  Proof.
    intros tf roots finite Hordinary st fr direct base Hreachable.
    pose proof (@first_discovery_reachable_control_round_origins
      tf roots finite
      {| R.cfg_state := st;
         R.cfg_control := R.RunCommit fr direct base |}
      Hordinary Hreachable) as Horigins.
    cbn in Horigins. exact (proj1 Horigins).
  Qed.

  (** Public FirstDiscovery narrowing-stability theorem.  An ordinary monotone
      system never falls back from narrowing to a second widening phase. *)
  Theorem first_discovery_ordinary_avoids_fallback :
    forall tf roots (finite : Sem.finite_system tf roots),
      ordinary_monotonic_system tf ->
      ordinary_avoids_fallback tf roots.
  Proof.
    intros tf roots finite Hordinary.
    eapply (@first_discovery_round_origin_avoids_fallback
      tf roots finite).
    - exact Hordinary.
    - now apply first_discovery_reachable_commit_round_origin.
  Qed.

  Theorem first_discovery_reachable_fresh_queue_below :
    forall tf roots c target,
      Sem.steps tf (R.initial_config roots) c ->
      R.Ranking.lookup (R.ranking (R.cfg_state c)) target = None ->
      Total.Termination.queue_strictly_below target
        (R.observe (R.cfg_state c) target).
  Proof.
    intros tf roots c target Hreachable Hfresh.
    eapply reachable_fresh_observe_queue_below.
    - apply first_discovery_fresh_ranks_above.
    - exact Hreachable.
    - exact Hfresh.
  Qed.

  Theorem first_discovery_unranked_target_clean :
    forall tf roots c target,
      Sem.steps tf (R.initial_config roots) c ->
      R.Ranking.lookup (R.ranking (R.cfg_state c)) target = None ->
      Total.Termination.queue_strictly_below target
        (R.observe (R.cfg_state c) target) /\
      set_has_no_members
        (R.lookup_set
          (R.readers (R.observe (R.cfg_state c) target)) target).
  Proof.
    intros tf roots c target Hreachable Hunranked. split.
    - eapply first_discovery_reachable_fresh_queue_below; eassumption.
    - assert (Hfresh :
        R.is_materialized (R.cfg_state c) target = false).
      { eapply reachable_unranked_is_unmaterialized; eassumption. }
      intros reader.
      unfold R.observe. destruct (R.Ranking.observe
        (R.ranking (R.cfg_state c)) target). cbn.
      exact (@reachable_fresh_target_has_no_readers
        tf roots c target Hreachable Hfresh reader).
  Qed.

  Theorem first_discovery_unranked_get_starts_episode :
    forall tf roots st fr target next k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.next_config tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Get target next) k |} =
      Some
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterGet fr target next k) |}.
  Proof.
    intros tf roots st fr target next k Hreachable Hunranked.
    eapply append_only_unranked_get_starts_episode.
    - apply first_discovery_fresh_ranks_above.
    - exact Hreachable.
    - exact Hunranked.
  Qed.

  Theorem first_discovery_unranked_spawn_starts_episode :
    forall tf roots st fr target next k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.next_config tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} =
      Some
        {| R.cfg_state := R.observe st target;
           R.cfg_control :=
             R.StartEpisode target (R.KAfterSpawn fr next k) |}.
  Proof.
    intros tf roots st fr target next k Hreachable Hunranked.
    eapply append_only_unranked_spawn_starts_episode.
    - apply first_discovery_fresh_ranks_above.
    - exact Hreachable.
    - exact Hunranked.
  Qed.

End FirstDiscovery.
End Make.
