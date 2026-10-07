From Stdlib Require Import List Bool Lia.
From TcSolvers Require Import common.Assumptions common.BoxUpdate
  solvers.slr.narrowing_fixed_point_compact.Proofs.
Import ListNotations.
Set Implicit Arguments.

(** Precision certificates use historical observations. Monotonicity keeps
    later reads below those observations, so narrowing waves have no growing
    owner input. The certificates are proof-only. *)
Module Make (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
Module U := OneBoxUpdate V D WN.
Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
  (WS : WIDEN_STABILITY D WN) (UL : UPDATE_LAWS V D U).
Module WithCollections (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
Module P := Proofs.Make V D U S M Features DL UL SL ML.
Module B := P.B.
Module R := P.R.
Module N := P.N.
Module Sem := P.Sem.
Module O := Sem.Observation.
Include P.Spec.
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
Theorem successful_run_fixed fuel tf roots final : Features.recompute_controlled = true ->
  monotonic_system tf -> N.solve_fuel fuel tf roots = Some final -> narrowing_fixed tf final.
Proof.
  intros Henabled Hmono Hrun; destruct (@P.successful_path fuel tf roots final Hrun) as [Hpath Hqueue].
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

End WithCollections.
End WithLaws.
End Make.
