From Stdlib Require Import
  List Lia Arith.PeanoNat Sorting.Sorted Sorting.Permutation
  Wellfounded Wf_nat
  Relations.Relation_Operators
  Wellfounded.Inverse_Image
  Wellfounded.Lexicographic_Product
  Wellfounded.List_Extension.
From TcSolvers Require Import
  common.Assumptions common.SolverContracts
  common.ConstraintSemantics
  solvers.slr.common.DiscoveryOrderLaws
  common.SideUpdate
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces
  solvers.slr.dirty_read_restarting.DirtyReadRestartingInterface.

Import ListNotations.
Set Implicit Arguments.

(** Proof-only interpretation of the Dormant Restarting machine. *)
Module Semantics.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : DirtyReadRestarting.FEATURES).

  Module Solver := DirtyReadRestartingInterface.Make V D U SU S M Rk Features.
  Module R := Solver.R.
  Module ConstraintSyntax := Solver.Syntax.
  Module ConstraintSemantics := Solver.TransferSemantics.
  Include ConstraintSemantics.

  Include Solver.ExecutionSemantics.
  Definition terminates_to
    (tf : R.ConstraintSystem.system)
    (initial : list V.t) (final : R.state) : Prop :=
    steps tf (R.initial_config initial) (terminal_config final) /\
    quiescent final.

  Module StateSpec := SolverSpecifications.Make V D Solver.Sem Solver.View.
  Definition solved := StateSpec.solved.
  Definition rhs_eval := StateSpec.replay.
  Definition side_effects_below := StateSpec.side_effects_below.
  Definition rhs_post_solution := StateSpec.rhs_post_solution.
  Definition state_valuation (st : R.state) : valuation := R.sigma_value st.

  Definition correct_final_state
    (tf : R.ConstraintSystem.system)
    (initial : list V.t) (final : R.state) : Prop :=
    forall owner,
      List.In owner initial ->
      solved final owner /\
      rhs_post_solution final owner (tf owner).

  Definition totally_correct_on
    (tf : R.ConstraintSystem.system) (initial : list V.t) : Prop :=
    exists fuel final,
      R.solve_fuel fuel tf initial = Some final /\
      correct_final_state tf initial final.


End Make.
End Semantics.

(** Internal partial-correctness proof for the Dormant Restarting machine.  The
    reviewer-facing results are re-stated in [solvers.slr.reluctant_restarting.Theorems].

    This file intentionally assumes only stable ranks and update soundness. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : DirtyReadRestarting.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (DL : DOMAIN_LAWS D)
  (OSL : ORDINARY_UPDATE_SOUND_LAWS V D U)
  (SSL : SIDE_UPDATE_SOUND_LAWS V D SU)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Sem := Semantics.Make V D U SU S M Rk Features.
  Module R := Sem.R.
  Module Solver := Sem.Solver.
  Module Spec := SolverContracts.ForSolver V D Solver.

  Definition rank_valid (st : R.state) : Prop :=
    RankLaws.valid (R.ranking st).

  Definition rank_extends (before after : R.state) : Prop :=
    forall x rank,
      R.Ranking.lookup (R.ranking before) x = Some rank ->
      R.Ranking.lookup (R.ranking after) x = Some rank.

  Definition ranked (st : R.state) (x : V.t) : Prop :=
    exists rank, R.Ranking.lookup (R.ranking st) x = Some rank.

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

  Lemma ranked_extended :
    forall before after x,
      rank_extends before after -> ranked before x -> ranked after x.
  Proof.
    intros before after x Hextends [rank Hrank].
    exists rank. now apply Hextends.
  Qed.

  Lemma empty_rank_valid : rank_valid R.empty_state.
  Proof. apply RankLaws.empty_valid. Qed.

  Lemma rank_valid_observe :
    forall st x next,
      rank_valid st ->
      R.observe st x = next ->
      rank_valid next.
  Proof.
    intros st x next Hvalid Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking rank] eqn:Hrank.
    inversion Hobserve; subst. unfold rank_valid in *. cbn.
    eapply RankLaws.observe_valid; eauto.
  Qed.

  Lemma rank_extends_observe :
    forall st x next,
      R.observe st x = next ->
      rank_extends st next.
  Proof.
    intros st x next Hobserve variable rank Hlookup.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking observed_rank] eqn:Hrank.
    inversion Hobserve; subst. cbn.
    eapply RankLaws.observe_preserves; eauto.
  Qed.

  Lemma observe_ranks_variable :
    forall st x next,
      R.observe st x = next -> ranked next x.
  Proof.
    intros st x next Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking observed_rank] eqn:Hrank.
    inversion Hobserve; subst. exists observed_rank. cbn.
    eapply RankLaws.observe_lookup; eauto.
  Qed.

  Lemma rank_extends_with_queue :
    forall st queue, rank_extends st (R.with_queue st queue).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_materialize :
    forall st x, rank_extends st (R.materialize st x).
  Proof.
    intros st x. apply rank_extends_same_ranking.
    unfold R.materialize. destruct (M.lookup (R.sigma st) x); reflexivity.
  Qed.

  Lemma rank_extends_enqueue :
    forall st x, rank_extends st (R.enqueue st x).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_enqueue_all :
    forall st xs, rank_extends st (R.enqueue_all st xs).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_sigma :
    forall st sigma, rank_extends st (R.with_sigma st sigma).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_readers :
    forall st readers, rank_extends st (R.with_readers st readers).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_contributions :
    forall st contributions,
      rank_extends st (R.with_contributions st contributions).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_cells_and_resets :
    forall st cells resets,
      rank_extends st (R.with_cells_and_resets st cells resets).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_last_targets :
    forall st targets, rank_extends st (R.with_last_targets st targets).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_dormant_bottom :
    forall st dormant,
      rank_extends st (R.with_dormant_bottom st dormant).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_remember_dormant :
    forall st variable,
      rank_extends st (R.remember_dormant st variable).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_add_reader :
    forall st target reader,
      rank_extends st (R.add_reader st target reader).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_publish_dormant_target :
    forall st target changed,
      rank_extends st (R.publish_dormant_target st target changed).
  Proof.
    intros. apply rank_extends_same_ranking.
    unfold R.publish_dormant_target, R.materialize.
    destruct (M.lookup (R.sigma st) target); destruct changed; reflexivity.
  Qed.

  Lemma rank_extends_with_controlled :
    forall st controlled, rank_extends st (R.with_controlled st controlled).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_with_dirty_side_targets :
    forall st dirty,
      rank_extends st (R.with_dirty_side_targets st dirty).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_extends_mark_side_dirty :
    forall st target, rank_extends st (R.mark_side_dirty st target).
  Proof. intros. apply rank_extends_with_dirty_side_targets. Qed.

  Lemma rank_extends_clear_side_dirty :
    forall st target, rank_extends st (R.clear_side_dirty st target).
  Proof. intros. apply rank_extends_with_dirty_side_targets. Qed.

  Lemma rank_valid_with_queue :
    forall st queue,
      rank_valid st -> rank_valid (R.with_queue st queue).
  Proof. intros st queue Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_sigma :
    forall st sigma,
      rank_valid st -> rank_valid (R.with_sigma st sigma).
  Proof. intros st sigma Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_readers :
    forall st readers,
      rank_valid st -> rank_valid (R.with_readers st readers).
  Proof. intros st readers Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_contributions :
    forall st contributions,
      rank_valid st -> rank_valid (R.with_contributions st contributions).
  Proof. intros st contributions Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_cells_and_resets :
    forall st cells resets,
      rank_valid st ->
      rank_valid (R.with_cells_and_resets st cells resets).
  Proof. intros st cells resets Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_last_targets :
    forall st targets,
      rank_valid st -> rank_valid (R.with_last_targets st targets).
  Proof. intros st targets Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_dormant_bottom :
    forall st dormant,
      rank_valid st -> rank_valid (R.with_dormant_bottom st dormant).
  Proof. intros st dormant Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_remember_dormant :
    forall st variable,
      rank_valid st -> rank_valid (R.remember_dormant st variable).
  Proof. intros st variable Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_add_reader :
    forall st target reader,
      rank_valid st -> rank_valid (R.add_reader st target reader).
  Proof. intros st target reader Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_controlled :
    forall st controlled,
      rank_valid st -> rank_valid (R.with_controlled st controlled).
  Proof. intros st controlled Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_with_dirty_side_targets :
    forall st dirty,
      rank_valid st -> rank_valid (R.with_dirty_side_targets st dirty).
  Proof. intros st dirty Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_flush_deferred :
    forall st,
      rank_valid st -> rank_valid (R.flush_deferred st).
  Proof. intros st Hvalid. exact Hvalid. Qed.

  Lemma rank_extends_flush_deferred :
    forall st, rank_extends st (R.flush_deferred st).
  Proof. intros st. apply rank_extends_same_ranking. reflexivity. Qed.

  Lemma rank_valid_mark_side_dirty :
    forall st target,
      rank_valid st -> rank_valid (R.mark_side_dirty st target).
  Proof. intros. now apply rank_valid_with_dirty_side_targets. Qed.

  Lemma rank_valid_clear_side_dirty :
    forall st target,
      rank_valid st -> rank_valid (R.clear_side_dirty st target).
  Proof. intros. now apply rank_valid_with_dirty_side_targets. Qed.

  Lemma rank_valid_cancel_dirty_target :
    forall st target,
      rank_valid st -> rank_valid (R.cancel_dirty_target st target).
  Proof. intros st target Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_write_dirty_value :
    forall st target value,
      rank_valid st -> rank_valid (R.write_dirty_value st target value).
  Proof. intros st target value Hvalid. exact Hvalid. Qed.

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
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      try discriminate; inversion Hread; subst; cbn; exact Hvalid.
  Qed.

  Lemma rank_extends_try_dirty_read :
    forall tf st owner target next,
      R.try_dirty_read tf st owner target = Some next ->
      rank_extends st next.
  Proof.
    intros tf st owner target next Hread.
    apply rank_extends_same_ranking.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      try discriminate; inversion Hread; reflexivity.
  Qed.

  Lemma rank_valid_materialize :
    forall st x, rank_valid st -> rank_valid (R.materialize st x).
  Proof.
    intros st x Hvalid. unfold R.materialize.
    destruct (M.lookup (R.sigma st) x); exact Hvalid.
  Qed.

  Lemma rank_valid_publish_dormant_target :
    forall st target changed,
      rank_valid st ->
      rank_valid (R.publish_dormant_target st target changed).
  Proof.
    intros st target changed Hvalid.
    unfold R.publish_dormant_target, R.materialize.
    destruct (M.lookup (R.sigma st) target); destruct changed;
      exact Hvalid.
  Qed.

  Lemma rank_valid_enqueue :
    forall st x, rank_valid st -> rank_valid (R.enqueue st x).
  Proof. intros st x Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_enqueue_all :
    forall st xs, rank_valid st -> rank_valid (R.enqueue_all st xs).
  Proof. intros st xs Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_promote_controlled :
    forall st x,
      rank_valid st -> rank_valid (R.promote_controlled st x).
  Proof.
    intros st x Hvalid. apply rank_valid_with_controlled. exact Hvalid.
  Qed.

  Lemma rank_extends_promote_controlled :
    forall st x, rank_extends st (R.promote_controlled st x).
  Proof. intros. apply rank_extends_with_controlled. Qed.

  Lemma rank_valid_get_control_state :
    forall st owner target,
      rank_valid st ->
      rank_valid
        (if R.rank_lt st owner target
         then st else R.promote_controlled st target).
  Proof.
    intros st owner target Hvalid.
    destruct (R.rank_lt st owner target);
      [exact Hvalid | now apply rank_valid_promote_controlled].
  Qed.

  Lemma rank_extends_get_control_state :
    forall st owner target,
      rank_extends st
        (if R.rank_lt st owner target
         then st else R.promote_controlled st target).
  Proof.
    intros st owner target. destruct (R.rank_lt st owner target);
      [apply rank_extends_refl | apply rank_extends_promote_controlled].
  Qed.

  Lemma rank_valid_promote_side_target :
    forall st fr target,
      rank_valid st -> rank_valid (R.promote_side_target st fr target).
  Proof.
    intros st fr target Hvalid. unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr));
      [exact Hvalid | now apply rank_valid_promote_controlled].
  Qed.

  Lemma rank_extends_promote_side_target :
    forall st fr target,
      rank_extends st (R.promote_side_target st fr target).
  Proof.
    intros st fr target. unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr));
      [apply rank_extends_refl | apply rank_extends_promote_controlled].
  Qed.

  Lemma rank_valid_register_reset :
    forall st source target scope phase,
      rank_valid st ->
      rank_valid (R.register_reset st source target scope phase).
  Proof.
    intros st source target scope phase Hvalid.
    unfold R.register_reset. apply rank_valid_with_cells_and_resets.
    exact Hvalid.
  Qed.

  Lemma rank_extends_register_reset :
    forall st source target scope phase,
      rank_extends st (R.register_reset st source target scope phase).
  Proof.
    intros. unfold R.register_reset.
    apply rank_extends_with_cells_and_resets.
  Qed.

  Lemma rank_valid_write_side_contribution :
    forall st fr target input next changed,
      rank_valid st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      rank_valid next.
  Proof.
    intros st fr target input next changed Hvalid Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted eqn:Hpromoted.
    inversion Hwrite; subst; cbn.
    apply rank_valid_register_reset.
    apply rank_valid_with_contributions.
    now apply rank_valid_promote_side_target.
  Qed.

  Lemma rank_extends_write_side_contribution :
    forall st fr target input next changed,
      R.write_side_contribution st fr target input = (next, changed) ->
      rank_extends st next.
  Proof.
    intros st fr target input next changed Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted eqn:Hpromoted.
    inversion Hwrite; subst; cbn.
    eapply rank_extends_trans.
    - apply rank_extends_promote_side_target.
    - eapply rank_extends_trans.
      + apply rank_extends_with_contributions.
      + apply rank_extends_register_reset.
  Qed.

  Lemma rank_valid_set_value :
    forall st fr direct next next_fr,
      rank_valid st ->
      R.set_value st fr direct = (next, next_fr) ->
      rank_valid next.
  Proof.
    intros st fr direct next next_fr Hvalid Hset.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn;
      repeat first
        [ apply rank_valid_with_readers
        | apply rank_valid_enqueue_all
        | apply rank_valid_with_sigma ];
      exact Hvalid.
  Qed.

  Lemma rank_extends_set_value :
    forall st fr direct next next_fr,
      R.set_value st fr direct = (next, next_fr) ->
      rank_extends st next.
  Proof.
    intros st fr direct next next_fr Hset variable rank Hlookup.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn; exact Hlookup.
  Qed.

  Lemma rank_valid_continue_side :
    forall st fr target next k changed,
      rank_valid st ->
      rank_valid (R.cfg_state (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed Hvalid. unfold R.continue_side.
    repeat destruct (_ : bool); cbn; exact Hvalid.
  Qed.

  Lemma rank_extends_continue_side :
    forall st fr target next k changed,
      rank_extends st
        (R.cfg_state (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed variable rank Hlookup.
    unfold R.continue_side.
    repeat destruct (_ : bool); cbn; exact Hlookup.
  Qed.

  Lemma rank_valid_continue_dead :
    forall st fr direct target remaining k changed,
      rank_valid st ->
      rank_valid
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed Hvalid.
    unfold R.continue_dead.
    repeat destruct (_ : bool); cbn; exact Hvalid.
  Qed.

  Lemma rank_extends_continue_dead :
    forall st fr direct target remaining k changed,
      rank_extends st
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed variable rank Hlookup.
    unfold R.continue_dead.
    repeat destruct (_ : bool); cbn; exact Hlookup.
  Qed.

  Lemma rank_lt_lookup :
    forall st x y x_rank y_rank,
      R.Ranking.lookup (R.ranking st) x = Some x_rank ->
      R.Ranking.lookup (R.ranking st) y = Some y_rank ->
      R.rank_lt st x y = Nat.ltb x_rank y_rank.
  Proof.
    intros st x y x_rank y_rank Hx Hy.
    unfold R.rank_lt, R.ranking_lt. now rewrite Hx, Hy.
  Qed.

  Lemma rank_lt_irrefl :
    forall st x,
      ranked st x -> R.rank_lt st x x = false.
  Proof.
    intros st x [rank Hrank].
    rewrite (@rank_lt_lookup st x x rank rank Hrank Hrank).
    apply Nat.ltb_ge. lia.
  Qed.

  Lemma rank_lt_asymmetric :
    forall st x y,
      ranked st x -> ranked st y ->
      R.rank_lt st x y = true ->
      R.rank_lt st y x = false.
  Proof.
    intros st x y [xrank Hx] [yrank Hy] Hxy.
    rewrite (@rank_lt_lookup st x y xrank yrank Hx Hy) in Hxy.
    rewrite (@rank_lt_lookup st y x yrank xrank Hy Hx).
    apply Nat.ltb_lt in Hxy. apply Nat.ltb_ge. lia.
  Qed.

  Lemma rank_lt_trans :
    forall st x y z,
      ranked st x -> ranked st y -> ranked st z ->
      R.rank_lt st x y = true ->
      R.rank_lt st y z = true ->
      R.rank_lt st x z = true.
  Proof.
    intros st x y z [xrank Hx] [yrank Hy] [zrank Hz] Hxy Hyz.
    rewrite (@rank_lt_lookup st x y xrank yrank Hx Hy) in Hxy.
    rewrite (@rank_lt_lookup st y z yrank zrank Hy Hz) in Hyz.
    rewrite (@rank_lt_lookup st x z xrank zrank Hx Hz).
    apply Nat.ltb_lt in Hxy. apply Nat.ltb_lt in Hyz.
    apply Nat.ltb_lt. lia.
  Qed.

  Lemma rank_lt_total :
    forall st x y,
      rank_valid st -> ranked st x -> ranked st y -> x <> y ->
      R.rank_lt st x y = true \/ R.rank_lt st y x = true.
  Proof.
    intros st x y Hvalid [xrank Hx] [yrank Hy] Hneq.
    rewrite (@rank_lt_lookup st x y xrank yrank Hx Hy).
    rewrite (@rank_lt_lookup st y x yrank xrank Hy Hx).
    destruct (Nat.ltb xrank yrank) eqn:Hlt; [now left |right].
    apply Nat.ltb_ge in Hlt. apply Nat.ltb_lt.
    assert (xrank <> yrank) as Hranks.
    { intros Heq. apply Hneq.
      subst yrank. eapply RankLaws.lookup_injective; eauto. }
    lia.
  Qed.

  Lemma rank_lt_stable :
    forall before after x y,
      rank_extends before after ->
      ranked before x -> ranked before y ->
      R.rank_lt before x y = R.rank_lt after x y.
  Proof.
    intros before after x y Hextends [xrank Hx] [yrank Hy].
    rewrite (@rank_lt_lookup before x y xrank yrank Hx Hy).
    rewrite (@rank_lt_lookup after x y xrank yrank
      (Hextends x xrank Hx) (Hextends y yrank Hy)).
    reflexivity.
  Qed.

  Lemma queue_contains_spec :
    forall x queue,
      R.queue_contains x queue = true <-> List.In x queue.
  Proof.
    intros x queue. induction queue as [|head rest IH]; cbn.
    - split; [discriminate |intros []].
    - destruct (V.eq_dec x head) as [-> | Hneq].
      + split; [intros; now left |intros; reflexivity].
      + rewrite IH. split.
        * intros Hin. now right.
        * intros [Heq | Hin].
          -- exfalso. apply Hneq. symmetry. exact Heq.
          -- exact Hin.
  Qed.

  Lemma queue_contains_false :
    forall x queue,
      R.queue_contains x queue = false <-> ~ List.In x queue.
  Proof.
    intros x queue. destruct (R.queue_contains x queue) eqn:Hcontains.
    - rewrite queue_contains_spec in Hcontains. split; [discriminate |].
      intros Hnot. contradiction.
    - split; [|intros; reflexivity].
      intros _ Hin. apply queue_contains_spec in Hin.
      rewrite Hcontains in Hin. discriminate.
  Qed.

  Lemma queue_insert_fresh_members :
    forall order x queue y,
      List.In y (R.queue_insert_fresh order x queue) <->
      y = x \/ List.In y queue.
  Proof.
    intros order x queue. induction queue as [|head rest IH]; intros y; cbn.
    - split.
      + intros [Heq | []]. left. symmetry. exact Heq.
      + intros [Heq | []]. left. symmetry. exact Heq.
    - destruct (R.ranking_lt order head x); cbn.
      + split.
        * intros [Hx | [Hhead | Hin]].
          -- left. symmetry. exact Hx.
          -- right. now left.
          -- right. now right.
        * intros [Hx | [Hhead | Hin]].
          -- left. symmetry. exact Hx.
          -- right. now left.
          -- right. now right.
      + rewrite IH. tauto.
  Qed.

  Lemma queue_insert_members :
    forall order x queue y,
      List.In y (R.queue_insert order x queue) <->
      y = x \/ List.In y queue.
  Proof.
    intros order x queue y. unfold R.queue_insert.
    destruct (R.queue_contains x queue) eqn:Hcontains.
    - apply queue_contains_spec in Hcontains. split; [now right |].
      intros [-> | Hin]; assumption.
    - apply queue_insert_fresh_members.
  Qed.

  Lemma queue_insert_fresh_nodup :
    forall order x queue,
      ~ List.In x queue ->
      NoDup queue ->
      NoDup (R.queue_insert_fresh order x queue).
  Proof.
    intros order x queue. induction queue as [|head rest IH];
      intros Hfresh Hnodup; cbn.
    - constructor; [intros [] |constructor].
    - inversion Hnodup as [|? ? Hhead Hrest]; subst.
      destruct (R.ranking_lt order head x) eqn:Hlt.
      + constructor.
        * intros [Heq | Hin].
          -- subst. apply Hfresh. now left.
          -- apply Hfresh. now right.
        * exact Hnodup.
      + constructor.
        * rewrite queue_insert_fresh_members. intros [Heq | Hin].
          -- subst. apply Hfresh. now left.
          -- contradiction.
        * apply IH.
          -- intros Hin. apply Hfresh. now right.
          -- exact Hrest.
  Qed.

  Lemma queue_insert_nodup :
    forall order x queue,
      NoDup queue -> NoDup (R.queue_insert order x queue).
  Proof.
    intros order x queue Hnodup. unfold R.queue_insert.
    destruct (R.queue_contains x queue) eqn:Hcontains; [exact Hnodup |].
    apply queue_insert_fresh_nodup; [|exact Hnodup].
    now apply queue_contains_false.
  Qed.

  Lemma queue_insert_all_nodup :
    forall order xs queue,
      NoDup queue -> NoDup (R.queue_insert_all order xs queue).
  Proof.
    intros order xs. induction xs as [|x rest IH]; intros queue Hnodup; cbn.
    - exact Hnodup.
    - apply IH. now apply queue_insert_nodup.
  Qed.

  Lemma queue_insert_all_members :
    forall order xs queue y,
      List.In y (R.queue_insert_all order xs queue) <->
      List.In y xs \/ List.In y queue.
  Proof.
    intros order xs. induction xs as [|x rest IH]; intros queue y; cbn.
    - tauto.
    - rewrite IH, queue_insert_members. split.
      + intros [Hin | [-> | Hin]].
        * left. now right.
        * left. now left.
        * now right.
      + intros [[-> | Hin] | Hin].
        * right. now left.
        * left. exact Hin.
        * right. now right.
  Qed.

  Lemma queue_remove_members :
    forall removed queue x,
      List.In x (R.queue_remove removed queue) -> List.In x queue.
  Proof.
    intros removed queue. induction queue as [|head rest IH]; intros x Hin;
      cbn in *; [contradiction |].
    destruct (V.eq_dec removed head).
    - now right.
    - destruct Hin as [-> | Hin]; [now left |right; now apply IH].
  Qed.

  Lemma queue_remove_nodup :
    forall removed queue,
      NoDup queue -> NoDup (R.queue_remove removed queue).
  Proof.
    intros removed queue Hnodup. induction Hnodup as [|head rest Hnotin Hrest IH].
    - constructor.
    - cbn. destruct (V.eq_dec removed head).
      + exact Hrest.
      + constructor.
        * intros Hin. apply Hnotin. now apply queue_remove_members in Hin.
        * exact IH.
  Qed.

  Definition queue_ranked (st : R.state) : Prop :=
    forall x, List.In x (R.queue st) -> ranked st x.

  Definition queue_distinct (st : R.state) : Prop :=
    NoDup (R.queue st).

  Lemma empty_queue_ranked : queue_ranked R.empty_state.
  Proof. intros x Hin. inversion Hin. Qed.

  Lemma empty_queue_distinct : queue_distinct R.empty_state.
  Proof. repeat constructor. Qed.

  Lemma enqueue_distinct :
    forall st x,
      queue_distinct st -> queue_distinct (R.enqueue st x).
  Proof. intros st x Hdistinct. apply queue_insert_nodup. exact Hdistinct. Qed.

  Lemma enqueue_all_distinct :
    forall st xs,
      queue_distinct st -> queue_distinct (R.enqueue_all st xs).
  Proof. intros st xs Hdistinct. apply queue_insert_all_nodup. exact Hdistinct. Qed.

  Lemma enqueue_ranked :
    forall st x,
      queue_ranked st -> ranked st x -> queue_ranked (R.enqueue st x).
  Proof.
    intros st x Hqueue Hx y Hin. unfold R.enqueue in Hin |- *; cbn in *.
    apply queue_insert_members in Hin. destruct Hin as [-> | Hin].
    - exact Hx.
    - now apply Hqueue.
  Qed.

  Lemma enqueue_all_ranked :
    forall st xs,
      queue_ranked st ->
      (forall x, List.In x xs -> ranked st x) ->
      queue_ranked (R.enqueue_all st xs).
  Proof.
    intros st xs Hqueue Hxs x Hin.
    unfold R.enqueue_all in Hin |- *. cbn in *.
    apply queue_insert_all_members in Hin. destruct Hin as [Hin | Hin].
    - now apply Hxs.
    - now apply Hqueue.
  Qed.

  Definition list_ranked (st : R.state) (xs : list V.t) : Prop :=
    forall x, List.In x xs -> ranked st x.

  Definition set_ranked (st : R.state) (xs : S.t) : Prop :=
    forall x, S.mem x xs = true -> ranked st x.

  Definition set_table_ranked (st : R.state) (table : M.t S.t) : Prop :=
    forall key xs,
      M.lookup table key = Some xs -> set_ranked st xs.

  Lemma list_ranked_extended :
    forall before after xs,
      rank_extends before after ->
      list_ranked before xs ->
      list_ranked after xs.
  Proof.
    intros before after xs Hextends Hxs x Hin.
    eapply ranked_extended; [exact Hextends | now apply Hxs].
  Qed.

  Lemma set_ranked_extended :
    forall before after xs,
      rank_extends before after ->
      set_ranked before xs ->
      set_ranked after xs.
  Proof.
    intros before after xs Hextends Hxs x Hmem.
    eapply ranked_extended; [exact Hextends | now apply Hxs].
  Qed.

  Lemma set_table_ranked_extended :
    forall before after table,
      rank_extends before after ->
      set_table_ranked before table ->
      set_table_ranked after table.
  Proof.
    intros before after table Hextends Htable key xs Hlookup.
    eapply set_ranked_extended; [exact Hextends |].
    exact (Htable key xs Hlookup).
  Qed.

  Lemma empty_set_ranked : forall st, set_ranked st S.empty.
  Proof.
    intros st x Hmem. rewrite SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma add_set_ranked :
    forall st xs inserted,
      set_ranked st xs ->
      ranked st inserted ->
      set_ranked st (S.add inserted xs).
  Proof.
    intros st xs inserted Hxs Hinserted x Hmem.
    apply SL.add_spec in Hmem. destruct Hmem as [-> | Hmem]; auto.
  Qed.

  Lemma empty_set_table_ranked :
    forall st, set_table_ranked st (M.empty S.t).
  Proof.
    intros st key xs Hlookup. rewrite ML.lookup_empty in Hlookup.
    discriminate.
  Qed.

  Lemma update_set_table_ranked :
    forall st table key xs,
      set_table_ranked st table ->
      set_ranked st xs ->
      set_table_ranked st (M.update table key xs).
  Proof.
    intros st table key xs Htable Hxs observed found Hlookup.
    destruct (V.eq_dec observed key) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hlookup. inversion Hlookup; subst.
      exact Hxs.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      exact (Htable observed found Hlookup).
  Qed.

  Lemma set_elements_ranked :
    forall st xs,
      set_ranked st xs -> list_ranked st (S.elements xs).
  Proof.
    intros st xs Hset x Hin. apply Hset. now apply SL.mem_spec.
  Qed.

  Definition option_ranked (st : R.state) (x : option V.t) : Prop :=
    match x with
    | Some variable => ranked st variable
    | None => True
    end.

  Definition frame_ranked (st : R.state) (fr : R.frame) : Prop :=
    ranked st (R.frame_owner fr) /\
    set_ranked st (R.frame_previous_targets fr) /\
    set_ranked st (R.frame_current_targets fr) /\
    ranked st (R.frame_min_scope fr) /\
    option_ranked st (R.frame_max_read fr).

  Fixpoint continuation_ranked (st : R.state) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop | R.KSeedLoop _ => True
    | R.KAfterGet fr target _ rest =>
        frame_ranked st fr /\ ranked st target /\ continuation_ranked st rest
    | R.KAfterSide fr _ rest
    | R.KAfterSpawn fr _ rest
    | R.KDrain fr rest =>
        frame_ranked st fr /\ continuation_ranked st rest
    | R.KDead fr _ remaining rest =>
        frame_ranked st fr /\ list_ranked st remaining /\
        continuation_ranked st rest
    end.

  Definition control_ranked (st : R.state) (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
    | R.StartEpisode owner k =>
        ranked st owner /\ continuation_ranked st k
    | R.RunRhs fr _ k
    | R.RunCommit fr _ k
    | R.RunDrain fr k =>
        frame_ranked st fr /\ continuation_ranked st k
    | R.RunDead fr _ remaining k =>
        frame_ranked st fr /\ list_ranked st remaining /\
        continuation_ranked st k
    | R.Return k => continuation_ranked st k
    end.

  Lemma option_ranked_extended :
    forall before after x,
      rank_extends before after ->
      option_ranked before x -> option_ranked after x.
  Proof.
    intros before after [x |] Hextends Hx; cbn in *; auto.
    exact (@ranked_extended before after x Hextends Hx).
  Qed.

  Lemma frame_ranked_extended :
    forall before after fr,
      rank_extends before after ->
      frame_ranked before fr -> frame_ranked after fr.
  Proof.
    intros before after fr Hextends
      [Howner [Hprevious [Hcurrent [Hminimum Hmaximum]]]].
    repeat split;
      eauto using ranked_extended, set_ranked_extended,
        option_ranked_extended.
  Qed.

  Lemma continuation_ranked_extended :
    forall before after k,
      rank_extends before after ->
      continuation_ranked before k -> continuation_ranked after k.
  Proof.
    intros before after k Hextends. induction k; cbn; intuition;
      eauto using frame_ranked_extended, ranked_extended,
        list_ranked_extended.
  Qed.

  Lemma control_ranked_extended :
    forall before after control,
      rank_extends before after ->
      control_ranked before control -> control_ranked after control.
  Proof.
    intros before after control Hextends. destruct control; cbn; intuition;
      eauto using frame_ranked_extended, ranked_extended,
        list_ranked_extended, continuation_ranked_extended.
  Qed.

  Lemma lookup_set_ranked :
    forall st table key,
      set_table_ranked st table -> set_ranked st (R.lookup_set table key).
  Proof.
    intros st table key Htable. unfold R.lookup_set.
    destruct (M.lookup table key) as [xs |] eqn:Hlookup.
    - exact (Htable key xs Hlookup).
    - apply empty_set_ranked.
  Qed.

  Lemma fresh_frame_ranked :
    forall st owner phase,
      ranked st owner ->
      set_table_ranked st (R.last_targets st) ->
      frame_ranked st (R.fresh_frame st owner phase).
  Proof.
    intros st owner phase Howner Htargets. unfold frame_ranked.
    cbn. repeat split; try exact Howner; try apply empty_set_ranked.
    now apply lookup_set_ranked.
  Qed.

  Lemma with_frame_phase_ranked :
    forall st fr phase,
      frame_ranked st fr -> frame_ranked st (R.with_frame_phase fr phase).
  Proof. intros st fr phase Hfr. exact Hfr. Qed.

  Lemma with_frame_read_ranked :
    forall st fr minimum maximum,
      frame_ranked st fr ->
      ranked st minimum -> option_ranked st maximum ->
      frame_ranked st (R.with_frame_read fr minimum maximum).
  Proof.
    intros st fr minimum maximum
      [Howner [Hprevious [Hcurrent [_ _]]]] Hminimum Hmaximum.
    repeat split; assumption.
  Qed.
  Lemma with_frame_side_ranked :
    forall st fr target input,
      frame_ranked st fr ->
      ranked st target ->
      frame_ranked st (R.with_frame_side fr target input).
  Proof.
    intros st fr target input
      [Howner [Hprevious [Hcurrent [Hminimum Hmaximum]]]] Htarget.
    repeat split; try assumption.
    now apply add_set_ranked.
  Qed.

  Lemma record_side_input_ranked :
    forall st fr target raw next_fr input,
      frame_ranked st fr -> ranked st target ->
      R.record_side_input fr target raw = (next_fr, input) ->
      frame_ranked st next_fr.
  Proof.
    intros st fr target raw next_fr input Hframe Htarget Hrecord.
    unfold R.record_side_input in Hrecord. inversion Hrecord; subst.
    now apply with_frame_side_ranked.
  Qed.

  Record state_data_ranked (st : R.state) : Prop := {
    data_queue_ranked : queue_ranked st;
    data_readers_ranked : set_table_ranked st (R.readers st);
    data_targets_ranked : set_table_ranked st (R.last_targets st);
    data_deferred_ranked : list_ranked st (R.deferred_wakes st);
  }.

  Lemma empty_state_data_ranked : state_data_ranked R.empty_state.
  Proof.
    constructor; cbn.
    - intros x Hin. inversion Hin.
    - apply empty_set_table_ranked.
    - apply empty_set_table_ranked.
    - apply empty_queue_ranked.
  Qed.

  Lemma state_data_ranked_preserved :
    forall before after,
      rank_extends before after ->
      R.queue after = R.queue before ->
      R.readers after = R.readers before ->
      R.last_targets after = R.last_targets before ->
      R.deferred_wakes after = R.deferred_wakes before ->
      state_data_ranked before -> state_data_ranked after.
  Proof.
    intros before after Hextends Hqueue Hreaders Htargets Hdeferred
      [Hqueue_ranked Hreaders_ranked Htargets_ranked Hdeferred_ranked].
    constructor.
    - intros x Hin. apply ranked_extended with before; [exact Hextends |].
      apply Hqueue_ranked. now rewrite <- Hqueue.
    - rewrite Hreaders. now apply set_table_ranked_extended with before.
    - rewrite Htargets. now apply set_table_ranked_extended with before.
    - rewrite Hdeferred. now apply list_ranked_extended with before.
  Qed.

  Lemma state_data_ranked_observe :
    forall st x,
      state_data_ranked st -> state_data_ranked (R.observe st x).
  Proof.
    intros st x Hdata. apply state_data_ranked_preserved with st.
    - eapply rank_extends_observe. reflexivity.
    - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
      reflexivity.
    - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
      reflexivity.
    - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
      reflexivity.
    - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
      reflexivity.
    - exact Hdata.
  Qed.

  Lemma state_data_ranked_with_queue :
    forall st queue,
      state_data_ranked st ->
      list_ranked st queue ->
      state_data_ranked (R.with_queue st queue).
  Proof.
    intros st queue [Hold Hreaders Htargets Hdeferred] Hqueue.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_enqueue :
    forall st x,
      state_data_ranked st -> ranked st x ->
      state_data_ranked (R.enqueue st x).
  Proof.
    intros st x [Hqueue Hreaders Htargets Hdeferred] Hx.
    constructor; cbn.
    - now apply enqueue_ranked.
    - exact Hreaders.
    - exact Htargets.
    - exact Hdeferred.
  Qed.

  Lemma state_data_ranked_enqueue_all :
    forall st xs,
      state_data_ranked st -> list_ranked st xs ->
      state_data_ranked (R.enqueue_all st xs).
  Proof.
    intros st xs [Hqueue Hreaders Htargets Hdeferred] Hxs.
    constructor; cbn.
    - now apply enqueue_all_ranked.
    - exact Hreaders.
    - exact Htargets.
    - exact Hdeferred.
  Qed.

  Lemma state_data_ranked_with_deferred_wakes :
    forall st wakes,
      state_data_ranked st -> list_ranked st wakes ->
      state_data_ranked (R.with_deferred_wakes st wakes).
  Proof.
    intros st wakes [Hqueue Hreaders Htargets Hold] Hwakes.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_defer_all :
    forall st xs,
      state_data_ranked st -> list_ranked st xs ->
      state_data_ranked (R.defer_all st xs).
  Proof.
    intros st xs Hdata Hxs. unfold R.defer_all.
    apply state_data_ranked_with_deferred_wakes; [exact Hdata |].
    intros x Hin. apply queue_insert_all_members in Hin.
    destruct Hin as [Hin | Hin].
    - now apply Hxs.
    - now apply (data_deferred_ranked Hdata).
  Qed.

  Lemma state_data_ranked_flush_deferred :
    forall st,
      state_data_ranked st -> state_data_ranked (R.flush_deferred st).
  Proof.
    intros st Hdata. unfold R.flush_deferred.
    apply state_data_ranked_with_deferred_wakes.
    - apply state_data_ranked_enqueue_all; [exact Hdata |].
      exact (data_deferred_ranked Hdata).
    - intros x Hin. inversion Hin.
  Qed.

  Lemma state_data_ranked_materialize :
    forall st x,
      state_data_ranked st -> state_data_ranked (R.materialize st x).
  Proof.
    intros st x Hdata. apply state_data_ranked_preserved with st.
    - apply rank_extends_materialize.
    - unfold R.materialize. destruct (M.lookup (R.sigma st) x); reflexivity.
    - unfold R.materialize. destruct (M.lookup (R.sigma st) x); reflexivity.
    - unfold R.materialize. destruct (M.lookup (R.sigma st) x); reflexivity.
    - unfold R.materialize. destruct (M.lookup (R.sigma st) x); reflexivity.
    - exact Hdata.
  Qed.

  Lemma state_data_ranked_with_readers :
    forall st readers,
      state_data_ranked st ->
      set_table_ranked st readers ->
      state_data_ranked (R.with_readers st readers).
  Proof.
    intros st readers [Hqueue Hreaders Htargets Hdeferred] Hnext.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_last_targets :
    forall st targets,
      state_data_ranked st ->
      set_table_ranked st targets ->
      state_data_ranked (R.with_last_targets st targets).
  Proof.
    intros st targets [Hqueue Hreaders Hold Hdeferred] Hnext.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_sigma :
    forall st sigma,
      state_data_ranked st -> state_data_ranked (R.with_sigma st sigma).
  Proof.
    intros st sigma [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_contributions :
    forall st contributions,
      state_data_ranked st ->
      state_data_ranked (R.with_contributions st contributions).
  Proof.
    intros st contributions [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_cells_and_resets :
    forall st cells resets,
      state_data_ranked st ->
      state_data_ranked (R.with_cells_and_resets st cells resets).
  Proof.
    intros st cells resets [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_controlled :
    forall st controlled,
      state_data_ranked st ->
      state_data_ranked (R.with_controlled st controlled).
  Proof.
    intros st controlled [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_dirty_side_targets :
    forall st dirty,
      state_data_ranked st ->
      state_data_ranked (R.with_dirty_side_targets st dirty).
  Proof.
    intros st dirty [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_mark_side_dirty :
    forall st target,
      state_data_ranked st -> state_data_ranked (R.mark_side_dirty st target).
  Proof. intros. now apply state_data_ranked_with_dirty_side_targets. Qed.

  Lemma state_data_ranked_clear_side_dirty :
    forall st target,
      state_data_ranked st -> state_data_ranked (R.clear_side_dirty st target).
  Proof. intros. now apply state_data_ranked_with_dirty_side_targets. Qed.

  Lemma state_data_ranked_cancel_dirty_target :
    forall st target,
      state_data_ranked st ->
      state_data_ranked (R.cancel_dirty_target st target).
  Proof.
    intros st target Hdata. unfold R.cancel_dirty_target.
    apply state_data_ranked_clear_side_dirty.
    apply state_data_ranked_with_queue; [exact Hdata |].
    intros x Hin. apply (data_queue_ranked Hdata x).
    now apply queue_remove_members in Hin.
  Qed.

  Lemma state_data_ranked_with_dormant_bottom :
    forall st dormant,
      state_data_ranked st ->
      state_data_ranked (R.with_dormant_bottom st dormant).
  Proof.
    intros st dormant [Hqueue Hreaders Htargets Hdeferred].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_remember_dormant :
    forall st variable,
      state_data_ranked st ->
      state_data_ranked (R.remember_dormant st variable).
  Proof. intros. now apply state_data_ranked_with_dormant_bottom. Qed.

  Lemma state_data_ranked_promote_controlled :
    forall st x,
      state_data_ranked st ->
      state_data_ranked (R.promote_controlled st x).
  Proof. intros. now apply state_data_ranked_with_controlled. Qed.

  Lemma state_data_ranked_promote_side_target :
    forall st fr target,
      state_data_ranked st ->
      state_data_ranked (R.promote_side_target st fr target).
  Proof.
    intros st fr target Hdata. unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr));
      [exact Hdata | now apply state_data_ranked_promote_controlled].
  Qed.

  Lemma state_data_ranked_register_reset :
    forall st source target scope phase,
      state_data_ranked st ->
      state_data_ranked (R.register_reset st source target scope phase).
  Proof.
    intros. unfold R.register_reset.
    now apply state_data_ranked_with_cells_and_resets.
  Qed.

  Lemma state_data_ranked_write_side_contribution :
    forall st fr target input next changed,
      state_data_ranked st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      state_data_ranked next.
  Proof.
    intros st fr target input next changed Hdata Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted eqn:Hpromoted.
    inversion Hwrite; subst; cbn.
    apply state_data_ranked_register_reset.
    apply state_data_ranked_with_contributions.
    now apply state_data_ranked_promote_side_target.
  Qed.

  Lemma frame_ranked_write_side_contribution :
    forall st fr target input next changed,
      frame_ranked st fr ->
      R.write_side_contribution st fr target input = (next, changed) ->
      frame_ranked next fr.
  Proof.
    intros st fr target input next changed Hframe Hwrite.
    eapply frame_ranked_extended; [|exact Hframe].
    eapply rank_extends_write_side_contribution. exact Hwrite.
  Qed.

  Lemma state_data_ranked_publish_targets :
    forall st fr,
      state_data_ranked st ->
      frame_ranked st fr ->
      state_data_ranked (R.publish_targets st fr).
  Proof.
    intros st fr Hdata Hframe. unfold R.publish_targets.
    apply state_data_ranked_with_last_targets; [exact Hdata |].
    apply update_set_table_ranked.
    - exact (data_targets_ranked Hdata).
    - exact (proj1 (proj2 (proj2 Hframe))).
  Qed.

  Lemma state_data_ranked_reset_registered_cells :
    forall st owner,
      state_data_ranked st ->
      state_data_ranked (R.reset_registered_cells st owner).
  Proof.
    intros st owner Hdata. unfold R.reset_registered_cells.
    destruct Features.restart_side_phases; cbn; [|exact Hdata].
    now apply state_data_ranked_with_cells_and_resets.
  Qed.

  Lemma rank_extends_reset_registered_cells :
    forall st owner,
      rank_extends st (R.reset_registered_cells st owner).
  Proof.
    intros st owner. unfold R.reset_registered_cells.
    destruct Features.restart_side_phases; cbn.
    - apply rank_extends_with_cells_and_resets.
    - apply rank_extends_refl.
  Qed.

  Lemma state_data_ranked_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.with_readers st
          (M.update (R.readers st) target
            (S.add owner (R.lookup_set (R.readers st) target)))).
  Proof.
    intros st owner target Hdata Howner.
    apply state_data_ranked_with_readers; [exact Hdata |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hdata).
    - apply add_set_ranked; [|exact Howner].
      now apply lookup_set_ranked, data_readers_ranked.
  Qed.

  Lemma state_data_ranked_add_reader_named :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked (R.add_reader st target owner).
  Proof. intros. unfold R.add_reader. now apply state_data_ranked_add_reader. Qed.

  Lemma state_data_ranked_remember_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.add_reader (R.remember_dormant st target) target owner).
  Proof.
    intros st owner target Hdata Howner.
    apply state_data_ranked_add_reader_named.
    - now apply state_data_ranked_remember_dormant.
    - exact Howner.
  Qed.

  Lemma state_data_ranked_observe_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.materialize
          (R.with_readers (R.observe st target)
            (M.update (R.readers (R.observe st target)) target
              (S.add owner
                (R.lookup_set (R.readers (R.observe st target)) target))))
          target).
  Proof.
    intros st owner target Hdata Howner.
    apply state_data_ranked_materialize.
    apply state_data_ranked_add_reader.
    - now apply state_data_ranked_observe.
    - eapply ranked_extended.
      + eapply rank_extends_observe. reflexivity.
      + exact Howner.
  Qed.

  Lemma state_data_ranked_observe_enqueue_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.materialize
          (R.with_readers (R.enqueue (R.observe st target) target)
            (M.update (R.readers (R.observe st target)) target
              (S.add owner
                (R.lookup_set (R.readers (R.observe st target)) target))))
          target).
  Proof.
    intros st owner target Hdata Howner.
    set (observed := R.observe st target).
    assert (state_data_ranked observed) as Hobserved.
    { unfold observed. now apply state_data_ranked_observe. }
    assert (ranked observed target) as Htarget.
    { unfold observed. eapply observe_ranks_variable. reflexivity. }
    set (queued := R.enqueue observed target).
    assert (state_data_ranked queued) as Hqueued.
    { unfold queued. now apply state_data_ranked_enqueue. }
    apply state_data_ranked_materialize.
    apply state_data_ranked_with_readers; [exact Hqueued |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hqueued).
    - apply add_set_ranked.
      + apply lookup_set_ranked. exact (data_readers_ranked Hobserved).
      + eapply ranked_extended.
        * eapply rank_extends_trans.
          -- unfold observed. eapply rank_extends_observe. reflexivity.
          -- apply rank_extends_enqueue.
        * exact Howner.
  Qed.

  Lemma state_data_ranked_observe_promote_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.materialize
          (R.with_readers (R.promote_controlled (R.observe st target) target)
            (M.update (R.readers (R.observe st target)) target
              (S.add owner
                (R.lookup_set (R.readers (R.observe st target)) target))))
          target).
  Proof.
    intros st owner target Hdata Howner.
    set (observed := R.observe st target).
    assert (state_data_ranked observed) as Hobserved.
    { unfold observed. now apply state_data_ranked_observe. }
    set (promoted := R.promote_controlled observed target).
    assert (state_data_ranked promoted) as Hpromoted.
    { unfold promoted. now apply state_data_ranked_promote_controlled. }
    apply state_data_ranked_materialize.
    apply state_data_ranked_with_readers; [exact Hpromoted |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hpromoted).
    - apply add_set_ranked.
      + apply lookup_set_ranked. exact (data_readers_ranked Hobserved).
      + eapply ranked_extended.
        * eapply rank_extends_trans.
          -- unfold observed. eapply rank_extends_observe. reflexivity.
          -- apply rank_extends_promote_controlled.
        * exact Howner.
  Qed.

  Lemma state_data_ranked_observe_enqueue_promote_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.materialize
          (R.with_readers
            (R.promote_controlled (R.enqueue (R.observe st target) target)
              target)
            (M.update (R.readers (R.observe st target)) target
              (S.add owner
                (R.lookup_set (R.readers (R.observe st target)) target))))
          target).
  Proof.
    intros st owner target Hdata Howner.
    set (observed := R.observe st target).
    assert (state_data_ranked observed) as Hobserved.
    { unfold observed. now apply state_data_ranked_observe. }
    assert (ranked observed target) as Htarget.
    { unfold observed. eapply observe_ranks_variable. reflexivity. }
    set (queued := R.enqueue observed target).
    assert (state_data_ranked queued) as Hqueued.
    { unfold queued. now apply state_data_ranked_enqueue. }
    set (promoted := R.promote_controlled queued target).
    assert (state_data_ranked promoted) as Hpromoted.
    { unfold promoted. now apply state_data_ranked_promote_controlled. }
    apply state_data_ranked_materialize.
    apply state_data_ranked_with_readers; [exact Hpromoted |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hpromoted).
    - apply add_set_ranked.
      + apply lookup_set_ranked. exact (data_readers_ranked Hobserved).
      + eapply ranked_extended.
        * eapply rank_extends_trans.
          -- unfold observed. eapply rank_extends_observe. reflexivity.
          -- eapply rank_extends_trans.
             ++ apply rank_extends_enqueue.
             ++ apply rank_extends_promote_controlled.
        * exact Howner.
  Qed.

  Lemma state_data_ranked_promote_add_reader :
    forall st owner target,
      state_data_ranked st -> ranked st owner ->
      state_data_ranked
        (R.materialize
          (R.with_readers (R.promote_controlled st target)
            (M.update (R.readers st) target
              (S.add owner (R.lookup_set (R.readers st) target))))
          target).
  Proof.
    intros st owner target Hdata Howner.
    set (promoted := R.promote_controlled st target).
    assert (state_data_ranked promoted) as Hpromoted.
    { unfold promoted. now apply state_data_ranked_promote_controlled. }
    apply state_data_ranked_materialize.
    apply state_data_ranked_with_readers; [exact Hpromoted |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hpromoted).
    - apply add_set_ranked.
      + apply lookup_set_ranked. exact (data_readers_ranked Hdata).
      + eapply ranked_extended.
        * apply rank_extends_promote_controlled.
        * exact Howner.
  Qed.

  Lemma rank_extends_complete_get :
    forall st fr target next next_fr value,
      R.complete_get st fr target = (next, next_fr, value) ->
      rank_extends st next.
  Proof.
    intros st fr target next next_fr value Hcomplete variable rank Hlookup.
    unfold R.complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      inversion Hcomplete; subst; cbn;
      unfold R.materialize; destruct (M.lookup _ target); cbn;
      exact Hlookup.
  Qed.

  Lemma state_data_ranked_complete_get :
    forall st fr target next next_fr value,
      state_data_ranked st -> frame_ranked st fr -> ranked st target ->
      R.complete_get st fr target = (next, next_fr, value) ->
      state_data_ranked next.
  Proof.
    intros st fr target next next_fr value Hdata Hframe Htarget Hcomplete.
    unfold R.complete_get in Hcomplete.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    assert (state_data_ranked base) as Hbase.
    { unfold base. destruct (R.rank_lt st (R.frame_owner fr) target).
      - exact Hdata.
      - now apply state_data_ranked_promote_controlled. }
    assert (rank_extends st base) as Hextends.
    { unfold base. destruct (R.rank_lt st (R.frame_owner fr) target).
      - apply rank_extends_refl.
      - apply rank_extends_promote_controlled. }
    destruct (R.rank_lt st target (R.frame_min_scope fr));
      destruct (R.frame_max_read fr) as [previous |];
      try destruct (R.rank_lt st previous target);
      inversion Hcomplete; subst; cbn.
    all: apply state_data_ranked_materialize.
    all: apply state_data_ranked_add_reader; [exact Hbase |].
    all: eapply ranked_extended; [exact Hextends | exact (proj1 Hframe)].
  Qed.

  Lemma frame_ranked_complete_get :
    forall st fr target next next_fr value,
      frame_ranked st fr -> ranked st target ->
      R.complete_get st fr target = (next, next_fr, value) ->
      frame_ranked next next_fr.
  Proof.
    intros st fr target next next_fr value Hframe Htarget Hcomplete.
    pose proof Hframe as Hparts.
    destruct Hparts as
      [Howner [Hprevious [Hcurrent [Hminimum_ranked Hmaximum_ranked]]]].
    assert (rank_extends st next) as Hextends.
    { eapply rank_extends_complete_get. exact Hcomplete. }
    unfold R.complete_get in Hcomplete.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in Hcomplete.
    destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hminimum;
      destruct (R.frame_max_read fr) as [previous |] eqn:Hmaximum;
      try destruct (R.rank_lt st previous target) eqn:Hlarger;
      inversion Hcomplete; subst; cbn.
    all: apply frame_ranked_extended with st; [exact Hextends |].
    all: apply with_frame_read_ranked; [exact Hframe | |]; cbn.
    all: try exact Htarget.
    all: try exact Hminimum_ranked.
    all: exact Hmaximum_ranked.
  Qed.

  Lemma state_data_ranked_write_dirty_value_pre :
    forall st target value,
      state_data_ranked st ->
      state_data_ranked (R.write_dirty_value st target value).
  Proof.
    intros st target value Hdata. unfold R.write_dirty_value. cbn.
    set (st1 := R.with_sigma st (M.update (R.sigma st) target value)).
    assert (state_data_ranked st1) as Hst1.
    { unfold st1. now apply state_data_ranked_with_sigma. }
    set (invalidated := S.elements (R.lookup_set (R.readers st1) target)).
    assert (list_ranked st1 invalidated) as Hinvalidated.
    { unfold invalidated. apply set_elements_ranked.
      apply lookup_set_ranked. exact (data_readers_ranked Hst1). }
    set (st2 := R.defer_all st1 invalidated).
    assert (state_data_ranked st2) as Hst2.
    { unfold st2. now apply state_data_ranked_defer_all. }
    constructor; cbn.
    - exact (data_queue_ranked Hst2).
    - apply update_set_table_ranked.
      + exact (data_readers_ranked Hst2).
      + apply empty_set_ranked.
    - exact (data_targets_ranked Hst2).
    - exact (data_deferred_ranked Hst2).
  Qed.

  Lemma state_data_ranked_try_dirty_read_pre :
    forall tf st owner target next,
      state_data_ranked st ->
      R.try_dirty_read tf st owner target = Some next ->
      state_data_ranked next.
  Proof.
    intros tf st owner target next Hdata Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using state_data_ranked_promote_controlled,
        state_data_ranked_cancel_dirty_target,
        state_data_ranked_write_dirty_value_pre.
  Qed.

  Lemma rank_extends_dirty_complete_get :
    forall tf st fr target next next_fr value,
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      rank_extends st next.
  Proof.
    intros tf st fr target next next_fr value Hcomplete.
    unfold R.dirty_complete_get in Hcomplete.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    assert (rank_extends st base) as Hbase.
    { unfold base. apply rank_extends_get_control_state. }
    set (prepared := R.materialize base target) in *.
    assert (rank_extends base prepared) as Hprepared.
    { unfold prepared. apply rank_extends_materialize. }
    destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
      as [flushed |] eqn:Hflush.
    - destruct (R.rank_lt st target (R.frame_min_scope fr));
        destruct (R.frame_max_read fr) as [previous |];
        try destruct (R.rank_lt st previous target);
        inversion Hcomplete; subst; cbn.
      all: eapply rank_extends_trans; [exact Hbase |].
      all: eapply rank_extends_trans; [exact Hprepared |].
      all: eapply rank_extends_trans;
        [eapply rank_extends_try_dirty_read; exact Hflush
        |apply rank_extends_add_reader].
    - destruct (R.rank_lt st target (R.frame_min_scope fr));
        destruct (R.frame_max_read fr) as [previous |];
        try destruct (R.rank_lt st previous target);
        inversion Hcomplete; subst; cbn.
      all: eapply rank_extends_trans; [exact Hbase |].
      all: eapply rank_extends_trans; [exact Hprepared |].
      all: apply rank_extends_add_reader.
  Qed.

  Lemma rank_valid_dirty_complete_get :
    forall tf st fr target next next_fr value,
      rank_valid st ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      rank_valid next.
  Proof.
    intros tf st fr target next next_fr value Hvalid Hcomplete.
    unfold R.dirty_complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      inversion Hcomplete; subst; cbn.
    all: apply rank_valid_add_reader.
    all: try (eapply rank_valid_try_dirty_read; [|eassumption]).
    all: apply rank_valid_materialize.
    all: try exact Hvalid.
    all: apply rank_valid_promote_controlled; exact Hvalid.
  Qed.

  Lemma state_data_ranked_dirty_complete_get :
    forall tf st fr target next next_fr value,
      state_data_ranked st -> frame_ranked st fr -> ranked st target ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      state_data_ranked next.
  Proof.
    intros tf st fr target next next_fr value Hdata Hframe Htarget Hcomplete.
    unfold R.dirty_complete_get in Hcomplete.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    assert (state_data_ranked base) as Hbase.
    { unfold base. destruct (R.rank_lt st (R.frame_owner fr) target);
        [exact Hdata |now apply state_data_ranked_promote_controlled]. }
    assert (rank_extends st base) as Hbase_extends.
    { unfold base. destruct (R.rank_lt st (R.frame_owner fr) target);
        [apply rank_extends_refl |apply rank_extends_promote_controlled]. }
    set (prepared := R.materialize base target) in *.
    assert (state_data_ranked prepared) as Hprepared.
    { unfold prepared. now apply state_data_ranked_materialize. }
    assert (ranked prepared (R.frame_owner fr)) as Howner.
    { eapply ranked_extended.
      - eapply rank_extends_trans; [exact Hbase_extends |].
        apply rank_extends_materialize.
      - exact (proj1 Hframe). }
    destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
      as [flushed |] eqn:Hflush.
    - assert (state_data_ranked flushed) as Hflushed.
      { eapply state_data_ranked_try_dirty_read_pre; eauto. }
      assert (ranked flushed (R.frame_owner fr)) as Howner_flushed.
      { eapply ranked_extended; [|exact Howner].
        eapply rank_extends_try_dirty_read. exact Hflush. }
      destruct (R.rank_lt st target (R.frame_min_scope fr));
        destruct (R.frame_max_read fr) as [previous |];
        try destruct (R.rank_lt st previous target);
        inversion Hcomplete; subst; cbn;
        now apply state_data_ranked_add_reader_named.
    - destruct (R.rank_lt st target (R.frame_min_scope fr));
        destruct (R.frame_max_read fr) as [previous |];
        try destruct (R.rank_lt st previous target);
        inversion Hcomplete; subst; cbn;
        now apply state_data_ranked_add_reader_named.
  Qed.

  Lemma frame_ranked_dirty_complete_get :
    forall tf st fr target next next_fr value,
      frame_ranked st fr -> ranked st target ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      frame_ranked next next_fr.
  Proof.
    intros tf st fr target next next_fr value Hframe Htarget Hcomplete.
    pose proof Hframe as Hparts.
    destruct Hparts as
      [Howner [Hprevious [Hcurrent [Hminimum_ranked Hmaximum_ranked]]]].
    assert (rank_extends st next) as Hextends.
    { eapply rank_extends_dirty_complete_get. exact Hcomplete. }
    unfold R.dirty_complete_get in Hcomplete.
    destruct (R.rank_lt st (R.frame_owner fr) target);
      destruct (R.rank_lt st target (R.frame_min_scope fr));
      destruct (R.frame_max_read fr) as [previous |];
      try destruct (R.rank_lt st previous target);
      repeat
        match type of Hcomplete with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        end;
      inversion Hcomplete; subst; cbn.
    all: apply frame_ranked_extended with st; [exact Hextends |].
    all: apply with_frame_read_ranked; [exact Hframe | |]; cbn.
    all: try exact Htarget.
    all: try exact Hminimum_ranked.
    all: exact Hmaximum_ranked.
  Qed.

  Lemma state_data_ranked_complete_get_after_observe :
    forall st fr target next next_fr value,
      state_data_ranked st -> frame_ranked st fr ->
      R.complete_get
        (if R.is_materialized (R.observe st target) target
         then R.observe st target
         else R.enqueue (R.observe st target) target)
        fr target = (next, next_fr, value) ->
      state_data_ranked next.
  Proof.
    intros st fr target next next_fr value Hdata Hframe Hcomplete.
    set (observed := R.observe st target) in *.
    set (base := if R.is_materialized observed target
      then observed else R.enqueue observed target) in *.
    assert (state_data_ranked observed) as Hobserved.
    { unfold observed. now apply state_data_ranked_observe. }
    assert (ranked observed target) as Htarget.
    { unfold observed. eapply observe_ranks_variable. reflexivity. }
    assert (state_data_ranked base) as Hbase.
    { unfold base. destruct (R.is_materialized observed target).
      - exact Hobserved.
      - now apply state_data_ranked_enqueue. }
    assert (rank_extends st base) as Hextends.
    { eapply rank_extends_trans.
      - unfold observed. eapply rank_extends_observe. reflexivity.
      - unfold base. destruct (R.is_materialized observed target).
        + apply rank_extends_refl.
        + apply rank_extends_enqueue. }
    eapply state_data_ranked_complete_get; [exact Hbase | | |exact Hcomplete].
    - now apply frame_ranked_extended with st.
    - eapply (@ranked_extended observed base target).
      + unfold base. destruct (R.is_materialized observed target).
        * apply rank_extends_refl.
        * exact (@rank_extends_enqueue observed target).
      + exact Htarget.
  Qed.

  Lemma control_ranked_complete_get :
    forall st fr target next next_fr value k,
      frame_ranked st fr -> ranked st target -> continuation_ranked st k ->
      R.complete_get st fr target = (next, next_fr, value) ->
      frame_ranked next next_fr /\ continuation_ranked next k.
  Proof.
    intros st fr target next next_fr value k Hframe Htarget Hk Hcomplete.
    split.
    - eapply frame_ranked_complete_get; eauto.
    - eapply continuation_ranked_extended.
      + eapply rank_extends_complete_get. exact Hcomplete.
      + exact Hk.
  Qed.

  Lemma control_ranked_dirty_complete_get :
    forall tf st fr target next next_fr value k,
      frame_ranked st fr -> ranked st target -> continuation_ranked st k ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      frame_ranked next next_fr /\ continuation_ranked next k.
  Proof.
    intros tf st fr target next next_fr value k Hframe Htarget Hk Hcomplete.
    split.
    - eapply frame_ranked_dirty_complete_get; eauto.
    - eapply continuation_ranked_extended.
      + eapply rank_extends_dirty_complete_get. exact Hcomplete.
      + exact Hk.
  Qed.

  Lemma control_ranked_complete_get_after_observe :
    forall st fr target next next_fr value k,
      frame_ranked st fr -> continuation_ranked st k ->
      R.complete_get
        (if R.is_materialized (R.observe st target) target
         then R.observe st target
         else R.enqueue (R.observe st target) target)
        fr target = (next, next_fr, value) ->
      frame_ranked next next_fr /\ continuation_ranked next k.
  Proof.
    intros st fr target next next_fr value k Hframe Hk Hcomplete.
    set (observed := R.observe st target) in *.
    set (base := if R.is_materialized observed target
      then observed else R.enqueue observed target) in *.
    assert (rank_extends st observed) as Hobserve.
    { unfold observed. eapply rank_extends_observe. reflexivity. }
    assert (ranked observed target) as Htarget_observed.
    { unfold observed. eapply observe_ranks_variable. reflexivity. }
    assert (rank_extends observed base) as Hbase.
    { unfold base. destruct (R.is_materialized observed target).
      - apply rank_extends_refl.
      - apply rank_extends_enqueue. }
    eapply control_ranked_complete_get with (st := base) (target := target).
    - apply frame_ranked_extended with st; [|exact Hframe].
      eapply rank_extends_trans; [exact Hobserve | exact Hbase].
    - now apply ranked_extended with observed.
    - apply continuation_ranked_extended with st; [|exact Hk].
      eapply rank_extends_trans; [exact Hobserve | exact Hbase].
    - exact Hcomplete.
  Qed.

  Lemma state_data_ranked_commit_value :
    forall st owner value,
      state_data_ranked st ->
      state_data_ranked
        (let st1 := R.with_sigma st (M.update (R.sigma st) owner value) in
         let invalidated := S.elements (R.lookup_set (R.readers st1) owner) in
         let st2 := R.enqueue_all st1 invalidated in
         R.with_readers st2 (M.update (R.readers st2) owner S.empty)).
  Proof.
    intros st owner value Hdata. cbn.
    set (st1 := R.with_sigma st (M.update (R.sigma st) owner value)).
    assert (state_data_ranked st1) as Hst1.
    { unfold st1. now apply state_data_ranked_with_sigma. }
    set (invalidated := S.elements (R.lookup_set (R.readers st1) owner)).
    assert (list_ranked st1 invalidated) as Hinvalidated.
    { unfold invalidated. apply set_elements_ranked.
      apply lookup_set_ranked. exact (data_readers_ranked Hst1). }
    set (st2 := R.enqueue_all st1 invalidated).
    assert (state_data_ranked st2) as Hst2.
    { unfold st2. now apply state_data_ranked_enqueue_all. }
    apply state_data_ranked_with_readers; [exact Hst2 |].
    apply update_set_table_ranked.
    - exact (data_readers_ranked Hst2).
    - apply empty_set_ranked.
  Qed.

  Lemma state_data_ranked_write_dirty_value :
    forall st target value,
      state_data_ranked st ->
      state_data_ranked (R.write_dirty_value st target value).
  Proof.
    intros st target value Hdata. unfold R.write_dirty_value. cbn.
    set (st1 := R.with_sigma st (M.update (R.sigma st) target value)).
    assert (state_data_ranked st1) as Hst1.
    { unfold st1. now apply state_data_ranked_with_sigma. }
    set (invalidated := S.elements (R.lookup_set (R.readers st1) target)).
    assert (list_ranked st1 invalidated) as Hinvalidated.
    { unfold invalidated. apply set_elements_ranked.
      apply lookup_set_ranked. exact (data_readers_ranked Hst1). }
    set (st2 := R.defer_all st1 invalidated).
    assert (state_data_ranked st2) as Hst2.
    { unfold st2. now apply state_data_ranked_defer_all. }
    constructor; cbn.
    - exact (data_queue_ranked Hst2).
    - apply update_set_table_ranked.
      + exact (data_readers_ranked Hst2).
      + apply empty_set_ranked.
    - exact (data_targets_ranked Hst2).
    - exact (data_deferred_ranked Hst2).
  Qed.

  Lemma state_data_ranked_try_dirty_read :
    forall tf st owner target next,
      state_data_ranked st ->
      R.try_dirty_read tf st owner target = Some next ->
      state_data_ranked next.
  Proof.
    intros tf st owner target next Hdata Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using state_data_ranked_promote_controlled,
        state_data_ranked_cancel_dirty_target,
        state_data_ranked_write_dirty_value.
  Qed.

  Lemma state_data_ranked_publish_dormant_target :
    forall st target changed,
      state_data_ranked st ->
      state_data_ranked (R.publish_dormant_target st target changed).
  Proof.
    intros st target changed Hdata.
    unfold R.publish_dormant_target.
    remember (R.materialize st target) as st1 eqn:Hst1.
    assert (state_data_ranked st1) as Hdata1.
    { rewrite Hst1. now apply state_data_ranked_materialize. }
    destruct changed.
    - now apply state_data_ranked_commit_value.
    - exact Hdata1.
  Qed.

  Lemma state_data_ranked_set_value :
    forall st fr direct next next_fr,
      state_data_ranked st ->
      R.set_value st fr direct = (next, next_fr) ->
      state_data_ranked next.
  Proof.
    intros st fr direct next next_fr Hdata Hset.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn; try exact Hdata;
      now apply state_data_ranked_commit_value.
  Qed.

  Lemma frame_ranked_set_value :
    forall st fr direct next next_fr,
      frame_ranked st fr ->
      R.set_value st fr direct = (next, next_fr) ->
      frame_ranked next next_fr.
  Proof.
    intros st fr direct next next_fr Hframe Hset.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn;
      auto using with_frame_phase_ranked.
  Qed.

  Lemma state_data_ranked_continue_side :
    forall st fr target next k changed,
      state_data_ranked st -> ranked st target ->
      state_data_ranked
        (R.cfg_state (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed Hdata Htarget.
    unfold R.continue_side.
    repeat destruct (_ : bool); cbn; try exact Hdata.
    now apply state_data_ranked_enqueue.
  Qed.

  Lemma control_ranked_continue_side :
    forall st fr target next k changed,
      frame_ranked st fr -> ranked st target -> continuation_ranked st k ->
      control_ranked
        (R.cfg_state (R.continue_side st fr target next k changed))
        (R.cfg_control (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed Hframe Htarget Hk.
    unfold R.continue_side.
    destruct changed.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))).
      + cbn. exact (conj Htarget (conj Hframe Hk)).
      + cbn. split.
        * now apply frame_ranked_extended with st;
            [apply rank_extends_enqueue |].
        * now apply continuation_ranked_extended with st;
            [apply rank_extends_enqueue |].
    - cbn. now split.
  Qed.

  Lemma control_ranked_continue_side_after_write :
    forall before fr target raw fr1 input next changed body k flag,
      frame_ranked before fr -> continuation_ranked before k ->
      R.record_side_input fr target raw = (fr1, input) ->
      R.write_side_contribution (R.observe before target)
        fr1 target input = (next, changed) ->
      control_ranked
        (R.cfg_state (R.continue_side next fr1 target body k flag))
        (R.cfg_control (R.continue_side next fr1 target body k flag)).
  Proof.
    intros before fr target raw fr1 input next changed body k flag
      Hframe Hk Hrecord Hwrite.
    apply control_ranked_continue_side.
    - eapply frame_ranked_write_side_contribution.
      + eapply record_side_input_ranked.
        * eapply frame_ranked_extended;
            [eapply rank_extends_observe; reflexivity |exact Hframe].
        * eapply observe_ranks_variable. reflexivity.
        * exact Hrecord.
      + exact Hwrite.
    - eapply ranked_extended.
      + eapply rank_extends_write_side_contribution. exact Hwrite.
      + eapply observe_ranks_variable. reflexivity.
    - eapply continuation_ranked_extended.
      + eapply rank_extends_trans.
        * eapply rank_extends_observe. reflexivity.
        * eapply rank_extends_write_side_contribution. exact Hwrite.
      + exact Hk.
  Qed.

  Lemma control_ranked_continue_marked_side_after_write :
    forall before fr target raw fr1 input next changed body k flag,
      frame_ranked before fr -> continuation_ranked before k ->
      R.record_side_input fr target raw = (fr1, input) ->
      R.write_side_contribution (R.observe before target)
        fr1 target input = (next, changed) ->
      control_ranked
        (R.cfg_state
          (R.continue_side (R.mark_side_dirty next target)
            fr1 target body k flag))
        (R.cfg_control
          (R.continue_side (R.mark_side_dirty next target)
            fr1 target body k flag)).
  Proof.
    intros before fr target raw fr1 input next changed body k flag
      Hframe Hk Hrecord Hwrite.
    apply control_ranked_continue_side.
    - eapply frame_ranked_extended.
      + apply rank_extends_mark_side_dirty.
      + eapply frame_ranked_write_side_contribution.
        * eapply record_side_input_ranked.
          -- eapply frame_ranked_extended;
               [eapply rank_extends_observe; reflexivity |exact Hframe].
          -- eapply observe_ranks_variable. reflexivity.
          -- exact Hrecord.
        * exact Hwrite.
    - eapply ranked_extended.
      + apply rank_extends_mark_side_dirty.
      + eapply ranked_extended.
        * eapply rank_extends_write_side_contribution. exact Hwrite.
        * eapply observe_ranks_variable. reflexivity.
    - eapply continuation_ranked_extended.
      + eapply rank_extends_trans.
        * eapply rank_extends_trans.
          -- eapply rank_extends_observe. reflexivity.
          -- eapply rank_extends_write_side_contribution. exact Hwrite.
        * apply rank_extends_mark_side_dirty.
      + exact Hk.
  Qed.

  Lemma state_data_ranked_continue_dead :
    forall st fr direct target remaining k changed,
      state_data_ranked st -> ranked st target ->
      state_data_ranked
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed Hdata Htarget.
    unfold R.continue_dead.
    repeat destruct (_ : bool); cbn; try exact Hdata.
    now apply state_data_ranked_enqueue.
  Qed.

  Lemma control_ranked_continue_dead :
    forall st fr direct target remaining k changed,
      frame_ranked st fr -> ranked st target ->
      list_ranked st remaining -> continuation_ranked st k ->
      control_ranked
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed))
        (R.cfg_control
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed
      Hframe Htarget Hremaining Hk.
    unfold R.continue_dead.
    destruct changed.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))).
      + cbn. exact (conj Htarget (conj Hframe (conj Hremaining Hk))).
      + cbn. split.
        * now apply frame_ranked_extended with st;
            [apply rank_extends_enqueue |].
        * split.
          -- now apply list_ranked_extended with st;
               [apply rank_extends_enqueue |].
          -- now apply continuation_ranked_extended with st;
               [apply rank_extends_enqueue |].
    - cbn. exact (conj Hframe (conj Hremaining Hk)).
  Qed.

  Lemma control_ranked_start_episode_step :
    forall st owner k phase body,
      state_data_ranked st -> ranked st owner -> continuation_ranked st k ->
      control_ranked (R.materialize st owner)
        (R.RunRhs (R.fresh_frame (R.materialize st owner) owner phase) body k).
  Proof.
    intros st owner k phase body Hdata Howner Hk. cbn. split.
    - apply fresh_frame_ranked.
      + eapply ranked_extended; [apply rank_extends_materialize | exact Howner].
      + exact (data_targets_ranked
          (state_data_ranked_materialize owner Hdata)).
    - now apply continuation_ranked_extended with st;
        [apply rank_extends_materialize |].
  Qed.

  Lemma control_ranked_start_episode_dirty_step :
    forall st owner k phase body,
      state_data_ranked st -> ranked st owner -> continuation_ranked st k ->
      control_ranked (R.clear_side_dirty (R.materialize st owner) owner)
        (R.RunRhs
          (R.fresh_frame
            (R.clear_side_dirty (R.materialize st owner) owner)
            owner phase) body k).
  Proof.
    intros st owner k phase body Hdata Howner Hk. cbn.
    assert (Hextends : rank_extends st
      (R.clear_side_dirty (R.materialize st owner) owner)).
    { eapply rank_extends_trans.
      - apply rank_extends_materialize.
      - apply rank_extends_clear_side_dirty. }
    assert (Hdata' : state_data_ranked
      (R.clear_side_dirty (R.materialize st owner) owner)).
    { apply state_data_ranked_clear_side_dirty.
      apply state_data_ranked_materialize. exact Hdata. }
    split.
    - apply fresh_frame_ranked.
      + now apply ranked_extended with st.
      + exact (data_targets_ranked Hdata').
    - now apply continuation_ranked_extended with st.
  Qed.

  Definition rank_above (st : R.state) (higher lower : V.t) : Prop :=
    R.rank_lt st lower higher = true.

  Definition queue_ordered_at (st : R.state) (queue : list V.t) : Prop :=
    StronglySorted (rank_above st) queue.

  Definition queue_ordered (st : R.state) : Prop :=
    queue_ordered_at st (R.queue st).

  Record configuration_ranked (c : R.config) : Prop := {
    configuration_rank_valid : rank_valid (R.cfg_state c);
    configuration_state_data : state_data_ranked (R.cfg_state c);
    configuration_control_ranked :
      control_ranked (R.cfg_state c) (R.cfg_control c);
    configuration_queue_distinct : queue_distinct (R.cfg_state c);
    configuration_queue_ordered : queue_ordered (R.cfg_state c);
  }.

  Lemma initial_configuration_ranked :
    forall roots, configuration_ranked (R.initial_config roots).
  Proof.
    intros roots. constructor; cbn.
    - apply empty_rank_valid.
    - apply empty_state_data_ranked.
    - exact I.
    - apply empty_queue_distinct.
    - constructor.
  Qed.

  Lemma queue_insert_fresh_ordered :
    forall st x queue,
      rank_valid st ->
      ranked st x ->
      (forall y, List.In y queue -> ranked st y) ->
      queue_ordered_at st queue ->
      ~ List.In x queue ->
      queue_ordered_at st (R.queue_insert_fresh (R.ranking st) x queue).
  Proof.
    intros st x queue Hvalid Hx Hranked Hordered.
    induction Hordered as [|head rest Hrest IH Hall]; intros Hfresh; cbn.
    - constructor; constructor.
    - change (queue_ordered_at st
        (if R.rank_lt st head x
         then x :: head :: rest
         else head :: R.queue_insert_fresh (R.ranking st) x rest)).
      destruct (R.rank_lt st head x) eqn:Hcompare.
      + constructor.
        * constructor; assumption.
        * apply Forall_forall. intros old [-> | Hin].
          -- exact Hcompare.
          -- eapply rank_lt_trans.
             ++ now apply Hranked; right.
             ++ now apply Hranked; left.
             ++ exact Hx.
             ++ apply Forall_forall with (x := old) in Hall; assumption.
             ++ exact Hcompare.
      + constructor.
        * apply IH.
          -- intros y Hin. apply Hranked. now right.
          -- intros Hin. apply Hfresh. now right.
        * apply Forall_forall. intros old Hin.
          apply queue_insert_fresh_members in Hin.
          destruct Hin as [-> | Hin].
          -- assert (x <> head) as Hneq.
             { intros Heq. subst. apply Hfresh. now left. }
             destruct (@rank_lt_total st x head Hvalid Hx
                (Hranked head (or_introl eq_refl)) Hneq) as [Hxh | Hhx].
             ++ exact Hxh.
             ++ rewrite Hcompare in Hhx. discriminate.
          -- apply Forall_forall with (x := old) in Hall; assumption.
  Qed.

  Lemma queue_insert_ordered :
    forall st x queue,
      rank_valid st ->
      ranked st x ->
      (forall y, List.In y queue -> ranked st y) ->
      queue_ordered_at st queue ->
      queue_ordered_at st (R.queue_insert (R.ranking st) x queue).
  Proof.
    intros st x queue Hvalid Hx Hranked Hordered.
    unfold R.queue_insert.
    destruct (R.queue_contains x queue) eqn:Hcontains; [exact Hordered |].
    apply queue_insert_fresh_ordered; try assumption.
    now apply queue_contains_false.
  Qed.

  Lemma enqueue_ordered :
    forall st x,
      rank_valid st ->
      queue_ranked st ->
      queue_ordered st ->
      ranked st x ->
      queue_ordered (R.enqueue st x).
  Proof.
    intros st x Hvalid Hranked Hordered Hx.
    unfold queue_ordered, R.enqueue in *; cbn in *.
    change (queue_ordered_at st
      (R.queue_insert (R.ranking st) x (R.queue st))).
    now apply queue_insert_ordered.
  Qed.

  Lemma queue_insert_all_ordered :
    forall st xs queue,
      rank_valid st ->
      list_ranked st xs ->
      (forall x, List.In x queue -> ranked st x) ->
      queue_ordered_at st queue ->
      queue_ordered_at st (R.queue_insert_all (R.ranking st) xs queue).
  Proof.
    intros st xs. induction xs as [|x rest IH]; intros queue
      Hvalid Hxs Hqueue Hordered; cbn.
    - exact Hordered.
    - apply IH; [exact Hvalid | | |].
      + intros y Hin. apply Hxs. now right.
      + intros y Hin. apply queue_insert_members in Hin.
        destruct Hin as [-> | Hin].
        * apply Hxs. now left.
        * now apply Hqueue.
      + apply queue_insert_ordered; try assumption.
        apply Hxs. now left.
  Qed.

  Lemma enqueue_all_ordered :
    forall st xs,
      rank_valid st ->
      state_data_ranked st ->
      queue_ordered st ->
      list_ranked st xs ->
      queue_ordered (R.enqueue_all st xs).
  Proof.
    intros st xs Hvalid Hdata Hordered Hxs.
    unfold queue_ordered, R.enqueue_all in *; cbn in *.
    change (queue_ordered_at st
      (R.queue_insert_all (R.ranking st) xs (R.queue st))).
    apply queue_insert_all_ordered; try assumption.
    exact (data_queue_ranked Hdata).
  Qed.

  Lemma queue_ordered_flush_deferred :
    forall st,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      queue_ordered (R.flush_deferred st).
  Proof.
    intros st Hvalid Hdata Hordered. unfold R.flush_deferred.
    change (queue_ordered (R.enqueue_all st (R.deferred_wakes st))).
    apply enqueue_all_ordered; try assumption.
    exact (data_deferred_ranked Hdata).
  Qed.

  Lemma queue_ordered_extended :
    forall before after queue,
      rank_extends before after ->
      (forall x, List.In x queue -> ranked before x) ->
      queue_ordered_at before queue ->
      queue_ordered_at after queue.
  Proof.
    intros before after queue Hextends Hranked Hordered.
    induction Hordered as [|head rest Hrest IH Hall].
    - constructor.
    - constructor.
      + apply IH. intros x Hin. apply Hranked. now right.
      + apply Forall_forall. intros x Hin.
        unfold rank_above.
        rewrite <- (@rank_lt_stable before after x head Hextends).
        * apply Forall_forall with (x := x) in Hall; assumption.
        * apply Hranked. now right.
        * apply Hranked. now left.
  Qed.

  Lemma queue_ordered_observe :
    forall st x,
      state_data_ranked st ->
      queue_ordered st -> queue_ordered (R.observe st x).
  Proof.
    intros st x Hdata Hordered. unfold queue_ordered in *.
    unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x)
      as [next rank] eqn:Hobserve; cbn.
    apply queue_ordered_extended with st.
    - eapply rank_extends_observe. unfold R.observe. rewrite Hobserve.
      reflexivity.
    - exact (data_queue_ranked Hdata).
    - exact Hordered.
  Qed.

  Lemma queue_ordered_materialize :
    forall st x,
      queue_ordered st -> queue_ordered (R.materialize st x).
  Proof.
    intros st x Hordered. unfold R.materialize, queue_ordered in *.
    destruct (M.lookup (R.sigma st) x); exact Hordered.
  Qed.

  Lemma queue_ordered_add_reader :
    forall st target owner,
      queue_ordered st -> queue_ordered (R.add_reader st target owner).
  Proof.
    intros st target owner H. unfold queue_ordered, R.add_reader,
      queue_ordered_at, rank_above, R.rank_lt in *; cbn. exact H.
  Qed.

  Lemma queue_remove_ordered :
    forall st removed queue,
      queue_ordered_at st queue ->
      queue_ordered_at st (R.queue_remove removed queue).
  Proof.
    intros st removed queue Hordered.
    induction Hordered as [|head rest Hrest IH Hall].
    - constructor.
    - cbn. destruct (V.eq_dec removed head).
      + exact Hrest.
      + constructor.
        * exact IH.
        * apply Forall_forall. intros x Hin.
          apply Forall_forall with (x := x) in Hall; [exact Hall |].
          now apply queue_remove_members in Hin.
  Qed.

  Lemma queue_ordered_mark_side_dirty :
    forall st target,
      queue_ordered st -> queue_ordered (R.mark_side_dirty st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_ordered_clear_side_dirty :
    forall st target,
      queue_ordered st -> queue_ordered (R.clear_side_dirty st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_ordered_promote_controlled :
    forall st target,
      queue_ordered st -> queue_ordered (R.promote_controlled st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_ordered_cancel_dirty_target :
    forall st target,
      queue_ordered st -> queue_ordered (R.cancel_dirty_target st target).
  Proof.
    intros st target H. unfold R.cancel_dirty_target, queue_ordered in *.
    cbn. now apply queue_remove_ordered.
  Qed.

  Lemma queue_ordered_complete_get :
    forall st fr target next next_fr value,
      queue_ordered st ->
      R.complete_get st fr target = (next, next_fr, value) ->
      queue_ordered next.
  Proof.
    intros st fr target next next_fr value Hordered Hcomplete.
    unfold R.complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      end;
      inversion Hcomplete; subst; cbn;
      unfold queue_ordered, R.materialize in *;
      destruct (M.lookup _ target); cbn; exact Hordered.
  Qed.

  Lemma queue_ordered_complete_get_after_observe :
    forall st fr target next next_fr value,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      R.complete_get
        (if R.is_materialized (R.observe st target) target
         then R.observe st target
         else R.enqueue (R.observe st target) target)
        fr target = (next, next_fr, value) ->
      queue_ordered next.
  Proof.
    intros st fr target next next_fr value Hvalid Hdata Hordered Hcomplete.
    eapply queue_ordered_complete_get; [|exact Hcomplete].
    destruct (R.is_materialized (R.observe st target) target).
    - now apply queue_ordered_observe.
    - apply enqueue_ordered.
      + eapply rank_valid_observe; [exact Hvalid |reflexivity].
      + exact (data_queue_ranked (state_data_ranked_observe target Hdata)).
      + apply queue_ordered_observe; assumption.
      + eapply observe_ranks_variable. reflexivity.
  Qed.

  Lemma queue_ordered_write_side_contribution :
    forall st fr target input next changed,
      queue_ordered st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      queue_ordered next.
  Proof.
    intros st fr target input next changed Hordered Hwrite.
    unfold R.write_side_contribution in Hwrite.
    inversion Hwrite; subst; cbn.
    unfold queue_ordered in *; cbn.
    unfold R.promote_side_target, R.promote_controlled.
    destruct (R.rank_lt st target (R.frame_owner fr)); cbn;
      exact Hordered.
  Qed.

  Lemma queue_ordered_commit_value :
    forall st owner value,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      queue_ordered
        (let st1 := R.with_sigma st (M.update (R.sigma st) owner value) in
         let invalidated := S.elements (R.lookup_set (R.readers st1) owner) in
         let st2 := R.enqueue_all st1 invalidated in
         R.with_readers st2 (M.update (R.readers st2) owner S.empty)).
  Proof.
    intros st owner value Hvalid Hdata Hordered. cbn.
    set (st1 := R.with_sigma st (M.update (R.sigma st) owner value)).
    assert (rank_valid st1) as Hvalid1.
    { unfold st1. now apply rank_valid_with_sigma. }
    assert (state_data_ranked st1) as Hdata1.
    { unfold st1. now apply state_data_ranked_with_sigma. }
    assert (queue_ordered st1) as Hordered1.
    { unfold st1, queue_ordered in *. exact Hordered. }
    set (invalidated := S.elements (R.lookup_set (R.readers st1) owner)).
    assert (list_ranked st1 invalidated) as Hinvalidated.
    { unfold invalidated. apply set_elements_ranked.
      now apply lookup_set_ranked, data_readers_ranked. }
    set (st2 := R.enqueue_all st1 invalidated).
    assert (queue_ordered st2) as Hordered2.
    { unfold st2. now apply enqueue_all_ordered. }
    unfold queue_ordered in *. exact Hordered2.
  Qed.

  Lemma queue_ordered_write_dirty_value :
    forall st target value,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      queue_ordered (R.write_dirty_value st target value).
  Proof.
    intros st target value Hvalid Hdata Hordered.
    exact Hordered.
  Qed.

  Lemma queue_ordered_try_dirty_read :
    forall tf st owner target next,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      R.try_dirty_read tf st owner target = Some next ->
      queue_ordered next.
  Proof.
    intros tf st owner target next Hvalid Hdata Hordered Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using queue_ordered_cancel_dirty_target,
        queue_ordered_write_dirty_value,
        rank_valid_cancel_dirty_target, state_data_ranked_cancel_dirty_target,
        rank_valid_write_dirty_value, state_data_ranked_write_dirty_value.
    all: eapply queue_ordered_write_dirty_value.
    all: eauto using rank_valid_cancel_dirty_target,
      rank_valid_promote_controlled, state_data_ranked_cancel_dirty_target,
      state_data_ranked_promote_controlled,
      queue_ordered_cancel_dirty_target, queue_ordered_promote_controlled.
  Qed.

  Lemma queue_ordered_dirty_complete_get :
    forall tf st fr target next next_fr value,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      queue_ordered next.
  Proof.
    intros tf st fr target next next_fr value Hvalid Hdata Hordered Hcomplete.
    unfold R.dirty_complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      end;
      inversion Hcomplete; subst; cbn in *.
    all: apply queue_ordered_add_reader.
    all: try (eapply queue_ordered_try_dirty_read;
      [apply rank_valid_materialize; exact Hvalid
      |apply state_data_ranked_materialize; exact Hdata
      |apply queue_ordered_materialize; exact Hordered |eassumption]).
    all: try (eapply queue_ordered_try_dirty_read;
      [apply rank_valid_materialize; apply rank_valid_promote_controlled;
       exact Hvalid
      |apply state_data_ranked_materialize;
       apply state_data_ranked_promote_controlled; exact Hdata
      |apply queue_ordered_materialize;
       apply queue_ordered_promote_controlled; exact Hordered |eassumption]).
    all: try (apply queue_ordered_materialize; exact Hordered).
    all: apply queue_ordered_materialize;
      apply queue_ordered_promote_controlled; exact Hordered.
  Qed.

  Lemma queue_ordered_publish_dormant_target :
    forall st target changed,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      queue_ordered (R.publish_dormant_target st target changed).
  Proof.
    intros st target changed Hvalid Hdata Hordered.
    unfold R.publish_dormant_target.
    remember (R.materialize st target) as st1 eqn:Hst1.
    assert (rank_valid st1) as Hvalid1.
    { rewrite Hst1. now apply rank_valid_materialize. }
    assert (state_data_ranked st1) as Hdata1.
    { rewrite Hst1. now apply state_data_ranked_materialize. }
    assert (queue_ordered st1) as Hordered1.
    { rewrite Hst1. now apply queue_ordered_materialize. }
    destruct changed.
    - now apply queue_ordered_commit_value.
    - exact Hordered1.
  Qed.

  Lemma queue_ordered_set_value :
    forall st fr direct next next_fr,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      R.set_value st fr direct = (next, next_fr) ->
      queue_ordered next.
  Proof.
    intros st fr direct next next_fr Hvalid Hdata Hordered Hset.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn; try exact Hordered;
      now apply queue_ordered_commit_value.
  Qed.

  Lemma queue_ordered_continue_side :
    forall st fr target next k changed,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      ranked st target ->
      queue_ordered
        (R.cfg_state (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed Hvalid Hdata Hordered Htarget.
    unfold R.continue_side. destruct changed.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))); cbn.
      + exact Hordered.
      + apply enqueue_ordered; try assumption.
        exact (data_queue_ranked Hdata).
    - exact Hordered.
  Qed.

  Lemma queue_ordered_continue_dead :
    forall st fr direct target remaining k changed,
      rank_valid st -> state_data_ranked st -> queue_ordered st ->
      ranked st target ->
      queue_ordered
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed
      Hvalid Hdata Hordered Htarget.
    unfold R.continue_dead. destruct changed.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))); cbn.
      + exact Hordered.
      + apply enqueue_ordered; try assumption.
        exact (data_queue_ranked Hdata).
    - exact Hordered.
  Qed.

  Lemma queue_pop_ordered :
    forall st queue head rest,
      queue_ordered_at st queue ->
      R.queue_pop queue = Some (head, rest) ->
      queue_ordered_at st rest /\
      forall x, List.In x rest -> R.rank_lt st x head = true.
  Proof.
    intros st queue head rest Hordered Hpop.
    destruct queue as [|first tail]; cbn in Hpop; try discriminate.
    inversion Hpop; subst. inversion Hordered; subst. split; [assumption |].
    intros x Hin. apply Forall_forall with (x := x) in H2; assumption.
  Qed.

  Lemma queue_pop_ranked :
    forall st head rest,
      queue_ranked st ->
      R.queue_pop (R.queue st) = Some (head, rest) ->
      ranked st head /\ list_ranked st rest.
  Proof.
    intros st head rest Hranked Hpop.
    destruct (R.queue st) as [|first tail] eqn:Hqueue;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. split.
    - apply Hranked. rewrite Hqueue. now left.
    - intros x Hin. apply Hranked. rewrite Hqueue. now right.
  Qed.

  Lemma queue_peek_pop_same :
    forall queue peek head rest,
      R.queue_peek queue = Some peek ->
      R.queue_pop queue = Some (head, rest) ->
      peek = head.
  Proof.
    intros [|first tail] peek head rest Hpeek Hpop;
      cbn in *; try discriminate. congruence.
  Qed.

  Lemma queue_pop_distinct :
    forall st head rest,
      queue_distinct st ->
      R.queue_pop (R.queue st) = Some (head, rest) ->
      NoDup rest.
  Proof.
    intros st head rest Hdistinct Hpop.
    destruct (R.queue st) as [|first tail] eqn:Hqueue;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. unfold queue_distinct in Hdistinct.
    rewrite Hqueue in Hdistinct. now inversion Hdistinct.
  Qed.

  Lemma queue_distinct_complete_get :
    forall st fr target next next_fr value,
      queue_distinct st ->
      R.complete_get st fr target = (next, next_fr, value) ->
      queue_distinct next.
  Proof.
    intros st fr target next next_fr value Hdistinct Hcomplete.
    unfold R.complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      end;
      inversion Hcomplete; subst; cbn;
      unfold queue_distinct, R.materialize in *;
      destruct (M.lookup _ target); cbn; exact Hdistinct.
  Qed.

  Lemma queue_distinct_observe :
    forall st x,
      queue_distinct st -> queue_distinct (R.observe st x).
  Proof.
    intros st x Hdistinct. unfold R.observe, queue_distinct in *.
    destruct (R.Ranking.observe (R.ranking st) x). exact Hdistinct.
  Qed.

  Lemma queue_distinct_materialize :
    forall st x,
      queue_distinct st -> queue_distinct (R.materialize st x).
  Proof.
    intros st x Hdistinct. unfold R.materialize, queue_distinct in *.
    destruct (M.lookup (R.sigma st) x); exact Hdistinct.
  Qed.

  Lemma queue_distinct_complete_get_after_observe :
    forall st fr target next next_fr value,
      queue_distinct st ->
      R.complete_get
        (if R.is_materialized (R.observe st target) target
         then R.observe st target
         else R.enqueue (R.observe st target) target)
        fr target = (next, next_fr, value) ->
      queue_distinct next.
  Proof.
    intros st fr target next next_fr value Hdistinct Hcomplete.
    eapply queue_distinct_complete_get; [|exact Hcomplete].
    destruct (R.is_materialized (R.observe st target) target).
    - now apply queue_distinct_observe.
    - apply enqueue_distinct. now apply queue_distinct_observe.
  Qed.

  Lemma queue_distinct_mark_side_dirty :
    forall st target,
      queue_distinct st -> queue_distinct (R.mark_side_dirty st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_distinct_clear_side_dirty :
    forall st target,
      queue_distinct st -> queue_distinct (R.clear_side_dirty st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_distinct_promote_controlled :
    forall st target,
      queue_distinct st -> queue_distinct (R.promote_controlled st target).
  Proof. intros st target H. exact H. Qed.

  Lemma queue_distinct_cancel_dirty_target :
    forall st target,
      queue_distinct st -> queue_distinct (R.cancel_dirty_target st target).
  Proof.
    intros st target H. unfold R.cancel_dirty_target, queue_distinct in *.
    cbn. now apply queue_remove_nodup.
  Qed.

  Lemma queue_distinct_write_dirty_value :
    forall st target value,
      queue_distinct st -> queue_distinct (R.write_dirty_value st target value).
  Proof.
    intros st target value H. exact H.
  Qed.

  Lemma queue_distinct_flush_deferred :
    forall st,
      queue_distinct st -> queue_distinct (R.flush_deferred st).
  Proof.
    intros st Hdistinct. unfold R.flush_deferred, queue_distinct; cbn.
    now apply queue_insert_all_nodup.
  Qed.

  Lemma queue_distinct_try_dirty_read :
    forall tf st owner target next,
      queue_distinct st ->
      R.try_dirty_read tf st owner target = Some next ->
      queue_distinct next.
  Proof.
    intros tf st owner target next Hdistinct Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn;
      eauto using queue_distinct_cancel_dirty_target,
        queue_distinct_write_dirty_value.
  Qed.

  Lemma queue_distinct_dirty_complete_get :
    forall tf st fr target next next_fr value,
      queue_distinct st ->
      R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
      queue_distinct next.
  Proof.
    intros tf st fr target next next_fr value Hdistinct Hcomplete.
    unfold R.dirty_complete_get in Hcomplete.
    repeat
      match type of Hcomplete with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      end;
      inversion Hcomplete; subst; cbn in *.
    all: unfold queue_distinct, R.add_reader; cbn.
    all: try (eapply queue_distinct_try_dirty_read;
      [apply queue_distinct_materialize; exact Hdistinct |eassumption]).
    all: try (eapply queue_distinct_try_dirty_read;
      [apply queue_distinct_materialize;
       apply queue_distinct_promote_controlled; exact Hdistinct |eassumption]).
    all: try (apply queue_distinct_materialize; exact Hdistinct).
    all: apply queue_distinct_materialize;
      apply queue_distinct_promote_controlled; exact Hdistinct.
  Qed.

  Lemma queue_distinct_publish_dormant_target :
    forall st target changed,
      queue_distinct st ->
      queue_distinct (R.publish_dormant_target st target changed).
  Proof.
    intros st target changed Hdistinct.
    unfold R.publish_dormant_target.
    remember (R.materialize st target) as st1 eqn:Hst1.
    assert (queue_distinct st1) as Hdistinct1.
    { rewrite Hst1. now apply queue_distinct_materialize. }
    destruct changed; cbn.
    - now apply enqueue_all_distinct.
    - exact Hdistinct1.
  Qed.

  Lemma queue_distinct_write_side_contribution :
    forall st fr target input next changed,
      queue_distinct st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      queue_distinct next.
  Proof.
    intros st fr target input next changed Hdistinct Hwrite.
    unfold R.write_side_contribution in Hwrite.
    inversion Hwrite; subst; cbn. unfold queue_distinct in *; cbn.
    unfold R.promote_side_target, R.promote_controlled.
    destruct (R.rank_lt st target (R.frame_owner fr)); cbn;
      exact Hdistinct.
  Qed.

  Lemma queue_distinct_set_value :
    forall st fr direct next next_fr,
      queue_distinct st ->
      R.set_value st fr direct = (next, next_fr) ->
      queue_distinct next.
  Proof.
    intros st fr direct next next_fr Hdistinct Hset.
    unfold R.set_value in Hset.
    repeat
      match type of Hset with
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn; try exact Hdistinct;
      now apply enqueue_all_distinct.
  Qed.

  Lemma queue_distinct_continue_side :
    forall st fr target next k changed,
      queue_distinct st ->
      queue_distinct
        (R.cfg_state (R.continue_side st fr target next k changed)).
  Proof.
    intros st fr target next k changed Hdistinct. unfold R.continue_side.
    repeat destruct (_ : bool); cbn; try exact Hdistinct.
    now apply enqueue_distinct.
  Qed.

  Lemma queue_distinct_continue_dead :
    forall st fr direct target remaining k changed,
      queue_distinct st ->
      queue_distinct
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed Hdistinct.
    unfold R.continue_dead.
    repeat destruct (_ : bool); cbn; try exact Hdistinct.
    now apply enqueue_distinct.
  Qed.

  (** Keep the shortened read as one proof-level state transformer. Its local
      preservation lemmas above expose exactly the facts needed by the global
      small-step case split without duplicating its internal branches. *)
  Local Opaque R.dirty_complete_get.

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
      try discriminate; inversion Hstep; subst; cbn in *;
      repeat first
        [ apply rank_valid_with_queue
        | apply rank_valid_with_sigma
        | apply rank_valid_with_readers
        | apply rank_valid_with_contributions
        | apply rank_valid_with_cells_and_resets
        | apply rank_valid_with_last_targets
        | apply rank_valid_with_dormant_bottom
        | apply rank_valid_with_controlled
        | apply rank_valid_with_dirty_side_targets
        | apply rank_valid_mark_side_dirty
        | apply rank_valid_clear_side_dirty
        | apply rank_valid_remember_dormant
        | apply rank_valid_add_reader
        | apply rank_valid_publish_dormant_target
        | apply rank_valid_materialize
        | apply rank_valid_enqueue
        | apply rank_valid_enqueue_all
        | eapply rank_valid_try_dirty_read; [|eassumption]
        | eapply rank_valid_dirty_complete_get; [|eassumption]
        | apply rank_valid_get_control_state
        | eapply rank_valid_observe; [|reflexivity] ];
      try exact Hvalid;
      eauto 5 using rank_valid_continue_side, rank_valid_continue_dead,
        rank_valid_write_side_contribution, rank_valid_set_value,
        rank_valid_observe, rank_valid_try_dirty_read,
        rank_valid_flush_deferred.
    all: repeat
      match goal with
      | |- rank_valid (R.cfg_state (if ?condition then _ else _)) =>
          destruct condition eqn:?Hbranch; cbn
      end.
    all: repeat first
      [ apply rank_valid_continue_side
      | apply rank_valid_continue_dead
      | apply rank_valid_enqueue
      | apply rank_valid_mark_side_dirty
      | apply rank_valid_register_reset
      | apply rank_valid_with_contributions
      | apply rank_valid_promote_side_target
      | apply rank_valid_flush_deferred
      | eapply rank_valid_observe; [|reflexivity] ].
    all: try exact Hvalid.
    all: unfold R.reset_registered_cells;
      destruct Features.restart_side_phases; cbn;
      [apply rank_valid_with_cells_and_resets; exact Hvalid | exact Hvalid].
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
      try discriminate; inversion Hstep; subst; cbn in *;
      repeat first
        [ eapply rank_extends_trans; [|apply rank_extends_with_queue]
        | eapply rank_extends_trans; [|apply rank_extends_with_sigma]
        | eapply rank_extends_trans; [|apply rank_extends_with_readers]
        | eapply rank_extends_trans; [|apply rank_extends_with_contributions]
        | eapply rank_extends_trans; [|apply rank_extends_with_cells_and_resets]
        | eapply rank_extends_trans; [|apply rank_extends_with_last_targets]
        | eapply rank_extends_trans; [|apply rank_extends_with_dormant_bottom]
        | eapply rank_extends_trans; [|apply rank_extends_with_controlled]
        | eapply rank_extends_trans;
            [|apply rank_extends_with_dirty_side_targets]
        | eapply rank_extends_trans; [|apply rank_extends_mark_side_dirty]
        | eapply rank_extends_trans; [|apply rank_extends_clear_side_dirty]
        | eapply rank_extends_trans; [|apply rank_extends_remember_dormant]
        | eapply rank_extends_trans; [|apply rank_extends_add_reader]
        | eapply rank_extends_trans;
            [|apply rank_extends_publish_dormant_target]
        | eapply rank_extends_trans; [|apply rank_extends_materialize]
        | eapply rank_extends_trans; [|apply rank_extends_enqueue]
        | eapply rank_extends_trans; [|apply rank_extends_enqueue_all]
        | eapply rank_extends_trans;
            [|eapply rank_extends_try_dirty_read; eassumption]
        | eapply rank_extends_trans; [|apply rank_extends_get_control_state]
        | eapply rank_extends_observe; reflexivity
        | apply rank_extends_refl ];
      eauto 5 using rank_extends_trans, rank_extends_observe,
        rank_extends_write_side_contribution,
        rank_extends_continue_side, rank_extends_continue_dead,
        rank_extends_set_value, rank_extends_reset_registered_cells,
        rank_extends_try_dirty_read, rank_extends_flush_deferred.
    all: repeat
      match goal with
      | |- rank_extends _ (R.cfg_state (if ?condition then _ else _)) =>
          destruct condition eqn:?Hbranch; cbn
      end.
    all: repeat
      match goal with
      | |- rank_extends ?before
          (R.cfg_state (R.continue_side ?mid _ _ _ _ _)) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_continue_side]
      | |- rank_extends ?before
          (R.cfg_state (R.continue_dead ?mid _ _ _ _ _ _)) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_continue_dead]
      | |- rank_extends ?before (R.enqueue ?mid _) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_enqueue]
      | |- rank_extends ?before (R.mark_side_dirty ?mid _) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_mark_side_dirty]
      | |- rank_extends ?before (R.register_reset ?mid _ _ _ _) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_register_reset]
      | |- rank_extends ?before (R.with_contributions ?mid _) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_with_contributions]
      | |- rank_extends ?before (R.promote_side_target ?mid _ _) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_promote_side_target]
      | |- rank_extends ?before (R.observe ?mid _) =>
          eapply (@rank_extends_trans before mid);
            [|eapply rank_extends_observe; reflexivity]
      | |- rank_extends ?before (R.flush_deferred ?mid) =>
          eapply (@rank_extends_trans before mid);
            [|apply rank_extends_flush_deferred]
      end.
    all: try (eapply rank_extends_trans;
      [eapply rank_extends_observe; reflexivity
      |eapply rank_extends_dirty_complete_get; eassumption]).
    all: try apply rank_extends_refl.
    all: try apply rank_extends_reset_registered_cells.
  Qed.

  Lemma next_config_state_data_ranked :
    forall tf before after,
      state_data_ranked (R.cfg_state before) ->
      control_ranked (R.cfg_state before) (R.cfg_control before) ->
      R.next_config tf before = Some after ->
      state_data_ranked (R.cfg_state after).
  Proof.
    intros tf [st control] after Hdata Hcontrol Hstep.
    cbn in Hstep. destruct control; cbn in Hstep, Hcontrol;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hdata.
    all: try (apply state_data_ranked_remember_dormant; exact Hdata).
    all: try (apply state_data_ranked_add_reader_named;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try (apply state_data_ranked_remember_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try (apply state_data_ranked_observe; exact Hdata).
    all: try (apply state_data_ranked_materialize; exact Hdata).
    all: try (apply state_data_ranked_clear_side_dirty;
      apply state_data_ranked_materialize; exact Hdata).
    all: try (apply state_data_ranked_with_dirty_side_targets;
      apply state_data_ranked_materialize; exact Hdata).
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- state_data_ranked (R.with_queue ?before ?rest) =>
          apply state_data_ranked_with_queue;
          [exact Hdata |
           exact (proj2 (queue_pop_ranked
             (data_queue_ranked Hdata) Hpop))]
      end.
    all: try (apply state_data_ranked_observe_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try (apply state_data_ranked_observe_enqueue_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try (apply state_data_ranked_observe_promote_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try (apply state_data_ranked_observe_enqueue_promote_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: try match goal with
      | Hcomplete : R.dirty_complete_get _ (R.observe ?before ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_dirty_complete_get;
          [apply state_data_ranked_observe; exact Hdata
          |apply frame_ranked_extended with before;
             [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol)]
          |eapply observe_ranks_variable; reflexivity
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_complete_get_after_observe;
          [exact Hdata | exact (proj1 Hcontrol) | exact Hcomplete]
      end.
    all: try match goal with
      | Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr ?target ?input = (?next, true)
        |- state_data_ranked
          (R.cfg_state
            (R.continue_side (R.mark_side_dirty ?next ?target)
              ?fr ?target ?body ?k true)) =>
          apply state_data_ranked_continue_side;
          [apply state_data_ranked_mark_side_dirty;
           eapply state_data_ranked_write_side_contribution;
           [apply state_data_ranked_observe; exact Hdata |exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_trans;
             [eapply rank_extends_write_side_contribution; exact Hwrite
             |apply rank_extends_mark_side_dirty]
           |eapply observe_ranks_variable; reflexivity]]
      end.
    all: try (apply state_data_ranked_materialize;
      apply state_data_ranked_enqueue;
      [apply state_data_ranked_observe; exact Hdata
      |eapply observe_ranks_variable; reflexivity]).
    all: try (apply state_data_ranked_publish_targets;
      [exact Hdata | exact (proj1 Hcontrol)]).
    all: try (apply state_data_ranked_reset_registered_cells; exact Hdata).
    all: try match goal with
      | Hset : R.set_value (R.flush_deferred ?before) ?fr ?direct =
          (?next, ?next_fr)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_set_value;
          [apply state_data_ranked_flush_deferred; exact Hdata | exact Hset]
      end.
    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_set_value; [exact Hdata | exact Hset]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\
          list_ranked ?before (?target :: ?rest) /\ _,
        Hwrite : R.write_side_contribution ?before ?fr ?target D.bottom =
          (?next, true)
        |- state_data_ranked
          (R.cfg_state
            (R.continue_dead (R.mark_side_dirty ?next ?target)
              ?fr ?direct ?target ?rest ?k true)) =>
          apply state_data_ranked_continue_dead;
          [apply state_data_ranked_mark_side_dirty;
           eapply state_data_ranked_write_side_contribution;
           [exact Hdata |exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_trans;
             [eapply rank_extends_write_side_contribution; exact Hwrite
             |apply rank_extends_mark_side_dirty]
           |apply (proj1 (proj2 Hcontrol0)); now left]]
      end.
    all: try match goal with
      | Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr ?target ?input = (?next, ?changed)
        |- state_data_ranked
          (R.cfg_state
            (R.continue_side ?next ?fr ?target ?body ?k ?changed)) =>
          apply state_data_ranked_continue_side;
          [eapply state_data_ranked_write_side_contribution;
           [apply state_data_ranked_observe; exact Hdata | exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_write_side_contribution; exact Hwrite
           |eapply observe_ranks_variable; reflexivity]]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\
          list_ranked ?before (?target :: ?rest) /\ _,
        Hwrite : R.write_side_contribution ?before ?fr ?target D.bottom =
          (?next, ?changed)
        |- state_data_ranked
          (R.cfg_state
            (R.continue_dead ?next ?fr ?direct ?target ?rest ?k ?changed)) =>
          apply state_data_ranked_continue_dead;
          [eapply state_data_ranked_write_side_contribution;
           [exact Hdata | exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_write_side_contribution; exact Hwrite
           |apply (proj1 (proj2 Hcontrol0)); now left]]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get ?before ?fr ?target =
          (?next, ?next_fr, ?value)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_complete_get;
          [exact Hdata | exact (proj1 Hcontrol)
          |exact (proj1 (proj2 Hcontrol)) |exact Hcomplete]
      end.
    all: try (eapply state_data_ranked_write_side_contribution;
      [apply state_data_ranked_observe; exact Hdata |reflexivity]).
    all: try (apply state_data_ranked_mark_side_dirty;
      eapply state_data_ranked_write_side_contribution;
      [apply state_data_ranked_observe; exact Hdata |reflexivity]).
    all: try (eapply state_data_ranked_write_side_contribution;
      [exact Hdata |reflexivity]).
    all: try (apply state_data_ranked_mark_side_dirty;
      eapply state_data_ranked_write_side_contribution;
      [exact Hdata |reflexivity]).
    all: try (apply state_data_ranked_register_reset;
      apply state_data_ranked_with_contributions;
      apply state_data_ranked_promote_side_target;
      apply state_data_ranked_observe; exact Hdata).
    all: try (apply state_data_ranked_mark_side_dirty;
      apply state_data_ranked_register_reset;
      apply state_data_ranked_with_contributions;
      apply state_data_ranked_promote_side_target;
      apply state_data_ranked_observe; exact Hdata).
    all: try (apply state_data_ranked_register_reset;
      apply state_data_ranked_with_contributions;
      apply state_data_ranked_promote_side_target; exact Hdata).
    all: try (apply state_data_ranked_mark_side_dirty;
      apply state_data_ranked_register_reset;
      apply state_data_ranked_with_contributions;
      apply state_data_ranked_promote_side_target; exact Hdata).
    all: try (apply state_data_ranked_enqueue;
      [apply state_data_ranked_register_reset;
       apply state_data_ranked_with_contributions;
       apply state_data_ranked_promote_side_target;
       apply state_data_ranked_observe; exact Hdata
      |eapply ranked_extended with (before := R.observe st t);
       [eapply rank_extends_trans;
        [apply rank_extends_promote_side_target
        |eapply rank_extends_trans;
         [apply rank_extends_with_contributions
         |apply rank_extends_register_reset]]
       |exact (@observe_ranks_variable st t (R.observe st t) eq_refl)]]).
    all: try (apply state_data_ranked_enqueue;
      [apply state_data_ranked_mark_side_dirty;
       apply state_data_ranked_register_reset;
       apply state_data_ranked_with_contributions;
       apply state_data_ranked_promote_side_target;
       apply state_data_ranked_observe; exact Hdata
      |eapply ranked_extended with (before := R.observe st t);
       [eapply rank_extends_trans;
        [apply rank_extends_promote_side_target
        |eapply rank_extends_trans;
         [apply rank_extends_with_contributions
         |eapply rank_extends_trans;
          [apply rank_extends_register_reset
          |apply rank_extends_mark_side_dirty]]]
       |exact (@observe_ranks_variable st t (R.observe st t) eq_refl)]]).
    all: try match goal with
      | |- state_data_ranked (R.cfg_state (if ?condition then _ else _)) =>
          destruct condition eqn:?Hcase; cbn
      end.
    all: try (apply state_data_ranked_enqueue;
      [apply state_data_ranked_mark_side_dirty;
       apply state_data_ranked_register_reset;
       apply state_data_ranked_with_contributions;
       apply state_data_ranked_promote_side_target; exact Hdata
      |eapply ranked_extended;
       [eapply rank_extends_trans;
        [apply rank_extends_promote_side_target
        |eapply rank_extends_trans;
         [apply rank_extends_with_contributions
         |eapply rank_extends_trans;
          [apply rank_extends_register_reset
          |apply rank_extends_mark_side_dirty]]]
       |apply (proj1 (proj2 Hcontrol)); now left]]).
    all: try (apply state_data_ranked_mark_side_dirty;
      apply state_data_ranked_register_reset;
      apply state_data_ranked_with_contributions;
      apply state_data_ranked_promote_side_target; exact Hdata).
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- state_data_ranked
          (R.clear_side_dirty (R.with_queue ?before ?rest) ?target) =>
          apply state_data_ranked_clear_side_dirty;
          apply state_data_ranked_with_queue;
          [exact Hdata
          |exact (proj2 (queue_pop_ranked
             (data_queue_ranked Hdata) Hpop))]
      end.
    all: try (apply state_data_ranked_materialize;
      apply state_data_ranked_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))]).
    all: apply state_data_ranked_promote_add_reader;
      [exact Hdata | exact (proj1 (proj1 Hcontrol))].
  Qed.

  Lemma next_config_control_ranked :
    forall tf before after,
      state_data_ranked (R.cfg_state before) ->
      control_ranked (R.cfg_state before) (R.cfg_control before) ->
      R.next_config tf before = Some after ->
      control_ranked (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hdata Hcontrol Hstep.
    pose proof (@next_config_rank_extends tf
      {| R.cfg_state := st; R.cfg_control := control |} after Hstep)
      as Hextends.
    pose proof (@next_config_state_data_ranked tf
      {| R.cfg_state := st; R.cfg_control := control |} after
      Hdata Hcontrol Hstep) as Hdata_after.
    unfold R.next_config in Hstep.
    cbn [R.cfg_state R.cfg_control] in Hstep.
    destruct control; cbn [R.cfg_state R.cfg_control] in Hstep;
      cbn in Hcontrol;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact I.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- ranked (R.with_queue ?before ?rest) ?head /\ True =>
          split;
          [change (ranked before head);
           exact (proj1 (queue_pop_ranked
             (data_queue_ranked Hdata) Hpop))
          |exact I]
      end.
    all: try match goal with
      | Hset : R.set_value (R.flush_deferred ?before) ?fr ?direct =
          (?next, ?next_fr),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          split;
          [eapply frame_ranked_set_value;
           [eapply frame_ranked_extended;
            [apply rank_extends_flush_deferred | exact (proj1 Hcontrol0)]
           |exact Hset]
          |eapply continuation_ranked_extended;
           [exact Hextends | exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          split;
          [eapply frame_ranked_set_value;
           [exact (proj1 Hcontrol0) | exact Hset]
          |eapply continuation_ranked_extended;
           [exact Hextends | exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- ranked (R.with_queue ?before ?rest) ?head /\
           frame_ranked (R.with_queue ?before ?rest) ?fr /\
           continuation_ranked (R.with_queue ?before ?rest) ?k =>
          split;
          [change (ranked before head);
           exact (proj1 (queue_pop_ranked
             (data_queue_ranked Hdata) Hpop))
          |split;
           [apply frame_ranked_extended with before;
            [apply rank_extends_with_queue | exact (proj1 Hcontrol0)]
           |apply continuation_ranked_extended with before;
            [apply rank_extends_with_queue | exact (proj2 Hcontrol0)]]]
      end.
    all: try match goal with
      | Hcontrol0 : ranked ?before ?owner /\ continuation_ranked ?before ?k
        |- frame_ranked (R.materialize ?before ?owner)
             (R.fresh_frame (R.materialize ?before ?owner) ?owner ?phase) /\
           continuation_ranked (R.materialize ?before ?owner) ?k =>
          exact (@control_ranked_start_episode_step
            before owner k phase (tf owner) Hdata
            (proj1 Hcontrol0) (proj2 Hcontrol0))
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- frame_ranked ?before ?fr /\
          list_ranked ?before (S.elements (R.frame_previous_targets ?fr)) /\
          continuation_ranked ?before ?k =>
          split; [exact (proj1 Hcontrol0) |]; split;
          [apply set_elements_ranked;
           exact (proj1 (proj2 (proj1 Hcontrol0)))
          |exact (proj2 Hcontrol0)]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- ranked (R.observe ?before ?target) ?target /\
          frame_ranked (R.observe ?before ?target) ?fr /\
          ranked (R.observe ?before ?target) ?target /\
          continuation_ranked (R.observe ?before ?target) ?k =>
          split; [eapply observe_ranks_variable; reflexivity |]; split;
          [eapply frame_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol0)]
          |split; [eapply observe_ranks_variable; reflexivity |];
           eapply continuation_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- ranked (R.observe ?before ?target) ?target /\
          frame_ranked (R.observe ?before ?target) ?fr /\
          continuation_ranked (R.observe ?before ?target) ?k =>
          split; [eapply observe_ranks_variable; reflexivity |]; split;
          [eapply frame_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol0)]
          |eapply continuation_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\
          list_ranked ?before (?head :: ?tail) /\
          continuation_ranked ?before ?k
        |- frame_ranked ?before ?fr /\ list_ranked ?before ?tail /\
          continuation_ranked ?before ?k =>
          split; [exact (proj1 Hcontrol0) |]; split;
          [intros x Hin; apply (proj1 (proj2 Hcontrol0)); now right
          |exact (proj2 (proj2 Hcontrol0))]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k,
        Hcomplete : R.dirty_complete_get _ (R.observe ?before ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          eapply control_ranked_dirty_complete_get;
          [eapply frame_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol0)]
          |eapply observe_ranks_variable; reflexivity
          |eapply continuation_ranked_extended;
           [eapply rank_extends_observe; reflexivity |exact (proj2 Hcontrol0)]
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcontrol0 : ranked ?before ?owner /\ continuation_ranked ?before ?k
        |- frame_ranked
             (R.clear_side_dirty (R.materialize ?before ?owner) ?owner)
             (R.fresh_frame
               (R.clear_side_dirty (R.materialize ?before ?owner) ?owner)
               ?owner ?phase) /\
           continuation_ranked
             (R.clear_side_dirty (R.materialize ?before ?owner) ?owner) ?k =>
          exact (@control_ranked_start_episode_dirty_step
            before owner k phase (tf owner) Hdata
            (proj1 Hcontrol0) (proj2 Hcontrol0))
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k,
        Hcomplete : R.complete_get (R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          eapply control_ranked_complete_get;
          [eapply frame_ranked_extended;
           [eapply rank_extends_trans;
            [eapply rank_extends_observe; reflexivity
            |apply rank_extends_enqueue]
           |exact (proj1 Hcontrol0)]
          |eapply ranked_extended;
           [apply rank_extends_enqueue
           |eapply observe_ranks_variable; reflexivity]
          |eapply continuation_ranked_extended;
           [eapply rank_extends_trans;
            [eapply rank_extends_observe; reflexivity
            |apply rank_extends_enqueue]
           |exact (proj2 Hcontrol0)]
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k,
        Hcomplete : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          eapply control_ranked_complete_get_after_observe;
          [exact (proj1 Hcontrol0) | exact (proj2 Hcontrol0) | exact Hcomplete]
      end.
    all: try match goal with
      | Hrecord : R.record_side_input ?fr ?target ?raw = (?fr1, ?input),
        Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr1 ?target ?input = (?next, ?changed),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- control_ranked
          (R.cfg_state (R.continue_side ?next ?fr1 ?target ?body ?k ?flag))
          (R.cfg_control (R.continue_side ?next ?fr1 ?target ?body ?k ?flag)) =>
          apply control_ranked_continue_side;
          [eapply frame_ranked_write_side_contribution;
           [eapply record_side_input_ranked;
            [eapply frame_ranked_extended;
             [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol0)]
            |eapply observe_ranks_variable; reflexivity |exact Hrecord]
           |exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_write_side_contribution; exact Hwrite
           |eapply observe_ranks_variable; reflexivity]
          |eapply continuation_ranked_extended;
           [eapply rank_extends_trans;
            [eapply rank_extends_observe; reflexivity
            |eapply rank_extends_write_side_contribution; exact Hwrite]
           |exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hrecord : R.record_side_input ?fr ?target ?raw = (?fr1, ?input),
        Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr1 ?target ?input = (?next, ?changed),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- control_ranked
          (R.cfg_state
            (R.continue_side (R.mark_side_dirty ?next ?target)
              ?fr1 ?target ?body ?k ?flag))
          (R.cfg_control
            (R.continue_side (R.mark_side_dirty ?next ?target)
              ?fr1 ?target ?body ?k ?flag)) =>
          apply control_ranked_continue_side;
          [eapply frame_ranked_extended;
           [apply rank_extends_mark_side_dirty
           |eapply frame_ranked_write_side_contribution;
            [eapply record_side_input_ranked;
             [eapply frame_ranked_extended;
              [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol0)]
             |eapply observe_ranks_variable; reflexivity |exact Hrecord]
            |exact Hwrite]]
          |eapply ranked_extended;
           [apply rank_extends_mark_side_dirty
           |eapply ranked_extended;
            [eapply rank_extends_write_side_contribution; exact Hwrite
            |eapply observe_ranks_variable; reflexivity]]
          |eapply continuation_ranked_extended;
           [eapply rank_extends_trans;
            [eapply rank_extends_trans;
             [eapply rank_extends_observe; reflexivity
             |eapply rank_extends_write_side_contribution; exact Hwrite]
            |apply rank_extends_mark_side_dirty]
           |exact (proj2 Hcontrol0)]]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\ ranked ?before ?target /\
          continuation_ranked ?before ?k,
        Hcomplete : R.complete_get ?before ?fr ?target =
          (?next, ?next_fr, ?value)
        |- frame_ranked ?next ?next_fr /\ continuation_ranked ?next ?k =>
          eapply control_ranked_complete_get;
          [exact (proj1 Hcontrol0) | exact (proj1 (proj2 Hcontrol0))
          |exact (proj2 (proj2 Hcontrol0)) |exact Hcomplete]
      end.
    all: try match goal with
      | Hextends0 : rank_extends ?before ?after,
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- frame_ranked ?after ?fr /\ continuation_ranked ?after ?k =>
          split;
          [now apply frame_ranked_extended with before
          |now apply continuation_ranked_extended with before]
      end.
    all: try match goal with
      | Hextends0 : rank_extends ?before ?after,
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- continuation_ranked ?after ?k =>
          apply continuation_ranked_extended with before;
          [exact Hextends0 |exact (proj2 Hcontrol0)]
      end.
    all: try match goal with
      | Hrecord : R.record_side_input ?fr ?target ?raw = (?fr1, ?input),
        Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr1 ?target ?input = (?next, ?changed),
        Hdormant : R.is_dormant ?before ?target = true,
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- control_ranked _ _ =>
          change (control_ranked
            (R.cfg_state
              (R.continue_side next fr1 target r0 k true))
            (R.cfg_control
              (R.continue_side next fr1 target r0 k true)));
          eapply control_ranked_continue_side_after_write;
          [exact (proj1 Hcontrol0) |exact (proj2 Hcontrol0)
          |exact Hrecord |exact Hwrite]
      end.
    all: try match goal with
      | Hrecord : R.record_side_input ?fr ?target ?raw = (?fr1, ?input),
        Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr1 ?target ?input = (?next, false),
        Hdormant : R.is_dormant ?before ?target = false,
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- control_ranked _ _ =>
          change (control_ranked
            (R.cfg_state
              (R.continue_side next fr1 target r0 k false))
            (R.cfg_control
              (R.continue_side next fr1 target r0 k false)));
          eapply control_ranked_continue_side_after_write;
          [exact (proj1 Hcontrol0) |exact (proj2 Hcontrol0)
          |exact Hrecord |exact Hwrite]
      end.
    all: try match goal with
      | Hrecord : R.record_side_input ?fr ?target ?raw = (?fr1, ?input),
        Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr1 ?target ?input = (?next, true),
        Hdormant : R.is_dormant ?before ?target = false,
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- control_ranked _ _ =>
          change (control_ranked
            (R.cfg_state
              (R.continue_side (R.mark_side_dirty next target)
                fr1 target r0 k true))
            (R.cfg_control
              (R.continue_side (R.mark_side_dirty next target)
                fr1 target r0 k true)));
          eapply control_ranked_continue_marked_side_after_write;
          [exact (proj1 Hcontrol0) |exact (proj2 Hcontrol0)
          |exact Hrecord |exact Hwrite]
      end.
    all: try (change (control_ranked
      (R.cfg_state (R.continue_side s f0 t r0 c false))
      (R.cfg_control (R.continue_side s f0 t r0 c false)));
      eapply control_ranked_continue_side_after_write;
      [exact (proj1 Hcontrol) |exact (proj2 Hcontrol)
      |exact Hcase0 |exact Hcase1]).
    all: try exact Hcontrol.
    split; [eapply observe_ranks_variable; reflexivity | exact I].
    split; [eapply observe_ranks_variable; reflexivity | exact I].
    split; [exact (proj1 Hcontrol) |]; split;
      [intros x Hin; inversion Hin | exact (proj2 Hcontrol)].
    split;
      [eapply frame_ranked_extended;
       [exact Hextends |exact (proj1 Hcontrol)]
      |eapply continuation_ranked_extended;
       [exact Hextends |exact (proj2 (proj2 Hcontrol))]].
    all: try (change (control_ranked
      (R.cfg_state
        (R.continue_dead (R.mark_side_dirty s t0) f t t0 l0 c true))
      (R.cfg_control
        (R.continue_dead (R.mark_side_dirty s t0) f t t0 l0 c true)));
      apply control_ranked_continue_dead;
      [eapply frame_ranked_extended;
       [apply rank_extends_mark_side_dirty
       |eapply frame_ranked_write_side_contribution;
        [exact (proj1 Hcontrol) |exact Hcase1]]
      |eapply ranked_extended;
       [apply rank_extends_mark_side_dirty
       |eapply ranked_extended;
        [eapply rank_extends_write_side_contribution; exact Hcase1
        |apply (proj1 (proj2 Hcontrol)); now left]]
      |eapply list_ranked_extended;
       [eapply rank_extends_trans;
        [eapply rank_extends_write_side_contribution; exact Hcase1
        |apply rank_extends_mark_side_dirty]
       |intros x Hin; apply (proj1 (proj2 Hcontrol)); now right]
      |eapply continuation_ranked_extended;
       [eapply rank_extends_trans;
        [eapply rank_extends_write_side_contribution; exact Hcase1
        |apply rank_extends_mark_side_dirty]
       |exact (proj2 (proj2 Hcontrol))]]).
    all: try (change (control_ranked
      (R.cfg_state (R.continue_dead s f t t0 l0 c false))
      (R.cfg_control (R.continue_dead s f t t0 l0 c false)));
      apply control_ranked_continue_dead;
      [eapply frame_ranked_write_side_contribution;
       [exact (proj1 Hcontrol) |exact Hcase1]
      |eapply ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |apply (proj1 (proj2 Hcontrol)); now left]
      |eapply list_ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |intros x Hin; apply (proj1 (proj2 Hcontrol)); now right]
      |eapply continuation_ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |exact (proj2 (proj2 Hcontrol))]]).
    split.
    { apply fresh_frame_ranked.
      { eapply ranked_extended;
        [exact Hextends |exact (proj1 (proj1 Hcontrol))]. }
      exact (data_targets_ranked Hdata_after). }
    eapply continuation_ranked_extended;
      [exact Hextends |exact (proj2 Hcontrol)].
    assert (t = t0) as -> by (eapply queue_peek_pop_same; eauto).
    split.
    { change (ranked st t0).
      exact (proj1 (queue_pop_ranked
        (data_queue_ranked Hdata) Hcase2)). }
    split;
      [eapply frame_ranked_extended;
       [exact Hextends |exact (proj1 Hcontrol)]
      |eapply continuation_ranked_extended;
      [exact Hextends |exact (proj2 Hcontrol)]].
  Qed.

  Lemma next_config_queue_distinct :
    forall tf before after,
      queue_distinct (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      queue_distinct (R.cfg_state after).
  Proof.
    intros tf [st control] after Hdistinct Hstep.
    unfold R.next_config in Hstep.
    cbn [R.cfg_state R.cfg_control] in Hstep.
    destruct control; cbn [R.cfg_state R.cfg_control] in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hdistinct.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- queue_distinct (R.with_queue ?before ?rest) =>
          exact (queue_pop_distinct Hdistinct Hpop)
      end.
    all: try (apply queue_distinct_observe; exact Hdistinct).
    all: try (apply queue_distinct_materialize; exact Hdistinct).
    all: try (apply queue_distinct_materialize;
      apply enqueue_distinct; apply queue_distinct_observe; exact Hdistinct).
    all: try match goal with
      | Hset : R.set_value (R.flush_deferred ?before) ?fr ?direct =
          (?next, ?next_fr)
        |- queue_distinct ?next =>
          eapply queue_distinct_set_value;
          [apply queue_distinct_flush_deferred; exact Hdistinct | exact Hset]
      end.
    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- queue_distinct ?next =>
          eapply queue_distinct_set_value; [exact Hdistinct |exact Hset]
      end.
    all: try match goal with
      | Hcomplete : R.dirty_complete_get _ (R.observe ?before ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_distinct ?next =>
          eapply queue_distinct_dirty_complete_get;
          [apply queue_distinct_observe; exact Hdistinct |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get
          (R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_distinct ?next =>
          eapply queue_distinct_complete_get;
          [apply enqueue_distinct; apply queue_distinct_observe; exact Hdistinct
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_distinct ?next =>
          eapply queue_distinct_complete_get_after_observe;
          [exact Hdistinct |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get ?before ?fr ?target =
          (?next, ?next_fr, ?value)
        |- queue_distinct ?next =>
          eapply queue_distinct_complete_get; [exact Hdistinct |exact Hcomplete]
      end.
    all: try match goal with
      | Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr ?target ?input = (?next, ?changed)
        |- queue_distinct
          (R.cfg_state (R.continue_side ?next ?fr ?target ?body ?k ?changed)) =>
          apply queue_distinct_continue_side;
          eapply queue_distinct_write_side_contribution;
          [apply queue_distinct_observe; exact Hdistinct |exact Hwrite]
      end.
    all: try match goal with
      | Hwrite : R.write_side_contribution ?before ?fr ?target ?input =
          (?next, ?changed)
        |- queue_distinct
          (R.cfg_state
            (R.continue_dead ?next ?fr ?direct ?target ?rest ?k ?changed)) =>
          apply queue_distinct_continue_dead;
          eapply queue_distinct_write_side_contribution;
          [exact Hdistinct |exact Hwrite]
      end.
    all: try (change (queue_distinct
      (R.cfg_state (R.continue_side s f0 t r0 c true)));
      apply queue_distinct_continue_side;
      eapply queue_distinct_write_side_contribution;
      [apply queue_distinct_observe; exact Hdistinct |exact Hcase1]).
    all: try (change (queue_distinct
      (R.cfg_state
        (R.continue_side (R.mark_side_dirty s t) f0 t r0 c true)));
      apply queue_distinct_continue_side;
      apply queue_distinct_mark_side_dirty;
      eapply queue_distinct_write_side_contribution;
      [apply queue_distinct_observe; exact Hdistinct |exact Hcase1]).
    all: try (change (queue_distinct
      (R.cfg_state (R.continue_side s f0 t r0 c false)));
      apply queue_distinct_continue_side;
      eapply queue_distinct_write_side_contribution;
      [apply queue_distinct_observe; exact Hdistinct |exact Hcase1]).
    all: try (change (queue_distinct
      (R.cfg_state
        (R.continue_dead (R.mark_side_dirty s t0) f t t0 l0 c true)));
      apply queue_distinct_continue_dead;
      apply queue_distinct_mark_side_dirty;
      eapply queue_distinct_write_side_contribution;
      [exact Hdistinct |exact Hcase1]).
    all: try (change (queue_distinct
      (R.cfg_state (R.continue_dead s f t t0 l0 c false)));
      apply queue_distinct_continue_dead;
      eapply queue_distinct_write_side_contribution;
      [exact Hdistinct |exact Hcase1]).
    all: try (apply queue_distinct_clear_side_dirty;
      unfold queue_distinct; eapply queue_pop_distinct; eauto).
    all: unfold R.reset_registered_cells;
      destruct Features.restart_side_phases; cbn; exact Hdistinct.
  Qed.

  Lemma next_config_queue_ordered :
    forall tf before after,
      rank_valid (R.cfg_state before) ->
      state_data_ranked (R.cfg_state before) ->
      control_ranked (R.cfg_state before) (R.cfg_control before) ->
      queue_ordered (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      queue_ordered (R.cfg_state after).
  Proof.
    intros tf [st control] after Hvalid Hdata Hcontrol Hordered Hstep.
    unfold R.next_config in Hstep.
    cbn [R.cfg_state R.cfg_control] in Hstep.
    destruct control; cbn [R.cfg_state R.cfg_control] in Hstep;
      cbn in Hcontrol;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hordered.
    all: try (apply queue_ordered_observe; [exact Hdata |exact Hordered]).
    all: try (apply queue_ordered_materialize; exact Hordered).
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- queue_ordered (R.with_queue ?before ?rest) =>
          unfold queue_ordered; cbn;
          exact (proj1 (queue_pop_ordered Hordered Hpop))
      end.
    all: try (apply queue_ordered_materialize;
      apply enqueue_ordered;
      [eapply rank_valid_observe; [exact Hvalid |reflexivity]
      |exact (data_queue_ranked (state_data_ranked_observe t Hdata))
      |apply queue_ordered_observe; [exact Hdata |exact Hordered]
      |eapply observe_ranks_variable; reflexivity]).
    all: try match goal with
      | Hset : R.set_value (R.flush_deferred ?before) ?fr ?direct =
          (?next, ?next_fr)
        |- queue_ordered ?next =>
          eapply queue_ordered_set_value;
          [apply rank_valid_flush_deferred; exact Hvalid
          |apply state_data_ranked_flush_deferred; exact Hdata
          |apply queue_ordered_flush_deferred;
             [exact Hvalid | exact Hdata | exact Hordered]
          |exact Hset]
      end.
    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- queue_ordered ?next =>
          eapply queue_ordered_set_value;
          [exact Hvalid |exact Hdata |exact Hordered |exact Hset]
      end.
    all: try match goal with
      | Hcomplete : R.dirty_complete_get _ (R.observe ?before ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_ordered ?next =>
          eapply queue_ordered_dirty_complete_get;
          [eapply rank_valid_observe; [exact Hvalid |reflexivity]
          |apply state_data_ranked_observe; exact Hdata
          |apply queue_ordered_observe; [exact Hdata |exact Hordered]
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get
          (R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_ordered ?next =>
          eapply queue_ordered_complete_get;
          [apply enqueue_ordered;
           [eapply rank_valid_observe; [exact Hvalid |reflexivity]
           |exact (data_queue_ranked
              (state_data_ranked_observe target Hdata))
           |apply queue_ordered_observe; [exact Hdata |exact Hordered]
           |eapply observe_ranks_variable; reflexivity]
          |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- queue_ordered ?next =>
          eapply queue_ordered_complete_get_after_observe;
          [exact Hvalid |exact Hdata |exact Hordered |exact Hcomplete]
      end.
    all: try match goal with
      | Hcomplete : R.complete_get ?before ?fr ?target =
          (?next, ?next_fr, ?value)
        |- queue_ordered ?next =>
          eapply queue_ordered_complete_get; [exact Hordered |exact Hcomplete]
      end.
    all: try match goal with
      | Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?fr ?target ?input = (?next, ?changed)
        |- queue_ordered
          (R.cfg_state (R.continue_side ?next ?fr ?target ?body ?k ?changed)) =>
          apply queue_ordered_continue_side;
          [eapply rank_valid_write_side_contribution;
           [eapply rank_valid_observe; [exact Hvalid |reflexivity] |exact Hwrite]
          |eapply state_data_ranked_write_side_contribution;
           [apply state_data_ranked_observe; exact Hdata |exact Hwrite]
          |eapply queue_ordered_write_side_contribution;
           [apply queue_ordered_observe; [exact Hdata |exact Hordered]
           |exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_write_side_contribution; exact Hwrite
           |eapply observe_ranks_variable; reflexivity]]
      end.
    all: try match goal with
      | Hcontrol0 : frame_ranked ?before ?fr /\
          list_ranked ?before (?target :: ?rest) /\ _,
        Hwrite : R.write_side_contribution ?before ?fr ?target D.bottom =
          (?next, ?changed)
        |- queue_ordered
          (R.cfg_state
            (R.continue_dead ?next ?fr ?direct ?target ?rest ?k ?changed)) =>
          apply queue_ordered_continue_dead;
          [eapply rank_valid_write_side_contribution;
           [exact Hvalid |exact Hwrite]
          |eapply state_data_ranked_write_side_contribution;
           [exact Hdata |exact Hwrite]
          |eapply queue_ordered_write_side_contribution;
           [exact Hordered |exact Hwrite]
          |eapply ranked_extended;
           [eapply rank_extends_write_side_contribution; exact Hwrite
          |apply (proj1 (proj2 Hcontrol0)); now left]]
      end.
    all: try (change (queue_ordered
      (R.cfg_state (R.continue_side s f0 t r0 c true)));
      apply queue_ordered_continue_side;
      [eapply rank_valid_write_side_contribution;
       [eapply rank_valid_observe; [exact Hvalid |reflexivity] |exact Hcase1]
      |eapply state_data_ranked_write_side_contribution;
       [apply state_data_ranked_observe; exact Hdata |exact Hcase1]
      |eapply queue_ordered_write_side_contribution;
       [apply queue_ordered_observe; [exact Hdata |exact Hordered]
       |exact Hcase1]
      |eapply ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |eapply observe_ranks_variable; reflexivity]]).
    all: try (change (queue_ordered
      (R.cfg_state
        (R.continue_side (R.mark_side_dirty s t) f0 t r0 c true)));
      apply queue_ordered_continue_side;
      [apply rank_valid_mark_side_dirty;
       eapply rank_valid_write_side_contribution;
       [eapply rank_valid_observe; [exact Hvalid |reflexivity] |exact Hcase1]
      |apply state_data_ranked_mark_side_dirty;
       eapply state_data_ranked_write_side_contribution;
       [apply state_data_ranked_observe; exact Hdata |exact Hcase1]
      |apply queue_ordered_mark_side_dirty;
       eapply queue_ordered_write_side_contribution;
       [apply queue_ordered_observe; [exact Hdata |exact Hordered]
       |exact Hcase1]
      |eapply ranked_extended;
       [apply rank_extends_mark_side_dirty
       |eapply ranked_extended;
        [eapply rank_extends_write_side_contribution; exact Hcase1
        |eapply observe_ranks_variable; reflexivity]]]).
    all: try (change (queue_ordered
      (R.cfg_state (R.continue_side s f0 t r0 c false)));
      apply queue_ordered_continue_side;
      [eapply rank_valid_write_side_contribution;
       [eapply rank_valid_observe; [exact Hvalid |reflexivity] |exact Hcase1]
      |eapply state_data_ranked_write_side_contribution;
       [apply state_data_ranked_observe; exact Hdata |exact Hcase1]
      |eapply queue_ordered_write_side_contribution;
       [apply queue_ordered_observe; [exact Hdata |exact Hordered]
       |exact Hcase1]
      |eapply ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |eapply observe_ranks_variable; reflexivity]]).
    all: try (change (queue_ordered
      (R.cfg_state
        (R.continue_dead (R.mark_side_dirty s t0) f t t0 l0 c true)));
      apply queue_ordered_continue_dead;
      [apply rank_valid_mark_side_dirty;
       eapply rank_valid_write_side_contribution; [exact Hvalid |exact Hcase1]
      |apply state_data_ranked_mark_side_dirty;
       eapply state_data_ranked_write_side_contribution;
       [exact Hdata |exact Hcase1]
      |apply queue_ordered_mark_side_dirty;
       eapply queue_ordered_write_side_contribution;
       [exact Hordered |exact Hcase1]
      |eapply ranked_extended;
       [apply rank_extends_mark_side_dirty
       |eapply ranked_extended;
        [eapply rank_extends_write_side_contribution; exact Hcase1
        |apply (proj1 (proj2 Hcontrol)); now left]]]).
    all: try (change (queue_ordered
      (R.cfg_state (R.continue_dead s f t t0 l0 c false)));
      apply queue_ordered_continue_dead;
      [eapply rank_valid_write_side_contribution; [exact Hvalid |exact Hcase1]
      |eapply state_data_ranked_write_side_contribution;
       [exact Hdata |exact Hcase1]
      |eapply queue_ordered_write_side_contribution;
       [exact Hordered |exact Hcase1]
      |eapply ranked_extended;
       [eapply rank_extends_write_side_contribution; exact Hcase1
       |apply (proj1 (proj2 Hcontrol)); now left]]).
    all: try (apply queue_ordered_clear_side_dirty;
      unfold queue_ordered, queue_ordered_at, rank_above, R.rank_lt; cbn;
      exact (proj1 (queue_pop_ordered Hordered Hcase1))).
    all: unfold R.reset_registered_cells;
      destruct Features.restart_side_phases; cbn; exact Hordered.
  Qed.

  Lemma next_config_configuration_ranked :
    forall tf before after,
      configuration_ranked before ->
      R.next_config tf before = Some after ->
      configuration_ranked after.
  Proof.
    intros tf before after
      [Hvalid Hdata Hcontrol Hdistinct Hordered] Hstep.
    constructor.
    - eapply next_config_rank_valid; eauto.
    - eapply next_config_state_data_ranked; eauto.
    - eapply next_config_control_ranked; eauto.
    - eapply next_config_queue_distinct; eauto.
    - eapply next_config_queue_ordered; eauto.
  Qed.

  Lemma steps_configuration_ranked :
    forall tf before after,
      configuration_ranked before ->
      Sem.steps tf before after ->
      configuration_ranked after.
  Proof.
    intros tf before after Hranked Hsteps.
    induction Hsteps; [exact Hranked |].
    apply IHHsteps. eapply next_config_configuration_ranked; eauto.
  Qed.

  Theorem reachable_configuration_ranked :
    forall tf roots c,
      Sem.steps tf (R.initial_config roots) c ->
      configuration_ranked c.
  Proof.
    intros tf roots c Hsteps.
    eapply steps_configuration_ranked; [apply initial_configuration_ranked |].
    exact Hsteps.
  Qed.

  Lemma rank_lt_true_ranked :
    forall st x y,
      R.rank_lt st x y = true -> ranked st x /\ ranked st y.
  Proof.
    intros st x y Hlt.
    unfold R.rank_lt, R.ranking_lt in Hlt.
    destruct (R.Ranking.lookup (R.ranking st) x) as [xr |] eqn:Hx;
      try discriminate.
    destruct (R.Ranking.lookup (R.ranking st) y) as [yr |] eqn:Hy;
      try discriminate.
    split; eexists; eauto.
  Qed.

  (** Termination-only finite-support and scheduler measures are intentionally
      absent from this soundness-only development. *)

  Lemma complete_get_owner :
    forall st fr target st' fr' value,
      R.complete_get st fr target = (st', fr', value) ->
      R.frame_owner fr' = R.frame_owner fr.
  Proof.
    intros st fr target st' fr' value Hget.
    unfold R.complete_get in Hget. inversion Hget. reflexivity.
  Qed.

  Local Transparent R.dirty_complete_get.

  Lemma dirty_complete_get_owner :
    forall tf st fr target st' fr' value,
      R.dirty_complete_get tf st fr target = (st', fr', value) ->
      R.frame_owner fr' = R.frame_owner fr.
  Proof.
    intros tf st fr target st' fr' value Hget.
    unfold R.dirty_complete_get in Hget.
    repeat destruct (_ : bool); repeat destruct (_ : option R.state);
      inversion Hget; reflexivity.
  Qed.

  Local Opaque R.dirty_complete_get.

  Lemma record_side_input_owner :
    forall fr target raw fr' input,
      R.record_side_input fr target raw = (fr', input) ->
      R.frame_owner fr' = R.frame_owner fr.
  Proof.
    intros fr target raw fr' input Hrecord.
    unfold R.record_side_input in Hrecord. inversion Hrecord. reflexivity.
  Qed.

  Lemma set_value_owner :
    forall st fr direct st' fr',
      R.set_value st fr direct = (st', fr') ->
      R.frame_owner fr' = R.frame_owner fr.
  Proof.
    intros st fr direct st' fr' Hset. unfold R.set_value in Hset.
    repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      end;
      try destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr))));
      inversion Hset; reflexivity.
  Qed.

  Module Termination.

    Lemma steps_transitive :
      forall tf first middle final,
        Sem.steps tf first middle ->
        Sem.steps tf middle final ->
        Sem.steps tf first final.
    Proof.
      intros tf first middle final Hfirst Hlast.
      induction Hfirst; [exact Hlast |econstructor; eauto].
    Qed.

    Lemma steps_append_one :
      forall tf first middle final,
        Sem.steps tf first middle ->
        Sem.step tf middle final ->
        Sem.steps tf first final.
    Proof.
      intros. eapply steps_transitive; [exact H |].
      econstructor; [exact H0 |constructor].
    Qed.

    Definition sigma_extends (before after : R.state) : Prop :=
      forall x value,
        M.lookup (R.sigma before) x = Some value ->
        exists next_value, M.lookup (R.sigma after) x = Some next_value.

    Lemma sigma_extends_refl : forall st, sigma_extends st st.
    Proof. intros st x value Hlookup. eauto. Qed.

    Lemma sigma_extends_trans :
      forall first middle final,
        sigma_extends first middle -> sigma_extends middle final ->
        sigma_extends first final.
    Proof.
      intros first middle final Hfirst Hlast x value Hlookup.
      destruct (Hfirst x value Hlookup) as [middle_value Hmiddle].
      now apply (Hlast x middle_value Hmiddle).
    Qed.

    Lemma sigma_extends_same :
      forall before after,
        R.sigma after = R.sigma before -> sigma_extends before after.
    Proof. intros before after Heq x value Hlookup. rewrite Heq. eauto. Qed.

    Lemma sigma_extends_observe :
      forall st x, sigma_extends st (R.observe st x).
    Proof.
      intros. apply sigma_extends_same. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) x); reflexivity.
    Qed.

    Lemma sigma_extends_with_queue :
      forall st queue, sigma_extends st (R.with_queue st queue).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_enqueue :
      forall st x, sigma_extends st (R.enqueue st x).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_flush_deferred :
      forall st, sigma_extends st (R.flush_deferred st).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_materialize :
      forall st target, sigma_extends st (R.materialize st target).
    Proof.
      intros st target x value Hlookup. unfold R.materialize.
      destruct (M.lookup (R.sigma st) target) eqn:Htarget; [eauto |].
      destruct (V.eq_dec x target) as [-> |Hneq].
      - congruence.
      - cbn. rewrite ML.lookup_update_other by exact Hneq. eauto.
    Qed.

    Lemma sigma_extends_complete_get :
      forall st fr target next next_fr value,
        R.complete_get st fr target = (next, next_fr, value) ->
        sigma_extends st next.
    Proof.
      intros st fr target next next_fr value Hget.
      unfold R.complete_get in Hget.
      repeat match type of Hget with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        end;
        inversion Hget; subst; cbn;
        match goal with
        | |- sigma_extends st (R.materialize ?base target) =>
            eapply sigma_extends_trans with (middle := base);
            [apply sigma_extends_same; reflexivity
            |apply sigma_extends_materialize]
        end.
    Qed.

    Lemma write_side_contribution_sigma :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        R.sigma next = R.sigma st.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      destruct (R.side_update (R.promote_side_target st fr target) (R.frame_owner fr) target input) as [phase contribution].
      inversion Hwrite; subst; cbn.
      unfold R.promote_side_target, R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma sigma_extends_write_side_contribution :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        sigma_extends st next.
    Proof.
      intros. apply sigma_extends_same.
      now apply write_side_contribution_sigma in H.
    Qed.

    Lemma sigma_extends_continue_side :
      forall st fr target body k changed,
        sigma_extends st
          (R.cfg_state (R.continue_side st fr target body k changed)).
    Proof.
      intros. unfold R.continue_side.
      repeat destruct (_ : bool); cbn;
        auto using sigma_extends_refl, sigma_extends_enqueue.
    Qed.

    Lemma sigma_extends_continue_dead :
      forall st fr direct target remaining k changed,
        sigma_extends st
          (R.cfg_state
            (R.continue_dead st fr direct target remaining k changed)).
    Proof.
      intros. unfold R.continue_dead.
      repeat destruct (_ : bool); cbn;
        auto using sigma_extends_refl, sigma_extends_enqueue.
    Qed.

    Lemma sigma_extends_set_value :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        sigma_extends st next.
    Proof.
      intros st fr direct next next_fr Hset. unfold R.set_value in Hset.
      repeat match type of Hset with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        end;
        try destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
          (R.sigma_value st (R.frame_owner fr))
          (D.join direct (R.aggregate st (R.frame_owner fr))));
        inversion Hset; subst; cbn; try apply sigma_extends_refl.
      all: intros x old Hlookup.
      all: destruct (V.eq_dec x (R.frame_owner fr)) as [-> |Hneq].
      all: cbn.
      all: try rewrite ML.lookup_update_same.
      all: try rewrite ML.lookup_update_other by exact Hneq.
      all: eauto.
    Qed.

    Lemma sigma_extends_reset_registered_cells :
      forall st owner, sigma_extends st (R.reset_registered_cells st owner).
    Proof.
      intros. apply sigma_extends_same.
      unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma sigma_extends_remember_dormant :
      forall st variable, sigma_extends st (R.remember_dormant st variable).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_add_reader :
      forall st target owner, sigma_extends st (R.add_reader st target owner).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_mark_side_dirty :
      forall st target, sigma_extends st (R.mark_side_dirty st target).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_clear_side_dirty :
      forall st target, sigma_extends st (R.clear_side_dirty st target).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_promote_controlled :
      forall st target, sigma_extends st (R.promote_controlled st target).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_cancel_dirty_target :
      forall st target, sigma_extends st (R.cancel_dirty_target st target).
    Proof. intros. apply sigma_extends_same. reflexivity. Qed.

    Lemma sigma_extends_write_dirty_value :
      forall st target value,
        sigma_extends st (R.write_dirty_value st target value).
    Proof.
      intros st target new_value x old Hlookup.
      unfold R.write_dirty_value. cbn.
      destruct (V.eq_dec x target) as [-> |Hneq].
      - exists new_value. now rewrite ML.lookup_update_same.
      - exists old. now rewrite ML.lookup_update_other by exact Hneq.
    Qed.

    Lemma sigma_extends_try_dirty_read :
      forall tf st owner target next,
        R.try_dirty_read tf st owner target = Some next ->
        sigma_extends st next.
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
        eauto using sigma_extends_cancel_dirty_target,
          sigma_extends_write_dirty_value, sigma_extends_promote_controlled,
          sigma_extends_trans.
    Qed.

    Local Transparent R.dirty_complete_get.

    Lemma sigma_extends_dirty_complete_get :
      forall tf st fr target next next_fr value,
        R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
        sigma_extends st next.
    Proof.
      intros tf st fr target next next_fr value Hcomplete.
      unfold R.dirty_complete_get in Hcomplete.
      repeat
        match type of Hcomplete with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        end;
        inversion Hcomplete; subst; cbn.
      all: eapply sigma_extends_trans; [|apply sigma_extends_add_reader].
      all: try (eapply sigma_extends_trans;
        [apply sigma_extends_materialize
        |eapply sigma_extends_try_dirty_read; eassumption]).
      all: try apply sigma_extends_materialize.
      all: eapply sigma_extends_trans;
        [apply sigma_extends_promote_controlled |].
      all: try (eapply sigma_extends_trans;
        [apply sigma_extends_materialize
        |eapply sigma_extends_try_dirty_read; eassumption]).
      all: apply sigma_extends_materialize.
    Qed.

    Local Opaque R.dirty_complete_get.

    Lemma is_dormant_sigma_absent :
      forall st target,
        R.is_dormant st target = true ->
        M.lookup (R.sigma st) target = None.
    Proof.
      intros st target Hdormant. unfold R.is_dormant in Hdormant.
      destruct (S.mem target (R.dormant_bottom st)); [|discriminate].
      destruct (M.lookup (R.sigma st) target); discriminate || reflexivity.
    Qed.

    Lemma sigma_extends_publish_absent :
      forall st target changed,
        M.lookup (R.sigma st) target = None ->
        sigma_extends st (R.publish_dormant_target st target changed).
    Proof.
      intros st target changed Habsent x old Hlookup.
      unfold R.publish_dormant_target, R.materialize.
      rewrite Habsent. destruct changed; cbn;
        destruct (V.eq_dec x target) as [-> |Hneq].
      - rewrite Habsent in Hlookup. discriminate.
      - repeat rewrite ML.lookup_update_other by exact Hneq.
        exists old. exact Hlookup.
      - rewrite Habsent in Hlookup. discriminate.
      - repeat rewrite ML.lookup_update_other by exact Hneq.
        exists old. exact Hlookup.
    Qed.

    Lemma next_config_sigma_extends :
      forall tf before after,
        R.next_config tf before = Some after ->
        sigma_extends (R.cfg_state before) (R.cfg_state after).
    Proof.
      intros tf [st control] after Hstep. destruct control as
        [|roots |remaining |owner k |fr body k |fr direct pending k
         |fr direct k |fr k |k].
      - cbn in Hstep. destruct (R.queue_pop (R.queue st)); try discriminate.
        destruct p. inversion Hstep; subst. apply sigma_extends_with_queue.
      - destruct roots as [|root roots]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. apply sigma_extends_refl.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. apply sigma_extends_refl.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. apply sigma_extends_observe.
            -- destruct (R.pure_bottom_rhs tf root).
              ++ inversion Hstep; subst. apply sigma_extends_remember_dormant.
              ++ inversion Hstep; subst. apply sigma_extends_observe.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[owner rest] |].
        + inversion Hstep; subst. apply sigma_extends_with_queue.
        + inversion Hstep; subst. apply sigma_extends_refl.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        eapply sigma_extends_trans.
        + apply sigma_extends_materialize.
        + apply sigma_extends_clear_side_dirty.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. apply sigma_extends_refl.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          destruct (R.is_dormant st target).
          * inversion Hstep; subst. apply sigma_extends_add_reader.
          * destruct (R.Ranking.lookup (R.ranking st) target) eqn:Hrank.
            -- set (observed := R.observe st target) in *.
               destruct (R.is_materialized observed target).
               ++ destruct (R.dirty_complete_get tf observed fr target)
                    as [[next_st next_fr] read] eqn:Hget.
                  inversion Hstep; subst.
                  eapply sigma_extends_trans.
                  ** unfold observed. apply sigma_extends_observe.
                  ** eapply sigma_extends_dirty_complete_get. exact Hget.
               ++ destruct (R.rank_lt observed (R.frame_owner fr) target).
                  ** inversion Hstep; subst. unfold observed.
                     apply sigma_extends_observe.
                  ** destruct (R.complete_get (R.enqueue observed target)
                       fr target) as [[next_st next_fr] read] eqn:Hget.
                     inversion Hstep; subst.
                     eapply sigma_extends_trans.
                     --- unfold observed. apply sigma_extends_observe.
                     --- eapply sigma_extends_trans.
                         +++ apply sigma_extends_enqueue.
                         +++ eapply sigma_extends_complete_get. exact Hget.
            -- destruct (R.pure_bottom_rhs tf target &&
                  negb (R.is_materialized st target))%bool.
               ++ inversion Hstep; subst. eapply sigma_extends_trans.
                  ** apply sigma_extends_remember_dormant.
                  ** apply sigma_extends_add_reader.
               ++ set (observed := R.observe st target) in *.
                  destruct (negb (R.is_materialized observed target) &&
                    R.rank_lt observed (R.frame_owner fr) target)%bool.
                  ** inversion Hstep; subst. unfold observed.
                     apply sigma_extends_observe.
                  ** set (base := if R.is_materialized observed target
                       then observed else R.enqueue observed target) in *.
                     destruct (R.complete_get base fr target)
                       as [[next_st next_fr] read] eqn:Hget.
                     inversion Hstep; subst.
                     eapply sigma_extends_trans with (middle := base).
                     --- unfold base, observed. destruct (R.is_materialized
                          (R.observe st target) target).
                         +++ apply sigma_extends_observe.
                         +++ eapply sigma_extends_trans with
                              (middle := R.observe st target);
                              [exact (@sigma_extends_observe st target)
                              |exact (@sigma_extends_enqueue
                                (R.observe st target) target)].
                     --- eapply sigma_extends_complete_get; exact Hget.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution (R.observe st target)
            fr1 target input) as [next_st changed] eqn:Hwrite.
          destruct (R.is_dormant st target).
          * inversion Hstep; subst. eapply sigma_extends_trans.
            -- apply sigma_extends_observe.
            -- eapply sigma_extends_trans.
               ++ eapply sigma_extends_write_side_contribution; exact Hwrite.
               ++ change (sigma_extends next_st
                    (R.cfg_state
                      (R.continue_side next_st fr1 target next k true))).
                  apply sigma_extends_continue_side.
          * destruct changed.
            -- inversion Hstep; subst.
               eapply sigma_extends_trans with (middle := R.observe st target).
               ++ apply sigma_extends_observe.
               ++ eapply sigma_extends_trans with (middle := next_st).
                  ** eapply sigma_extends_write_side_contribution; exact Hwrite.
                  ** eapply sigma_extends_trans with
                       (middle := R.mark_side_dirty next_st target).
                     --- apply sigma_extends_mark_side_dirty.
                     --- change (sigma_extends (R.mark_side_dirty next_st target)
                          (R.cfg_state
                            (R.continue_side
                              (R.mark_side_dirty next_st target)
                              fr1 target next k true))).
                         exact (sigma_extends_continue_side
                           (R.mark_side_dirty next_st target)
                           fr1 target next k true).
            -- inversion Hstep; subst. eapply sigma_extends_trans.
               ++ apply sigma_extends_observe.
               ++ eapply sigma_extends_trans.
                  ** eapply sigma_extends_write_side_contribution; exact Hwrite.
                  ** change (sigma_extends next_st
                       (R.cfg_state
                         (R.continue_side next_st fr1 target next k false))).
                     apply sigma_extends_continue_side.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          destruct (R.is_dormant st target).
          * inversion Hstep; subst. apply sigma_extends_refl.
          * destruct (R.Ranking.lookup (R.ranking st) target).
            -- set (observed := R.observe st target) in *.
               destruct (R.is_materialized observed target).
               ++ inversion Hstep; subst. unfold observed.
                  apply sigma_extends_observe.
               ++ destruct (R.rank_lt observed (R.frame_owner fr) target).
                  ** inversion Hstep; subst. unfold observed.
                     apply sigma_extends_observe.
                  ** inversion Hstep; subst. eapply sigma_extends_trans.
                     --- unfold observed. apply sigma_extends_observe.
                     --- eapply sigma_extends_trans;
                          [apply sigma_extends_enqueue
                          |apply sigma_extends_materialize].
            -- destruct (R.pure_bottom_rhs tf target &&
                  negb (R.is_materialized st target))%bool.
               ++ inversion Hstep; subst. apply sigma_extends_remember_dormant.
               ++ set (observed := R.observe st target) in *.
                  destruct (R.is_materialized observed target).
                  ** inversion Hstep; subst. unfold observed.
                     apply sigma_extends_observe.
                  ** destruct (R.rank_lt observed (R.frame_owner fr) target).
                     --- inversion Hstep; subst. unfold observed.
                         apply sigma_extends_observe.
                     --- inversion Hstep; subst. eapply sigma_extends_trans.
                         +++ unfold observed. apply sigma_extends_observe.
                         +++ eapply sigma_extends_trans;
                              [apply sigma_extends_enqueue
                              |apply sigma_extends_materialize].
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          apply sigma_extends_same. reflexivity.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. apply sigma_extends_refl.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [next_st changed] eqn:Hwrite.
        destruct changed.
        -- inversion Hstep; subst.
           eapply sigma_extends_trans with (middle := next_st).
           ++ eapply sigma_extends_write_side_contribution; exact Hwrite.
           ++ eapply sigma_extends_trans with
                (middle := R.mark_side_dirty next_st target).
              ** apply sigma_extends_mark_side_dirty.
              ** change (sigma_extends (R.mark_side_dirty next_st target)
                   (R.cfg_state
                      (R.continue_dead (R.mark_side_dirty next_st target)
                         fr direct target remaining k true))).
                 exact (sigma_extends_continue_dead
                   (R.mark_side_dirty next_st target)
                   fr direct target remaining k true).
        -- inversion Hstep; subst. eapply sigma_extends_trans.
           ++ eapply sigma_extends_write_side_contribution; exact Hwrite.
           ++ change (sigma_extends next_st
                (R.cfg_state
                   (R.continue_dead next_st fr direct target remaining k false))).
              apply sigma_extends_continue_dead.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value (R.flush_deferred st) fr direct)
          as [next_st next_fr] eqn:Hset.
        inversion Hstep; subst. eapply sigma_extends_trans.
        + apply sigma_extends_flush_deferred.
        + eapply sigma_extends_set_value; exact Hset.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head rest] |];
              try discriminate. inversion Hstep; subst.
            eapply sigma_extends_trans.
            -- apply sigma_extends_with_queue.
            -- apply sigma_extends_clear_side_dirty.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head rest] |];
                 try discriminate. inversion Hstep; subst.
               apply sigma_extends_with_queue.
            -- inversion Hstep; subst. apply sigma_extends_reset_registered_cells.
        + inversion Hstep; subst. apply sigma_extends_reset_registered_cells.
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep;
          try (inversion Hstep; subst; apply sigma_extends_refl).
        destruct (R.complete_get st fr target)
          as [[next_st next_fr] value] eqn:Hget.
        inversion Hstep; subst. eapply sigma_extends_complete_get; exact Hget.
    Qed.

    Fixpoint continuation_below
      (st : R.state) (upper : V.t) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          R.rank_lt st (R.frame_owner fr) upper = true /\
          continuation_below st (R.frame_owner fr) rest
      end.

    Definition continuation_ordered
      (st : R.state) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest => continuation_below st (R.frame_owner fr) rest
      end.

    Definition control_ordered
      (st : R.state) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
      | R.StartEpisode owner k => continuation_below st owner k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k => continuation_below st (R.frame_owner fr) k
      | R.Return k => continuation_ordered st k
      end.

    Lemma continuation_below_extended :
      forall before after upper k,
        rank_extends before after -> ranked before upper ->
        continuation_ranked before k ->
        continuation_below before upper k ->
        continuation_below after upper k.
    Proof.
      intros before after upper k Hextends Hupper.
      revert upper Hupper. induction k; cbn;
        intros upper Hupper Hranked Hbelow; try exact I.
      all: destruct Hranked as [Hfr Htail].
      all: try destruct Htail as [Htarget Hrest].
      all: destruct Hbelow as [Hlt Hbelow]; split.
      all: try (rewrite <- (@rank_lt_stable before after
        (R.frame_owner f) upper Hextends (proj1 Hfr) Hupper); exact Hlt).
      all: eapply IHk; eauto; exact (proj1 Hfr).
    Qed.

    Lemma continuation_ordered_tail :
      forall st fr k,
        continuation_below st (R.frame_owner fr) k ->
        continuation_ordered st k.
    Proof. intros st fr k Hbelow. destruct k; cbn in *; tauto. Qed.

    Lemma continuation_ordered_extended :
      forall before after k,
        rank_extends before after -> continuation_ranked before k ->
        continuation_ordered before k -> continuation_ordered after k.
    Proof.
      intros before after k Hextends Hranked Hordered.
      destruct k; cbn in *; try exact I.
      all: destruct Hranked as [Hfr Htail].
      all: try destruct Htail as [Htarget Hrest].
      all: eapply continuation_below_extended; eauto; exact (proj1 Hfr).
    Qed.

    Lemma control_ordered_extended :
      forall before after control,
        rank_extends before after -> control_ranked before control ->
        control_ordered before control -> control_ordered after control.
    Proof.
      intros before after control Hextends Hranked Hordered.
      destruct control; cbn in *; try exact I.
      - destruct Hranked as [Howner Hk].
        eapply continuation_below_extended; eauto.
      - destruct Hranked as [Hfr Hk].
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - destruct Hranked as [Hfr [Hpending Hk]].
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - destruct Hranked as [Hfr Hk].
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - destruct Hranked as [Hfr Hk].
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - eapply continuation_ordered_extended; eauto.
    Qed.

    Lemma next_runrhs_control_ordered :
      forall tf st fr body k after,
        frame_ranked st fr -> continuation_ranked st k ->
        continuation_below st (R.frame_owner fr) k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} =
          Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf st fr body k after Hfr Hk Hordered Hstep.
      pose proof (@next_config_rank_extends tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
        after Hstep) as Hextends.
      destruct body as [direct |target next |target raw next |target next].
      - cbn in Hstep. inversion Hstep; subst.
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        destruct (R.is_dormant st target).
        + inversion Hstep; subst.
          eapply continuation_below_extended; eauto. exact (proj1 Hfr).
        + destruct (R.Ranking.lookup (R.ranking st) target).
          * remember (R.observe st target) as observed eqn:Hobserve.
            assert (Hext0 : rank_extends st observed).
            { subst. exact (@rank_extends_observe st target
                (R.observe st target) eq_refl). }
            assert (Howner0 : ranked observed (R.frame_owner fr)).
            { eapply ranked_extended; eauto. exact (proj1 Hfr). }
            assert (Hk0 : continuation_ranked observed k).
            { eapply continuation_ranked_extended; eauto. }
            assert (Hordered0 :
              continuation_below observed (R.frame_owner fr) k).
            { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
            destruct (R.is_materialized observed target) eqn:Hmaterialized.
            -- destruct (R.dirty_complete_get tf observed fr target)
                 as [[next_st next_fr] value] eqn:Hget.
               inversion Hstep; subst. cbn.
               rewrite (dirty_complete_get_owner Hget).
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
            -- destruct (R.rank_lt observed (R.frame_owner fr) target)
                 eqn:Hguard.
               ++ inversion Hstep; subst. cbn. split; assumption.
               ++ destruct (R.complete_get (R.enqueue observed target)
                    fr target) as [[next_st next_fr] value] eqn:Hget.
                  inversion Hstep; subst. cbn.
                  rewrite (complete_get_owner Hget).
                  eapply continuation_below_extended; eauto.
                  exact (proj1 Hfr).
          * destruct (R.pure_bottom_rhs tf target &&
              negb (R.is_materialized st target))%bool.
            -- inversion Hstep; subst.
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
            -- remember (R.observe st target) as observed eqn:Hobserve.
               assert (Hext0 : rank_extends st observed).
               { subst. exact (@rank_extends_observe st target
                   (R.observe st target) eq_refl). }
               assert (Howner0 : ranked observed (R.frame_owner fr)).
               { eapply ranked_extended; eauto. exact (proj1 Hfr). }
               assert (Hk0 : continuation_ranked observed k).
               { eapply continuation_ranked_extended; eauto. }
               assert (Hordered0 :
                 continuation_below observed (R.frame_owner fr) k).
               { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
               destruct (negb (R.is_materialized observed target) &&
                 R.rank_lt observed (R.frame_owner fr) target)%bool eqn:Hguard.
               ++ apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
                  cbn. split; [exact (proj2 Hguard) |exact Hordered0].
               ++ remember (if R.is_materialized observed target
                    then observed else R.enqueue observed target) as base.
                  destruct (R.complete_get base fr target)
                    as [[next_st next_fr] value] eqn:Hget.
                  inversion Hstep; subst. cbn.
                  rewrite (complete_get_owner Hget).
                  eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - cbn -[R.observe R.record_side_input
          R.write_side_contribution R.continue_side] in Hstep.
        remember (R.observe st target) as observed eqn:Hobserve.
        destruct (R.record_side_input fr target raw)
          as [fr1 input] eqn:Hrecord.
        pose proof (@record_side_input_owner fr target raw fr1 input Hrecord)
          as Howner.
        destruct (R.write_side_contribution observed fr1 target input)
          as [next_st changed] eqn:Hwrite.
        destruct (R.is_dormant st target) eqn:Hdormant.
        + unfold R.continue_side in Hstep.
          destruct (R.rank_lt next_st (R.frame_owner fr1) target &&
            negb (R.is_materialized next_st target))%bool eqn:Hguard.
          * apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
            cbn. split; [exact (proj1 Hguard) |]. rewrite Howner.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
          * inversion Hstep; subst. cbn. rewrite Howner.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
        + destruct changed.
          * unfold R.continue_side in Hstep.
            destruct (R.rank_lt (R.mark_side_dirty next_st target)
                (R.frame_owner fr1) target &&
              negb (R.is_materialized
                (R.mark_side_dirty next_st target) target))%bool eqn:Hguard.
            -- apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
               cbn. split; [exact (proj1 Hguard) |]. rewrite Howner.
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
            -- inversion Hstep; subst. cbn. rewrite Howner.
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
          * inversion Hstep; subst. cbn. rewrite Howner.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - cbn -[R.observe R.materialize R.enqueue] in Hstep.
        destruct (R.is_dormant st target).
        + inversion Hstep; subst. exact Hordered.
        + destruct (R.Ranking.lookup (R.ranking st) target).
          * remember (R.observe st target) as observed eqn:Hobserve.
            assert (Hext0 : rank_extends st observed).
            { subst. exact (@rank_extends_observe st target
                (R.observe st target) eq_refl). }
            assert (Hordered0 :
              continuation_below observed (R.frame_owner fr) k).
            { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
            destruct (R.is_materialized observed target).
            -- inversion Hstep; subst. exact Hordered0.
            -- destruct (R.rank_lt observed (R.frame_owner fr) target) eqn:Hlt.
               ++ inversion Hstep; subst. cbn. split; assumption.
               ++ inversion Hstep; subst.
                  eapply continuation_below_extended; eauto. exact (proj1 Hfr).
          * destruct (R.pure_bottom_rhs tf target &&
              negb (R.is_materialized st target))%bool.
            -- inversion Hstep; subst.
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
            -- remember (R.observe st target) as observed eqn:Hobserve.
               assert (Hext0 : rank_extends st observed).
               { subst. exact (@rank_extends_observe st target
                   (R.observe st target) eq_refl). }
               assert (Hordered0 :
                 continuation_below observed (R.frame_owner fr) k).
               { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
               destruct (R.is_materialized observed target).
               ++ inversion Hstep; subst. exact Hordered0.
               ++ destruct (R.rank_lt observed (R.frame_owner fr) target)
                    eqn:Hlt.
                  ** inversion Hstep; subst. cbn. split; assumption.
                  ** inversion Hstep; subst.
                     eapply continuation_below_extended; eauto.
                     exact (proj1 Hfr).
    Qed.

    Lemma next_rundead_control_ordered :
      forall tf st fr direct pending k after,
        frame_ranked st fr -> continuation_ranked st k ->
        continuation_below st (R.frame_owner fr) k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf st fr direct pending k after Hfr Hk Hordered Hstep.
      pose proof (@next_config_rank_extends tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |}
        after Hstep) as Hextends.
      destruct pending as [|target remaining].
      - cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        + inversion Hstep; subst.
          eapply continuation_below_extended; eauto. exact (proj1 Hfr).
        + destruct (R.write_side_contribution st fr target D.bottom)
            as [next_st changed] eqn:Hwrite.
          unfold R.continue_dead in Hstep. destruct changed.
          * destruct (R.rank_lt (R.mark_side_dirty next_st target)
                (R.frame_owner fr) target &&
              negb (R.is_materialized
                (R.mark_side_dirty next_st target) target))%bool eqn:Hguard.
            -- apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
               cbn. split; [exact (proj1 Hguard) |].
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
            -- inversion Hstep; subst. cbn.
               eapply continuation_below_extended; eauto. exact (proj1 Hfr).
          * inversion Hstep; subst. cbn.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
    Qed.

    Lemma next_runcommit_control_ordered :
      forall tf st fr direct k after,
        frame_ranked st fr -> continuation_ranked st k ->
        continuation_below st (R.frame_owner fr) k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit fr direct k |} = Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf st fr direct k after Hfr Hk Hordered Hstep.
      pose proof (@next_config_rank_extends tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunCommit fr direct k |}
        after Hstep) as Hextends.
      cbn -[R.set_value] in Hstep.
      destruct (R.set_value (R.flush_deferred st) fr direct)
        as [next_st next_fr] eqn:Hset.
      inversion Hstep; subst. cbn.
      rewrite (@set_value_owner (R.flush_deferred st) fr direct
        next_st next_fr Hset).
      eapply continuation_below_extended; eauto. exact (proj1 Hfr).
    Qed.

    Lemma next_rundrain_control_ordered :
      forall tf st fr k after,
        frame_ranked st fr -> continuation_ranked st k ->
        continuation_below st (R.frame_owner fr) k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} =
          Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf st fr k after Hfr Hk Hordered Hstep.
      pose proof (@next_config_rank_extends tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
        after Hstep) as Hextends.
      assert (Hbelow_after :
        continuation_below (R.cfg_state after) (R.frame_owner fr) k).
      { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      - destruct (V.eq_dec next (R.frame_owner fr)).
        + destruct (R.queue_pop (R.queue st)) as [[head rest] |];
            try discriminate. inversion Hstep; subst. exact Hbelow_after.
        + destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hlt.
          * destruct (R.queue_pop (R.queue st)) as [[head rest] |];
              try discriminate. inversion Hstep; subst. cbn.
            split; [exact Hlt |exact Hbelow_after].
          * inversion Hstep; subst. now apply continuation_ordered_tail with fr.
      - inversion Hstep; subst. now apply continuation_ordered_tail with fr.
    Qed.

    Lemma next_return_control_ordered :
      forall tf st k after,
        continuation_ranked st k -> continuation_ordered st k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf st k after Hranked Hordered Hstep.
      pose proof (@next_config_rank_extends tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |}
        after Hstep) as Hextends.
      destruct k; cbn -[R.complete_get] in Hstep;
        cbn in Hranked, Hordered.
      - inversion Hstep; subst. exact I.
      - inversion Hstep; subst. exact I.
      - destruct Hranked as [Hfr [Htarget Hrest]].
        destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst. cbn. rewrite (complete_get_owner Hget).
        eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - destruct Hranked as [Hfr Hrest]. inversion Hstep; subst.
        exact Hordered.
      - destruct Hranked as [Hfr Hrest]. inversion Hstep; subst.
        exact Hordered.
      - destruct Hranked as [Hfr [Hpending Hrest]]. inversion Hstep; subst.
        exact Hordered.
      - destruct Hranked as [Hfr Hrest]. inversion Hstep; subst.
        exact Hordered.
    Qed.

    Lemma next_config_control_ordered :
      forall tf before after,
        configuration_ranked before ->
        control_ordered (R.cfg_state before) (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf [st control] after Hranked Hordered Hstep.
      destruct Hranked as [Hvalid Hdata Hcontrol Hdistinct Hqueue].
      destruct control as
        [|roots |remaining |owner k |fr body k |fr direct pending k
         |fr direct k |fr k |k].
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[owner rest] |]; try discriminate.
        inversion Hstep; subst. exact I.
      - destruct roots as [|root remaining]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. exact I.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. exact I.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. exact I.
            -- destruct (R.pure_bottom_rhs tf root);
                 inversion Hstep; subst; exact I.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[owner rest] |]; inversion Hstep; subst; exact I.
      - cbn in Hcontrol. destruct Hcontrol as [Howner Hk].
        cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        eapply continuation_below_extended; eauto.
        apply rank_extends_materialize.
      - cbn in Hcontrol, Hordered. destruct Hcontrol as [Hfr Hk].
        eapply next_runrhs_control_ordered; eauto.
      - cbn in Hcontrol, Hordered.
        destruct Hcontrol as [Hfr [Hpending Hk]].
        eapply next_rundead_control_ordered; eauto.
      - cbn in Hcontrol, Hordered. destruct Hcontrol as [Hfr Hk].
        eapply next_runcommit_control_ordered; eauto.
      - cbn in Hcontrol, Hordered. destruct Hcontrol as [Hfr Hk].
        eapply next_rundrain_control_ordered; eauto.
      - cbn in Hcontrol, Hordered.
        eapply next_return_control_ordered; eauto.
    Qed.

    Lemma steps_control_ordered :
      forall tf before after,
        configuration_ranked before ->
        control_ordered (R.cfg_state before) (R.cfg_control before) ->
        Sem.steps tf before after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf before after Hranked Hordered Hsteps. induction Hsteps.
      - exact Hordered.
      - apply IHHsteps.
        + eapply next_config_configuration_ranked; eauto.
        + eapply next_config_control_ordered; eauto.
    Qed.

    Theorem reachable_control_ordered :
      forall tf roots after,
        Sem.steps tf (R.initial_config roots) after ->
        control_ordered (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf roots after Hsteps. eapply steps_control_ordered; eauto.
      - apply initial_configuration_ranked.
      - exact I.
    Qed.

    Lemma rank_lt_trans_true :
      forall st x y z,
        R.rank_lt st x y = true ->
        R.rank_lt st y z = true ->
        R.rank_lt st x z = true.
    Proof.
      intros st x y z Hxy Hyz.
      pose proof (@rank_lt_true_ranked st x y Hxy) as [Hx Hy].
      pose proof (@rank_lt_true_ranked st y z Hyz) as [_ Hz].
      exact (@rank_lt_trans st x y z Hx Hy Hz Hxy Hyz).
    Qed.

  End Termination.

  Lemma run_fuel_steps :
    forall fuel tf start,
      Sem.steps tf start (R.run_fuel fuel tf start).
  Proof.
    induction fuel as [|fuel IH]; intros tf start; cbn.
    - constructor.
    - destruct (R.next_config tf start) as [next |] eqn:Hnext.
      + econstructor; [exact Hnext |apply IH].
      + constructor.
  Qed.

  Lemma terminal_state_shape :
    forall config final,
      R.terminal_state config = Some final ->
      config = Sem.terminal_config final /\ Sem.quiescent final.
  Proof.
    intros [st control] final Hterminal. destruct control;
      cbn in Hterminal; try discriminate.
    destruct (R.queue_peek (R.queue st)) eqn:Hqueue; try discriminate.
    destruct (R.queue_peek (R.deferred_wakes st)) eqn:Hdeferred;
      try discriminate.
    inversion Hterminal; subst. split; [reflexivity |].
    now split.
  Qed.

  Theorem successful_run_terminates_to :
    forall fuel tf roots final,
      R.solve_fuel fuel tf roots = Some final ->
      Sem.terminates_to tf roots final.
  Proof.
    intros fuel tf roots final Hsolve. unfold R.solve_fuel in Hsolve.
    destruct (@terminal_state_shape
      (R.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
      as [Hshape Hquiet].
    split; [|exact Hquiet]. rewrite <- Hshape. apply run_fuel_steps.
  Qed.

  Section Correctness.

    Variable spawned : V.t -> Prop.

    Inductive rhs_trace : R.ConstraintSystem.rhs -> D.t ->
      list (V.t * D.t) -> list (V.t * D.t) -> Prop :=
    | TraceRet : forall direct,
        rhs_trace (R.ConstraintSystem.Ret direct) direct [] []
    | TraceGet : forall target value next direct reads effects,
        rhs_trace (next value) direct reads effects ->
        rhs_trace (R.ConstraintSystem.Get target next)
          direct ((target, value) :: reads) effects
    | TraceSide : forall target value next direct reads effects,
        rhs_trace next direct reads effects ->
        rhs_trace (R.ConstraintSystem.Side target value next)
          direct reads ((target, value) :: effects)
    | TraceSpawn : forall target next direct reads effects,
        spawned target -> rhs_trace next direct reads effects ->
        rhs_trace (R.ConstraintSystem.Spawn target next)
          direct reads effects.

    Definition reads_agree
      (st : R.state) (reads : list (V.t * D.t)) : Prop :=
      forall target value, List.In (target, value) reads ->
        R.semantic_lookup st target = Some value.

    Lemma rhs_trace_replay :
      forall st body direct reads effects,
        rhs_trace body direct reads effects ->
        reads_agree st reads ->
        Sem.rhs_eval st body direct reads effects.
    Proof.
      intros st body direct reads effects Htrace.
      induction Htrace; intros Hagree.
      - constructor.
      - econstructor.
        + apply Hagree. left. reflexivity.
        + apply IHHtrace. intros read value' Hin.
          apply Hagree. right. exact Hin.
      - constructor. apply IHHtrace. exact Hagree.
      - constructor. apply IHHtrace. exact Hagree.
    Qed.

    Lemma rhs_eval_deterministic :
      forall st body direct1 reads1 effects1 direct2 reads2 effects2,
        Sem.rhs_eval st body direct1 reads1 effects1 ->
        Sem.rhs_eval st body direct2 reads2 effects2 ->
        direct1 = direct2 /\ reads1 = reads2 /\ effects1 = effects2.
    Proof.
      intros st body direct1 reads1 effects1 direct2 reads2 effects2
        Heval1. revert direct2 reads2 effects2.
      induction Heval1; intros direct2 reads2 effects2 Heval2;
        inversion Heval2; subst.
      - repeat split; reflexivity.
      - match goal with
        | Hleft : R.semantic_lookup _ _ = Some _,
          Hright : R.semantic_lookup _ _ = Some _ |- _ =>
            rewrite Hleft in Hright; inversion Hright; subst
        end.
        destruct (IHHeval1 _ _ _ H6) as [-> [-> ->]].
        repeat split; reflexivity.
      - destruct (IHHeval1 _ _ _ H5) as [-> [-> ->]].
        repeat split; reflexivity.
      - destruct (IHHeval1 _ _ _ H4) as [-> [-> ->]].
        repeat split; reflexivity.
    Qed.

    Lemma value_below_join_values :
      forall value values,
        List.In value values -> D.leq value (R.join_values values) = true.
    Proof.
      intros value values Hin. induction values as [|head rest IH]; cbn in *.
      - contradiction.
      - destruct Hin as [-> |Hin].
        + apply DL.join_upper_left.
        + eapply DL.leq_trans; [apply IH; exact Hin |].
          apply DL.join_upper_right.
    Qed.

    Lemma stored_contribution_below_aggregate :
      forall st source target contribution,
        M.lookup (R.lookup_map (R.contributions st) target) source =
          Some contribution ->
        D.leq contribution (R.aggregate st target) = true.
    Proof.
      intros st source target contribution Hlookup.
      unfold R.aggregate. apply value_below_join_values.
      eapply ML.lookup_values. exact Hlookup.
    Qed.

    Definition queued (st : R.state) (x : V.t) : Prop :=
      List.In x (R.queue st) \/ List.In x (R.deferred_wakes st).

    Definition guarded_reads
      (st : R.state) (owner : V.t) (reads : list (V.t * D.t)) : Prop :=
      forall target value, List.In (target, value) reads ->
        Sem.solved st target /\
        (S.mem owner (R.lookup_set (R.readers st) target) = true \/
         queued st owner) /\
        (value = R.sigma_value st target \/ queued st owner).

    Definition recorded_effects
      (st : R.state) (owner : V.t) (effects : list (V.t * D.t)) : Prop :=
      forall target value, List.In (target, value) effects ->
        exists contribution,
          M.lookup (R.lookup_map (R.contributions st) target) owner =
            Some contribution /\ D.leq value contribution = true.

    Definition summary_valid
      (tf : R.ConstraintSystem.system) (st : R.state) (owner : V.t) : Prop :=
      Sem.solved st owner /\
      exists direct reads effects,
        rhs_trace (tf owner) direct reads effects /\
        guarded_reads st owner reads /\
        recorded_effects st owner effects /\
        D.leq direct (R.sigma_value st owner) = true.

    Lemma quiescent_not_queued :
      forall st x, Sem.quiescent st -> ~ queued st x.
    Proof.
      intros st x [Hqueue Hdeferred] [Hin | Hin];
        unfold R.queue_peek in *.
      - destruct (R.queue st); [contradiction |discriminate].
      - destruct (R.deferred_wakes st); [contradiction |discriminate].
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

    Lemma guarded_reads_agree :
      forall st owner reads,
        Sem.quiescent st -> guarded_reads st owner reads ->
        reads_agree st reads.
    Proof.
      intros st owner reads Hquiet Hguard target value Hin.
      destruct (Hguard target value Hin)
        as [[current Hlookup] [_ [Hequal |Hqueued]]].
      - rewrite (semantic_lookup_solved
          (ex_intro _ current Hlookup)). now rewrite Hequal.
      - exfalso. exact (@quiescent_not_queued st owner Hquiet Hqueued).
    Qed.

    Lemma recorded_effects_below :
      forall st owner effects,
        recorded_effects st owner effects ->
        (forall target, D.leq (R.aggregate st target)
          (R.sigma_value st target) = true) ->
        Sem.side_effects_below st effects.
    Proof.
      intros st owner effects Hrecorded Haggregate target value Hin.
      destruct (Hrecorded target value Hin)
        as [contribution [Hlookup Hvalue]].
      eapply DL.leq_trans; [exact Hvalue |]. eapply DL.leq_trans.
      - eapply stored_contribution_below_aggregate. exact Hlookup.
      - apply Haggregate.
    Qed.

    Lemma summary_post_solution :
      forall tf st owner,
        Sem.quiescent st ->
        (forall target, D.leq (R.aggregate st target)
          (R.sigma_value st target) = true) ->
        summary_valid tf st owner ->
        Sem.rhs_post_solution st owner (tf owner).
    Proof.
      intros tf st owner Hquiet Haggregate
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      pose proof (rhs_trace_replay Htrace
        (@guarded_reads_agree st owner reads Hquiet Hreads)) as Hreplay.
      unfold Sem.rhs_post_solution.
      intros direct' reads' effects' Heval.
      destruct (rhs_eval_deterministic Hreplay Heval) as [-> [-> ->]].
      split; [exact Hdirect |]. eapply recorded_effects_below; eauto.
    Qed.

    Lemma observe_solver_view :
      forall st x,
        R.sigma (R.observe st x) = R.sigma st /\
        R.queue (R.observe st x) = R.queue st /\
        R.readers (R.observe st x) = R.readers st /\
        R.contributions (R.observe st x) = R.contributions st.
    Proof.
      intros st x. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) x). repeat split.
    Qed.

    Lemma solved_observe :
      forall st x owner,
        Sem.solved st owner -> Sem.solved (R.observe st x) owner.
    Proof.
      intros st x owner [value Hlookup]. exists value.
      unfold R.semantic_lookup in *. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) x). exact Hlookup.
    Qed.

    Lemma queued_observe :
      forall st x owner, queued st owner -> queued (R.observe st x) owner.
    Proof.
      intros st x owner Hqueued. unfold queued in *.
      destruct Hqueued as [Hqueued | Hqueued].
      - left. rewrite (proj1 (proj2 (observe_solver_view st x))). exact Hqueued.
      - right. unfold R.observe.
        destruct (R.Ranking.observe (R.ranking st) x). exact Hqueued.
    Qed.

    Lemma guarded_reads_observe :
      forall st x owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.observe st x) owner reads.
    Proof.
      intros st x owner reads Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split; [now apply solved_observe |]. split.
      - rewrite (proj1 (proj2 (proj2 (observe_solver_view st x)))).
        destruct Hreader as [Hreader |Hqueued];
          [now left |right; now apply queued_observe].
      - unfold R.sigma_value in *.
        rewrite (proj1 (observe_solver_view st x)).
        destruct Hvalue as [Hvalue |Hqueued];
          [now left |right; now apply queued_observe].
    Qed.

    Lemma recorded_effects_observe :
      forall st x owner effects,
        recorded_effects st owner effects ->
        recorded_effects (R.observe st x) owner effects.
    Proof.
      intros st x owner effects Hrecord target value Hin.
      destruct (Hrecord target value Hin)
        as [contribution [Hlookup Hle]].
      exists contribution. split; [|exact Hle].
      rewrite (proj2 (proj2 (proj2 (observe_solver_view st x)))).
      exact Hlookup.
    Qed.

    Lemma summary_valid_observe :
      forall tf st x owner,
        summary_valid tf st owner ->
        summary_valid tf (R.observe st x) owner.
    Proof.
      intros tf st x owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      split; [now apply solved_observe |].
      exists direct, reads, effects. split; [exact Htrace |].
      split; [now apply guarded_reads_observe |].
      split; [now apply recorded_effects_observe |].
      unfold R.sigma_value in *. rewrite (proj1 (observe_solver_view st x)).
      exact Hdirect.
    Qed.

    Lemma lookup_update_map_same :
      forall A (table : M.t (M.t A)) outer inner value,
        M.lookup (R.lookup_map
          (R.update_map table outer inner value) outer) inner = Some value.
    Proof.
      intros. unfold R.update_map, R.lookup_map.
      rewrite ML.lookup_update_same. apply ML.lookup_update_same.
    Qed.

    Lemma aggregate_register_reset :
      forall st source target scope phase observed,
        R.aggregate (R.register_reset st source target scope phase) observed =
        R.aggregate st observed.
    Proof.
      intros. unfold R.register_reset.
      destruct (R.stored_side_cell st source target)
        as [old_phase old_reset]. cbn.
      repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      | |- context [match ?value with _ => _ end] => destruct value
      end; reflexivity.
    Qed.

    Lemma contributions_register_reset :
      forall st source target scope phase,
        R.contributions (R.register_reset st source target scope phase) =
        R.contributions st.
    Proof.
      intros. unfold R.register_reset.
      destruct (R.stored_side_cell st source target)
        as [old_phase old_reset]. cbn.
      repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      | |- context [match ?value with _ => _ end] => destruct value
      end; reflexivity.
    Qed.

    Lemma contributions_promote_side_target :
      forall st fr target,
        R.contributions (R.promote_side_target st fr target) =
        R.contributions st.
    Proof.
      intros. unfold R.promote_side_target, R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma contribution_update_below_aggregate :
      forall st source target contribution,
        D.leq contribution
          (R.aggregate
            (R.with_contributions st
              (R.update_map (R.contributions st)
                target source contribution)) target) = true.
    Proof.
      intros. apply stored_contribution_below_aggregate with (source := source).
      apply lookup_update_map_same.
    Qed.

    Lemma write_side_contribution_sound :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        D.leq input (R.aggregate next target) = true.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input)
        as [next_phase contribution] eqn:Hupdate.
      inversion Hwrite; subst next changed. rewrite aggregate_register_reset.
      eapply DL.leq_trans.
      - pose proof (SSL.update_sound (R.frame_owner fr) target
          (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
          (R.stored_contribution base (R.frame_owner fr) target) input
          (R.aggregate base target)) as Hsound.
        unfold R.side_update in Hupdate.
        rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
      - apply contribution_update_below_aggregate.
    Qed.

    Lemma sigma_value_with_readers :
      forall st readers x,
        R.sigma_value (R.with_readers st readers) x = R.sigma_value st x.
    Proof. reflexivity. Qed.

    Lemma sigma_value_enqueue_all :
      forall st values x,
        R.sigma_value (R.enqueue_all st values) x = R.sigma_value st x.
    Proof. reflexivity. Qed.

    Lemma sigma_value_update_same :
      forall st owner value,
        R.sigma_value
          (R.with_sigma st (M.update (R.sigma st) owner value)) owner = value.
    Proof.
      intros. unfold R.sigma_value. cbn.
      rewrite ML.lookup_update_same. reflexivity.
    Qed.

    Lemma set_value_candidate_sound :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        D.leq (D.join direct (R.aggregate st (R.frame_owner fr)))
          (R.sigma_value next (R.frame_owner fr)) = true.
    Proof.
      intros st fr direct next next_fr Hset.
      unfold R.set_value in Hset.
      set (owner := R.frame_owner fr) in *.
      set (candidate := D.join direct (R.aggregate st owner)) in *.
      set (old := R.sigma_value st owner) in *.
      destruct (R.equivalent candidate old) eqn:Hcandidate.
      - inversion Hset; subst. unfold R.equivalent in Hcandidate.
        apply Bool.andb_true_iff in Hcandidate. exact (proj1 Hcandidate).
      - destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
        + destruct (U.update false owner (R.frame_phase fr) old candidate)
            as [next_phase value] eqn:Hupdate. cbn in Hset.
          destruct (R.equivalent value old) eqn:Hvalue.
          * inversion Hset; subst. eapply DL.leq_trans.
            -- pose proof (OSL.update_sound
                 owner (R.frame_phase fr) old candidate) as Hsound.
               rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
            -- unfold R.equivalent in Hvalue.
               apply Bool.andb_true_iff in Hvalue. exact (proj1 Hvalue).
          * inversion Hset; subst.
            rewrite sigma_value_with_readers, sigma_value_enqueue_all,
              sigma_value_update_same.
            pose proof (OSL.update_sound
              owner (R.frame_phase fr) old candidate) as Hsound.
            rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
        + cbn in Hset. rewrite Hcandidate in Hset. inversion Hset; subst.
          rewrite sigma_value_with_readers, sigma_value_enqueue_all,
            sigma_value_update_same. apply DL.leq_refl.
    Qed.

    Lemma set_value_direct_sound :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        D.leq direct (R.sigma_value next (R.frame_owner fr)) = true.
    Proof.
      intros. eapply DL.leq_trans; [apply DL.join_upper_left |].
      eapply set_value_candidate_sound. exact H.
    Qed.

    Lemma set_value_aggregate_sound :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        D.leq (R.aggregate st (R.frame_owner fr))
          (R.sigma_value next (R.frame_owner fr)) = true.
    Proof.
      intros. eapply DL.leq_trans; [apply DL.join_upper_right |].
      eapply set_value_candidate_sound. exact H.
    Qed.

    Lemma lookup_update_map_other :
      forall A (table : M.t (M.t A)) outer inner value observed,
        observed <> outer ->
        R.lookup_map (R.update_map table outer inner value) observed =
        R.lookup_map table observed.
    Proof.
      intros A table outer inner value observed Hneq.
      unfold R.update_map, R.lookup_map.
      now rewrite ML.lookup_update_other by exact Hneq.
    Qed.

    Lemma lookup_update_map_same_outer_other_inner :
      forall A (table : M.t (M.t A)) outer inner value observed,
        observed <> inner ->
        M.lookup (R.lookup_map
          (R.update_map table outer inner value) outer) observed =
        M.lookup (R.lookup_map table outer) observed.
    Proof.
      intros A table outer inner value observed Hneq.
      unfold R.update_map, R.lookup_map. rewrite ML.lookup_update_same.
      now rewrite ML.lookup_update_other by exact Hneq.
    Qed.

    Lemma write_side_contribution_records_input :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        exists contribution,
          M.lookup (R.lookup_map (R.contributions next) target)
            (R.frame_owner fr) = Some contribution /\
          D.leq input contribution = true.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input)
        as [next_phase contribution] eqn:Hupdate.
      inversion Hwrite; subst next changed. exists contribution. split.
      - rewrite contributions_register_reset. apply lookup_update_map_same.
      - pose proof (SSL.update_sound (R.frame_owner fr) target
          (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
          (R.stored_contribution base (R.frame_owner fr) target) input
          (R.aggregate base target)) as Hsound.
        unfold R.side_update in Hupdate.
        rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
    Qed.

    Lemma write_side_contribution_other :
      forall st fr target input next changed observed,
        R.write_side_contribution st fr target input = (next, changed) ->
        observed <> target ->
        R.lookup_map (R.contributions next) observed =
        R.lookup_map (R.contributions st) observed.
    Proof.
      intros st fr target input next changed observed Hwrite Hneq.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input).
      inversion Hwrite; subst next changed.
      rewrite contributions_register_reset. cbn.
      rewrite lookup_update_map_other by exact Hneq.
      unfold base. now rewrite contributions_promote_side_target.
    Qed.

    Lemma write_side_contribution_other_source :
      forall st fr target input next changed source observed,
        R.write_side_contribution st fr target input = (next, changed) ->
        source <> R.frame_owner fr ->
        M.lookup (R.lookup_map (R.contributions next) observed) source =
        M.lookup (R.lookup_map (R.contributions st) observed) source.
    Proof.
      intros st fr target input next changed source observed Hwrite Hneq.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input).
      inversion Hwrite; subst next changed.
      rewrite contributions_register_reset. cbn.
      destruct (V.eq_dec observed target) as [-> |Htarget].
      - rewrite lookup_update_map_same_outer_other_inner by exact Hneq.
        unfold base. now rewrite contributions_promote_side_target.
      - rewrite lookup_update_map_other by exact Htarget.
        unfold base. now rewrite contributions_promote_side_target.
    Qed.

    Definition same_read_view (before after : R.state) : Prop :=
      R.sigma after = R.sigma before /\
      R.readers after = R.readers before /\
      R.queue after = R.queue before /\
      R.deferred_wakes after = R.deferred_wakes before /\
      R.dormant_bottom after = R.dormant_bottom before.

    Definition same_solver_view (before after : R.state) : Prop :=
      same_read_view before after /\
      R.contributions after = R.contributions before.

    Lemma same_read_view_trans :
      forall first middle last,
        same_read_view first middle -> same_read_view middle last ->
        same_read_view first last.
    Proof.
      intros first middle last [Hs1 [Hr1 [Hq1 [Hw1 Hd1]]]]
        [Hs2 [Hr2 [Hq2 [Hw2 Hd2]]]].
      repeat split; congruence.
    Qed.

    Lemma same_read_view_observe :
      forall st x, same_read_view st (R.observe st x).
    Proof.
      intros st x. unfold same_read_view, R.observe.
      destruct (R.Ranking.observe (R.ranking st) x).
      repeat split; reflexivity.
    Qed.

    Lemma guarded_reads_same_view :
      forall before after owner reads,
        same_read_view before after ->
        guarded_reads before owner reads ->
        guarded_reads after owner reads.
    Proof.
      intros before after owner reads
        [Hsigma [Hreaders [Hqueue [Hdeferred Hdormant]]]]
        Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split.
      - destruct Hsolved as [current Hlookup]. exists current.
        unfold R.semantic_lookup in *. now rewrite Hsigma, Hdormant.
      - split.
        + destruct Hreader as [Hreader |Hqueued].
          * left. unfold R.lookup_set. now rewrite Hreaders.
          * right. unfold queued in *.
            now rewrite Hqueue, Hdeferred.
        + destruct Hvalue as [Hvalue |Hqueued].
          * left. unfold R.sigma_value in *. now rewrite Hsigma.
          * right. unfold queued in *.
            now rewrite Hqueue, Hdeferred.
    Qed.

    Lemma solved_same_read_view :
      forall before after x,
        same_read_view before after ->
        Sem.solved before x -> Sem.solved after x.
    Proof.
      intros before after x [Hsigma [_ [_ [_ Hdormant]]]] [value Hlookup].
      exists value. unfold R.semantic_lookup in *.
      now rewrite Hsigma, Hdormant.
    Qed.

    Lemma solved_same_read_view_back :
      forall before after x,
        same_read_view before after ->
        Sem.solved after x -> Sem.solved before x.
    Proof.
      intros before after x [Hsigma [_ [_ [_ Hdormant]]]] [value Hlookup].
      exists value. unfold R.semantic_lookup in *.
      now rewrite Hsigma, Hdormant in Hlookup.
    Qed.

    Lemma write_side_contribution_same_read_view :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        same_read_view st next.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input)
        as [next_phase contribution].
      inversion Hwrite; subst next changed.
      unfold same_read_view, R.register_reset.
      destruct (R.stored_side_cell
        (R.with_contributions base
          (R.update_map (R.contributions base) target
            (R.frame_owner fr) contribution))
        (R.frame_owner fr) target) as [old_phase old_reset]. cbn.
      repeat match goal with
      | |- context [if ?test then _ else _] => destruct test
      | |- context [match ?value with _ => _ end] => destruct value
      end; unfold base, R.promote_side_target, R.promote_controlled;
        destruct (R.rank_lt st target (R.frame_owner fr));
        repeat split; reflexivity.
    Qed.

    Lemma solved_same_solver_view :
      forall before after x,
        same_solver_view before after ->
        Sem.solved before x -> Sem.solved after x.
    Proof.
      intros before after x [[Hsigma [_ [_ [_ Hdormant]]]] _] [value Hlookup].
      exists value. unfold R.semantic_lookup in *.
      now rewrite Hsigma, Hdormant.
    Qed.

    Lemma solved_same_solver_view_back :
      forall before after x,
        same_solver_view before after ->
        Sem.solved after x -> Sem.solved before x.
    Proof.
      intros before after x [[Hsigma [_ [_ [_ Hdormant]]]] _] [value Hlookup].
      exists value. unfold R.semantic_lookup in *.
      now rewrite Hsigma, Hdormant in Hlookup.
    Qed.

    Lemma queued_same_solver_view :
      forall before after x,
        same_solver_view before after -> queued before x -> queued after x.
    Proof.
      intros before after x [[_ [_ [Hqueue [Hdeferred _]]]] _] Hqueued.
      unfold queued in *. now rewrite Hqueue, Hdeferred.
    Qed.

    Lemma recorded_effects_same_solver_view :
      forall before after owner effects,
        same_solver_view before after ->
        recorded_effects before owner effects ->
        recorded_effects after owner effects.
    Proof.
      intros before after owner effects [_ Hcontributions] Hrecord.
      unfold recorded_effects in *. now rewrite Hcontributions.
    Qed.

    Lemma recorded_effects_write_other_source :
      forall st fr target input next changed owner effects,
        R.write_side_contribution st fr target input = (next, changed) ->
        owner <> R.frame_owner fr ->
        recorded_effects st owner effects ->
        recorded_effects next owner effects.
    Proof.
      intros st fr target input next changed owner effects
        Hwrite Hneq Hrecord observed value Hin.
      destruct (Hrecord observed value Hin)
        as [contribution [Hlookup Hle]]. exists contribution. split.
      - rewrite (@write_side_contribution_other_source st fr target input
          next changed owner observed Hwrite Hneq). exact Hlookup.
      - exact Hle.
    Qed.

    Definition commit_value
      (st : R.state) (owner : V.t) (value : D.t) : R.state :=
      let st1 := R.with_sigma st (M.update (R.sigma st) owner value) in
      let invalidated := S.elements (R.lookup_set (R.readers st1) owner) in
      let st2 := R.enqueue_all st1 invalidated in
      R.with_readers st2 (M.update (R.readers st2) owner S.empty).

    Definition dirty_commit_value
      (st : R.state) (owner : V.t) (value : D.t) : R.state :=
      let st1 := R.with_sigma st (M.update (R.sigma st) owner value) in
      let invalidated := S.elements (R.lookup_set (R.readers st1) owner) in
      let st2 := R.defer_all st1 invalidated in
      R.with_readers st2 (M.update (R.readers st2) owner S.empty).

    Definition add_reader
      (st : R.state) (target owner : V.t) : R.state :=
      R.with_readers st (M.update (R.readers st) target
        (S.add owner (R.lookup_set (R.readers st) target))).

    Lemma queued_commit_value :
      forall st owner value x,
        queued st x -> queued (commit_value st owner value) x.
    Proof.
      intros st owner value x [Hqueued | Hdeferred].
      - left. cbn. apply queue_insert_all_members. now right.
      - right. exact Hdeferred.
    Qed.

    Lemma queued_dirty_commit_value :
      forall st owner value x,
        queued st x -> queued (dirty_commit_value st owner value) x.
    Proof.
      intros st owner value x [Hqueued | Hdeferred].
      - left. exact Hqueued.
      - right. cbn. apply queue_insert_all_members. now right.
    Qed.

    Lemma guarded_reads_enqueue :
      forall st inserted owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.enqueue st inserted) owner reads.
    Proof.
      intros st inserted owner reads Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split; [exact Hsolved |]. split.
      - destruct Hreader as [Hreader |[Hqueued |Hdeferred]].
        + now left.
        + right. left. cbn. apply queue_insert_members. now right.
        + right. now right.
      - destruct Hvalue as [Hvalue |[Hqueued |Hdeferred]].
        + now left.
        + right. left. cbn. apply queue_insert_members. now right.
        + right. now right.
    Qed.

    Lemma guarded_reads_pop_other :
      forall st popped rest owner reads,
        R.queue_pop (R.queue st) = Some (popped, rest) ->
        owner <> popped ->
        guarded_reads st owner reads ->
        guarded_reads (R.with_queue st rest) owner reads.
    Proof.
      intros st popped rest owner reads Hpop Hneq Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      assert (Htail : forall x, List.In x (R.queue st) ->
        x <> popped -> List.In x rest).
      { intros x Hmember Hxpopped. destruct (R.queue st) as [|head tail]
          eqn:Hqueue; cbn in Hpop; try discriminate.
        inversion Hpop; subst head tail.
        destruct Hmember as [Heq |Hmember]; [congruence |exact Hmember]. }
      split; [exact Hsolved |]. split.
      - destruct Hreader as [Hreader |[Hqueued |Hdeferred]].
        + now left.
        + right. left. eapply Htail; eauto.
        + right. now right.
      - destruct Hvalue as [Hvalue |[Hqueued |Hdeferred]].
        + now left.
        + right. left. eapply Htail; eauto.
        + right. now right.
    Qed.

    Lemma guarded_reads_materialize :
      forall st inserted owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.materialize st inserted) owner reads.
    Proof.
      intros st inserted owner reads Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split.
      - destruct Hsolved as [found Hfound]. exists found.
        unfold R.materialize, R.semantic_lookup in *.
        destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted;
          [exact Hfound |cbn].
        destruct (V.eq_dec target inserted) as [-> |Hneq].
        + rewrite ML.lookup_update_same. rewrite Hinserted in Hfound.
          destruct (S.mem inserted (R.dormant_bottom st));
            inversion Hfound; reflexivity.
        + now rewrite ML.lookup_update_other by exact Hneq.
      - split.
        + destruct Hreader as [Hreader |Hqueued]; [left |right];
            unfold R.materialize, queued;
            destruct (M.lookup (R.sigma st) inserted); exact Hreader || exact Hqueued.
        + destruct Hvalue as [Hequal |Hqueued].
          * left. unfold R.materialize, R.sigma_value in *.
            destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted;
              [exact Hequal |cbn].
            destruct (V.eq_dec target inserted) as [-> |Hneq].
            -- rewrite ML.lookup_update_same. rewrite Hinserted in Hequal.
               exact Hequal.
            -- now rewrite ML.lookup_update_other by exact Hneq.
          * right. unfold R.materialize, queued in *.
            destruct (M.lookup (R.sigma st) inserted); exact Hqueued.
    Qed.

    Lemma guarded_reads_add_reader :
      forall st target added owner reads,
        guarded_reads st owner reads ->
        guarded_reads (add_reader st target added) owner reads.
    Proof.
      intros st target added owner reads Hguard observed value Hin.
      destruct (Hguard observed value Hin) as [Hsolved [Hreader Hvalue]].
      split; [exact Hsolved |]. split.
      - destruct Hreader as [Hmember |Hqueued]; [left |now right].
        unfold add_reader, R.lookup_set in *. cbn.
        destruct (V.eq_dec observed target) as [-> |Hneq].
        + rewrite ML.lookup_update_same. apply SL.add_spec. now right.
        + rewrite ML.lookup_update_other by exact Hneq. exact Hmember.
      - exact Hvalue.
    Qed.

    Lemma add_reader_registered_after_materialize :
      forall st target owner,
        S.mem owner (R.lookup_set
          (R.readers (R.materialize (add_reader st target owner) target))
          target) = true.
    Proof.
      intros st target owner. unfold R.materialize.
      destruct (M.lookup (R.sigma (add_reader st target owner)) target);
        cbn; unfold add_reader; cbn; unfold R.lookup_set;
        rewrite ML.lookup_update_same; apply SL.add_spec; left; reflexivity.
    Qed.

    Lemma dormant_semantic_bottom :
      forall st target,
        R.is_dormant st target = true ->
        R.semantic_lookup st target = Some D.bottom /\
        R.sigma_value st target = D.bottom.
    Proof.
      intros st target Hdormant. unfold R.is_dormant in Hdormant.
      apply Bool.andb_true_iff in Hdormant as [Hmember Hrest].
      apply Bool.andb_true_iff in Hrest as [Hsigma _].
      destruct (M.lookup (R.sigma st) target) eqn:Hlookup;
        [discriminate |]. split.
      - unfold R.semantic_lookup. rewrite Hlookup, Hmember. reflexivity.
      - unfold R.sigma_value. now rewrite Hlookup.
    Qed.

    Lemma solved_dormant :
      forall st target,
        R.is_dormant st target = true -> Sem.solved st target.
    Proof.
      intros. exists D.bottom. now apply dormant_semantic_bottom.
    Qed.

    Lemma solved_add_reader :
      forall st target owner x,
        Sem.solved st x -> Sem.solved (R.add_reader st target owner) x.
    Proof. intros st target owner x [value Hlookup]. now exists value. Qed.

    Lemma solved_add_reader_back :
      forall st target owner x,
        Sem.solved (R.add_reader st target owner) x -> Sem.solved st x.
    Proof. intros st target owner x [value Hlookup]. now exists value. Qed.

    Lemma solved_remember_dormant :
      forall st target x,
        Sem.solved st x -> Sem.solved (R.remember_dormant st target) x.
    Proof.
      intros st target x [value Hlookup]. exists value.
      unfold R.remember_dormant, R.with_dormant_bottom,
        R.semantic_lookup in *; cbn.
      destruct (M.lookup (R.sigma st) x); [exact Hlookup |].
      destruct (S.mem x (R.dormant_bottom st)) eqn:Hmember.
      - assert (S.mem x (S.add target (R.dormant_bottom st)) = true)
          as Hadded.
        { apply SL.add_spec. now right. }
        rewrite Hadded. inversion Hlookup. reflexivity.
      - discriminate Hlookup.
    Qed.

    Lemma guarded_reads_remember_dormant :
      forall st target owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.remember_dormant st target) owner reads.
    Proof.
      intros st target owner reads Hguard observed value Hin.
      destruct (Hguard observed value Hin)
        as [Hsolved [Hreader Hvalue]]. split.
      - now apply solved_remember_dormant.
      - split; [exact Hreader |].
        unfold R.remember_dormant, R.with_dormant_bottom in *; exact Hvalue.
    Qed.

    Lemma guarded_reads_commit_value :
      forall st owner value reader reads,
        guarded_reads st reader reads ->
        guarded_reads (commit_value st owner value) reader reads.
    Proof.
      intros st owner value reader reads Hguard target observed Hin.
      destruct (Hguard target observed Hin) as [Hsolved [Hreader Hvalue]].
      unfold commit_value. split.
      - destruct Hsolved as [current Hlookup].
        destruct (V.eq_dec target owner) as [-> |Hneq].
        + exists value. unfold R.semantic_lookup. cbn.
          now rewrite ML.lookup_update_same.
        + exists current. unfold R.semantic_lookup in *. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      - cbn. split.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * destruct Hreader as [Hmember |Hqueued].
            -- right. left. cbn. apply queue_insert_all_members.
               left. apply SL.mem_spec. exact Hmember.
            -- right. now apply queued_commit_value.
          * destruct Hreader as [Hmember |Hqueued].
            -- left. unfold R.lookup_set in *.
               rewrite ML.lookup_update_other by exact Hneq. exact Hmember.
            -- right. now apply queued_commit_value.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * destruct Hreader as [Hmember |Hqueued].
            -- right. left. cbn. apply queue_insert_all_members.
               left. apply SL.mem_spec. exact Hmember.
            -- right. now apply queued_commit_value.
          * destruct Hvalue as [Hequal |Hqueued].
            -- left. unfold R.sigma_value in *. cbn.
               rewrite ML.lookup_update_other by exact Hneq. exact Hequal.
            -- right. now apply queued_commit_value.
    Qed.

    Lemma guarded_reads_dirty_commit_value :
      forall st owner value reader reads,
        guarded_reads st reader reads ->
        guarded_reads (dirty_commit_value st owner value) reader reads.
    Proof.
      intros st owner value reader reads Hguard target observed Hin.
      destruct (Hguard target observed Hin) as [Hsolved [Hreader Hvalue]].
      unfold dirty_commit_value. split.
      - destruct Hsolved as [current Hlookup].
        destruct (V.eq_dec target owner) as [-> |Hneq].
        + exists value. unfold R.semantic_lookup. cbn.
          now rewrite ML.lookup_update_same.
        + exists current. unfold R.semantic_lookup in *. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      - cbn. split.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * destruct Hreader as [Hmember |Hqueued].
            -- right. right. apply queue_insert_all_members. left.
               apply SL.mem_spec. exact Hmember.
            -- right. now apply queued_dirty_commit_value.
          * destruct Hreader as [Hmember |Hqueued].
            -- left. unfold R.lookup_set in *.
               rewrite ML.lookup_update_other by exact Hneq. exact Hmember.
            -- right. now apply queued_dirty_commit_value.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * destruct Hreader as [Hmember |Hqueued].
            -- right. right. apply queue_insert_all_members. left.
               apply SL.mem_spec. exact Hmember.
            -- right. now apply queued_dirty_commit_value.
          * destruct Hvalue as [Hequal |Hqueued].
            -- left. unfold R.sigma_value in *. cbn.
               rewrite ML.lookup_update_other by exact Hneq. exact Hequal.
            -- right. now apply queued_dirty_commit_value.
    Qed.

    Lemma guarded_reads_set_value :
      forall st fr direct next next_fr reader reads,
        R.set_value st fr direct = (next, next_fr) ->
        guarded_reads st reader reads -> guarded_reads next reader reads.
    Proof.
      intros st fr direct next next_fr reader reads Hset Hreads.
      unfold R.set_value in Hset.
      destruct (R.equivalent
        (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr))) eqn:Hcandidate.
      - inversion Hset; subst. exact Hreads.
      - destruct (S.mem (R.frame_owner fr) (R.controlled st)).
        + destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr))))
            as [phase value]. cbn in Hset.
          destruct (R.equivalent value
            (R.sigma_value st (R.frame_owner fr))).
          * inversion Hset; subst. exact Hreads.
          * inversion Hset; subst. now apply guarded_reads_commit_value.
        + cbn in Hset. rewrite Hcandidate in Hset. inversion Hset; subst.
          now apply guarded_reads_commit_value.
    Qed.

    Lemma set_value_contributions :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        R.contributions next = R.contributions st.
    Proof.
      intros st fr direct next next_fr Hset. unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end; inversion Hset; reflexivity.
    Qed.

    Lemma set_value_solved :
      forall st fr direct next next_fr x,
        R.set_value st fr direct = (next, next_fr) ->
        Sem.solved st x -> Sem.solved next x.
    Proof.
      intros st fr direct next next_fr x Hset [current Hlookup].
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end; inversion Hset; subst; try (now exists current).
      all: destruct (V.eq_dec x (R.frame_owner fr)) as [-> |Hneq].
      all: try (eexists; unfold R.semantic_lookup; cbn;
        now rewrite ML.lookup_update_same).
      all: exists current; unfold R.semantic_lookup in *; cbn;
        rewrite ML.lookup_update_other by exact Hneq; exact Hlookup.
    Qed.

    Lemma set_value_solved_origin :
      forall st fr direct next next_fr x,
        R.set_value st fr direct = (next, next_fr) ->
        Sem.solved next x -> Sem.solved st x \/ x = R.frame_owner fr.
    Proof.
      intros st fr direct next next_fr x Hset [current Hlookup].
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end; inversion Hset; subst; try (left; now exists current).
      all: destruct (V.eq_dec x (R.frame_owner fr)) as [Heq |Hneq];
        [now right |left; exists current; unfold R.semantic_lookup in *;
         cbn in Hlookup;
         rewrite ML.lookup_update_other in Hlookup by exact Hneq;
         exact Hlookup].
    Qed.

    Lemma recorded_effects_set_value :
      forall st fr direct next next_fr owner effects,
        R.set_value st fr direct = (next, next_fr) ->
        recorded_effects st owner effects ->
        recorded_effects next owner effects.
    Proof.
      intros st fr direct next next_fr owner effects Hset Hrecord.
      unfold recorded_effects in *.
      rewrite (@set_value_contributions st fr direct next next_fr Hset).
      exact Hrecord.
    Qed.

    Inductive rhs_context : R.ConstraintSystem.rhs -> R.ConstraintSystem.rhs ->
      list (V.t * D.t) -> list (V.t * D.t) -> Prop :=
    | PrefixHere body : rhs_context body body [] []
    | PrefixGet target value next current reads effects :
        rhs_context (next value) current reads effects ->
        rhs_context (R.ConstraintSystem.Get target next) current ((target,value)::reads) effects
    | PrefixSide target value next current reads effects :
        rhs_context next current reads effects ->
        rhs_context (R.ConstraintSystem.Side target value next) current reads ((target,value)::effects)
    | PrefixSpawn target next current reads effects :
        spawned target -> rhs_context next current reads effects ->
        rhs_context (R.ConstraintSystem.Spawn target next) current reads effects.

    Lemma rhs_context_complete root current prefix_reads prefix_effects :
      rhs_context root current prefix_reads prefix_effects ->
      forall direct reads effects, rhs_trace current direct reads effects ->
        rhs_trace root direct (prefix_reads ++ reads) (prefix_effects ++ effects).
    Proof.
      intros Hprefix. induction Hprefix; intros direct rs es Htrace; cbn.
      - exact Htrace.
      - constructor. now apply IHHprefix.
      - constructor. now apply IHHprefix.
      - constructor; [assumption |now apply IHHprefix].
    Qed.

    Lemma rhs_context_get :
      forall root target next prefix_reads prefix_effects value,
        rhs_context root (R.ConstraintSystem.Get target next)
          prefix_reads prefix_effects ->
        rhs_context root (next value)
          (prefix_reads ++ [(target, value)]) prefix_effects.
    Proof.
      intros root target next reads effects value Hprefix.
      remember (R.ConstraintSystem.Get target next) as current eqn:Hcurrent.
      revert target next value Hcurrent.
      induction Hprefix; intros target0 next0 value0 Hcurrent.
      - inversion Hcurrent; subst. cbn. constructor. constructor.
      - cbn. constructor. eapply IHHprefix. exact Hcurrent.
      - cbn. constructor. eapply IHHprefix. exact Hcurrent.
      - cbn. constructor; [assumption |]. eapply IHHprefix. exact Hcurrent.
    Qed.

    Definition frame_effects
      (fr : R.frame) (effects : list (V.t * D.t)) : Prop :=
      forall target value,
        List.In (target, value) effects ->
        exists accumulated,
          M.lookup (R.frame_local_side fr) target = Some accumulated /\
          D.leq value accumulated = true /\
          S.mem target (R.frame_current_targets fr) = true.

    Lemma record_side_input_lookup :
      forall fr target raw,
        M.lookup
          (R.frame_local_side
            (fst (R.record_side_input fr target raw))) target =
        Some (snd (R.record_side_input fr target raw)).
    Proof.
      intros fr target raw.
      unfold R.record_side_input, R.accumulated_side_input.
      destruct (M.lookup (R.frame_local_side fr) target);
        cbn; apply ML.lookup_update_same.
    Qed.

    Lemma frame_effects_record_side :
      forall fr effects target raw,
        frame_effects fr effects ->
        frame_effects
          (fst (R.record_side_input fr target raw))
          (effects ++ [(target, raw)]).
    Proof.
      intros fr effects target raw Hframe observed value Hin.
      apply List.in_app_or in Hin. destruct Hin as [Hold | Hnew].
      - destruct (Hframe observed value Hold)
          as [accumulated [Hlookup [Hle Hmem]]].
        destruct (V.eq_dec observed target) as [-> | Hneq].
        + exists (snd (R.record_side_input fr target raw)). split.
          * apply record_side_input_lookup.
          * split.
            -- unfold R.record_side_input, R.accumulated_side_input.
               rewrite Hlookup. cbn. eapply DL.leq_trans;
                 [exact Hle |apply DL.join_upper_left].
            -- unfold R.record_side_input. cbn.
               apply SL.add_spec. now left.
        + exists accumulated. split.
          * unfold R.record_side_input. cbn.
            rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
          * split; [exact Hle |]. unfold R.record_side_input. cbn.
            apply SL.add_spec. now right.
      - cbn in Hnew. destruct Hnew as [Heq | Hfalse];
          [inversion Heq; subst |contradiction].
        exists (snd (R.record_side_input fr observed value)). split.
        + apply record_side_input_lookup.
        + split.
          * unfold R.record_side_input, R.accumulated_side_input.
            destruct (M.lookup (R.frame_local_side fr) observed); cbn;
              [apply DL.join_upper_right |apply DL.leq_refl].
          * unfold R.record_side_input. cbn.
            apply SL.add_spec. now left.
    Qed.

    Lemma recorded_effects_write_side :
      forall st fr target input st' changed effects,
        R.write_side_contribution st fr target input = (st', changed) ->
        M.lookup (R.frame_local_side fr) target = Some input ->
        frame_effects fr effects ->
        recorded_effects st (R.frame_owner fr) effects ->
        recorded_effects st' (R.frame_owner fr) effects.
    Proof.
      intros st fr target input st' changed effects
        Hwrite Hinput Hframe Hrecord observed value Hin.
      destruct (V.eq_dec observed target) as [-> | Hneq].
      - destruct (Hframe target value Hin)
          as [accumulated [Hlookup [Hle Hmem]]].
        rewrite Hinput in Hlookup. inversion Hlookup; subst.
        destruct (write_side_contribution_records_input Hwrite)
          as [contribution [Hstored Hcovered]].
        exists contribution. split; [exact Hstored |].
        eapply DL.leq_trans; eassumption.
      - destruct (Hrecord observed value Hin)
          as [contribution [Hstored Hcovered]].
        exists contribution. split.
        + rewrite (write_side_contribution_other Hwrite Hneq). exact Hstored.
        + exact Hcovered.
    Qed.

    Lemma recorded_effects_write_side_append :
      forall st fr target raw input st' changed effects,
        R.write_side_contribution st fr target input = (st', changed) ->
        M.lookup (R.frame_local_side fr) target = Some input ->
        frame_effects fr (effects ++ [(target, raw)]) ->
        recorded_effects st (R.frame_owner fr) effects ->
        recorded_effects st' (R.frame_owner fr)
          (effects ++ [(target, raw)]).
    Proof.
      intros st fr target raw input st' changed effects
        Hwrite Hinput Hframe Hrecord observed value Hin.
      destruct (V.eq_dec observed target) as [-> | Hneq].
      - destruct (Hframe target value Hin)
          as [accumulated [Hlookup [Hle Hmem]]].
        rewrite Hinput in Hlookup. inversion Hlookup; subst.
        destruct (write_side_contribution_records_input Hwrite)
          as [contribution [Hstored Hcovered]].
        exists contribution. split; [exact Hstored |].
        eapply DL.leq_trans; eassumption.
      - apply List.in_app_or in Hin. destruct Hin as [Hold | Hnew].
        + destruct (Hrecord observed value Hold)
            as [contribution [Hstored Hcovered]].
          exists contribution. split.
          * rewrite (write_side_contribution_other Hwrite Hneq).
            exact Hstored.
          * exact Hcovered.
        + cbn in Hnew. destruct Hnew as [Heq | Hfalse].
          * injection Heq as Htarget Hvalue. exfalso.
            apply Hneq. symmetry. exact Htarget.
          * contradiction.
    Qed.

    Definition evaluation_witness
      (tf : R.ConstraintSystem.system) (st : R.state)
      (fr : R.frame) (current : R.ConstraintSystem.rhs) : Prop :=
      Sem.solved st (R.frame_owner fr) /\
      exists reads effects,
        rhs_context (tf (R.frame_owner fr)) current reads effects /\
        guarded_reads st (R.frame_owner fr) reads /\
        recorded_effects st (R.frame_owner fr) effects /\
        frame_effects fr effects.

    Definition completed_witness
      (tf : R.ConstraintSystem.system) (st : R.state)
      (fr : R.frame) (direct : D.t) : Prop :=
      Sem.solved st (R.frame_owner fr) /\
      exists reads effects,
        rhs_trace (tf (R.frame_owner fr)) direct reads effects /\
        guarded_reads st (R.frame_owner fr) reads /\
        recorded_effects st (R.frame_owner fr) effects /\
        frame_effects fr effects.

    Fixpoint continuation_history
      (tf : R.ConstraintSystem.system) (st : R.state)
      (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr target next rest =>
          evaluation_witness tf st fr (R.ConstraintSystem.Get target next) /\
          continuation_history tf st rest
      | R.KAfterSide fr next rest
      | R.KAfterSpawn fr next rest =>
          evaluation_witness tf st fr next /\
          continuation_history tf st rest
      | R.KDead fr direct _ rest =>
          completed_witness tf st fr direct /\
          continuation_history tf st rest
      | R.KDrain fr rest =>
          summary_valid tf st (R.frame_owner fr) /\
          continuation_history tf st rest
      end.

    Definition control_history
      (tf : R.ConstraintSystem.system) (st : R.state)
      (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
      | R.StartEpisode _ k => continuation_history tf st k
      | R.RunRhs fr current k =>
          evaluation_witness tf st fr current /\
          continuation_history tf st k
      | R.RunDead fr direct _ k
      | R.RunCommit fr direct k =>
          completed_witness tf st fr direct /\
          continuation_history tf st k
      | R.RunDrain fr k =>
          summary_valid tf st (R.frame_owner fr) /\
          continuation_history tf st k
      | R.Return k => continuation_history tf st k
      end.

    Lemma evaluation_witness_same_solver_view :
      forall tf before after fr current,
        same_solver_view before after ->
        evaluation_witness tf before fr current ->
        evaluation_witness tf after fr current.
    Proof.
      intros tf before after fr current
        [Hread Hcontributions]
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split.
      - eapply solved_same_solver_view; [split; eassumption |exact Hsolved].
      - exists reads, effects. split; [exact Hcontext |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_same_solver_view; eauto.
            split; assumption.
          * exact Hframe.
    Qed.

    Lemma completed_witness_same_solver_view :
      forall tf before after fr direct,
        same_solver_view before after ->
        completed_witness tf before fr direct ->
        completed_witness tf after fr direct.
    Proof.
      intros tf before after fr direct
        [Hread Hcontributions]
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split.
      - eapply solved_same_solver_view; [split; eassumption |exact Hsolved].
      - exists reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_same_solver_view; eauto.
            split; assumption.
          * exact Hframe.
    Qed.

    Lemma summary_valid_same_solver_view :
      forall tf before after owner,
        same_solver_view before after ->
        summary_valid tf before owner ->
        summary_valid tf after owner.
    Proof.
      intros tf before after owner
        [Hread Hcontributions]
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split.
      - eapply solved_same_solver_view; [split; eassumption |exact Hsolved].
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_same_solver_view; eauto.
            split; assumption.
          * unfold R.sigma_value in *.
            rewrite (proj1 Hread). exact Hdirect.
    Qed.

    Lemma continuation_history_same_solver_view :
      forall tf before after k,
        same_solver_view before after ->
        continuation_history tf before k ->
        continuation_history tf after k.
    Proof.
      intros tf before after k Hview.
      induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hrest]; split.
      all: try (eapply evaluation_witness_same_solver_view; eauto).
      all: try (eapply completed_witness_same_solver_view; eauto).
      all: try (eapply summary_valid_same_solver_view; eauto).
      all: eapply IHk; eauto.
    Qed.

    Lemma observe_same_solver_view :
      forall st x, same_solver_view st (R.observe st x).
    Proof.
      intros st x. unfold same_solver_view, same_read_view, R.observe.
      destruct (R.Ranking.observe (R.ranking st) x).
      repeat split; reflexivity.
    Qed.

    Lemma evaluation_witness_observe :
      forall tf st x fr body,
        evaluation_witness tf st fr body ->
        evaluation_witness tf (R.observe st x) fr body.
    Proof.
      intros. eapply evaluation_witness_same_solver_view;
        [apply observe_same_solver_view |exact H].
    Qed.

    Lemma completed_witness_observe :
      forall tf st x fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.observe st x) fr direct.
    Proof.
      intros. eapply completed_witness_same_solver_view;
        [apply observe_same_solver_view |exact H].
    Qed.

    Lemma continuation_history_observe :
      forall tf st x k,
        continuation_history tf st k ->
        continuation_history tf (R.observe st x) k.
    Proof.
      intros. eapply continuation_history_same_solver_view;
        [apply observe_same_solver_view |exact H].
    Qed.

    Lemma evaluation_witness_write_other_source :
      forall tf st fr target input st' changed other current,
        R.write_side_contribution st fr target input = (st', changed) ->
        R.frame_owner other <> R.frame_owner fr ->
        evaluation_witness tf st other current ->
        evaluation_witness tf st' other current.
    Proof.
      intros tf st fr target input st' changed other current
        Hwrite Hneq
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]].
      pose proof (write_side_contribution_same_read_view Hwrite) as Hview.
      split.
      - now apply solved_same_read_view with st.
      - exists reads, effects. split; [exact Hcontext |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_write_other_source; eauto.
          * exact Hframe.
    Qed.

    Lemma completed_witness_write_other_source :
      forall tf st fr target input st' changed other direct,
        R.write_side_contribution st fr target input = (st', changed) ->
        R.frame_owner other <> R.frame_owner fr ->
        completed_witness tf st other direct ->
        completed_witness tf st' other direct.
    Proof.
      intros tf st fr target input st' changed other direct
        Hwrite Hneq
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]].
      pose proof (write_side_contribution_same_read_view Hwrite) as Hview.
      split.
      - now apply solved_same_read_view with st.
      - exists reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_write_other_source; eauto.
          * exact Hframe.
    Qed.

    Lemma summary_valid_write_other_source :
      forall tf st fr target input st' changed owner,
        R.write_side_contribution st fr target input = (st', changed) ->
        owner <> R.frame_owner fr ->
        summary_valid tf st owner ->
        summary_valid tf st' owner.
    Proof.
      intros tf st fr target input st' changed owner Hwrite Hneq
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      pose proof (write_side_contribution_same_read_view Hwrite) as Hview.
      split.
      - now apply solved_same_read_view with st.
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * eapply recorded_effects_write_other_source; eauto.
          * unfold R.sigma_value in *. rewrite (proj1 Hview). exact Hdirect.
    Qed.

    Lemma set_value_sigma_value_other_correctness :
      forall st fr direct st' fr' owner,
        R.set_value st fr direct = (st', fr') ->
        owner <> R.frame_owner fr ->
        R.sigma_value st' owner = R.sigma_value st owner.
    Proof.
      intros st fr direct st' fr' owner Hset Hneq.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; subst; unfold R.sigma_value; cbn;
      try reflexivity;
      rewrite ML.lookup_update_other by exact Hneq; reflexivity.
    Qed.

    Lemma evaluation_witness_set_value :
      forall tf st fr direct st' fr' other current,
        R.set_value st fr direct = (st', fr') ->
        evaluation_witness tf st other current ->
        evaluation_witness tf st' other current.
    Proof.
      intros tf st fr direct st' fr' other current Hset
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split.
      - eapply set_value_solved; eauto.
      - exists reads, effects. split; [exact Hcontext |]. split.
        + eapply guarded_reads_set_value; eauto.
        + split; [eapply recorded_effects_set_value; eauto |exact Hframe].
    Qed.

    Lemma completed_witness_set_value :
      forall tf st fr direct st' fr' other result,
        R.set_value st fr direct = (st', fr') ->
        completed_witness tf st other result ->
        completed_witness tf st' other result.
    Proof.
      intros tf st fr direct st' fr' other result Hset
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split.
      - eapply set_value_solved; eauto.
      - exists reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_set_value; eauto.
        + split; [eapply recorded_effects_set_value; eauto |exact Hframe].
    Qed.

    Lemma summary_valid_set_value_other :
      forall tf st fr direct st' fr' owner,
        R.set_value st fr direct = (st', fr') ->
        owner <> R.frame_owner fr ->
        summary_valid tf st owner ->
        summary_valid tf st' owner.
    Proof.
      intros tf st fr direct st' fr' owner Hset Hneq
        [Hsolved [result [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split.
      - eapply set_value_solved; eauto.
      - exists result, reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_set_value; eauto.
        + split.
          * eapply recorded_effects_set_value; eauto.
          * rewrite (@set_value_sigma_value_other_correctness
              st fr direct st' fr' owner Hset Hneq). exact Hdirect.
    Qed.

    Lemma evaluation_witness_enqueue :
      forall tf st inserted fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.enqueue st inserted) fr current.
    Proof.
      intros tf st inserted fr current
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - now apply guarded_reads_enqueue.
      - split; assumption.
    Qed.

    Lemma completed_witness_enqueue :
      forall tf st inserted fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.enqueue st inserted) fr direct.
    Proof.
      intros tf st inserted fr direct
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_enqueue.
      - split; assumption.
    Qed.

    Lemma summary_valid_enqueue :
      forall tf st inserted owner,
        summary_valid tf st owner ->
        summary_valid tf (R.enqueue st inserted) owner.
    Proof.
      intros tf st inserted owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split; [exact Hsolved |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_enqueue.
      - split; assumption.
    Qed.

    Lemma continuation_history_enqueue :
      forall tf st inserted k,
        continuation_history tf st k ->
        continuation_history tf (R.enqueue st inserted) k.
    Proof.
      intros tf st inserted k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hhistory]; split.
      all: try (now apply evaluation_witness_enqueue).
      all: try (now apply completed_witness_enqueue).
      all: try (now apply summary_valid_enqueue).
      all: now apply IHk.
    Qed.

    Lemma materialize_solved_correctness :
      forall st x, Sem.solved (R.materialize st x) x.
    Proof.
      intros st x. unfold Sem.solved, Sem.StateSpec.solved, R.materialize, R.semantic_lookup.
      destruct (M.lookup (R.sigma st) x) as [value|] eqn:Hlookup.
      - exists value. cbn. now rewrite Hlookup.
      - exists D.bottom. cbn. now rewrite ML.lookup_update_same.
    Qed.

    Lemma materialize_preserves_solved :
      forall st inserted x,
        Sem.solved st x -> Sem.solved (R.materialize st inserted) x.
    Proof.
      intros st inserted x [value Hlookup].
      unfold R.materialize, R.semantic_lookup in *.
      destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted.
      - now exists value.
      - destruct (V.eq_dec x inserted) as [-> | Hneq].
        + rewrite Hinserted in Hlookup.
          destruct (S.mem inserted (R.dormant_bottom st));
            inversion Hlookup; subst. exists D.bottom.
          unfold R.semantic_lookup. cbn.
          now rewrite ML.lookup_update_same.
        + exists value. unfold R.semantic_lookup. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
    Qed.

    Lemma materialize_sigma_value_solved :
      forall st inserted x,
        Sem.solved st x ->
        R.sigma_value (R.materialize st inserted) x = R.sigma_value st x.
    Proof.
      intros st inserted x [value Hlookup]. unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted;
        [reflexivity |].
      destruct (V.eq_dec x inserted) as [-> |Hneq].
      - unfold R.sigma_value. cbn. rewrite ML.lookup_update_same, Hinserted.
        reflexivity.
      - unfold R.sigma_value. cbn.
        rewrite ML.lookup_update_other by exact Hneq. reflexivity.
    Qed.

    Lemma recorded_effects_materialize :
      forall st inserted owner effects,
        recorded_effects st owner effects ->
        recorded_effects (R.materialize st inserted) owner effects.
    Proof.
      intros st inserted owner effects Hrecord. unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted); exact Hrecord.
    Qed.

    Lemma evaluation_witness_materialize :
      forall tf st inserted fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.materialize st inserted) fr current.
    Proof.
      intros tf st inserted fr current
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split.
      - now apply materialize_preserves_solved.
      - exists reads, effects. split; [exact Hcontext |]. split.
        + now apply guarded_reads_materialize.
        + split; [now apply recorded_effects_materialize |exact Hframe].
    Qed.

    Lemma completed_witness_materialize :
      forall tf st inserted fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.materialize st inserted) fr direct.
    Proof.
      intros tf st inserted fr direct
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split.
      - now apply materialize_preserves_solved.
      - exists reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_materialize.
        + split; [now apply recorded_effects_materialize |exact Hframe].
    Qed.

    Lemma summary_valid_materialize :
      forall tf st inserted owner,
        summary_valid tf st owner ->
        summary_valid tf (R.materialize st inserted) owner.
    Proof.
      intros tf st inserted owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split.
      - now apply materialize_preserves_solved.
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_materialize.
        + split; [now apply recorded_effects_materialize |].
          rewrite (@materialize_sigma_value_solved st inserted owner Hsolved).
          exact Hdirect.
    Qed.

    Lemma continuation_history_materialize :
      forall tf st inserted k,
        continuation_history tf st k ->
        continuation_history tf (R.materialize st inserted) k.
    Proof.
      intros tf st inserted k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hhistory]; split.
      all: try (now apply evaluation_witness_materialize).
      all: try (now apply completed_witness_materialize).
      all: try (now apply summary_valid_materialize).
      all: now apply IHk.
    Qed.

    Lemma solved_clear_side_dirty :
      forall st target x,
        Sem.solved st x -> Sem.solved (R.clear_side_dirty st target) x.
    Proof.
      intros st target x [value Hlookup]. exists value.
      unfold R.clear_side_dirty, R.with_dirty_side_targets,
        R.semantic_lookup in *. cbn. exact Hlookup.
    Qed.

    Lemma guarded_reads_clear_side_dirty :
      forall st target owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.clear_side_dirty st target) owner reads.
    Proof.
      intros st target owner reads Hreads observed value Hin.
      specialize (Hreads observed value Hin).
      unfold R.clear_side_dirty, R.with_dirty_side_targets,
        queued, R.sigma_value in *. cbn in *.
      destruct Hreads as [Hsolved [Hregistered Hvalue]].
      split; [now apply solved_clear_side_dirty |].
      tauto.
    Qed.

    Lemma recorded_effects_clear_side_dirty :
      forall st target owner effects,
        recorded_effects st owner effects ->
        recorded_effects (R.clear_side_dirty st target) owner effects.
    Proof.
      intros st target owner effects Hrecord observed value Hin.
      specialize (Hrecord observed value Hin).
      unfold R.clear_side_dirty, R.with_dirty_side_targets in *. cbn in *.
      exact Hrecord.
    Qed.

    Lemma evaluation_witness_clear_side_dirty :
      forall tf st target fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.clear_side_dirty st target) fr current.
    Proof.
      intros tf st target fr current
        [Hsolved [reads [effects [Hcontext [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_clear_side_dirty |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - now apply guarded_reads_clear_side_dirty.
      - split; [now apply recorded_effects_clear_side_dirty |exact Hframe].
    Qed.

    Lemma completed_witness_clear_side_dirty :
      forall tf st target fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.clear_side_dirty st target) fr direct.
    Proof.
      intros tf st target fr direct
        [Hsolved [reads [effects [Htrace [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_clear_side_dirty |].
      exists reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_clear_side_dirty.
      - split; [now apply recorded_effects_clear_side_dirty |exact Hframe].
    Qed.

    Lemma summary_valid_clear_side_dirty :
      forall tf st target owner,
        summary_valid tf st owner ->
        summary_valid tf (R.clear_side_dirty st target) owner.
    Proof.
      intros tf st target owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      split; [now apply solved_clear_side_dirty |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_clear_side_dirty.
      - split; [now apply recorded_effects_clear_side_dirty |].
        unfold R.clear_side_dirty, R.with_dirty_side_targets,
          R.sigma_value. cbn. exact Hdirect.
    Qed.

    Lemma continuation_history_clear_side_dirty :
      forall tf st target k,
        continuation_history tf st k ->
        continuation_history tf (R.clear_side_dirty st target) k.
    Proof.
      intros tf st target k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hhistory]; split.
      all: try (now apply evaluation_witness_clear_side_dirty).
      all: try (now apply completed_witness_clear_side_dirty).
      all: try (now apply summary_valid_clear_side_dirty).
      all: now apply IHk.
    Qed.

    Lemma evaluation_witness_add_reader :
      forall tf st target added fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (add_reader st target added) fr current.
    Proof.
      intros tf st target added fr current
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - now apply guarded_reads_add_reader.
      - split; assumption.
    Qed.

    Lemma completed_witness_add_reader :
      forall tf st target added fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (add_reader st target added) fr direct.
    Proof.
      intros tf st target added fr direct
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_add_reader.
      - split; assumption.
    Qed.

    Lemma summary_valid_add_reader :
      forall tf st target added owner,
        summary_valid tf st owner ->
        summary_valid tf (add_reader st target added) owner.
    Proof.
      intros tf st target added owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split; [exact Hsolved |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_add_reader.
      - split; assumption.
    Qed.

    Lemma continuation_history_add_reader :
      forall tf st target added k,
        continuation_history tf st k ->
        continuation_history tf (add_reader st target added) k.
    Proof.
      intros tf st target added k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hhistory]; split.
      all: try (now apply evaluation_witness_add_reader).
      all: try (now apply completed_witness_add_reader).
      all: try (now apply summary_valid_add_reader).
      all: now apply IHk.
    Qed.

    Lemma evaluation_witness_remember_dormant :
      forall tf st target fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.remember_dormant st target) fr current.
    Proof.
      intros tf st target fr current
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split.
      - now apply solved_remember_dormant.
      - exists reads, effects. split; [exact Hcontext |]. split.
        + now apply guarded_reads_remember_dormant.
        + split.
          * unfold recorded_effects, R.remember_dormant,
              R.with_dormant_bottom in *; exact Heffects.
          * exact Hframe.
    Qed.

    Lemma completed_witness_remember_dormant :
      forall tf st target fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.remember_dormant st target) fr direct.
    Proof.
      intros tf st target fr direct
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split.
      - now apply solved_remember_dormant.
      - exists reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_remember_dormant.
        + split.
          * unfold recorded_effects, R.remember_dormant,
              R.with_dormant_bottom in *; exact Heffects.
          * exact Hframe.
    Qed.

    Lemma summary_valid_remember_dormant :
      forall tf st target owner,
        summary_valid tf st owner ->
        summary_valid tf (R.remember_dormant st target) owner.
    Proof.
      intros tf st target owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split.
      - now apply solved_remember_dormant.
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_remember_dormant.
        + split.
          * unfold recorded_effects, R.remember_dormant,
              R.with_dormant_bottom in *; exact Heffects.
          * unfold R.remember_dormant, R.with_dormant_bottom,
              R.sigma_value. exact Hdirect.
    Qed.

    Lemma summary_valid_pure_dormant :
      forall tf st target,
        R.pure_bottom_rhs tf target = true ->
        summary_valid tf (R.remember_dormant st target) target.
    Proof.
      intros tf st target Hpure.
      unfold R.pure_bottom_rhs in Hpure.
      destruct (tf target) as
        [direct | read next | side raw next | spawn next] eqn:Hrhs;
        try discriminate.
      unfold R.equivalent in Hpure.
      apply Bool.andb_true_iff in Hpure as [Hdirect _].
      split.
      - exists (R.sigma_value st target).
        unfold R.semantic_lookup, R.sigma_value, R.remember_dormant,
          R.with_dormant_bottom. cbn.
        destruct (M.lookup (R.sigma st) target); [reflexivity |].
        assert (S.mem target (S.add target (R.dormant_bottom st)) = true)
          as Hmember by (apply SL.add_spec; now left).
        now rewrite Hmember.
      - exists direct, [], []. split.
        + rewrite Hrhs. constructor.
        + split.
          * intros read read_value Hin. contradiction.
          * split.
            -- intros side side_value Hin. contradiction.
            -- unfold R.remember_dormant, R.with_dormant_bottom,
                 R.sigma_value. cbn.
               eapply DL.leq_trans; [exact Hdirect |apply DL.bottom_least].
    Qed.

    Lemma solved_remember_dormant_origin :
      forall st target x,
        Sem.solved (R.remember_dormant st target) x ->
        Sem.solved st x \/ x = target.
    Proof.
      intros st target x [value Hlookup].
      unfold R.semantic_lookup, R.remember_dormant,
        R.with_dormant_bottom in Hlookup. cbn in Hlookup.
      destruct (M.lookup (R.sigma st) x) eqn:Hsigma.
      - left. exists value. unfold R.semantic_lookup. now rewrite Hsigma.
      - destruct (V.eq_dec x target) as [-> |Hneq]; [now right |left].
        exists value. unfold R.semantic_lookup. rewrite Hsigma.
        destruct (S.mem x (S.add target (R.dormant_bottom st))) eqn:Hmember;
          try discriminate.
        inversion Hlookup; subst value.
        apply SL.add_spec in Hmember as [Heq |Hmember]; [congruence |].
        now rewrite Hmember.
    Qed.

    Lemma continuation_history_remember_dormant :
      forall tf st target k,
        continuation_history tf st k ->
        continuation_history tf (R.remember_dormant st target) k.
    Proof.
      intros tf st target k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Htail]; split.
      all: try (now apply evaluation_witness_remember_dormant).
      all: try (now apply completed_witness_remember_dormant).
      all: try (now apply summary_valid_remember_dormant).
      all: now apply IHk.
    Qed.

    Lemma evaluation_witness_get_dormant :
      forall tf st fr target next,
        R.is_dormant st target = true ->
        evaluation_witness tf st fr (R.ConstraintSystem.Get target next) ->
        evaluation_witness tf (R.add_reader st target (R.frame_owner fr))
          fr (next D.bottom).
    Proof.
      intros tf st fr target next Hdormant
        [Howner [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split.
      - now apply solved_add_reader.
      - exists (reads ++ [(target, D.bottom)]), effects. split.
        + eapply rhs_context_get. exact Hcontext.
        + split.
          * intros observed value Hin. apply List.in_app_or in Hin.
            destruct Hin as [Hold |Hnew].
            -- exact (@guarded_reads_add_reader st target
                 (R.frame_owner fr) (R.frame_owner fr) reads Hreads
                 observed value Hold).
            -- cbn in Hnew. destruct Hnew as [Heq |Hfalse];
                 [inversion Heq; subst |contradiction]. split.
               ++ apply solved_add_reader. now apply solved_dormant.
               ++ split.
                  ** left. unfold R.add_reader, R.lookup_set. cbn.
                     rewrite ML.lookup_update_same. apply SL.add_spec.
                     now left.
                  ** left. change (D.bottom = R.sigma_value st observed).
                     symmetry. exact (proj2
                       (@dormant_semantic_bottom st observed Hdormant)).
          * split; [exact Heffects |exact Hframe].
    Qed.

    Lemma evaluation_witness_get_remembered :
      forall tf st fr target next,
        R.is_dormant (R.remember_dormant st target) target = true ->
        evaluation_witness tf st fr (R.ConstraintSystem.Get target next) ->
        evaluation_witness tf
          (R.add_reader (R.remember_dormant st target)
             target (R.frame_owner fr)) fr (next D.bottom).
    Proof.
      intros. apply evaluation_witness_get_dormant; [exact H |].
      now apply evaluation_witness_remember_dormant.
    Qed.

    Lemma evaluation_witness_pop_other :
      forall tf st popped rest fr current,
        R.queue_pop (R.queue st) = Some (popped, rest) ->
        R.frame_owner fr <> popped ->
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.with_queue st rest) fr current.
    Proof.
      intros tf st popped rest fr current Hpop Hneq
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - eapply guarded_reads_pop_other; eauto.
      - split; assumption.
    Qed.

    Lemma completed_witness_pop_other :
      forall tf st popped rest fr direct,
        R.queue_pop (R.queue st) = Some (popped, rest) ->
        R.frame_owner fr <> popped ->
        completed_witness tf st fr direct ->
        completed_witness tf (R.with_queue st rest) fr direct.
    Proof.
      intros tf st popped rest fr direct Hpop Hneq
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split; [exact Htrace |]. split.
      - eapply guarded_reads_pop_other; eauto.
      - split; assumption.
    Qed.

    Lemma summary_valid_pop_other :
      forall tf st popped rest owner,
        R.queue_pop (R.queue st) = Some (popped, rest) ->
        owner <> popped ->
        summary_valid tf st owner ->
        summary_valid tf (R.with_queue st rest) owner.
    Proof.
      intros tf st popped rest owner Hpop Hneq
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]]. split; [exact Hsolved |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - eapply guarded_reads_pop_other; eauto.
      - split; assumption.
    Qed.

    Lemma initial_rhs_context : forall body, rhs_context body body [] [].
    Proof. constructor. Qed.

    Lemma initial_evaluation_witness :
      forall tf st owner phase,
        Sem.solved st owner ->
        evaluation_witness tf st (R.fresh_frame st owner phase) (tf owner).
    Proof.
      intros tf st owner phase Hsolved. split; [exact Hsolved |].
      exists [], []. split; [apply initial_rhs_context |]. split.
      - intros target value Hin. contradiction.
      - split; intros target value Hin; contradiction.
    Qed.



    Lemma rhs_context_side :
      forall root target value next prefix_reads prefix_effects,
        rhs_context root (R.ConstraintSystem.Side target value next)
          prefix_reads prefix_effects ->
        rhs_context root next prefix_reads
          (prefix_effects ++ [(target, value)]).
    Proof.
      intros root target value next reads effects Hprefix.
      remember (R.ConstraintSystem.Side target value next) as current eqn:Hcurrent.
      revert target value next Hcurrent.
      induction Hprefix; intros target0 value0 next0 Hcurrent.
      - inversion Hcurrent; subst. cbn. constructor. constructor.
      - cbn. constructor. eapply IHHprefix. exact Hcurrent.
      - cbn. constructor. eapply IHHprefix. exact Hcurrent.
      - cbn. constructor; [assumption |]. eapply IHHprefix. exact Hcurrent.
    Qed.

    Lemma evaluation_witness_side :
      forall tf st fr target raw next fr' input st' changed,
        R.record_side_input fr target raw = (fr', input) ->
        R.write_side_contribution st fr' target input = (st', changed) ->
        evaluation_witness tf st fr (R.ConstraintSystem.Side target raw next) ->
        evaluation_witness tf st' fr' next.
    Proof.
      intros tf st fr target raw next fr' input st' changed
        Hrecord Hwrite
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]].
      assert (Howner : R.frame_owner fr' = R.frame_owner fr).
      { pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord) as H.
        cbn in H. symmetry. exact H. }
      assert (Hlookup :
        M.lookup (R.frame_local_side fr') target = Some input).
      { pose proof (record_side_input_lookup fr target raw) as H.
        rewrite Hrecord in H. cbn in H. exact H. }
      assert (Hframe' : frame_effects fr' (effects ++ [(target, raw)])).
      { pose proof (@frame_effects_record_side
          fr effects target raw Hframe) as H.
        rewrite Hrecord in H. cbn in H. exact H. }
      pose proof (write_side_contribution_same_read_view Hwrite) as Hview.
      split.
      - rewrite Howner. now apply solved_same_read_view with st.
      - exists reads, (effects ++ [(target, raw)]). split.
        + rewrite Howner. eapply rhs_context_side. exact Hcontext.
        + split.
          * eapply guarded_reads_same_view; [exact Hview |].
            rewrite Howner. exact Hreads.
          * split.
            -- eapply recorded_effects_write_side_append; eauto.
               rewrite Howner. exact Heffects.
            -- exact Hframe'.
    Qed.

    Lemma rhs_context_spawn :
      forall root target next prefix_reads prefix_effects,
        spawned target ->
        rhs_context root (R.ConstraintSystem.Spawn target next)
          prefix_reads prefix_effects ->
        rhs_context root next prefix_reads prefix_effects.
    Proof.
      intros root target next reads effects Hspawn Hprefix.
      remember (R.ConstraintSystem.Spawn target next) as current eqn:Hcurrent.
      revert target next Hspawn Hcurrent.
      induction Hprefix; intros target0 next0 Hspawn Hcurrent.
      - inversion Hcurrent; subst. cbn. constructor; [exact Hspawn |constructor].
      - cbn. constructor. eapply IHHprefix; eassumption.
      - cbn. constructor. eapply IHHprefix; eassumption.
      - cbn. constructor; [assumption |]. eapply IHHprefix; eassumption.
    Qed.

    Lemma evaluation_witness_spawn :
      forall tf st fr target next,
        spawned target ->
        evaluation_witness tf st fr (R.ConstraintSystem.Spawn target next) ->
        evaluation_witness tf st fr next.
    Proof.
      intros tf st fr target next Hspawn
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split.
      - eapply rhs_context_spawn; eassumption.
      - split; [exact Hreads |split; assumption].
    Qed.

    Lemma evaluation_ret_completed :
      forall tf st fr direct,
        evaluation_witness tf st fr (R.ConstraintSystem.Ret direct) ->
        completed_witness tf st fr direct.
    Proof.
      intros tf st fr direct
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split.
      - pose proof (rhs_context_complete Hcontext (TraceRet direct)) as Hcomplete.
        now rewrite !List.app_nil_r in Hcomplete.
      - split; [exact Hreads |split; assumption].
    Qed.

    Lemma completed_witness_set_value_summary :
      forall tf st fr direct st' fr',
        completed_witness tf st fr direct ->
        R.set_value st fr direct = (st', fr') ->
        summary_valid tf st' (R.frame_owner fr).
    Proof.
      intros tf st fr direct st' fr'
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]] Hset. split.
      - eapply set_value_solved; eauto.
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_set_value; eauto.
        + split.
          * eapply recorded_effects_set_value; eauto.
          * eapply set_value_direct_sound. exact Hset.
    Qed.

    Lemma completed_witness_dead_side :
      forall tf st fr direct target st' changed,
        S.mem target (R.frame_current_targets fr) = false ->
        R.write_side_contribution st fr target D.bottom = (st', changed) ->
        completed_witness tf st fr direct ->
        completed_witness tf st' fr direct.
    Proof.
      intros tf st fr direct target st' changed Hdead Hwrite
        [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]].
      pose proof (write_side_contribution_same_read_view Hwrite) as Hview.
      split.
      - now apply solved_same_read_view with st.
      - exists reads, effects. split; [exact Htrace |]. split.
        + eapply guarded_reads_same_view; eauto.
        + split.
          * intros observed value Hin.
            assert (Hneq : observed <> target).
            { intro Heq. subst.
              destruct (Hframe target value Hin)
                as [accumulated [Hlookup [Hle Hmem]]].
              rewrite Hdead in Hmem. discriminate. }
            destruct (Heffects observed value Hin)
              as [contribution [Hlookup Hle]].
            exists contribution. split.
            -- rewrite (write_side_contribution_other Hwrite Hneq).
               exact Hlookup.
            -- exact Hle.
          * exact Hframe.
    Qed.

    Lemma publish_targets_same_solver_view :
      forall st fr, same_solver_view st (R.publish_targets st fr).
    Proof. intros. repeat split; reflexivity. Qed.

    Lemma promote_controlled_same_solver_view :
      forall st owner, same_solver_view st (R.promote_controlled st owner).
    Proof. intros. repeat split; reflexivity. Qed.

    Lemma mark_side_dirty_same_solver_view :
      forall st target, same_solver_view st (R.mark_side_dirty st target).
    Proof. intros. repeat split; reflexivity. Qed.

    Lemma solved_flush_deferred :
      forall st x, Sem.solved st x -> Sem.solved (R.flush_deferred st) x.
    Proof. intros st x [value Hlookup]. exists value. exact Hlookup. Qed.

    Lemma solved_flush_deferred_back :
      forall st x, Sem.solved (R.flush_deferred st) x -> Sem.solved st x.
    Proof. intros st x [value Hlookup]. exists value. exact Hlookup. Qed.

    Lemma queued_flush_deferred :
      forall st x, queued st x -> queued (R.flush_deferred st) x.
    Proof.
      intros st x [Hqueue | Hdeferred]; left; cbn;
        apply queue_insert_all_members.
      - now right.
      - now left.
    Qed.

    Lemma guarded_reads_flush_deferred :
      forall st owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.flush_deferred st) owner reads.
    Proof.
      intros st owner reads Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split; [now apply solved_flush_deferred |]. split.
      - destruct Hreader as [Hreader | Hqueued];
          [now left |right; now apply queued_flush_deferred].
      - destruct Hvalue as [Hvalue | Hqueued];
          [now left |right; now apply queued_flush_deferred].
    Qed.

    Lemma recorded_effects_flush_deferred :
      forall st owner effects,
        recorded_effects st owner effects ->
        recorded_effects (R.flush_deferred st) owner effects.
    Proof. intros st owner effects Hrecord. exact Hrecord. Qed.

    Lemma evaluation_witness_flush_deferred :
      forall tf st fr body,
        evaluation_witness tf st fr body ->
        evaluation_witness tf (R.flush_deferred st) fr body.
    Proof.
      intros tf st fr body
        [Hsolved [reads [effects [Hcontext [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_flush_deferred |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - now apply guarded_reads_flush_deferred.
      - split; [now apply recorded_effects_flush_deferred |exact Hframe].
    Qed.

    Lemma completed_witness_flush_deferred :
      forall tf st fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.flush_deferred st) fr direct.
    Proof.
      intros tf st fr direct
        [Hsolved [reads [effects [Htrace [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_flush_deferred |].
      exists reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_flush_deferred.
      - split; [now apply recorded_effects_flush_deferred |exact Hframe].
    Qed.

    Lemma summary_valid_flush_deferred :
      forall tf st owner,
        summary_valid tf st owner ->
        summary_valid tf (R.flush_deferred st) owner.
    Proof.
      intros tf st owner
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      split; [now apply solved_flush_deferred |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_flush_deferred.
      - split; [now apply recorded_effects_flush_deferred |exact Hdirect].
    Qed.

    Lemma continuation_history_flush_deferred :
      forall tf st k,
        continuation_history tf st k ->
        continuation_history tf (R.flush_deferred st) k.
    Proof.
      intros tf st k. induction k; cbn; intros Hhistory; try exact I.
      all: destruct Hhistory as [Hhead Hrest]; split.
      all: try (now apply evaluation_witness_flush_deferred).
      all: try (now apply completed_witness_flush_deferred).
      all: try (now apply summary_valid_flush_deferred).
      all: now apply IHk.
    Qed.

    Lemma control_history_continue_side :
      forall tf st fr target next k changed,
        evaluation_witness tf st fr next ->
        continuation_history tf st k ->
        control_history tf (R.cfg_state
          (R.continue_side st fr target next k changed))
          (R.cfg_control (R.continue_side st fr target next k changed)).
    Proof.
      intros tf st fr target next k changed Hcurrent Hcontinuation.
      unfold R.continue_side. destruct changed; [|cbn; tauto].
      destruct (R.rank_lt st (R.frame_owner fr) target &&
        negb (R.is_materialized st target))%bool; cbn.
      - tauto.
      - split; [now apply evaluation_witness_enqueue
               |now apply continuation_history_enqueue].
    Qed.

    Lemma control_history_continue_dead :
      forall tf st fr direct target remaining k changed,
        completed_witness tf st fr direct ->
        continuation_history tf st k ->
        control_history tf (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed))
          (R.cfg_control
            (R.continue_dead st fr direct target remaining k changed)).
    Proof.
      intros tf st fr direct target remaining k changed
        Hcurrent Hcontinuation.
      unfold R.continue_dead. destruct changed; [|cbn; tauto].
      destruct (R.rank_lt st (R.frame_owner fr) target &&
        negb (R.is_materialized st target))%bool; cbn.
      - tauto.
      - split; [now apply completed_witness_enqueue
               |now apply continuation_history_enqueue].
    Qed.

    Lemma reset_registered_cells_same_solver_view :
      forall st owner, same_solver_view st (R.reset_registered_cells st owner).
    Proof.
      intros. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; repeat split; reflexivity.
    Qed.

    Lemma continuation_history_complete_get :
      forall tf st fr target st' fr' value k,
        R.complete_get st fr target = (st', fr', value) ->
        continuation_history tf st k -> continuation_history tf st' k.
    Proof.
      intros tf st fr target st' fr' value k Hget Hhistory.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      inversion Hget; subst.
      apply continuation_history_materialize.
      apply continuation_history_add_reader. subst base.
      destruct (R.rank_lt st (R.frame_owner fr) target).
      - exact Hhistory.
      - eapply continuation_history_same_solver_view;
          [apply promote_controlled_same_solver_view |exact Hhistory].
    Qed.

    Lemma evaluation_witness_complete_get :
      forall tf st fr target next st' fr' value,
        R.complete_get st fr target = (st', fr', value) ->
        evaluation_witness tf st fr (R.ConstraintSystem.Get target next) ->
        evaluation_witness tf st' fr' (next value).
    Proof.
      intros tf st fr target next st' fr' value Hget Hwitness.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (read_state := add_reader base target (R.frame_owner fr)) in *.
      fold add_reader in Hget. inversion Hget; subst.
      assert (Hbase : evaluation_witness tf base fr
        (R.ConstraintSystem.Get target next)).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
        - exact Hwitness.
        - eapply evaluation_witness_same_solver_view;
            [apply promote_controlled_same_solver_view |exact Hwitness]. }
      assert (Hread : evaluation_witness tf read_state fr
        (R.ConstraintSystem.Get target next)).
      { subst read_state. now apply evaluation_witness_add_reader. }
      assert (Hfinal : evaluation_witness tf
        (R.materialize read_state target) fr
        (R.ConstraintSystem.Get target next)).
      { now apply evaluation_witness_materialize. }
      destruct Hfinal as [Hsolved [reads [effects
        [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists (reads ++ [(target,
        R.sigma_value (R.materialize read_state target) target)]), effects.
      split; [eapply rhs_context_get; exact Hcontext |]. split.
      - intros observed seen Hin. apply List.in_app_or in Hin.
        destruct Hin as [Hold | Hnew].
        + apply Hreads. exact Hold.
        + cbn in Hnew. destruct Hnew as [Heq | Hfalse];
            [inversion Heq; subst |contradiction]. split.
          * apply materialize_solved_correctness.
          * split.
            -- left. apply add_reader_registered_after_materialize.
            -- now left.
      - split; [exact Heffects |exact Hframe].
    Qed.

    Local Transparent R.dirty_complete_get R.try_dirty_read.

    Lemma queue_remove_other_preserved :
      forall queue removed x,
        x <> removed -> List.In x queue -> List.In x (R.queue_remove removed queue).
    Proof.
      induction queue as [|head rest IH]; intros removed x Hneq Hin; cbn in *.
      - contradiction.
      - destruct (V.eq_dec removed head) as [-> | Hhead].
        + destruct Hin as [Heq | Hin]; [congruence |exact Hin].
        + destruct Hin as [-> | Hin]; [now left |right].
          eapply IH; [exact Hneq |exact Hin].
    Qed.

    Lemma queued_cancel_dirty_target_other :
      forall st target x,
        x <> target -> queued st x -> queued (R.cancel_dirty_target st target) x.
    Proof.
      intros st target x Hneq Hqueued.
      unfold queued, R.cancel_dirty_target, R.clear_side_dirty,
        R.with_dirty_side_targets, R.with_queue in *. cbn.
      destruct Hqueued as [Hqueued | Hdeferred].
      - left. now apply queue_remove_other_preserved.
      - right. exact Hdeferred.
    Qed.

    Lemma solved_cancel_dirty_target :
      forall st target x,
        Sem.solved st x -> Sem.solved (R.cancel_dirty_target st target) x.
    Proof.
      intros st target x [value Hlookup]. exists value.
      unfold R.cancel_dirty_target, R.clear_side_dirty,
        R.with_dirty_side_targets, R.with_queue, R.semantic_lookup in *.
      exact Hlookup.
    Qed.

    Lemma guarded_reads_cancel_dirty_target_other :
      forall st target owner reads,
        owner <> target ->
        guarded_reads st owner reads ->
        guarded_reads (R.cancel_dirty_target st target) owner reads.
    Proof.
      intros st target owner reads Hneq Hguard observed value Hin.
      destruct (Hguard observed value Hin) as [Hsolved [Hreader Hvalue]].
      split; [now apply solved_cancel_dirty_target |]. split.
      - destruct Hreader as [Hreader |Hqueued]; [now left |right].
        now apply queued_cancel_dirty_target_other.
      - destruct Hvalue as [Hvalue |Hqueued]; [now left |right].
        now apply queued_cancel_dirty_target_other.
    Qed.

    Lemma recorded_effects_cancel_dirty_target :
      forall st target owner effects,
        recorded_effects st owner effects ->
        recorded_effects (R.cancel_dirty_target st target) owner effects.
    Proof.
      intros st target owner effects Hrecord observed value Hin.
      specialize (Hrecord observed value Hin).
      unfold R.cancel_dirty_target, R.clear_side_dirty,
        R.with_dirty_side_targets, R.with_queue in *. exact Hrecord.
    Qed.

    Lemma evaluation_witness_cancel_dirty_target_other :
      forall tf st target fr current,
        R.frame_owner fr <> target ->
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.cancel_dirty_target st target) fr current.
    Proof.
      intros tf st target fr current Hneq
        [Hsolved [reads [effects [Hcontext [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_cancel_dirty_target |].
      exists reads, effects. split; [exact Hcontext |]. split.
      - now apply guarded_reads_cancel_dirty_target_other.
      - split; [now apply recorded_effects_cancel_dirty_target |exact Hframe].
    Qed.

    Lemma completed_witness_cancel_dirty_target_other :
      forall tf st target fr direct,
        R.frame_owner fr <> target ->
        completed_witness tf st fr direct ->
        completed_witness tf (R.cancel_dirty_target st target) fr direct.
    Proof.
      intros tf st target fr direct Hneq
        [Hsolved [reads [effects [Htrace [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_cancel_dirty_target |].
      exists reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_cancel_dirty_target_other.
      - split; [now apply recorded_effects_cancel_dirty_target |exact Hframe].
    Qed.

    Lemma summary_valid_cancel_dirty_target_other :
      forall tf st target owner,
        owner <> target -> summary_valid tf st owner ->
        summary_valid tf (R.cancel_dirty_target st target) owner.
    Proof.
      intros tf st target owner Hneq
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      split; [now apply solved_cancel_dirty_target |].
      exists direct, reads, effects. split; [exact Htrace |]. split.
      - now apply guarded_reads_cancel_dirty_target_other.
      - split; [now apply recorded_effects_cancel_dirty_target |].
        unfold R.cancel_dirty_target, R.clear_side_dirty,
          R.with_dirty_side_targets, R.with_queue, R.sigma_value.
        exact Hdirect.
    Qed.

    Lemma write_dirty_value_is_dirty_commit_value :
      forall st target value,
        R.write_dirty_value st target value =
        dirty_commit_value st target value.
    Proof. reflexivity. Qed.

    Lemma evaluation_witness_write_dirty_value :
      forall tf st target value fr current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf (R.write_dirty_value st target value) fr current.
    Proof.
      intros tf st target value fr current
        [Hsolved [reads [effects [Hcontext [Hreads [Heffects Hframe]]]]]].
      rewrite write_dirty_value_is_dirty_commit_value. split.
      - destruct Hsolved as [old Hlookup].
        destruct (V.eq_dec (R.frame_owner fr) target) as [-> |Hneq].
        + exists value. unfold dirty_commit_value, R.semantic_lookup. cbn.
          now rewrite ML.lookup_update_same.
        + exists old. unfold dirty_commit_value, R.semantic_lookup in *. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      - exists reads, effects. split; [exact Hcontext |]. split.
        + now apply guarded_reads_dirty_commit_value.
        + split; [|exact Hframe].
          unfold recorded_effects, dirty_commit_value in *. exact Heffects.
    Qed.

    Lemma completed_witness_write_dirty_value :
      forall tf st target value fr direct,
        completed_witness tf st fr direct ->
        completed_witness tf (R.write_dirty_value st target value) fr direct.
    Proof.
      intros tf st target value fr direct
        [Hsolved [reads [effects [Htrace [Hreads [Heffects Hframe]]]]]].
      rewrite write_dirty_value_is_dirty_commit_value. split.
      - destruct Hsolved as [old Hlookup].
        destruct (V.eq_dec (R.frame_owner fr) target) as [-> |Hneq].
        + exists value. unfold dirty_commit_value, R.semantic_lookup. cbn.
          now rewrite ML.lookup_update_same.
        + exists old. unfold dirty_commit_value, R.semantic_lookup in *. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      - exists reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_dirty_commit_value.
        + split; [|exact Hframe].
          unfold recorded_effects, dirty_commit_value in *. exact Heffects.
    Qed.

    Lemma summary_valid_write_dirty_value_other :
      forall tf st target value owner,
        owner <> target -> summary_valid tf st owner ->
        summary_valid tf (R.write_dirty_value st target value) owner.
    Proof.
      intros tf st target value owner Hneq
        [Hsolved [direct [reads [effects
          [Htrace [Hreads [Heffects Hdirect]]]]]]].
      rewrite write_dirty_value_is_dirty_commit_value. split.
      - destruct Hsolved as [old Hlookup]. exists old.
        unfold dirty_commit_value, R.semantic_lookup in *. cbn.
        rewrite ML.lookup_update_other by exact Hneq. exact Hlookup.
      - exists direct, reads, effects. split; [exact Htrace |]. split.
        + now apply guarded_reads_dirty_commit_value.
        + split.
          * unfold recorded_effects, dirty_commit_value in *. exact Heffects.
          * unfold dirty_commit_value, R.sigma_value in *. cbn.
            rewrite ML.lookup_update_other by exact Hneq. exact Hdirect.
    Qed.

    Lemma try_dirty_read_ret :
      forall tf st owner target next,
        R.try_dirty_read tf st owner target = Some next ->
        exists direct, tf target = R.ConstraintSystem.Ret direct.
    Proof.
      intros tf st owner target next Hread. unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; eauto.
    Qed.

    Lemma solved_try_dirty_read :
      forall tf st owner target next x,
        R.try_dirty_read tf st owner target = Some next ->
        Sem.solved st x -> Sem.solved next x.
    Proof.
      intros tf st owner target next x Hread Hsolved.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn in *.
      all: try (now apply solved_cancel_dirty_target).
      all: rewrite write_dirty_value_is_dirty_commit_value.
      all: destruct Hsolved as [old Hlookup].
      all: destruct (V.eq_dec x target) as [-> |Hneq].
      all: try (eexists; unfold dirty_commit_value, R.semantic_lookup; cbn;
        now rewrite ML.lookup_update_same).
      all: exists old; unfold dirty_commit_value, R.semantic_lookup in *; cbn;
        rewrite ML.lookup_update_other by exact Hneq; exact Hlookup.
    Qed.

    Lemma direct_below_try_dirty_read_target :
      forall tf st owner target next direct,
        tf target = R.ConstraintSystem.Ret direct ->
        R.try_dirty_read tf st owner target = Some next ->
        D.leq direct (R.sigma_value next target) = true.
    Proof.
      intros tf st owner target next direct Htf Hread.
      unfold R.try_dirty_read in Hread. rewrite Htf in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn in *;
        unfold R.cancel_dirty_target, R.clear_side_dirty,
          R.with_dirty_side_targets, R.with_queue,
          R.write_dirty_value, R.sigma_value in *; cbn in *;
        repeat rewrite ML.lookup_update_same.
      all: match goal with
      | Heq : R.equivalent ?candidate ?old = true |- _ =>
          apply Bool.andb_true_iff in Heq;
          eapply DL.leq_trans; [apply DL.join_upper_left |exact (proj1 Heq)]
      | Hstutter : R.equivalent
            (snd (U.update false ?variable ?phase ?old ?candidate)) ?old = true
          |- _ =>
          pose proof (OSL.update_sound variable phase old candidate) as Hsound;
          apply Bool.andb_true_iff in Hstutter;
          eapply DL.leq_trans; [apply DL.join_upper_left |];
          eapply DL.leq_trans; [exact Hsound |exact (proj1 Hstutter)]
      | |- D.leq _ (snd (U.update false ?variable ?phase ?old ?candidate)) = true =>
          pose proof (OSL.update_sound variable phase old candidate) as Hsound;
          eapply DL.leq_trans; [apply DL.join_upper_left |exact Hsound]
      | |- D.leq _ (D.join _ _) = true => apply DL.join_upper_left
      end.
    Qed.

    Lemma summary_valid_try_dirty_read_target :
      forall tf st owner target next,
        R.try_dirty_read tf st owner target = Some next ->
        Sem.solved st target ->
        summary_valid tf next target.
    Proof.
      intros tf st owner target next Hread Hsolved.
      destruct (@try_dirty_read_ret tf st owner target next Hread)
        as [direct Htf]. split.
      - unfold R.try_dirty_read in Hread. rewrite Htf in Hread.
        repeat match type of Hread with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
        end; try discriminate; inversion Hread; subst; cbn in *.
        all: try (now apply solved_cancel_dirty_target).
        all: rewrite write_dirty_value_is_dirty_commit_value.
        all: destruct Hsolved as [old Hlookup].
        all: unfold Sem.solved, Sem.StateSpec.solved; eexists;
          unfold dirty_commit_value, R.semantic_lookup; cbn;
          now rewrite ML.lookup_update_same.
      - exists direct, [], []. split.
        + rewrite Htf. constructor.
        + split.
          * intros observed seen Hin. contradiction.
          * split.
            -- intros observed emitted Hin. contradiction.
            -- eapply direct_below_try_dirty_read_target; eauto.
    Qed.

    Lemma evaluation_witness_try_dirty_read :
      forall tf st owner target next fr current,
        R.try_dirty_read tf st owner target = Some next ->
        evaluation_witness tf st fr current ->
        evaluation_witness tf next fr current.
    Proof.
      intros tf st owner target next fr current Hread Hwitness.
      destruct (V.eq_dec (R.frame_owner fr) target) as [Heq |Hneq].
      - subst target.
        destruct (@try_dirty_read_ret tf st owner (R.frame_owner fr) next Hread)
          as [direct Htf].
        destruct Hwitness as [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]].
        rewrite Htf in Hcontext. inversion Hcontext; subst.
        split.
        + exact (proj1 (@summary_valid_try_dirty_read_target
            tf st owner (R.frame_owner fr) next Hread Hsolved)).
        + exists [], []. split.
          * rewrite Htf. constructor.
          * split.
            -- intros observed seen Hin. contradiction.
            -- split.
               ++ intros observed emitted Hin. contradiction.
               ++ intros observed emitted Hin. contradiction.
      - unfold R.try_dirty_read in Hread.
        repeat match type of Hread with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
        end; try discriminate; inversion Hread; subst; cbn in *.
        all: try (now apply evaluation_witness_cancel_dirty_target_other).
        all: apply evaluation_witness_write_dirty_value.
        all: now apply evaluation_witness_cancel_dirty_target_other.
    Qed.

    Lemma completed_witness_try_dirty_read :
      forall tf st owner target next fr direct,
        R.try_dirty_read tf st owner target = Some next ->
        completed_witness tf st fr direct ->
        completed_witness tf next fr direct.
    Proof.
      intros tf st owner target next fr direct Hread Hwitness.
      destruct (V.eq_dec (R.frame_owner fr) target) as [Heq |Hneq].
      - subst target.
        destruct (@try_dirty_read_ret tf st owner (R.frame_owner fr) next Hread)
          as [result Htf].
        destruct Hwitness as [Hsolved [reads [effects
          [Htrace [Hreads [Heffects Hframe]]]]]].
        rewrite Htf in Htrace. inversion Htrace; subst.
        split; [exact (proj1 (@summary_valid_try_dirty_read_target
          tf st owner (R.frame_owner fr) next Hread Hsolved)) |].
        exists [], []. split; [rewrite Htf; constructor |]. split.
        + intros observed seen Hin. contradiction.
        + split.
          * intros observed emitted Hin. contradiction.
          * intros observed emitted Hin. contradiction.
      - unfold R.try_dirty_read in Hread.
        repeat match type of Hread with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
        end; try discriminate; inversion Hread; subst; cbn in *.
        all: try (now apply completed_witness_cancel_dirty_target_other).
        all: apply completed_witness_write_dirty_value.
        all: now apply completed_witness_cancel_dirty_target_other.
    Qed.

    Lemma evaluation_witness_add_get_reader :
      forall tf st fr target next,
        Sem.solved st target ->
        evaluation_witness tf st fr (R.ConstraintSystem.Get target next) ->
        evaluation_witness tf
          (R.add_reader st target (R.frame_owner fr)) fr
          (next (R.sigma_value
            (R.add_reader st target (R.frame_owner fr)) target)).
    Proof.
      intros tf st fr target next Htarget
        [Howner [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]].
      split; [now apply solved_add_reader |].
      exists (reads ++ [(target, R.sigma_value
        (R.add_reader st target (R.frame_owner fr)) target)]), effects.
      split; [eapply rhs_context_get; exact Hcontext |]. split.
      - intros observed seen Hin. apply List.in_app_or in Hin.
        destruct Hin as [Hold |Hnew].
        + eapply guarded_reads_add_reader; eauto.
        + cbn in Hnew. destruct Hnew as [Heq |Hfalse];
            [inversion Heq; subst |contradiction]. split.
          * now apply solved_add_reader.
          * split.
            -- left. unfold R.add_reader, R.lookup_set. cbn.
               rewrite ML.lookup_update_same. apply SL.add_spec. now left.
            -- now left.
      - split; [exact Heffects |exact Hframe].
    Qed.

    Lemma evaluation_witness_with_frame_read :
      forall tf st fr minimum maximum current,
        evaluation_witness tf st fr current ->
        evaluation_witness tf st (R.with_frame_read fr minimum maximum) current.
    Proof.
      intros tf st fr minimum maximum current
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]].
      split; [exact Hsolved |]. exists reads, effects.
      split; [exact Hcontext |]. split; [exact Hreads |]. split.
      - exact Heffects.
      - unfold frame_effects, R.with_frame_read in *. cbn. exact Hframe.
    Qed.

    Lemma continuation_history_try_dirty_read :
      forall tf st owner target next k,
        R.try_dirty_read tf st owner target = Some next ->
        continuation_history tf st k -> continuation_history tf next k.
    Proof.
      intros tf st owner target next k Hread.
      induction k; cbn; intros Hhistory; try exact I;
        destruct Hhistory as [Hhead Htail]; split.
      all: try (eapply evaluation_witness_try_dirty_read; eauto).
      all: try (eapply completed_witness_try_dirty_read; eauto).
      all: try (now apply IHk).
      destruct (V.eq_dec (R.frame_owner f) target) as [Heq |Hneq].
      - subst target. eapply summary_valid_try_dirty_read_target;
          [exact Hread |exact (proj1 Hhead)].
      - unfold R.try_dirty_read in Hread.
        repeat match type of Hread with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
        end; try discriminate; inversion Hread; subst; cbn in *.
        all: try (now apply summary_valid_cancel_dirty_target_other).
        all: apply summary_valid_write_dirty_value_other; [exact Hneq |].
        all: now apply summary_valid_cancel_dirty_target_other.
    Qed.

    Lemma continuation_history_dirty_complete_get :
      forall tf st fr target st' fr' value k,
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        continuation_history tf st k -> continuation_history tf st' k.
    Proof.
      intros tf st fr target st' fr' value k Hget Hhistory.
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase : continuation_history tf base k).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
        - exact Hhistory.
        - eapply continuation_history_same_solver_view;
            [apply promote_controlled_same_solver_view |exact Hhistory]. }
      assert (Hprepared : continuation_history tf prepared k).
      { subst prepared. now apply continuation_history_materialize. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst; cbn.
      - apply continuation_history_add_reader.
        eapply continuation_history_try_dirty_read; eauto.
      - now apply continuation_history_add_reader.
    Qed.

    Lemma evaluation_witness_dirty_complete_get :
      forall tf st fr target next st' fr' value,
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        evaluation_witness tf st fr (R.ConstraintSystem.Get target next) ->
        evaluation_witness tf st' fr' (next value).
    Proof.
      intros tf st fr target next st' fr' value Hget Hwitness.
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase : evaluation_witness tf base fr
        (R.ConstraintSystem.Get target next)).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
        - exact Hwitness.
        - eapply evaluation_witness_same_solver_view;
            [apply promote_controlled_same_solver_view |exact Hwitness]. }
      assert (Hprepared : evaluation_witness tf prepared fr
        (R.ConstraintSystem.Get target next)).
      { subst prepared. now apply evaluation_witness_materialize. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst; cbn.
      - eapply (@evaluation_witness_add_get_reader tf flushed
          (R.with_frame_read fr
            (if R.rank_lt st target (R.frame_min_scope fr)
             then target else R.frame_min_scope fr)
            (match R.frame_max_read fr with
             | None => Some target
             | Some previous =>
                 if R.rank_lt st previous target
                 then Some target else Some previous
             end)) target next).
        + eapply solved_try_dirty_read; [exact Hflush |].
          subst prepared. apply materialize_solved_correctness.
        + apply evaluation_witness_with_frame_read.
          eapply evaluation_witness_try_dirty_read; eauto.
      - eapply (@evaluation_witness_add_get_reader tf prepared
          (R.with_frame_read fr
            (if R.rank_lt st target (R.frame_min_scope fr)
             then target else R.frame_min_scope fr)
            (match R.frame_max_read fr with
             | None => Some target
             | Some previous =>
                 if R.rank_lt st previous target
                 then Some target else Some previous
             end)) target next).
        + subst prepared. apply materialize_solved_correctness.
        + now apply evaluation_witness_with_frame_read.
    Qed.

    Lemma queued_write_dirty_value :
      forall st target value x,
        queued st x -> queued (R.write_dirty_value st target value) x.
    Proof.
      intros st target value x Hqueued.
      rewrite write_dirty_value_is_dirty_commit_value.
      now apply queued_dirty_commit_value.
    Qed.

    Lemma queued_try_dirty_read_other :
      forall tf st owner target next x,
        x <> target ->
        R.try_dirty_read tf st owner target = Some next ->
        queued st x -> queued next x.
    Proof.
      intros tf st owner target next x Hneq Hread Hqueued.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn in *.
      all: try (now apply queued_cancel_dirty_target_other).
      all: apply queued_write_dirty_value.
      all: apply queued_cancel_dirty_target_other; [exact Hneq | exact Hqueued].
    Qed.

    Lemma aggregate_cancel_dirty_target :
      forall st target observed,
        R.aggregate (R.cancel_dirty_target st target) observed =
        R.aggregate st observed.
    Proof. reflexivity. Qed.

    Lemma aggregate_write_dirty_value :
      forall st target value observed,
        R.aggregate (R.write_dirty_value st target value) observed =
        R.aggregate st observed.
    Proof. reflexivity. Qed.

    Lemma sigma_value_cancel_dirty_target :
      forall st target observed,
        R.sigma_value (R.cancel_dirty_target st target) observed =
        R.sigma_value st observed.
    Proof. reflexivity. Qed.

    Lemma sigma_value_write_dirty_value_other :
      forall st target value observed,
        observed <> target ->
        R.sigma_value (R.write_dirty_value st target value) observed =
        R.sigma_value st observed.
    Proof.
      intros st target value observed Hneq.
      unfold R.write_dirty_value, R.sigma_value. cbn.
      now rewrite ML.lookup_update_other by exact Hneq.
    Qed.

    Lemma aggregate_try_dirty_read :
      forall tf st owner target next observed,
        R.try_dirty_read tf st owner target = Some next ->
        R.aggregate next observed = R.aggregate st observed.
    Proof.
      intros tf st owner target next observed Hread.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn;
        repeat rewrite aggregate_write_dirty_value;
        repeat rewrite aggregate_cancel_dirty_target; reflexivity.
    Qed.

    Lemma sigma_value_try_dirty_read_other :
      forall tf st owner target next observed,
        observed <> target ->
        R.try_dirty_read tf st owner target = Some next ->
        R.sigma_value next observed = R.sigma_value st observed.
    Proof.
      intros tf st owner target next observed Hneq Hread.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn;
        repeat rewrite sigma_value_write_dirty_value_other by exact Hneq;
        repeat rewrite sigma_value_cancel_dirty_target; reflexivity.
    Qed.

    Lemma aggregate_bounded_try_dirty_read_target :
      forall tf st owner target next,
        R.try_dirty_read tf st owner target = Some next ->
        D.leq (R.aggregate next target) (R.sigma_value next target) = true.
    Proof.
      intros tf st owner target next Hread.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn in *;
        repeat rewrite aggregate_write_dirty_value;
        repeat rewrite aggregate_cancel_dirty_target;
        unfold R.write_dirty_value, R.sigma_value; cbn;
        repeat rewrite ML.lookup_update_same;
        repeat rewrite sigma_value_cancel_dirty_target.
      all: match goal with
      | Heq : R.equivalent ?candidate ?old = true |- _ =>
          apply Bool.andb_true_iff in Heq;
          eapply DL.leq_trans; [apply DL.join_upper_right |exact (proj1 Heq)]
      | Hstutter : R.equivalent
            (snd (U.update false ?variable ?phase ?old ?candidate)) ?old = true
          |- _ =>
          pose proof (OSL.update_sound variable phase old candidate) as Hsound;
          apply Bool.andb_true_iff in Hstutter;
          eapply DL.leq_trans; [apply DL.join_upper_right |];
          eapply DL.leq_trans; [exact Hsound |exact (proj1 Hstutter)]
      | |- D.leq _ (snd (U.update false ?variable ?phase ?old ?candidate)) = true =>
          pose proof (OSL.update_sound variable phase old candidate) as Hsound;
          eapply DL.leq_trans; [apply DL.join_upper_right |exact Hsound]
      | |- D.leq _ (D.join _ _) = true => apply DL.join_upper_right
      end.
    Qed.

    Lemma solved_write_dirty_value_origin :
      forall st target value x,
        Sem.solved (R.write_dirty_value st target value) x ->
        x = target \/ Sem.solved st x.
    Proof.
      intros st target value x [observed Hlookup].
      unfold R.write_dirty_value, R.semantic_lookup in Hlookup. cbn in Hlookup.
      destruct (V.eq_dec x target) as [-> |Hneq]; [now left |right].
      exists observed. rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      exact Hlookup.
    Qed.

    Lemma solved_try_dirty_read_origin :
      forall tf st owner target next x,
        R.try_dirty_read tf st owner target = Some next ->
        Sem.solved next x -> x = target \/ Sem.solved st x.
    Proof.
      intros tf st owner target next x Hread Hsolved.
      unfold R.try_dirty_read in Hread.
      repeat match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end; try discriminate; inversion Hread; subst; cbn in *.
      all: try (right; exact Hsolved).
      all: apply solved_write_dirty_value_origin in Hsolved.
      all: destruct Hsolved as [-> |Hsolved]; [now left |right; exact Hsolved].
    Qed.

    Local Opaque R.dirty_complete_get R.try_dirty_read.

    Lemma rank_lt_true_neq_correctness :
      forall st x y, R.rank_lt st x y = true -> x <> y.
    Proof.
      intros st x y Hlt Heq. subst.
      unfold R.rank_lt, R.ranking_lt in Hlt.
      destruct (R.Ranking.lookup (R.ranking st) y); try discriminate.
      now rewrite Nat.ltb_irrefl in Hlt.
    Qed.

    Lemma set_value_frame_owner :
      forall st fr direct st' fr',
        R.set_value st fr direct = (st', fr') ->
        R.frame_owner fr' = R.frame_owner fr.
    Proof.
      intros st fr direct st' fr' Hset. unfold R.set_value in Hset.
      destruct (R.equivalent
        (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr))).
      - inversion Hset. reflexivity.
      - destruct (S.mem (R.frame_owner fr) (R.controlled st)).
        + destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr))))
            as [next_phase value]. cbn in Hset.
          destruct (R.equivalent value
            (R.sigma_value st (R.frame_owner fr)));
            inversion Hset; reflexivity.
        + cbn in Hset.
          destruct (R.equivalent
            (D.join direct (R.aggregate st (R.frame_owner fr)))
            (R.sigma_value st (R.frame_owner fr)));
            inversion Hset; reflexivity.
    Qed.

    Lemma continuation_below_raise_correctness :
      forall st lower upper k,
        R.rank_lt st lower upper = true ->
        Termination.continuation_below st lower k ->
        Termination.continuation_below st upper k.
    Proof.
      intros st lower upper k Hlt Hbelow.
      destruct k; cbn in *; try exact I;
        destruct Hbelow as [Htop Hrest]; split.
      all: try (eapply Termination.rank_lt_trans_true; eauto).
      all: exact Hrest.
    Qed.

    Lemma continuation_history_set_value :
      forall tf st fr direct st' fr' k,
        R.set_value st fr direct = (st', fr') ->
        Termination.continuation_below st (R.frame_owner fr) k ->
        continuation_history tf st k -> continuation_history tf st' k.
    Proof.
      intros tf st fr direct st' fr' k Hset.
      induction k; intros Hbelow Hhistory; cbn in *; try exact I.
      all: destruct Hbelow as [Hlt Hbelow].
      all: destruct Hhistory as [Hhead Hhistory].
      all: split.
      all: try match goal with
      | |- evaluation_witness _ _ _ _ =>
          eapply evaluation_witness_set_value; [exact Hset |exact Hhead]
      | |- completed_witness _ _ _ _ =>
          eapply completed_witness_set_value; [exact Hset |exact Hhead]
      | |- summary_valid _ _ _ =>
          eapply summary_valid_set_value_other;
            [exact Hset |exact (@rank_lt_true_neq_correctness st _ _ Hlt)
            |exact Hhead]
      end.
      all: eapply IHk;
        [eapply continuation_below_raise_correctness; eauto |exact Hhistory].
    Qed.

    Lemma continuation_history_write_side :
      forall tf st fr target input st' changed k,
        R.write_side_contribution st fr target input = (st', changed) ->
        Termination.continuation_below st (R.frame_owner fr) k ->
        continuation_history tf st k -> continuation_history tf st' k.
    Proof.
      intros tf st fr target input st' changed k Hwrite.
      induction k; intros Hbelow Hhistory; cbn in *; try exact I.
      all: destruct Hbelow as [Hlt Hbelow].
      all: destruct Hhistory as [Hhead Hhistory].
      all: split.
      all: try match goal with
      | |- evaluation_witness _ _ _ _ =>
          eapply evaluation_witness_write_other_source;
            [exact Hwrite |exact (@rank_lt_true_neq_correctness st _ _ Hlt)
            |exact Hhead]
      | |- completed_witness _ _ _ _ =>
          eapply completed_witness_write_other_source;
            [exact Hwrite |exact (@rank_lt_true_neq_correctness st _ _ Hlt)
            |exact Hhead]
      | |- summary_valid _ _ _ =>
          eapply summary_valid_write_other_source;
            [exact Hwrite |exact (@rank_lt_true_neq_correctness st _ _ Hlt)
            |exact Hhead]
      end.
      all: eapply IHk;
        [eapply continuation_below_raise_correctness; eauto |exact Hhistory].
    Qed.

    Lemma continuation_history_pop_above :
      forall tf st popped rest upper k,
        R.queue_pop (R.queue st) = Some (popped, rest) ->
        Termination.continuation_below st upper k ->
        (popped = upper \/ R.rank_lt st upper popped = true) ->
        continuation_history tf st k ->
        continuation_history tf (R.with_queue st rest) k.
    Proof.
      intros tf st popped rest upper k Hpop.
      induction k; intros Hbelow Habove Hhistory; cbn in *; try exact I.
      all: destruct Hbelow as [Hlt Hbelow].
      all: destruct Hhistory as [Hhead Hhistory].
      all: assert (Hneq : R.frame_owner f <> popped).
      all: try (apply (@rank_lt_true_neq_correctness st);
        destruct Habove as [-> | Habove];
        [exact Hlt |eapply Termination.rank_lt_trans_true; eauto]).
      all: split.
      all: try match goal with
      | |- evaluation_witness _ _ _ _ =>
          eapply evaluation_witness_pop_other;
            [exact Hpop |exact Hneq |exact Hhead]
      | |- completed_witness _ _ _ _ =>
          eapply completed_witness_pop_other;
            [exact Hpop |exact Hneq |exact Hhead]
      | |- summary_valid _ _ _ =>
          eapply summary_valid_pop_other;
            [exact Hpop |exact Hneq |exact Hhead]
      end.
      all: eapply IHk;
        [eapply continuation_below_raise_correctness; eauto
        |exact Habove |exact Hhistory].
    Qed.

    Lemma observed_continuation_below :
      forall st target fr k,
        frame_ranked st fr ->
        continuation_ranked st k ->
        Termination.continuation_below st (R.frame_owner fr) k ->
        Termination.continuation_below (R.observe st target)
          (R.frame_owner fr) k.
    Proof.
      intros st target fr k Hfr Hk Hbelow.
      eapply Termination.continuation_below_extended.
      - exact (@rank_extends_observe st target (R.observe st target) eq_refl).
      - exact (proj1 Hfr).
      - exact Hk.
      - exact Hbelow.
    Qed.

    Definition step_spawned (before : R.config) : Prop :=
      match R.cfg_control before with
      | R.RunRhs _ (R.ConstraintSystem.Spawn target _) _ => spawned target
      | _ => True
      end.

    Definition spawned_path tf first final : Prop :=
      forall before after, Sem.steps tf first before ->
        R.next_config tf before = Some after -> Sem.steps tf after final ->
        step_spawned before.

    Lemma next_config_control_history :
      forall tf before after,
        step_spawned before ->
        configuration_ranked before ->
        Termination.control_ordered (R.cfg_state before)
          (R.cfg_control before) ->
        control_history tf (R.cfg_state before) (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        control_history tf (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf [st control] after Hspawn Hranked Hordered Hhistory Hstep.
      pose proof (configuration_control_ranked Hranked) as Hcontrol_ranked.
      destruct control; cbn in Hspawn, Hordered, Hhistory, Hcontrol_ranked, Hstep.
      - destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
          try discriminate. inversion Hstep; subst. exact I.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. exact I.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. exact I.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. exact I.
            -- destruct (R.pure_bottom_rhs tf root);
                 inversion Hstep; subst; exact I.
      - destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
          inversion Hstep; subst; exact I.
      - inversion Hstep; subst. cbn. split.
        + apply initial_evaluation_witness.
          apply materialize_solved_correctness.
        + apply continuation_history_clear_side_dirty.
          now apply continuation_history_materialize.
      - destruct Hcontrol_ranked as [Hframe_ranked Hcontinuation_ranked].
        destruct Hhistory as [Hcurrent Hcontinuation].
        destruct r; cbn in Hspawn; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. cbn. split.
          * now apply evaluation_ret_completed.
          * exact Hcontinuation.
        + destruct (R.is_dormant st t) eqn:Hdormant.
          * inversion Hstep; subst. cbn. split.
            -- now apply evaluation_witness_get_dormant.
            -- now apply continuation_history_add_reader.
          * destruct (R.Ranking.lookup (R.ranking st) t) eqn:Hrank.
            -- set (observed := R.observe st t) in *.
               assert (Hcurrent0 : evaluation_witness tf observed f
                 (R.ConstraintSystem.Get t r)).
               { subst observed. now apply evaluation_witness_observe. }
               assert (Hcontinuation0 : continuation_history tf observed c).
               { subst observed. now apply continuation_history_observe. }
               destruct (R.is_materialized observed t) eqn:Hmaterialized.
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst. cbn. split.
                  ** eapply evaluation_witness_dirty_complete_get; eauto.
                  ** eapply continuation_history_dirty_complete_get; eauto.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. cbn. split; assumption.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. cbn. split.
                     --- eapply evaluation_witness_complete_get; [exact Hget |].
                         now apply evaluation_witness_enqueue.
                     --- eapply continuation_history_complete_get;
                           [exact Hget |].
                         now apply continuation_history_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool eqn:Hpure.
               ++ inversion Hstep; subst. cbn. split.
                  ** apply evaluation_witness_get_remembered;
                       [|exact Hcurrent].
                     unfold R.is_dormant, R.remember_dormant,
                       R.with_dormant_bottom. cbn.
                     apply Bool.andb_true_iff in Hpure as [_ Hmaterialized].
                     unfold R.is_materialized in Hmaterialized.
                     destruct (M.lookup (R.sigma st) t) eqn:Hsigma;
                       [discriminate |].
                     assert (S.mem t (S.add t (R.dormant_bottom st)) = true)
                       as Hmember.
                     { apply SL.add_spec. now left. }
                     rewrite Hmember, Hrank. reflexivity.
                  ** apply continuation_history_add_reader,
                       continuation_history_remember_dormant.
                     exact Hcontinuation.
               ++ set (observed := R.observe st t) in *.
                  assert (Hcurrent0 : evaluation_witness tf observed f
                    (R.ConstraintSystem.Get t r)).
                  { subst observed. now apply evaluation_witness_observe. }
                  assert (Hcontinuation0 : continuation_history tf observed c).
                  { subst observed. now apply continuation_history_observe. }
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. cbn. split; assumption.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. cbn. split.
                     --- eapply evaluation_witness_complete_get;
                           [exact Hget |].
                         unfold st0. destruct (R.is_materialized observed t);
                           [exact Hcurrent0
                           |now apply evaluation_witness_enqueue].
                     --- eapply continuation_history_complete_get;
                           [exact Hget |].
                         unfold st0. destruct (R.is_materialized observed t);
                           [exact Hcontinuation0
                           |now apply continuation_history_enqueue].
        + set (observed := R.observe st t) in *.
          assert (Hcurrent0 : evaluation_witness tf observed f
            (R.ConstraintSystem.Side t t0 r)).
          { subst observed. now apply evaluation_witness_observe. }
          assert (Hcontinuation0 : continuation_history tf observed c).
          { subst observed. now apply continuation_history_observe. }
          assert (Hordered0 : Termination.continuation_below observed
            (R.frame_owner f) c).
          { subst observed. eapply observed_continuation_below; eauto. }
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0)
              as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            change (control_history tf
              (R.cfg_state (R.continue_side st1 fr1 t r c true))
              (R.cfg_control (R.continue_side st1 fr1 t r c true))).
            apply control_history_continue_side.
            -- eapply evaluation_witness_side; eauto.
            -- eapply continuation_history_write_side;
                 [exact Hwrite | |exact Hcontinuation0].
               rewrite (record_side_input_owner Hrecord). exact Hordered0.
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, changed) :=
                 R.write_side_contribution observed fr1 t input in
               if changed then
                 Some (R.continue_side (R.mark_side_dirty st1 t)
                   fr1 t r c true)
               else Some (R.continue_side st1 fr1 t r c false)) =
              Some after) in Hstep.
            destruct (R.record_side_input f t t0)
              as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            assert (Hcurrent1 : evaluation_witness tf st1 fr1 r).
            { eapply evaluation_witness_side; eauto. }
            assert (Hcontinuation1 : continuation_history tf st1 c).
            { eapply continuation_history_write_side;
                [exact Hwrite | |exact Hcontinuation0].
              rewrite (record_side_input_owner Hrecord). exact Hordered0. }
            destruct changed; inversion Hstep; subst.
            -- change (control_history tf
                 (R.cfg_state (R.continue_side
                   (R.mark_side_dirty st1 t) fr1 t r c true))
                 (R.cfg_control (R.continue_side
                   (R.mark_side_dirty st1 t) fr1 t r c true))).
               apply control_history_continue_side.
               ++ eapply evaluation_witness_same_solver_view;
                    [apply mark_side_dirty_same_solver_view |exact Hcurrent1].
               ++ eapply continuation_history_same_solver_view;
                    [apply mark_side_dirty_same_solver_view
                    |exact Hcontinuation1].
            -- change (control_history tf
                 (R.cfg_state (R.continue_side st1 fr1 t r c false))
                 (R.cfg_control (R.continue_side st1 fr1 t r c false))).
               now apply control_history_continue_side.
        + destruct (R.is_dormant st t) eqn:Hdormant.
          * inversion Hstep; subst. cbn. split.
            -- now apply evaluation_witness_spawn in Hcurrent.
            -- exact Hcontinuation.
          * destruct (R.Ranking.lookup (R.ranking st) t) eqn:Hrank.
            -- set (observed := R.observe st t) in *.
               assert (Hcurrent0 : evaluation_witness tf observed f
                 (R.ConstraintSystem.Spawn t r)).
               { subst observed. now apply evaluation_witness_observe. }
               assert (Hcontinuation0 : continuation_history tf observed c).
               { subst observed. now apply continuation_history_observe. }
               pose proof (evaluation_witness_spawn Hspawn Hcurrent0) as Hnext.
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. cbn. split; assumption.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. cbn. split; assumption.
                  ** inversion Hstep; subst. cbn. split.
                     --- apply evaluation_witness_materialize.
                         now apply evaluation_witness_enqueue.
                     --- apply continuation_history_materialize.
                         now apply continuation_history_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool eqn:Hpure.
               ++ inversion Hstep; subst. cbn. split.
                  ** apply evaluation_witness_remember_dormant.
                     now apply evaluation_witness_spawn in Hcurrent.
                  ** now apply continuation_history_remember_dormant.
               ++ set (observed := R.observe st t) in *.
                  assert (Hcurrent0 : evaluation_witness tf observed f
                    (R.ConstraintSystem.Spawn t r)).
                  { subst observed. now apply evaluation_witness_observe. }
                  assert (Hcontinuation0 :
                    continuation_history tf observed c).
                  { subst observed. now apply continuation_history_observe. }
                  pose proof (evaluation_witness_spawn Hspawn Hcurrent0) as Hnext.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. cbn. split; assumption.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. cbn. split; assumption.
                     --- inversion Hstep; subst. cbn. split.
                         +++ apply evaluation_witness_materialize.
                             now apply evaluation_witness_enqueue.
                         +++ apply continuation_history_materialize.
                             now apply continuation_history_enqueue.
      - destruct Hcontrol_ranked as [Hframe_ranked
          [Hpending_ranked Hcontinuation_ranked]].
        destruct Hhistory as [Hcurrent Hcontinuation].
        destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. cbn. split.
          * eapply completed_witness_same_solver_view;
              [apply publish_targets_same_solver_view |exact Hcurrent].
          * eapply continuation_history_same_solver_view;
              [apply publish_targets_same_solver_view |exact Hcontinuation].
        + destruct (S.mem target (R.frame_current_targets f)) eqn:Hmem.
          * inversion Hstep; subst. cbn. split; assumption.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) = Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            assert (Hcurrent1 : completed_witness tf st1 f t).
            { eapply completed_witness_dead_side; eauto. }
            assert (Hcontinuation1 : continuation_history tf st1 c).
            { eapply continuation_history_write_side; eauto. }
            destruct changed; inversion Hstep; subst.
            -- change (control_history tf
                 (R.cfg_state (R.continue_dead
                   (R.mark_side_dirty st1 target)
                   f t target remaining c true))
                 (R.cfg_control (R.continue_dead
                   (R.mark_side_dirty st1 target)
                   f t target remaining c true))).
               apply control_history_continue_dead.
               ++ eapply completed_witness_same_solver_view;
                    [apply mark_side_dirty_same_solver_view |exact Hcurrent1].
               ++ eapply continuation_history_same_solver_view;
                    [apply mark_side_dirty_same_solver_view
                    |exact Hcontinuation1].
            -- change (control_history tf
                 (R.cfg_state (R.continue_dead st1 f t target remaining c false))
                 (R.cfg_control
                   (R.continue_dead st1 f t target remaining c false))).
               now apply control_history_continue_dead.
      - destruct Hcontrol_ranked as [Hframe_ranked Hcontinuation_ranked].
        destruct Hhistory as [Hcurrent Hcontinuation].
        assert (Hcurrent0 : completed_witness tf (R.flush_deferred st) f t)
          by now apply completed_witness_flush_deferred.
        assert (Hcontinuation0 :
          continuation_history tf (R.flush_deferred st) c)
          by now apply continuation_history_flush_deferred.
        destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. cbn.
        assert (Howner : R.frame_owner fr1 = R.frame_owner f)
          by (eapply set_value_frame_owner; eauto). split.
        + rewrite Howner.
          eapply completed_witness_set_value_summary;
            [exact Hcurrent0 | exact Hset].
        + eapply continuation_history_set_value;
            [exact Hset | | exact Hcontinuation0].
          eapply Termination.continuation_below_extended.
          * apply rank_extends_flush_deferred.
          * exact (proj1 Hframe_ranked).
          * exact Hcontinuation_ranked.
          * exact Hordered.
      - destruct Hcontrol_ranked as [Hframe_ranked Hcontinuation_ranked].
        destruct Hhistory as [Hsummary Hcontinuation].
        destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst.
          eapply continuation_history_same_solver_view;
            [apply reset_registered_cells_same_solver_view
            |exact Hcontinuation].
        + destruct (V.eq_dec next (R.frame_owner f)) as [Heq | Hneq].
          * inversion Hstep; subst. cbn. split.
            -- apply initial_evaluation_witness. exact (proj1 Hsummary).
            -- apply continuation_history_clear_side_dirty.
               eapply continuation_history_pop_above.
               ++ unfold R.queue_pop. rewrite Hqueue. reflexivity.
               ++ exact Hordered.
               ++ left. reflexivity.
               ++ exact Hcontinuation.
          * destruct (R.rank_lt st (R.frame_owner f) next) eqn:Hlt.
            -- inversion Hstep; subst. cbn. split.
               ++ eapply summary_valid_pop_other.
                  ** unfold R.queue_pop. rewrite Hqueue. reflexivity.
                  ** intro Hback. apply Hneq. symmetry. exact Hback.
                  ** exact Hsummary.
               ++ eapply continuation_history_pop_above.
                  ** unfold R.queue_pop. rewrite Hqueue. reflexivity.
                  ** exact Hordered.
                  ** now right.
                  ** exact Hcontinuation.
            -- inversion Hstep; subst.
               eapply continuation_history_same_solver_view;
                 [apply reset_registered_cells_same_solver_view
                 |exact Hcontinuation].
      - destruct c; cbn in Hhistory, Hstep.
        + inversion Hstep; subst. exact I.
        + inversion Hstep; subst. exact I.
        + destruct Hhistory as [Hcurrent Hcontinuation].
          change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. cbn. split.
          * eapply evaluation_witness_complete_get; eauto.
          * eapply continuation_history_complete_get; eauto.
        + inversion Hstep; subst. exact Hhistory.
        + inversion Hstep; subst. exact Hhistory.
        + inversion Hstep; subst. exact Hhistory.
        + inversion Hstep; subst. exact Hhistory.
    Qed.

    Lemma summary_valid_complete_get :
      forall tf st fr target st' fr' value owner,
        R.complete_get st fr target = (st', fr', value) ->
        summary_valid tf st owner -> summary_valid tf st' owner.
    Proof.
      intros tf st fr target st' fr' value owner Hget Hsummary.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (read_state := add_reader base target (R.frame_owner fr)) in *.
      fold add_reader in Hget. inversion Hget; subst.
      apply summary_valid_materialize. subst read_state.
      apply summary_valid_add_reader. subst base.
      destruct (R.rank_lt st (R.frame_owner fr) target).
      - exact Hsummary.
      - eapply summary_valid_same_solver_view;
          [apply promote_controlled_same_solver_view |exact Hsummary].
    Qed.

    Lemma summary_valid_dirty_complete_get_guarded :
      forall tf st fr target st' fr' value owner,
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        summary_valid tf st owner ->
        queued st' owner \/ summary_valid tf st' owner.
    Proof.
      intros tf st fr target st' fr' value owner Hget Hsummary.
      Local Transparent R.dirty_complete_get R.try_dirty_read.
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase : summary_valid tf base owner).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target).
        - exact Hsummary.
        - eapply summary_valid_same_solver_view;
            [apply promote_controlled_same_solver_view |exact Hsummary]. }
      assert (Hprepared : summary_valid tf prepared owner).
      { subst prepared. now apply summary_valid_materialize. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst; right.
      - apply summary_valid_add_reader.
        assert (Hhistory : continuation_history tf prepared
          (R.KDrain (R.fresh_frame prepared owner
            (U.initial_phase false owner)) R.KLoop)).
        { cbn. split; [exact Hprepared |exact I]. }
        pose proof (@continuation_history_try_dirty_read tf prepared
          (R.frame_owner fr) target flushed
          (R.KDrain (R.fresh_frame prepared owner
            (U.initial_phase false owner)) R.KLoop) Hflush Hhistory)
          as Hnext. exact (proj1 Hnext).
      - now apply summary_valid_add_reader.
      Local Opaque R.dirty_complete_get R.try_dirty_read.
    Qed.

    Lemma queued_enqueue :
      forall st inserted x, queued st x -> queued (R.enqueue st inserted) x.
    Proof.
      intros st inserted x [Hqueued | Hdeferred].
      - left. cbn. apply queue_insert_members. now right.
      - right. exact Hdeferred.
    Qed.

    Lemma queued_materialize :
      forall st inserted x,
        queued st x -> queued (R.materialize st inserted) x.
    Proof.
      intros st inserted x Hqueued. unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted); exact Hqueued.
    Qed.

    Lemma queued_observe_preserved :
      forall st observed x,
        queued st x -> queued (R.observe st observed) x.
    Proof. exact queued_observe. Qed.

    Lemma queued_complete_get :
      forall st fr target st' fr' value x,
        R.complete_get st fr target = (st', fr', value) ->
        queued st x -> queued st' x.
    Proof.
      intros st fr target st' fr' value x Hget Hqueued.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      inversion Hget; subst. apply queued_materialize. subst base.
      destruct (R.rank_lt st (R.frame_owner fr) target); exact Hqueued.
    Qed.

    Lemma queued_dirty_complete_get_or_summary :
      forall tf st fr target st' fr' value x,
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        queued st x ->
        queued st' x \/
        (summary_valid tf st' x /\
         D.leq (R.aggregate st' x) (R.sigma_value st' x) = true).
    Proof.
      intros tf st fr target st' fr' value x Hget Hqueued.
      Local Transparent R.dirty_complete_get R.try_dirty_read.
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase_queued : queued base x).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
          exact Hqueued. }
      assert (Hprepared_queued : queued prepared x).
      { subst prepared. now apply queued_materialize. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst.
      - destruct (V.eq_dec x target) as [-> |Hneq].
        + right. split.
          * apply summary_valid_add_reader.
            eapply (@summary_valid_try_dirty_read_target tf prepared
              (R.frame_owner fr) target flushed); [exact Hflush |].
            subst prepared. apply materialize_solved_correctness.
          * pose proof (@aggregate_bounded_try_dirty_read_target tf prepared
              (R.frame_owner fr) target flushed Hflush) as Hbound.
            unfold R.add_reader. cbn. exact Hbound.
        + left. unfold R.add_reader, queued. cbn.
          eapply queued_try_dirty_read_other; eauto.
      - left. unfold R.add_reader, queued. cbn. exact Hprepared_queued.
      Local Opaque R.dirty_complete_get R.try_dirty_read.
    Qed.

    Lemma complete_get_frame_owner :
      forall st fr target st' fr' value,
        R.complete_get st fr target = (st', fr', value) ->
        R.frame_owner fr' = R.frame_owner fr.
    Proof.
      intros st fr target st' fr' value Hget.
      unfold R.complete_get in Hget. inversion Hget. reflexivity.
    Qed.

    Lemma queued_write_side :
      forall st fr target input st' changed x,
        R.write_side_contribution st fr target input = (st', changed) ->
        queued st x -> queued st' x.
    Proof.
      intros st fr target input st' changed x Hwrite Hqueued.
      destruct (write_side_contribution_same_read_view Hwrite)
        as [_ [_ [Hqueue [Hdeferred _]]]].
      unfold queued in *. now rewrite Hqueue, Hdeferred.
    Qed.

    Lemma queued_set_value :
      forall st fr direct st' fr' x,
        R.set_value st fr direct = (st', fr') ->
        queued st x -> queued st' x.
    Proof.
      intros st fr direct st' fr' x Hset Hqueued.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end; inversion Hset; subst; try exact Hqueued.
      all: now apply queued_commit_value.
    Qed.

    Fixpoint continuation_active_correctness
      (x : V.t) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => False
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest =>
          x = R.frame_owner fr \/ continuation_active_correctness x rest
      | R.KDrain _ rest => continuation_active_correctness x rest
      end.

    Definition control_active_correctness
      (x : V.t) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
      | R.StartEpisode owner k =>
          x = owner \/ continuation_active_correctness x k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k =>
          x = R.frame_owner fr \/ continuation_active_correctness x k
      | R.RunDrain _ k => continuation_active_correctness x k
      | R.Return k => continuation_active_correctness x k
      end.

    Lemma continuation_history_active_solved :
      forall tf st k x,
        continuation_history tf st k ->
        continuation_active_correctness x k -> Sem.solved st x.
    Proof.
      intros tf st k. induction k; intros x Hhistory Hactive; cbn in *;
        try contradiction.
      all: destruct Hhistory as [Hhead Hhistory].
      - destruct Hactive as [-> | Hactive];
          [exact (proj1 Hhead) |eapply IHk; eauto].
      - destruct Hactive as [-> | Hactive];
          [exact (proj1 Hhead) |eapply IHk; eauto].
      - destruct Hactive as [-> | Hactive];
          [exact (proj1 Hhead) |eapply IHk; eauto].
      - destruct Hactive as [-> | Hactive];
          [exact (proj1 Hhead) |eapply IHk; eauto].
      - eapply IHk; eauto.
    Qed.

    Definition control_active := control_active_correctness.

    Definition commit_discharge
      (before after : R.config) (x : V.t) : Prop :=
      exists st fr direct k st' fr',
        before =
          {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} /\
        R.set_value (R.flush_deferred st) fr direct = (st', fr') /\
        after =
          {| R.cfg_state := st'; R.cfg_control := R.RunDrain fr' k |} /\
        x = R.frame_owner fr.

    Lemma queued_queue_cons_cases :
      forall st owner rest x,
        R.queue st = owner :: rest -> queued st x ->
        x = owner \/ queued (R.with_queue st rest) x.
    Proof.
      intros st owner rest x Hqueue [Hqueued | Hdeferred].
      - rewrite Hqueue in Hqueued. cbn in Hqueued.
        destruct Hqueued as [Heq | Hqueued].
        + left. symmetry. exact Heq.
        + right. now left.
      - right. now right.
    Qed.

    Lemma queued_step_scheduled :
      forall tf before after x,
        queued (R.cfg_state before) x ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) x \/
        control_active x (R.cfg_control after) \/
        (summary_valid tf (R.cfg_state after) x /\
         D.leq (R.aggregate (R.cfg_state after) x)
           (R.sigma_value (R.cfg_state after) x) = true).
    Proof.
      intros tf [st control] after x Hqueued Hstep.
      destruct control; cbn in Hstep.
      - destruct (R.queue st) as [|owner rest] eqn:Hqueue;
          try discriminate. inversion Hstep; subst.
        destruct (queued_queue_cons_cases Hqueue Hqueued)
          as [-> | Hqueued_after].
        + right. left. cbn. now left.
        + now left.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. now left.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. left.
               now apply queued_observe_preserved.
            -- destruct (R.pure_bottom_rhs tf root).
               ++ inversion Hstep; subst. now left.
               ++ inversion Hstep; subst. left.
                  now apply queued_observe_preserved.
      - destruct (R.queue st) as [|owner rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst.
          destruct (queued_queue_cons_cases Hqueue Hqueued)
            as [-> | Hqueued_after].
          * right. left. cbn. now left.
          * now left.
      - inversion Hstep; subst. left. now apply queued_materialize.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (R.is_dormant st t) eqn:Hdormant.
          * inversion Hstep; subst. now left.
          * destruct (R.Ranking.lookup (R.ranking st) t) eqn:Hrank.
            -- set (observed := R.observe st t) in *.
               assert (Hqueued0 : queued observed x)
                 by (subst observed; now apply queued_observe_preserved).
               destruct (R.is_materialized observed t) eqn:Hmaterialized.
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst.
                  destruct (@queued_dirty_complete_get_or_summary
                    tf observed f t st1 fr1 value x Hget Hqueued0)
                    as [Hqueued1 | Hsummary].
                  ** now left.
                  ** now right; right.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. now left.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. left.
                     eapply queued_complete_get; [exact Hget |].
                     now apply queued_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. now left.
               ++ set (observed := R.observe st t) in *.
                  assert (Hqueued0 : queued observed x)
                    by (subst observed; now apply queued_observe_preserved).
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. now left.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. left.
                     eapply queued_complete_get; [exact Hget |]. unfold st0.
                     destruct (R.is_materialized observed t);
                       [exact Hqueued0 |now apply queued_enqueue].
        + set (observed := R.observe st t) in *.
          assert (Hqueued0 : queued observed x)
            by (subst observed; now apply queued_observe_preserved).
          destruct (R.is_dormant st t) eqn:Hwas.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            assert (Hqueued1 : queued st1 x)
              by (eapply queued_write_side; eauto).
            inversion Hstep; subst. unfold R.continue_side.
            destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool;
              [now left |left; now apply queued_enqueue].
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            assert (Hqueued1 : queued st1 x)
              by (eapply queued_write_side; eauto).
            destruct changed.
            -- inversion Hstep; subst. unfold R.continue_side.
               assert (Hqueued2 : queued (R.mark_side_dirty st1 t) x).
               { eapply queued_same_solver_view;
                   [apply mark_side_dirty_same_solver_view |exact Hqueued1]. }
               destruct (R.rank_lt (R.mark_side_dirty st1 t)
                 (R.frame_owner fr1) t &&
                 negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool;
                 [now left |left; now apply queued_enqueue].
            -- inversion Hstep; subst. now left.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. now left.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               assert (Hqueued0 : queued observed x)
                 by (subst observed; now apply queued_observe_preserved).
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. now left.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. now left.
                  ** inversion Hstep; subst. left. apply queued_materialize.
                     now apply queued_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. now left.
               ++ set (observed := R.observe st t) in *.
                  assert (Hqueued0 : queued observed x)
                    by (subst observed; now apply queued_observe_preserved).
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. now left.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. now left.
                     --- inversion Hstep; subst. left.
                         apply queued_materialize. now apply queued_enqueue.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. now left.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            assert (Hqueued1 : queued st1 x)
              by (eapply queued_write_side; eauto).
            destruct changed.
            -- inversion Hstep; subst. unfold R.continue_dead.
               assert (Hqueued2 : queued (R.mark_side_dirty st1 target) x).
               { eapply queued_same_solver_view;
                   [apply mark_side_dirty_same_solver_view |exact Hqueued1]. }
               destruct (R.rank_lt (R.mark_side_dirty st1 target)
                   (R.frame_owner f) target &&
                 negb (R.is_materialized (R.mark_side_dirty st1 target)
                   target))%bool;
                 [now left |left; now apply queued_enqueue].
            -- inversion Hstep; subst. now left.
      - destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. left. eapply queued_set_value;
          [exact Hset |now apply queued_flush_deferred].
      - destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. left.
          eapply queued_same_solver_view;
            [apply reset_registered_cells_same_solver_view |exact Hqueued].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst.
            destruct (queued_queue_cons_cases Hqueue Hqueued)
              as [Hx | Hqueued_after].
            -- subst x. right. left. cbn. now left.
            -- left. exact Hqueued_after.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst.
               destruct (queued_queue_cons_cases Hqueue Hqueued)
                 as [Hx | Hqueued_after].
               ++ subst x. right. left. cbn. now left.
               ++ now left.
            -- inversion Hstep; subst. left.
               eapply queued_same_solver_view;
                 [apply reset_registered_cells_same_solver_view |exact Hqueued].
      - destruct c; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. left. eapply queued_complete_get; eauto.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
    Qed.

    Lemma active_step_scheduled_or_commit :
      forall tf before after x,
        control_active x (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) x \/
        control_active x (R.cfg_control after) \/
        commit_discharge before after x.
    Proof.
      intros tf [st control] after x Hactive Hstep.
      destruct control; cbn in Hactive, Hstep; try contradiction.
      - inversion Hstep; subst. right. left. exact Hactive.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. right. left. exact Hactive.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. left. exact Hactive.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst. right. left.
                  destruct Hactive as [Howner | Hactive].
                  ** left. rewrite (@dirty_complete_get_owner
                       tf observed f t st1 fr1 value Hget). exact Howner.
                  ** right. exact Hactive.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. right. left. cbn. right.
                     exact Hactive.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. right. left.
                     destruct Hactive as [Howner | Hactive].
                     --- left. rewrite (@complete_get_frame_owner
                          (R.enqueue observed t) f t st1 fr1 value Hget).
                         exact Howner.
                     --- right. exact Hactive.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. left. exact Hactive.
               ++ set (observed := R.observe st t) in *.
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. right. left. cbn. right.
                     exact Hactive.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. right. left.
                     destruct Hactive as [Howner | Hactive].
                     --- left. rewrite (@complete_get_frame_owner
                          st0 f t st1 fr1 value Hget). exact Howner.
                     --- right. exact Hactive.
        + set (observed := R.observe st t) in *.
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Howner : R.frame_owner fr1 = R.frame_owner f)
              by now apply record_side_input_owner in Hrecord.
            unfold R.continue_side.
            destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool.
            -- right. left. cbn. right. rewrite Howner. exact Hactive.
            -- right. left. cbn. rewrite Howner. exact Hactive.
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            assert (Howner : R.frame_owner fr1 = R.frame_owner f)
              by now apply record_side_input_owner in Hrecord.
            destruct changed; inversion Hstep; subst; unfold R.continue_side.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 t)
                 (R.frame_owner fr1) t &&
                 negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool.
               ++ right. left. cbn. right. rewrite Howner. exact Hactive.
               ++ right. left. cbn. rewrite Howner. exact Hactive.
            -- right. left. cbn. rewrite Howner. exact Hactive.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. left. exact Hactive.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. right. left. exact Hactive.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. right. left. cbn. right.
                     exact Hactive.
                  ** inversion Hstep; subst. right. left. exact Hactive.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. left. exact Hactive.
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. right. left. exact Hactive.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. left. cbn. right.
                         exact Hactive.
                     --- inversion Hstep; subst. right. left. exact Hactive.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hactive.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. right. left. exact Hactive.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            destruct changed; inversion Hstep; subst; unfold R.continue_dead.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 target)
                   (R.frame_owner f) target &&
                 negb (R.is_materialized (R.mark_side_dirty st1 target)
                   target))%bool.
               ++ right. left. cbn. right. exact Hactive.
               ++ right. left. cbn. exact Hactive.
            -- right. left. cbn. exact Hactive.
      - destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        destruct Hactive as [Howner | Hactive].
        + inversion Hstep; subst. right. right.
          exists st, f, t, c, st1, fr1.
          repeat split; try reflexivity; assumption.
        + inversion Hstep; subst. right. left. exact Hactive.
      - destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hactive.
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. right. left. cbn. right. exact Hactive.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst. right. left. cbn. right. exact Hactive.
            -- inversion Hstep; subst. right. left. exact Hactive.
      - destruct c; cbn in Hactive, Hstep.
        + contradiction.
        + contradiction.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. right. left.
          destruct Hactive as [Howner | Hactive].
          * left. rewrite (@complete_get_frame_owner
              st f t st1 fr1 value Hget). exact Howner.
          * right. exact Hactive.
        + inversion Hstep; subst. right. left. exact Hactive.
        + inversion Hstep; subst. right. left. exact Hactive.
        + inversion Hstep; subst. right. left. exact Hactive.
        + inversion Hstep; subst. right. left. exact Hactive.
    Qed.

    Definition aggregate_bounded (st : R.state) (target : V.t) : Prop :=
      D.leq (R.aggregate st target) (R.sigma_value st target) = true.

    Lemma aggregate_bounded_same_solver_view :
      forall before after target,
        same_solver_view before after ->
        aggregate_bounded before target -> aggregate_bounded after target.
    Proof.
      intros before after target [[Hsigma _] Hcontributions] Hbounded.
      unfold aggregate_bounded, R.aggregate, R.sigma_value in *.
      now rewrite Hsigma, Hcontributions.
    Qed.

    Lemma aggregate_bounded_enqueue :
      forall st inserted target,
        aggregate_bounded st target ->
        aggregate_bounded (R.enqueue st inserted) target.
    Proof. exact (fun _ _ _ H => H). Qed.

    Lemma aggregate_bounded_observe :
      forall st observed target,
        aggregate_bounded st target ->
        aggregate_bounded (R.observe st observed) target.
    Proof.
      intros st observed target Hbounded. unfold aggregate_bounded in *.
      destruct (observe_solver_view st observed)
        as [Hsigma [_ [_ Hcontributions]]].
      unfold R.aggregate, R.sigma_value. now rewrite Hsigma, Hcontributions.
    Qed.

    Lemma aggregate_bounded_materialize :
      forall st inserted target,
        aggregate_bounded st target ->
        aggregate_bounded (R.materialize st inserted) target.
    Proof.
      intros st inserted target Hbounded.
      unfold aggregate_bounded, R.materialize in *.
      destruct (M.lookup (R.sigma st) inserted) eqn:Hlookup;
        [exact Hbounded |].
      destruct (V.eq_dec target inserted) as [-> | Hneq].
      - unfold R.sigma_value in *. cbn.
        rewrite ML.lookup_update_same, Hlookup in *. exact Hbounded.
      - unfold R.sigma_value in *. cbn.
        rewrite ML.lookup_update_other by exact Hneq. exact Hbounded.
    Qed.

    Lemma aggregate_bounded_complete_get :
      forall st fr target st' fr' value observed,
        R.complete_get st fr target = (st', fr', value) ->
        aggregate_bounded st observed -> aggregate_bounded st' observed.
    Proof.
      intros st fr target st' fr' value observed Hget Hbounded.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      inversion Hget; subst. apply aggregate_bounded_materialize.
      subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
        exact Hbounded.
    Qed.

    Lemma aggregate_bounded_dirty_complete_get :
      forall tf st fr target st' fr' value observed,
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        aggregate_bounded st observed -> aggregate_bounded st' observed.
    Proof.
      intros tf st fr target st' fr' value observed Hget Hbounded.
      Local Transparent R.dirty_complete_get R.try_dirty_read.
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase : aggregate_bounded base observed).
      { subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
          exact Hbounded. }
      assert (Hprepared : aggregate_bounded prepared observed).
      { subst prepared. now apply aggregate_bounded_materialize. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst;
        unfold aggregate_bounded, R.add_reader; cbn.
      - destruct (V.eq_dec observed target) as [-> |Hneq].
        + exact (@aggregate_bounded_try_dirty_read_target tf prepared
            (R.frame_owner fr) target flushed Hflush).
        + unfold aggregate_bounded in Hprepared.
          change (D.leq (R.aggregate flushed observed)
            (R.sigma_value flushed observed) = true).
          rewrite (@aggregate_try_dirty_read tf prepared
            (R.frame_owner fr) target flushed observed Hflush).
          rewrite (@sigma_value_try_dirty_read_other tf prepared
            (R.frame_owner fr) target flushed observed Hneq Hflush).
          exact Hprepared.
      - exact Hprepared.
      Local Opaque R.dirty_complete_get R.try_dirty_read.
    Qed.

    Lemma aggregate_bounded_write_other :
      forall st fr target input st' changed observed,
        R.write_side_contribution st fr target input = (st', changed) ->
        observed <> target ->
        aggregate_bounded st observed -> aggregate_bounded st' observed.
    Proof.
      intros st fr target input st' changed observed Hwrite Hneq Hbounded.
      unfold aggregate_bounded, R.aggregate in *.
      rewrite (write_side_contribution_other Hwrite Hneq).
      destruct (write_side_contribution_same_read_view Hwrite)
        as [Hsigma _]. unfold R.sigma_value in *. now rewrite Hsigma.
    Qed.

    Lemma write_side_unchanged_equivalent :
      forall st fr target input st',
        R.write_side_contribution st fr target input = (st', false) ->
        R.equivalent
          (R.aggregate st' target) (R.aggregate st target) = true.
    Proof.
      intros st fr target input st' Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (R.side_update base (R.frame_owner fr) target input)
        as [phase value]. cbn in Hwrite. inversion Hwrite.
      assert (Hbase : R.aggregate base target = R.aggregate st target).
      { subst base. unfold R.promote_side_target, R.promote_controlled.
        destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
      rewrite <- Hbase. apply Bool.negb_false_iff. exact H1.
    Qed.

    Lemma aggregate_bounded_write_unchanged :
      forall st fr target input st',
        R.write_side_contribution st fr target input = (st', false) ->
        aggregate_bounded st target -> aggregate_bounded st' target.
    Proof.
      intros st fr target input st' Hwrite Hbounded.
      pose proof (write_side_unchanged_equivalent Hwrite) as Hequiv.
      unfold R.equivalent in Hequiv. apply Bool.andb_true_iff in Hequiv.
      unfold aggregate_bounded in *.
      eapply DL.leq_trans; [exact (proj1 Hequiv) |].
      destruct (write_side_contribution_same_read_view Hwrite)
        as [Hsigma _]. unfold R.sigma_value in *. now rewrite Hsigma.
    Qed.

    Lemma aggregate_bounded_set_value :
      forall st fr direct st' fr' target,
        R.set_value st fr direct = (st', fr') ->
        aggregate_bounded st target -> aggregate_bounded st' target.
    Proof.
      intros st fr direct st' fr' target Hset Hbounded.
      destruct (V.eq_dec target (R.frame_owner fr)) as [-> | Hneq].
      - unfold aggregate_bounded, R.aggregate.
        rewrite (@set_value_contributions st fr direct st' fr' Hset).
        eapply set_value_aggregate_sound; eauto.
      - unfold aggregate_bounded in *.
        rewrite (@set_value_sigma_value_other_correctness
          st fr direct st' fr' target Hset Hneq).
        unfold R.aggregate.
        rewrite (@set_value_contributions st fr direct st' fr' Hset).
        exact Hbounded.
    Qed.

    Lemma aggregate_bounded_remember_dormant :
      forall st dormant target,
        aggregate_bounded st target ->
        aggregate_bounded (R.remember_dormant st dormant) target.
    Proof.
      intros st dormant target Hbounded.
      unfold aggregate_bounded, R.remember_dormant, R.with_dormant_bottom,
        R.aggregate, R.sigma_value in *. exact Hbounded.
    Qed.

    Lemma aggregate_bounded_add_reader :
      forall st read owner target,
        aggregate_bounded st target ->
        aggregate_bounded (R.add_reader st read owner) target.
    Proof.
      intros st read owner target Hbounded.
      unfold aggregate_bounded, R.add_reader, R.with_readers,
        R.aggregate, R.sigma_value in *. exact Hbounded.
    Qed.

    Lemma aggregate_bounded_step_guarded :
      forall tf before after target,
        aggregate_bounded (R.cfg_state before) target ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) target \/
        control_active target (R.cfg_control after) \/
        aggregate_bounded (R.cfg_state after) target.
    Proof.
      intros tf [st control] after target Hbounded Hstep.
      destruct control; cbn in Hstep.
      - destruct (R.queue st); try discriminate.
        inversion Hstep; subst. right. right. exact Hbounded.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. right. right. exact Hbounded.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. right. right.
               now apply aggregate_bounded_observe.
            -- destruct (R.pure_bottom_rhs tf root).
               ++ inversion Hstep; subst. right. right.
                  now apply aggregate_bounded_remember_dormant.
               ++ inversion Hstep; subst. right. right.
                  now apply aggregate_bounded_observe.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; right; right; exact Hbounded.
      - inversion Hstep; subst. right. right.
        now apply aggregate_bounded_materialize.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. right.
            now apply aggregate_bounded_add_reader.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               assert (Hbounded0 : aggregate_bounded observed target)
                 by (subst observed; now apply aggregate_bounded_observe).
               destruct (R.is_materialized observed t).
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst. right. right.
                  eapply aggregate_bounded_dirty_complete_get; eauto.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. right. right. exact Hbounded0.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. right. right.
                     eapply aggregate_bounded_complete_get; [exact Hget |].
                     now apply aggregate_bounded_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. right.
                  apply aggregate_bounded_add_reader.
                  now apply aggregate_bounded_remember_dormant.
               ++ set (observed := R.observe st t) in *.
                  assert (Hbounded0 : aggregate_bounded observed target)
                    by (subst observed; now apply aggregate_bounded_observe).
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. right. right. exact Hbounded0.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. right. right.
                     eapply aggregate_bounded_complete_get; [exact Hget |].
                     unfold st0. destruct (R.is_materialized observed t);
                       [exact Hbounded0 |now apply aggregate_bounded_enqueue].
        + set (observed := R.observe st t) in *.
          assert (Hbounded0 : aggregate_bounded observed target)
            by (subst observed; now apply aggregate_bounded_observe).
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst. destruct (V.eq_dec target t) as [-> | Hneq].
            -- unfold R.continue_side.
               destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool.
               ++ right. left. now left.
               ++ left. unfold queued. left. apply queue_insert_members. now left.
            -- assert (Hbounded1 : aggregate_bounded st1 target)
                 by (eapply aggregate_bounded_write_other; eauto).
               unfold R.continue_side.
               destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool;
                 [right; right; exact Hbounded1 |
                  right; right; now apply aggregate_bounded_enqueue].
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            destruct changed; inversion Hstep; subst.
            -- destruct (V.eq_dec target t) as [-> | Hneq].
               ++ unfold R.continue_side.
                  destruct (R.rank_lt (R.mark_side_dirty st1 t)
                    (R.frame_owner fr1) t &&
                    negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool.
                  ** right. left. now left.
                  ** left. unfold queued. left. apply queue_insert_members. now left.
               ++ assert (Hbounded1 : aggregate_bounded st1 target)
                    by (eapply aggregate_bounded_write_other; eauto).
                  assert (Hbounded2 :
                    aggregate_bounded (R.mark_side_dirty st1 t) target).
                  { eapply aggregate_bounded_same_solver_view;
                      [apply mark_side_dirty_same_solver_view |exact Hbounded1]. }
                  unfold R.continue_side.
                  destruct (R.rank_lt (R.mark_side_dirty st1 t)
                    (R.frame_owner fr1) t &&
                    negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool;
                    [right; right; exact Hbounded2 |
                     right; right; now apply aggregate_bounded_enqueue].
            -- right. right. destruct (V.eq_dec target t) as [-> | Hneq].
               ++ eapply aggregate_bounded_write_unchanged; eauto.
               ++ eapply aggregate_bounded_write_other; eauto.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. right. exact Hbounded.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               assert (Hbounded0 : aggregate_bounded observed target)
                 by (subst observed; now apply aggregate_bounded_observe).
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. right. right. exact Hbounded0.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. right. right. exact Hbounded0.
                  ** inversion Hstep; subst. right. right.
                     apply aggregate_bounded_materialize.
                     now apply aggregate_bounded_enqueue.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. right.
                  now apply aggregate_bounded_remember_dormant.
               ++ set (observed := R.observe st t) in *.
                  assert (Hbounded0 : aggregate_bounded observed target)
                    by (subst observed; now apply aggregate_bounded_observe).
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. right. right. exact Hbounded0.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. right. exact Hbounded0.
                     --- inversion Hstep; subst. right. right.
                         apply aggregate_bounded_materialize.
                         now apply aggregate_bounded_enqueue.
      - destruct l as [|dead remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + destruct (S.mem dead (R.frame_current_targets f)).
          * inversion Hstep; subst. right. right. exact Hbounded.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f dead D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 dead else st1)
                 f t dead remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f dead D.bottom)
              as [st1 changed] eqn:Hwrite.
            destruct changed; inversion Hstep; subst.
            -- destruct (V.eq_dec target dead) as [-> | Hneq].
               ++ unfold R.continue_dead.
                  destruct (R.rank_lt (R.mark_side_dirty st1 dead)
                    (R.frame_owner f) dead &&
                    negb (R.is_materialized (R.mark_side_dirty st1 dead)
                      dead))%bool.
                  ** right. left. now left.
                  ** left. unfold queued. left.
                     apply queue_insert_members. now left.
               ++ assert (Hbounded1 : aggregate_bounded st1 target)
                    by (eapply aggregate_bounded_write_other; eauto).
                  assert (Hbounded2 :
                    aggregate_bounded (R.mark_side_dirty st1 dead) target).
                  { eapply aggregate_bounded_same_solver_view;
                      [apply mark_side_dirty_same_solver_view |exact Hbounded1]. }
                  unfold R.continue_dead.
                  destruct (R.rank_lt (R.mark_side_dirty st1 dead)
                    (R.frame_owner f) dead &&
                    negb (R.is_materialized (R.mark_side_dirty st1 dead)
                      dead))%bool;
                    [right; right; exact Hbounded2 |
                     right; right; now apply aggregate_bounded_enqueue].
            -- right. right. destruct (V.eq_dec target dead) as [-> | Hneq].
               ++ eapply aggregate_bounded_write_unchanged; eauto.
               ++ eapply aggregate_bounded_write_other; eauto.
      - assert (Hbounded0 : aggregate_bounded (R.flush_deferred st) target)
          by exact Hbounded.
        destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. right. right.
        eapply aggregate_bounded_set_value; [exact Hset |exact Hbounded0].
      - destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. right. right.
          eapply aggregate_bounded_same_solver_view;
            [apply reset_registered_cells_same_solver_view |exact Hbounded].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. right. right. exact Hbounded.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst. right. right. exact Hbounded.
            -- inversion Hstep; subst. right. right.
               eapply aggregate_bounded_same_solver_view;
                 [apply reset_registered_cells_same_solver_view
                 |exact Hbounded].
      - destruct c; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. right. right.
          eapply aggregate_bounded_complete_get; eauto.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + inversion Hstep; subst. right. right. exact Hbounded.
    Qed.

    Lemma next_config_aggregate_guarded :
      forall tf before after target,
        (queued (R.cfg_state before) target \/
         control_active target (R.cfg_control before) \/
         aggregate_bounded (R.cfg_state before) target) ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) target \/
        control_active target (R.cfg_control after) \/
        aggregate_bounded (R.cfg_state after) target.
    Proof.
      intros tf before after target Hguard Hstep.
      destruct Hguard as [Hqueued | [Hactive | Hbounded]].
      - destruct (@queued_step_scheduled tf before after target Hqueued Hstep)
          as [Hqueued' | [Hactive' | [_ Hbounded']]].
        + now left.
        + now right; left.
        + now right; right.
      - destruct (@active_step_scheduled_or_commit
          tf before after target Hactive Hstep)
          as [Hqueued | [Hactive' | Hcommit]];
          try (now left); try (now right; left).
        right. right. destruct Hcommit as
          [st [fr [direct [k [st' [fr'
            [-> [Hset [-> ->]]]]]]]]].
        unfold aggregate_bounded. cbn. unfold R.aggregate.
        rewrite (@set_value_contributions (R.flush_deferred st)
          fr direct st' fr' Hset).
        eapply set_value_aggregate_sound. exact Hset.
      - eapply aggregate_bounded_step_guarded; eauto.
    Qed.

    Lemma summary_valid_step_guarded :
      forall tf before after owner,
        control_history tf (R.cfg_state before) (R.cfg_control before) ->
        summary_valid tf (R.cfg_state before) owner ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) owner \/
        control_active owner (R.cfg_control after) \/
        summary_valid tf (R.cfg_state after) owner.
    Proof.
      intros tf [st control] after owner Hhistory Hsummary Hstep.
      destruct control; cbn in Hhistory, Hstep.
      - destruct (R.queue st) as [|head rest] eqn:Hqueue;
          try discriminate. inversion Hstep; subst.
        destruct (V.eq_dec owner head) as [-> | Hneq].
        + right. left. now left.
        + right. right. eapply summary_valid_pop_other.
          * unfold R.queue_pop. rewrite Hqueue. reflexivity.
          * exact Hneq.
          * exact Hsummary.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. right. right. exact Hsummary.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. right. right.
               now apply summary_valid_observe.
            -- destruct (R.pure_bottom_rhs tf root).
               ++ inversion Hstep; subst. right. right.
                  now apply summary_valid_remember_dormant.
               ++ inversion Hstep; subst. right. right.
                  now apply summary_valid_observe.
      - destruct (R.queue st) as [|head rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + inversion Hstep; subst.
          destruct (V.eq_dec owner head) as [-> | Hneq].
          * right. left. now left.
          * right. right. eapply summary_valid_pop_other.
            -- unfold R.queue_pop. rewrite Hqueue. reflexivity.
            -- exact Hneq.
            -- exact Hsummary.
      - inversion Hstep; subst. right. right.
        now apply summary_valid_materialize.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hother].
        + destruct r; cbn -[R.observe R.complete_get R.enqueue
            R.record_side_input R.write_side_contribution R.continue_side
            R.materialize] in Hstep.
          * inversion Hstep; subst. right. left. now left.
          * destruct (R.is_dormant st t).
            -- inversion Hstep; subst. right. left. now left.
            -- destruct (R.Ranking.lookup (R.ranking st) t).
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** destruct (R.dirty_complete_get tf observed f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. right. left. left.
                     symmetry. eapply dirty_complete_get_owner; eauto.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. left. cbn.
                         now right; left.
                     --- change (Some
                          (let '(st1, fr1, value) :=
                             R.complete_get (R.enqueue observed t) f t in
                           {| R.cfg_state := st1;
                              R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                          Some after) in Hstep.
                         destruct (R.complete_get (R.enqueue observed t) f t)
                           as [[st1 fr1] value] eqn:Hget.
                         inversion Hstep; subst. right. left. left.
                         symmetry. eapply complete_get_frame_owner; eauto.
               ++ destruct (R.pure_bottom_rhs tf t &&
                    negb (R.is_materialized st t))%bool.
                  ** inversion Hstep; subst. right. left. now left.
                  ** set (observed := R.observe st t) in *.
                     destruct (negb (R.is_materialized observed t) &&
                       R.rank_lt observed (R.frame_owner f) t)%bool.
                     --- inversion Hstep; subst. right. left. cbn.
                         now right; left.
                     --- set (st0 := if R.is_materialized observed t
                          then observed else R.enqueue observed t) in *.
                         change (Some
                           (let '(st1, fr1, value) :=
                              R.complete_get st0 f t in
                            {| R.cfg_state := st1;
                               R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                           Some after) in Hstep.
                         destruct (R.complete_get st0 f t)
                           as [[st1 fr1] value] eqn:Hget.
                         inversion Hstep; subst. right. left. left.
                         symmetry. eapply complete_get_frame_owner; eauto.
          * set (observed := R.observe st t) in *.
            destruct (R.is_dormant st t) eqn:Hdormant.
            -- change (Some
                 (let '(fr1, input) := R.record_side_input f t t0 in
                  let '(st1, _) :=
                    R.write_side_contribution observed fr1 t input in
                  R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
               destruct (R.record_side_input f t t0)
                 as [fr1 input] eqn:Hrecord.
               destruct (R.write_side_contribution observed fr1 t input)
                 as [st1 changed] eqn:Hwrite.
               inversion Hstep; subst.
               pose proof (record_side_input_owner Hrecord) as Howner.
               unfold R.continue_side.
               destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool.
               ++ right. left. cbn. right. left. symmetry. exact Howner.
               ++ right. left. cbn. left. symmetry. exact Howner.
            -- change
                 ((let '(fr1, input) := R.record_side_input f t t0 in
                   let '(st1, changed) :=
                     R.write_side_contribution observed fr1 t input in
                   if changed then
                     Some (R.continue_side (R.mark_side_dirty st1 t)
                       fr1 t r c true)
                   else Some (R.continue_side st1 fr1 t r c false)) =
                  Some after) in Hstep.
               destruct (R.record_side_input f t t0)
                 as [fr1 input] eqn:Hrecord.
               destruct (R.write_side_contribution observed fr1 t input)
                 as [st1 changed] eqn:Hwrite.
               pose proof (record_side_input_owner Hrecord) as Howner.
               destruct changed; inversion Hstep; subst; unfold R.continue_side.
               ++ destruct (R.rank_lt (R.mark_side_dirty st1 t)
                    (R.frame_owner fr1) t &&
                    negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool.
                  ** right. left. cbn. right. left. symmetry. exact Howner.
                  ** right. left. cbn. left. symmetry. exact Howner.
               ++ right. left. cbn. left. symmetry. exact Howner.
          * destruct (R.is_dormant st t).
            -- inversion Hstep; subst. right. left. now left.
            -- destruct (R.Ranking.lookup (R.ranking st) t).
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. right. left. now left.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. left. cbn.
                         now right; left.
                     --- inversion Hstep; subst. right. left. now left.
               ++ destruct (R.pure_bottom_rhs tf t &&
                    negb (R.is_materialized st t))%bool.
                  ** inversion Hstep; subst. right. left. now left.
                  ** set (observed := R.observe st t) in *.
                     destruct (R.is_materialized observed t).
                     --- inversion Hstep; subst. right. left. now left.
                     --- destruct (R.rank_lt observed (R.frame_owner f) t).
                         +++ inversion Hstep; subst. right. left. cbn.
                             now right; left.
                         +++ inversion Hstep; subst. right. left. now left.
        + destruct r; cbn -[R.observe R.complete_get R.enqueue
            R.record_side_input R.write_side_contribution R.continue_side
            R.materialize] in Hstep.
          * inversion Hstep; subst. right. right. exact Hsummary.
          * destruct (R.is_dormant st t).
            -- inversion Hstep; subst. right. right.
               now apply summary_valid_add_reader.
            -- destruct (R.Ranking.lookup (R.ranking st) t).
               ++ set (observed := R.observe st t) in *.
                  assert (Hsummary0 : summary_valid tf observed owner)
                    by (subst observed; now apply summary_valid_observe).
                  destruct (R.is_materialized observed t).
                  ** destruct (R.dirty_complete_get tf observed f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst.
                     destruct (summary_valid_dirty_complete_get_guarded
                       Hget Hsummary0) as [Hqueued | Hsummary1].
                     --- now left.
                     --- now right; right.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. right. exact Hsummary0.
                     --- change (Some
                          (let '(st1, fr1, value) :=
                             R.complete_get (R.enqueue observed t) f t in
                           {| R.cfg_state := st1;
                              R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                          Some after) in Hstep.
                         destruct (R.complete_get (R.enqueue observed t) f t)
                           as [[st1 fr1] value] eqn:Hget.
                         inversion Hstep; subst. right. right.
                         eapply summary_valid_complete_get; [exact Hget |].
                         now apply summary_valid_enqueue.
               ++ destruct (R.pure_bottom_rhs tf t &&
                    negb (R.is_materialized st t))%bool.
                  ** inversion Hstep; subst. right. right.
                     apply summary_valid_add_reader.
                     now apply summary_valid_remember_dormant.
                  ** set (observed := R.observe st t) in *.
                     assert (Hsummary0 : summary_valid tf observed owner)
                       by (subst observed; now apply summary_valid_observe).
                     destruct (negb (R.is_materialized observed t) &&
                       R.rank_lt observed (R.frame_owner f) t)%bool.
                     --- inversion Hstep; subst. right. right. exact Hsummary0.
                     --- set (st0 := if R.is_materialized observed t
                          then observed else R.enqueue observed t) in *.
                         change (Some
                           (let '(st1, fr1, value) :=
                              R.complete_get st0 f t in
                            {| R.cfg_state := st1;
                               R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                           Some after) in Hstep.
                         destruct (R.complete_get st0 f t)
                           as [[st1 fr1] value] eqn:Hget.
                         inversion Hstep; subst. right. right.
                         eapply summary_valid_complete_get; [exact Hget |].
                         unfold st0.
                         destruct (R.is_materialized observed t);
                           [exact Hsummary0
                           |now apply summary_valid_enqueue].
          * set (observed := R.observe st t) in *.
            assert (Hsummary0 : summary_valid tf observed owner)
              by (subst observed; now apply summary_valid_observe).
            destruct (R.is_dormant st t) eqn:Hdormant.
            -- change (Some
                 (let '(fr1, input) := R.record_side_input f t t0 in
                  let '(st1, _) :=
                    R.write_side_contribution observed fr1 t input in
                  R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
               destruct (R.record_side_input f t t0)
                 as [fr1 input] eqn:Hrecord.
               destruct (R.write_side_contribution observed fr1 t input)
                 as [st1 changed] eqn:Hwrite.
               inversion Hstep; subst.
               assert (Hsummary1 : summary_valid tf st1 owner).
               { eapply summary_valid_write_other_source;
                   [exact Hwrite | |exact Hsummary0].
                 rewrite (record_side_input_owner Hrecord). exact Hother. }
               unfold R.continue_side.
               destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool;
                 [right; right; exact Hsummary1 |
                  right; right; now apply summary_valid_enqueue].
            -- change
                 ((let '(fr1, input) := R.record_side_input f t t0 in
                   let '(st1, changed) :=
                     R.write_side_contribution observed fr1 t input in
                   if changed then
                     Some (R.continue_side (R.mark_side_dirty st1 t)
                       fr1 t r c true)
                   else Some (R.continue_side st1 fr1 t r c false)) =
                  Some after) in Hstep.
               destruct (R.record_side_input f t t0)
                 as [fr1 input] eqn:Hrecord.
               destruct (R.write_side_contribution observed fr1 t input)
                 as [st1 changed] eqn:Hwrite.
               assert (Hsummary1 : summary_valid tf st1 owner).
               { eapply summary_valid_write_other_source;
                   [exact Hwrite | |exact Hsummary0].
                 rewrite (record_side_input_owner Hrecord). exact Hother. }
               destruct changed; inversion Hstep; subst.
               ++ assert (Hsummary2 :
                    summary_valid tf (R.mark_side_dirty st1 t) owner).
                  { eapply summary_valid_same_solver_view;
                      [apply mark_side_dirty_same_solver_view |exact Hsummary1]. }
                  unfold R.continue_side.
                  destruct (R.rank_lt (R.mark_side_dirty st1 t)
                    (R.frame_owner fr1) t &&
                    negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool;
                    [right; right; exact Hsummary2 |
                     right; right; now apply summary_valid_enqueue].
               ++ right. right. exact Hsummary1.
          * destruct (R.is_dormant st t).
            -- inversion Hstep; subst. right. right. exact Hsummary.
            -- destruct (R.Ranking.lookup (R.ranking st) t).
               ++ set (observed := R.observe st t) in *.
                  assert (Hsummary0 : summary_valid tf observed owner)
                    by (subst observed; now apply summary_valid_observe).
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. right. right. exact Hsummary0.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. right. right. exact Hsummary0.
                     --- inversion Hstep; subst. right. right.
                         apply summary_valid_materialize.
                         now apply summary_valid_enqueue.
               ++ destruct (R.pure_bottom_rhs tf t &&
                    negb (R.is_materialized st t))%bool.
                  ** inversion Hstep; subst. right. right.
                     now apply summary_valid_remember_dormant.
                  ** set (observed := R.observe st t) in *.
                     assert (Hsummary0 : summary_valid tf observed owner)
                       by (subst observed; now apply summary_valid_observe).
                     destruct (R.is_materialized observed t).
                     --- inversion Hstep; subst. right. right. exact Hsummary0.
                     --- destruct (R.rank_lt observed (R.frame_owner f) t).
                         +++ inversion Hstep; subst. right. right.
                             exact Hsummary0.
                         +++ inversion Hstep; subst. right. right.
                             apply summary_valid_materialize.
                             now apply summary_valid_enqueue.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hother].
        + destruct l as [|dead remaining]; cbn in Hstep.
          * inversion Hstep; subst. right. left. now left.
          * destruct (S.mem dead (R.frame_current_targets f)).
            -- inversion Hstep; subst. right. left. now left.
            -- change (Some
                (let '(st1, changed) :=
                   R.write_side_contribution st f dead D.bottom in
                 R.continue_dead
                   (if changed then R.mark_side_dirty st1 dead else st1)
                   f t dead remaining c changed) =
                Some after) in Hstep.
               destruct (R.write_side_contribution st f dead D.bottom)
                 as [st1 changed] eqn:Hwrite.
               destruct changed; inversion Hstep; subst; unfold R.continue_dead.
               ++ destruct (R.rank_lt (R.mark_side_dirty st1 dead)
                    (R.frame_owner f) dead &&
                    negb (R.is_materialized (R.mark_side_dirty st1 dead)
                      dead))%bool.
                  ** right. left. cbn. right. left. reflexivity.
                  ** right. left. cbn. now left.
               ++ right. left. cbn. now left.
        + destruct l as [|dead remaining]; cbn in Hstep.
          * inversion Hstep; subst. right. right. exact Hsummary.
          * destruct (S.mem dead (R.frame_current_targets f)).
            -- inversion Hstep; subst. right. right. exact Hsummary.
            -- change (Some
                (let '(st1, changed) :=
                   R.write_side_contribution st f dead D.bottom in
                 R.continue_dead
                   (if changed then R.mark_side_dirty st1 dead else st1)
                   f t dead remaining c changed) =
                Some after) in Hstep.
               destruct (R.write_side_contribution st f dead D.bottom)
                 as [st1 changed] eqn:Hwrite.
               assert (Hsummary1 : summary_valid tf st1 owner)
                 by (eapply summary_valid_write_other_source; eauto).
               destruct changed; inversion Hstep; subst.
               ++ assert (Hsummary2 :
                    summary_valid tf (R.mark_side_dirty st1 dead) owner).
                  { eapply summary_valid_same_solver_view;
                      [apply mark_side_dirty_same_solver_view |exact Hsummary1]. }
                  unfold R.continue_dead.
                  destruct (R.rank_lt (R.mark_side_dirty st1 dead)
                    (R.frame_owner f) dead &&
                    negb (R.is_materialized (R.mark_side_dirty st1 dead)
                      dead))%bool;
                    [right; right; exact Hsummary2 |
                     right; right; now apply summary_valid_enqueue].
               ++ right. right. exact Hsummary1.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        assert (Hcurrent0 : completed_witness tf (R.flush_deferred st) f t)
          by now apply completed_witness_flush_deferred.
        assert (Hsummary0 : summary_valid tf (R.flush_deferred st) owner)
          by now apply summary_valid_flush_deferred.
        destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst.
        destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hother].
        + right. right. eapply completed_witness_set_value_summary;
            [exact Hcurrent0 |exact Hset].
        + right. right. eapply summary_valid_set_value_other;
            [exact Hset |exact Hother |exact Hsummary0].
      - destruct Hhistory as [Hframe Hcontinuation].
        destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. right. right.
          eapply summary_valid_same_solver_view;
            [apply reset_registered_cells_same_solver_view |exact Hsummary].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst.
            destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hneq].
            -- right. left. now left.
            -- right. right. apply summary_valid_clear_side_dirty.
               eapply summary_valid_pop_other.
               ++ unfold R.queue_pop. rewrite Hqueue. reflexivity.
               ++ exact Hneq.
               ++ exact Hsummary.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst.
               destruct (V.eq_dec owner next) as [-> | Hneq].
               ++ right. left. now left.
               ++ right. right. eapply summary_valid_pop_other.
                  ** unfold R.queue_pop. rewrite Hqueue. reflexivity.
                  ** exact Hneq.
                  ** exact Hsummary.
            -- inversion Hstep; subst. right. right.
               eapply summary_valid_same_solver_view;
                 [apply reset_registered_cells_same_solver_view
                 |exact Hsummary].
      - destruct c; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. right. right.
          eapply summary_valid_complete_get; eauto.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + inversion Hstep; subst. right. right. exact Hsummary.
        + inversion Hstep; subst. right. right. exact Hsummary.
    Qed.

    Definition expects_get (owner : V.t) (k : R.continuation) : Prop :=
      match k with
      | R.KAfterGet _ target _ _ => owner = target
      | _ => True
      end.

    Fixpoint continuation_get_consistent (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          expects_get (R.frame_owner fr) rest /\
          continuation_get_consistent rest
      end.

    Definition return_get_ready (st : R.state) (k : R.continuation) : Prop :=
      match k with
      | R.KAfterGet _ target _ _ => Sem.solved st target
      | _ => True
      end.

    Definition control_get_consistent
      (st : R.state) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
      | R.StartEpisode owner k =>
          expects_get owner k /\ continuation_get_consistent k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          expects_get (R.frame_owner fr) k /\ continuation_get_consistent k
      | R.Return k =>
          return_get_ready st k /\ continuation_get_consistent k
      end.

    Lemma next_config_control_get_consistent :
      forall tf before after,
        control_get_consistent
          (R.cfg_state before) (R.cfg_control before) ->
        control_history tf
          (R.cfg_state before) (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        control_get_consistent
          (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf [st control] after Hconsistent Hhistory Hstep.
      destruct control; cbn in Hconsistent, Hhistory, Hstep.
      - destruct (R.queue st); try discriminate.
        inversion Hstep; subst. split; exact I.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. exact I.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. exact I.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst; cbn; repeat split; exact I.
            -- destruct (R.pure_bottom_rhs tf root);
                 inversion Hstep; subst; cbn; repeat split; exact I.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; cbn; repeat split; exact I.
      - inversion Hstep; subst. exact Hconsistent.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. split; assumption.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. split; assumption.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst. split.
                  ** rewrite (@dirty_complete_get_owner
                       tf observed f t st1 fr1 value Hget). exact Hexpect.
                  ** exact Hcontinuation.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. cbn. split; [reflexivity |].
                     split; assumption.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. split.
                     --- rewrite (@complete_get_frame_owner
                          (R.enqueue observed t) f t st1 fr1 value Hget).
                         exact Hexpect.
                     --- exact Hcontinuation.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. split; assumption.
               ++ set (observed := R.observe st t) in *.
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. cbn. split; [reflexivity |].
                     split; assumption.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst. split.
                     --- rewrite (@complete_get_frame_owner
                          st0 f t st1 fr1 value Hget). exact Hexpect.
                     --- exact Hcontinuation.
        + set (observed := R.observe st t) in *.
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            pose proof (record_side_input_owner Hrecord) as Howner.
            unfold R.continue_side.
            destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool.
            -- cbn. split; [exact I |]. split; [now rewrite Howner |assumption].
            -- cbn. split; [now rewrite Howner |assumption].
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            pose proof (record_side_input_owner Hrecord) as Howner.
            destruct changed; inversion Hstep; subst; unfold R.continue_side.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 t)
                 (R.frame_owner fr1) t &&
                 negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool.
               ++ cbn. split; [exact I |]. split; [now rewrite Howner |assumption].
               ++ cbn. split; [now rewrite Howner |assumption].
            -- cbn. split; [now rewrite Howner |assumption].
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. split; assumption.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. split; assumption.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. cbn. split; [exact I |].
                     split; assumption.
                  ** inversion Hstep; subst. split; assumption.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. split; assumption.
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. split; assumption.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. cbn. split; [exact I |].
                         split; assumption.
                     --- inversion Hstep; subst. split; assumption.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. split; assumption.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. split; assumption.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            destruct changed; inversion Hstep; subst; unfold R.continue_dead.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 target)
                 (R.frame_owner f) target &&
                 negb (R.is_materialized (R.mark_side_dirty st1 target)
                   target))%bool.
               ++ cbn. split; [exact I |]. split; assumption.
               ++ cbn. split; assumption.
            -- cbn. split; assumption.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. split.
        + rewrite (@set_value_frame_owner (R.flush_deferred st)
            f t st1 fr1 Hset).
          exact Hexpect.
        + exact Hcontinuation.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct Hhistory as [Hsummary Hhistory].
        destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst.
          destruct c; cbn in Hexpect, Hcontinuation |- *;
            split; try exact I; try exact Hcontinuation.
          rewrite <- Hexpect. eapply solved_same_solver_view;
            [apply reset_registered_cells_same_solver_view
            |exact (proj1 Hsummary)].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. split; assumption.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst. cbn. split; [exact I |].
               split; assumption.
            -- inversion Hstep; subst.
               destruct c; cbn in Hexpect, Hcontinuation |- *;
                 split; try exact I; try exact Hcontinuation.
               rewrite <- Hexpect. eapply solved_same_solver_view;
                 [apply reset_registered_cells_same_solver_view
                 |exact (proj1 Hsummary)].
      - destruct Hconsistent as [Hready Hcontinuation].
        destruct c; cbn in Hready, Hcontinuation, Hstep.
        + inversion Hstep; subst. exact I.
        + inversion Hstep; subst. exact I.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          destruct Hcontinuation as [Hexpect Hcontinuation]. split.
          * rewrite (@complete_get_frame_owner st f t st1 fr1 value Hget).
            exact Hexpect.
          * exact Hcontinuation.
        + inversion Hstep; subst. exact Hcontinuation.
        + inversion Hstep; subst. exact Hcontinuation.
        + inversion Hstep; subst. exact Hcontinuation.
        + inversion Hstep; subst. exact Hcontinuation.
    Qed.

    Lemma materialize_solved_origin_correctness :
      forall st inserted x,
        Sem.solved (R.materialize st inserted) x ->
        Sem.solved st x \/ x = inserted.
    Proof.
      intros st inserted x Hsolved. unfold R.materialize in Hsolved.
      destruct (M.lookup (R.sigma st) inserted) eqn:Hlookup;
        [now left |].
      destruct (V.eq_dec x inserted) as [-> | Hneq]; [now right |left].
      destruct Hsolved as [value Hvalue]. exists value.
      unfold R.semantic_lookup in *. cbn in Hvalue.
      rewrite ML.lookup_update_other in Hvalue by exact Hneq. exact Hvalue.
    Qed.

    Lemma complete_get_solved_origin :
      forall st fr target st' fr' value x,
        R.complete_get st fr target = (st', fr', value) ->
        Sem.solved st' x -> Sem.solved st x \/ x = target.
    Proof.
      intros st fr target st' fr' value x Hget Hsolved.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (read_state := R.with_readers base
        (M.update (R.readers base) target
          (S.add (R.frame_owner fr) (R.lookup_set (R.readers base) target))))
        in *.
      inversion Hget; subst.
      destruct (@materialize_solved_origin_correctness
        read_state target x Hsolved) as [Hread | Heq]; [left |now right].
      destruct Hread as [found Hfound]. exists found. unfold read_state in Hfound.
      cbn in Hfound. unfold base in Hfound.
      destruct (R.rank_lt st (R.frame_owner fr) target); exact Hfound.
    Qed.

    Lemma dirty_complete_get_solved_origin :
      forall tf st fr target st' fr' value x,
        R.is_materialized st target = true ->
        R.dirty_complete_get tf st fr target = (st', fr', value) ->
        Sem.solved st' x -> Sem.solved st x.
    Proof.
      intros tf st fr target st' fr' value x Hmaterialized Hget Hsolved.
      Local Transparent R.dirty_complete_get R.try_dirty_read.
      assert (Htarget_solved : Sem.solved st target).
      { unfold R.is_materialized in Hmaterialized.
        destruct (M.lookup (R.sigma st) target) as [stored |] eqn:Hlookup;
          try discriminate. exists stored. unfold R.semantic_lookup.
        now rewrite Hlookup. }
      unfold R.dirty_complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      assert (Hbase_back : forall observed,
        Sem.solved base observed -> Sem.solved st observed).
      { intros observed Hbase. subst base.
        destruct (R.rank_lt st (R.frame_owner fr) target).
        - exact Hbase.
        - eapply solved_same_solver_view_back;
            [apply promote_controlled_same_solver_view |exact Hbase]. }
      assert (Hprepared_back : forall observed,
        Sem.solved prepared observed -> Sem.solved st observed).
      { intros observed Hprepared. subst prepared.
        destruct (@materialize_solved_origin_correctness
          base target observed Hprepared)
          as [Hbase |Heq].
        - now apply Hbase_back.
        - subst observed. exact Htarget_solved. }
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed |] eqn:Hflush; inversion Hget; subst.
      - destruct (@solved_try_dirty_read_origin tf prepared
          (R.frame_owner fr) target flushed x Hflush Hsolved)
          as [-> |Hprepared]; [exact Htarget_solved |].
        now apply Hprepared_back.
      - now apply Hprepared_back.
      Local Opaque R.dirty_complete_get R.try_dirty_read.
    Qed.

    Lemma solved_observe_back :
      forall st observed x,
        Sem.solved (R.observe st observed) x -> Sem.solved st x.
    Proof.
      intros st observed x [value Hlookup]. exists value.
      unfold R.semantic_lookup in *.
      unfold R.observe in Hlookup.
      destruct (R.Ranking.observe (R.ranking st) observed).
      exact Hlookup.
    Qed.

    Lemma next_config_solved_origin_guarded :
      forall tf before after x,
        control_get_consistent
          (R.cfg_state before) (R.cfg_control before) ->
        control_history tf
          (R.cfg_state before) (R.cfg_control before) ->
        Sem.solved (R.cfg_state after) x ->
        R.next_config tf before = Some after ->
        Sem.solved (R.cfg_state before) x \/
        queued (R.cfg_state after) x \/
        control_active x (R.cfg_control after) \/
        summary_valid tf (R.cfg_state after) x.
    Proof.
      intros tf [st control] after x Hconsistent Hhistory Hsolved Hstep.
      destruct control; cbn in Hconsistent, Hhistory, Hstep.
      - destruct (R.queue st); try discriminate.
        inversion Hstep; subst. now left.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. now left.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. left.
               exact (@solved_observe_back st root x Hsolved).
            -- destruct (R.pure_bottom_rhs tf root) eqn:Hpure.
               ++ inversion Hstep; subst.
                  destruct (@solved_remember_dormant_origin st root x Hsolved)
                    as [Hbefore | ->]; [now left |].
                  right. right. right.
                  now apply summary_valid_pure_dormant.
               ++ inversion Hstep; subst. left.
                  exact (@solved_observe_back st root x Hsolved).
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; now left.
      - inversion Hstep; subst.
        destruct (@materialize_solved_origin_correctness st t x Hsolved)
          as [Hbefore | ->]; [now left |].
        right. right. left. cbn. now left.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. left.
            now apply solved_add_reader_back in Hsolved.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t) eqn:Hmat.
               ++ destruct (R.dirty_complete_get tf observed f t)
                    as [[st1 fr1] value] eqn:Hget.
                  inversion Hstep; subst. left. subst observed.
                  apply (@solved_observe_back st t x).
                  eapply dirty_complete_get_solved_origin; eauto.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. left. subst observed.
                     exact (@solved_observe_back st t x Hsolved).
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst.
                     destruct (@complete_get_solved_origin
                       (R.enqueue observed t) f t st1 fr1 value x Hget Hsolved)
                       as [Hst0 | ->].
                     --- left. subst observed.
                         exact (@solved_observe_back st t x Hst0).
                     --- right. left. eapply queued_complete_get;
                           [exact Hget |].
                         unfold queued. left. apply queue_insert_members. now left.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool eqn:Hpure.
               ++ inversion Hstep; subst.
                  apply solved_add_reader_back in Hsolved.
                  destruct (@solved_remember_dormant_origin st t x Hsolved)
                    as [Hbefore | ->]; [now left |].
                  right. right. right. apply summary_valid_add_reader.
                  apply summary_valid_pure_dormant.
                  now apply Bool.andb_true_iff in Hpure as [Hpure _].
               ++ set (observed := R.observe st t) in *.
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. left. subst observed.
                     exact (@solved_observe_back st t x Hsolved).
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t)
                       as [[st1 fr1] value] eqn:Hget.
                     inversion Hstep; subst.
                     destruct (@complete_get_solved_origin
                       st0 f t st1 fr1 value x Hget Hsolved)
                       as [Hst0 | ->].
                     --- left. unfold st0 in Hst0.
                         destruct (R.is_materialized observed t);
                           subst observed;
                           exact (@solved_observe_back st t x Hst0).
                     --- unfold st0.
                         destruct (R.is_materialized observed t) eqn:Hmat.
                         +++ left. subst observed.
                             apply (@solved_observe_back st t t).
                             unfold R.is_materialized in Hmat.
                             destruct (M.lookup
                               (R.sigma (R.observe st t)) t)
                               as [current|] eqn:Hlookup; try discriminate.
                             exists current. unfold R.semantic_lookup.
                             now rewrite Hlookup.
                         +++ right. left. eapply queued_complete_get;
                               [exact Hget |].
                             unfold queued. left. apply queue_insert_members.
                             now left.
        + set (observed := R.observe st t) in *.
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Hst1 : Sem.solved st1 x).
            { unfold R.continue_side in Hsolved.
              destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                negb (R.is_materialized st1 t))%bool; exact Hsolved. }
            left. apply solved_observe_back with (observed := t).
            eapply solved_same_read_view_back;
              [eapply write_side_contribution_same_read_view; exact Hwrite
              |exact Hst1].
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            destruct changed; inversion Hstep; subst.
            -- assert (Hmarked : Sem.solved (R.mark_side_dirty st1 t) x).
               { unfold R.continue_side in Hsolved.
                 destruct (R.rank_lt (R.mark_side_dirty st1 t)
                   (R.frame_owner fr1) t &&
                   negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool;
                   exact Hsolved. }
               assert (Hst1 : Sem.solved st1 x).
               { eapply solved_same_solver_view_back;
                   [apply mark_side_dirty_same_solver_view |exact Hmarked]. }
               left. apply solved_observe_back with (observed := t).
               eapply solved_same_read_view_back;
                 [eapply write_side_contribution_same_read_view; exact Hwrite
                 |exact Hst1].
            -- left. apply solved_observe_back with (observed := t).
               eapply solved_same_read_view_back;
                 [eapply write_side_contribution_same_read_view; exact Hwrite
                 |exact Hsolved].
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. now left.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. left. subst observed.
                  exact (@solved_observe_back st t x Hsolved).
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. left. subst observed.
                     exact (@solved_observe_back st t x Hsolved).
                  ** inversion Hstep; subst.
                     destruct (@materialize_solved_origin_correctness
                       (R.enqueue observed t) t x Hsolved)
                       as [Horigin | ->].
                     --- left. subst observed.
                         exact (@solved_observe_back st t x Horigin).
                     --- right. left. apply queued_materialize.
                         unfold queued. left. apply queue_insert_members. now left.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool eqn:Hpure.
               ++ inversion Hstep; subst.
                  destruct (@solved_remember_dormant_origin st t x Hsolved)
                    as [Hbefore | ->]; [now left |].
                  right. right. right. apply summary_valid_pure_dormant.
                  now apply Bool.andb_true_iff in Hpure as [Hpure _].
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. left. subst observed.
                     exact (@solved_observe_back st t x Hsolved).
                  ** destruct (R.rank_lt observed (R.frame_owner f) t).
                     --- inversion Hstep; subst. left. subst observed.
                         exact (@solved_observe_back st t x Hsolved).
                     --- inversion Hstep; subst.
                         destruct (@materialize_solved_origin_correctness
                           (R.enqueue observed t) t x Hsolved)
                           as [Horigin | ->].
                         +++ left. subst observed.
                             exact (@solved_observe_back st t x Horigin).
                         +++ right. left. apply queued_materialize.
                             unfold queued. left. apply queue_insert_members.
                             now left.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. now left.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            destruct changed.
            -- inversion Hstep; subst.
               assert (Hmarked :
                 Sem.solved (R.mark_side_dirty st1 target) x).
               { unfold R.continue_dead in Hsolved.
                 destruct (R.rank_lt (R.mark_side_dirty st1 target)
                   (R.frame_owner f) target &&
                   negb (R.is_materialized (R.mark_side_dirty st1 target)
                     target))%bool; exact Hsolved. }
               assert (Hst1 : Sem.solved st1 x).
               { eapply solved_same_solver_view_back;
                   [apply mark_side_dirty_same_solver_view |exact Hmarked]. }
               left. eapply solved_same_read_view_back;
                 [eapply write_side_contribution_same_read_view; exact Hwrite
                 |exact Hst1].
            -- inversion Hstep; subst. left.
               eapply solved_same_read_view_back;
                 [eapply write_side_contribution_same_read_view; exact Hwrite
                 |exact Hsolved].
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (R.set_value (R.flush_deferred st) f t)
          as [st1 fr1] eqn:Hset.
        inversion Hstep; subst.
        destruct (@set_value_solved_origin
          (R.flush_deferred st) f t st1 fr1 x Hset Hsolved)
          as [Hbefore | ->].
        + left. now apply solved_flush_deferred_back.
        + left. exact (proj1 Hcurrent).
      - destruct (R.queue st) as [|next rest]; cbn in Hstep.
        + inversion Hstep; subst. left.
          eapply solved_same_solver_view_back;
            [apply reset_registered_cells_same_solver_view |exact Hsolved].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. now left.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst. now left.
            -- inversion Hstep; subst. left.
               eapply solved_same_solver_view_back;
                 [apply reset_registered_cells_same_solver_view |exact Hsolved].
      - destruct Hconsistent as [Hready Hcontinuation].
        destruct c; cbn in Hready, Hstep.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + change (Some
            (let '(st1, fr1, value) := R.complete_get st f t in
             {| R.cfg_state := st1;
                R.cfg_control := R.RunRhs fr1 (r value) c |}) =
            Some after) in Hstep.
          destruct (R.complete_get st f t)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          destruct (@complete_get_solved_origin
            st f t st1 fr1 value x Hget Hsolved) as [Hbefore | ->].
          * now left.
          * left. exact Hready.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
    Qed.

    Definition dormant_extends (before after : R.state) : Prop :=
      forall x,
        S.mem x (R.dormant_bottom before) = true ->
        S.mem x (R.dormant_bottom after) = true.

    Lemma dormant_extends_refl : forall st, dormant_extends st st.
    Proof. firstorder. Qed.

    Lemma dormant_extends_trans :
      forall first middle last,
        dormant_extends first middle -> dormant_extends middle last ->
        dormant_extends first last.
    Proof. unfold dormant_extends. eauto. Qed.

    Lemma dormant_extends_same :
      forall before after,
        R.dormant_bottom after = R.dormant_bottom before ->
        dormant_extends before after.
    Proof. unfold dormant_extends. intros. now rewrite H. Qed.

    Lemma dormant_extends_remember :
      forall st target, dormant_extends st (R.remember_dormant st target).
    Proof.
      intros st target x Hmember. unfold R.remember_dormant,
        R.with_dormant_bottom. cbn. apply SL.add_spec. now right.
    Qed.

    Lemma dormant_extends_observe :
      forall st target, dormant_extends st (R.observe st target).
    Proof.
      intros. apply dormant_extends_same. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) target). reflexivity.
    Qed.

    Lemma dormant_extends_materialize :
      forall st target, dormant_extends st (R.materialize st target).
    Proof.
      intros. apply dormant_extends_same. unfold R.materialize.
      destruct (M.lookup (R.sigma st) target); reflexivity.
    Qed.

    Lemma dormant_extends_enqueue :
      forall st target, dormant_extends st (R.enqueue st target).
    Proof. intros. apply dormant_extends_same. reflexivity. Qed.

    Lemma dormant_extends_complete_get :
      forall st fr target next next_fr value,
        R.complete_get st fr target = (next, next_fr, value) ->
        dormant_extends st next.
    Proof.
      intros st fr target next next_fr value Hget.
      unfold R.complete_get in Hget.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      inversion Hget; subst.
      eapply dormant_extends_trans with (middle := base).
      - subst base. destruct (R.rank_lt st (R.frame_owner fr) target);
          apply dormant_extends_same; reflexivity.
      - eapply dormant_extends_trans with
          (middle := R.with_readers base
            (M.update (R.readers base) target
              (S.add (R.frame_owner fr)
                (R.lookup_set (R.readers base) target)))).
        + apply dormant_extends_same. reflexivity.
        + apply dormant_extends_materialize.
    Qed.

    Lemma dormant_extends_dirty_complete_get :
      forall tf st fr target next next_fr value,
        R.dirty_complete_get tf st fr target = (next, next_fr, value) ->
        dormant_extends st next.
    Proof.
      intros tf st fr target next next_fr value Hcomplete.
      assert (Htry : forall tf0 st0 owner0 target0 next0,
        R.try_dirty_read tf0 st0 owner0 target0 = Some next0 ->
        R.dormant_bottom next0 = R.dormant_bottom st0).
      { intros tf0 st0 owner0 target0 next0 Hread.
        Local Transparent R.try_dirty_read.
        unfold R.try_dirty_read in Hread.
        repeat match type of Hread with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        | context [match ?subject with _ => _ end] => destruct subject eqn:?
        end; try discriminate; inversion Hread; reflexivity. }
      Local Transparent R.dirty_complete_get.
      unfold R.dirty_complete_get in Hcomplete.
      set (base := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (prepared := R.materialize base target) in *.
      destruct (R.try_dirty_read tf prepared (R.frame_owner fr) target)
        as [flushed|] eqn:Hflush;
        inversion Hcomplete; subst; apply dormant_extends_same;
        unfold R.add_reader; cbn.
      - rewrite (Htry _ _ _ _ _ Hflush). subst prepared base.
        unfold R.materialize.
        destruct (R.rank_lt st (R.frame_owner fr) target); cbn;
          destruct (M.lookup (R.sigma st) target); reflexivity.
      - subst prepared base. unfold R.materialize.
        destruct (R.rank_lt st (R.frame_owner fr) target); cbn;
          destruct (M.lookup (R.sigma st) target); reflexivity.
      Local Opaque R.dirty_complete_get R.try_dirty_read.
    Qed.

    Lemma dormant_extends_write_side :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        dormant_extends st next.
    Proof.
      intros. apply dormant_extends_same.
      exact (proj2 (proj2 (proj2 (proj2
        (write_side_contribution_same_read_view H))))).
    Qed.

    Lemma dormant_extends_continue_side :
      forall st fr target body k changed,
        dormant_extends st
          (R.cfg_state (R.continue_side st fr target body k changed)).
    Proof.
      intros. unfold R.continue_side.
      repeat destruct (_ : bool); apply dormant_extends_same; reflexivity.
    Qed.

    Lemma dormant_extends_continue_dead :
      forall st fr direct target remaining k changed,
        dormant_extends st
          (R.cfg_state
            (R.continue_dead st fr direct target remaining k changed)).
    Proof.
      intros. unfold R.continue_dead.
      repeat destruct (_ : bool); apply dormant_extends_same; reflexivity.
    Qed.

    Lemma dormant_extends_set_value :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        dormant_extends st next.
    Proof.
      intros st fr direct next next_fr Hset. unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      end;
      try destruct (U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr))));
      inversion Hset; subst; apply dormant_extends_same; reflexivity.
    Qed.

    Lemma dormant_extends_reset :
      forall st owner,
        dormant_extends st (R.reset_registered_cells st owner).
    Proof.
      intros. apply dormant_extends_same. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma next_config_dormant_extends :
      forall tf before after,
        R.next_config tf before = Some after ->
        dormant_extends (R.cfg_state before) (R.cfg_state after).
    Proof.
      intros tf [st control] after Hstep. destruct control as
        [|roots |remaining |owner k |fr body k |fr direct pending k
         |fr direct k |fr k |k].
      - cbn in Hstep. destruct (R.queue_pop (R.queue st)); try discriminate.
        destruct p. inversion Hstep; subst. apply dormant_extends_same.
        reflexivity.
      - destruct roots as [|root roots]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. apply dormant_extends_refl.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. apply dormant_extends_refl.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. apply dormant_extends_observe.
            -- destruct (R.pure_bottom_rhs tf root).
               ++ inversion Hstep; subst. apply dormant_extends_remember.
               ++ inversion Hstep; subst. apply dormant_extends_observe.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[head rest]|].
        + inversion Hstep; subst. apply dormant_extends_same. reflexivity.
        + inversion Hstep; subst. apply dormant_extends_refl.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        apply dormant_extends_materialize.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. apply dormant_extends_refl.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          destruct (R.is_dormant st target).
          * inversion Hstep; subst. apply dormant_extends_same. reflexivity.
          * destruct (R.Ranking.lookup (R.ranking st) target).
            -- set (observed := R.observe st target) in *.
               destruct (R.is_materialized observed target).
               ++ destruct (R.dirty_complete_get tf observed fr target)
                    as [[next_st next_fr] read] eqn:Hget.
                  inversion Hstep; subst.
                  eapply dormant_extends_trans;
                    [apply dormant_extends_observe
                    |eapply dormant_extends_dirty_complete_get; exact Hget].
               ++ destruct (R.rank_lt observed (R.frame_owner fr) target).
                  ** inversion Hstep; subst. apply dormant_extends_observe.
                  ** destruct (R.complete_get (R.enqueue observed target)
                       fr target) as [[next_st next_fr] read] eqn:Hget.
                     inversion Hstep; subst.
                     eapply dormant_extends_trans; [apply dormant_extends_observe |].
                     eapply dormant_extends_trans;
                       [apply dormant_extends_enqueue
                       |eapply dormant_extends_complete_get; exact Hget].
            -- destruct (R.pure_bottom_rhs tf target &&
                 negb (R.is_materialized st target))%bool.
               ++ inversion Hstep; subst. eapply dormant_extends_trans;
                    [apply dormant_extends_remember
                    |apply dormant_extends_same; reflexivity].
               ++ set (observed := R.observe st target) in *.
                  destruct (negb (R.is_materialized observed target) &&
                    R.rank_lt observed (R.frame_owner fr) target)%bool.
                  ** inversion Hstep; subst. apply dormant_extends_observe.
                  ** set (base := if R.is_materialized observed target
                       then observed else R.enqueue observed target) in *.
                     destruct (R.complete_get base fr target)
                       as [[next_st next_fr] read] eqn:Hget.
                     inversion Hstep; subst.
                     eapply dormant_extends_trans with (middle := base).
                     --- unfold base, observed.
                         destruct (R.is_materialized
                           (R.observe st target) target).
                         +++ apply dormant_extends_observe.
                         +++ eapply dormant_extends_trans;
                               [apply dormant_extends_observe
                               |exact (@dormant_extends_enqueue
                                  (R.observe st target) target)].
                     --- eapply dormant_extends_complete_get; exact Hget.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution (R.observe st target)
            fr1 target input) as [next_st changed] eqn:Hwrite.
          eapply dormant_extends_trans; [apply dormant_extends_observe |].
          eapply dormant_extends_trans;
            [eapply dormant_extends_write_side; exact Hwrite |].
          destruct (R.is_dormant st target); [inversion Hstep; subst |].
          * unfold R.continue_side.
            destruct (R.rank_lt next_st (R.frame_owner fr1) target &&
              negb (R.is_materialized next_st target))%bool;
              apply dormant_extends_same; reflexivity.
          * destruct changed; inversion Hstep; subst.
            -- eapply dormant_extends_trans.
               ++ apply dormant_extends_same. reflexivity.
               ++ unfold R.continue_side.
                  destruct (R.rank_lt (R.mark_side_dirty next_st target)
                    (R.frame_owner fr1) target &&
                    negb (R.is_materialized
                      (R.mark_side_dirty next_st target) target))%bool;
                    apply dormant_extends_same; reflexivity.
            -- apply dormant_extends_same. reflexivity.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          destruct (R.is_dormant st target).
          * inversion Hstep; subst. apply dormant_extends_refl.
          * destruct (R.Ranking.lookup (R.ranking st) target).
            -- set (observed := R.observe st target) in *.
               destruct (R.is_materialized observed target).
               ++ inversion Hstep; subst. apply dormant_extends_observe.
               ++ destruct (R.rank_lt observed (R.frame_owner fr) target).
                  ** inversion Hstep; subst. apply dormant_extends_observe.
                  ** inversion Hstep; subst. eapply dormant_extends_trans.
                     --- apply dormant_extends_observe.
                     --- eapply dormant_extends_trans;
                           [apply dormant_extends_enqueue
                           |apply dormant_extends_materialize].
            -- destruct (R.pure_bottom_rhs tf target &&
                 negb (R.is_materialized st target))%bool.
               ++ inversion Hstep; subst. apply dormant_extends_remember.
               ++ set (observed := R.observe st target) in *.
                  destruct (R.is_materialized observed target).
                  ** inversion Hstep; subst. apply dormant_extends_observe.
                  ** destruct (R.rank_lt observed (R.frame_owner fr) target).
                     --- inversion Hstep; subst. apply dormant_extends_observe.
                     --- inversion Hstep; subst. eapply dormant_extends_trans.
                         +++ apply dormant_extends_observe.
                         +++ eapply dormant_extends_trans;
                               [apply dormant_extends_enqueue
                               |apply dormant_extends_materialize].
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          apply dormant_extends_same. reflexivity.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. apply dormant_extends_refl.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [next_st changed] eqn:Hwrite.
            eapply dormant_extends_trans;
              [eapply dormant_extends_write_side; exact Hwrite |].
            destruct changed; inversion Hstep; subst.
            -- eapply dormant_extends_trans.
               ++ apply dormant_extends_same. reflexivity.
               ++ unfold R.continue_dead.
                  destruct (R.rank_lt (R.mark_side_dirty next_st target)
                    (R.frame_owner fr) target &&
                    negb (R.is_materialized
                      (R.mark_side_dirty next_st target) target))%bool;
                    apply dormant_extends_same; reflexivity.
            -- apply dormant_extends_same. reflexivity.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value (R.flush_deferred st) fr direct)
          as [next_st next_fr] eqn:Hset.
        inversion Hstep; subst.
        eapply dormant_extends_trans with
          (middle := R.flush_deferred st).
        + apply dormant_extends_same. reflexivity.
        + eapply dormant_extends_set_value; exact Hset.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head rest] |];
              try discriminate. inversion Hstep; subst.
            apply dormant_extends_same. reflexivity.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head rest] |];
                 try discriminate. inversion Hstep; subst.
               apply dormant_extends_same. reflexivity.
            -- inversion Hstep; subst. apply dormant_extends_reset.
        + inversion Hstep; subst. apply dormant_extends_reset.
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep;
          try (inversion Hstep; subst; apply dormant_extends_refl).
        destruct (R.complete_get st fr target)
          as [[next_st next_fr] value] eqn:Hget.
        inversion Hstep; subst. eapply dormant_extends_complete_get; exact Hget.
    Qed.

    Lemma next_config_preserves_solved :
      forall tf before after x,
        Sem.solved (R.cfg_state before) x ->
        R.next_config tf before = Some after ->
        Sem.solved (R.cfg_state after) x.
    Proof.
      intros tf before after x [value Hlookup] Hstep.
      unfold R.semantic_lookup in Hlookup.
      destruct (M.lookup (R.sigma (R.cfg_state before)) x)
        as [stored|] eqn:Hsigma.
      - destruct (@Termination.next_config_sigma_extends
          tf before after Hstep x stored Hsigma) as [next Hnext].
        exists next. unfold R.semantic_lookup. now rewrite Hnext.
      - destruct (S.mem x (R.dormant_bottom (R.cfg_state before)))
          eqn:Hmember; try discriminate.
        pose proof (@next_config_dormant_extends tf before after Hstep)
          as Hextends.
        specialize (Hextends x Hmember).
        unfold Sem.solved, Sem.StateSpec.solved, R.semantic_lookup.
        destruct (M.lookup (R.sigma (R.cfg_state after)) x)
          as [next|] eqn:Hnext.
        + exists next. reflexivity.
        + exists D.bottom. now rewrite Hextends.
    Qed.

    Lemma next_config_summary_guarded :
      forall tf before after owner,
        control_get_consistent
          (R.cfg_state before) (R.cfg_control before) ->
        control_history tf
          (R.cfg_state before) (R.cfg_control before) ->
        (forall x,
          Sem.solved (R.cfg_state before) x ->
          queued (R.cfg_state before) x \/
          control_active x (R.cfg_control before) \/
          summary_valid tf (R.cfg_state before) x) ->
        Sem.solved (R.cfg_state after) owner ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) owner \/
        control_active owner (R.cfg_control after) \/
        summary_valid tf (R.cfg_state after) owner.
    Proof.
      intros tf before after owner Hconsistent Hhistory
        Hguard Hsolved Hstep.
      destruct (@next_config_solved_origin_guarded
        tf before after owner Hconsistent Hhistory Hsolved Hstep)
        as [Hbefore | [Hqueued | [Hactive | Hsummary]]].
      - destruct (Hguard owner Hbefore)
          as [Hqueued | [Hactive | Hsummary]].
        + destruct (@queued_step_scheduled
            tf before after owner Hqueued Hstep)
            as [Hqueued' | [Hactive' | [Hsummary' _]]].
          * now left.
          * now right; left.
          * now right; right.
        + destruct (@active_step_scheduled_or_commit
            tf before after owner Hactive Hstep)
            as [Hqueued' | [Hactive' | Hcommit]].
          * now left.
          * now right; left.
          * right. right. destruct Hcommit as
              [st [fr [direct [k [st' [fr'
                [-> [Hset [-> ->]]]]]]]]].
            cbn in Hhistory.
            eapply completed_witness_set_value_summary; eauto.
            apply completed_witness_flush_deferred.
            exact (proj1 Hhistory).
        + eapply summary_valid_step_guarded; eauto.
      - now left.
      - now right; left.
      - now right; right.
    Qed.

    Fixpoint continuation_pending
      (x : V.t) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop => False
      | R.KSeedLoop remaining => List.In x remaining
      | R.KAfterGet _ _ _ rest
      | R.KAfterSide _ _ rest
      | R.KAfterSpawn _ _ rest
      | R.KDead _ _ _ rest
      | R.KDrain _ rest => continuation_pending x rest
      end.

    Definition control_pending (x : V.t) (control : R.control) : Prop :=
      match control with
      | R.RunLoop => False
      | R.RunSeeds remaining | R.RunSeedLoop remaining => List.In x remaining
      | R.StartEpisode _ rest
      | R.RunRhs _ _ rest
      | R.RunDead _ _ _ rest
      | R.RunCommit _ _ rest
      | R.RunDrain _ rest
      | R.Return rest => continuation_pending x rest
      end.

    Definition roots_guarded (roots : list V.t) (c : R.config) : Prop :=
      forall x, List.In x roots ->
        Sem.solved (R.cfg_state c) x \/
        queued (R.cfg_state c) x \/
        control_pending x (R.cfg_control c) \/
        control_active x (R.cfg_control c).

    Lemma initial_roots_guarded :
      forall roots, roots_guarded roots (R.initial_config roots).
    Proof. intros roots x Hin. right. right. left. exact Hin. Qed.

    Lemma materialized_solved :
      forall st x, R.is_materialized st x = true -> Sem.solved st x.
    Proof.
      intros st x Hmaterialized. unfold R.is_materialized in Hmaterialized.
      destruct (M.lookup (R.sigma st) x) as [value|] eqn:Hlookup;
        try discriminate. exists value. unfold R.semantic_lookup.
      now rewrite Hlookup.
    Qed.

    Lemma control_pending_step :
      forall tf x before after,
        control_pending x (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        Sem.solved (R.cfg_state after) x \/
        control_pending x (R.cfg_control after) \/
        control_active x (R.cfg_control after).
    Proof.
      intros tf x [st control] after Hpending Hstep.
      destruct control; cbn in Hpending, Hstep; try contradiction.
      - destruct l as [|root remaining]; cbn in Hpending, Hstep;
          [contradiction |].
        destruct Hpending as [Heq | Hpending].
        + subst x.
          destruct (R.is_materialized st root || R.is_dormant st root)%bool
            eqn:Hknown.
          * inversion Hstep; subst. left.
            apply Bool.orb_true_iff in Hknown as [Hmat |Hdormant].
            -- now apply materialized_solved.
            -- now apply solved_dormant.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. right. right. now left.
            -- destruct (R.pure_bottom_rhs tf root) eqn:Hpure.
               ++ inversion Hstep; subst. left.
                  exact (proj1
                    (@summary_valid_pure_dormant tf st root Hpure)).
               ++ inversion Hstep; subst. right. right. now left.
        + destruct (R.is_materialized st root || R.is_dormant st root)%bool.
          * inversion Hstep; subst. right. left. exact Hpending.
          * destruct (R.Ranking.lookup (R.ranking st) root).
            -- inversion Hstep; subst. right. left. exact Hpending.
            -- destruct (R.pure_bottom_rhs tf root);
                 inversion Hstep; subst; right; left; exact Hpending.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; right; left; exact Hpending.
      - inversion Hstep; subst. right. left. exact Hpending.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. right. left. exact Hpending.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. left. exact Hpending.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ destruct (R.dirty_complete_get tf observed f t).
                  destruct p. inversion Hstep; subst. right. left. exact Hpending.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t).
                  ** inversion Hstep; subst. right. left. exact Hpending.
                  ** change (Some
                       (let '(st1, fr1, value) :=
                          R.complete_get (R.enqueue observed t) f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get (R.enqueue observed t) f t).
                     destruct p. inversion Hstep; subst. right. left.
                     exact Hpending.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. left. exact Hpending.
               ++ set (observed := R.observe st t) in *.
                  destruct (negb (R.is_materialized observed t) &&
                    R.rank_lt observed (R.frame_owner f) t)%bool.
                  ** inversion Hstep; subst. right. left. exact Hpending.
                  ** set (st0 := if R.is_materialized observed t
                       then observed else R.enqueue observed t) in *.
                     change (Some
                       (let '(st1, fr1, value) := R.complete_get st0 f t in
                        {| R.cfg_state := st1;
                           R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                       Some after) in Hstep.
                     destruct (R.complete_get st0 f t). destruct p.
                     inversion Hstep; subst. right. left. exact Hpending.
        + set (observed := R.observe st t) in *.
          destruct (R.is_dormant st t) eqn:Hdormant.
          * change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, _) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c true) = Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input].
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed].
            inversion Hstep; subst. unfold R.continue_side.
            destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool;
              cbn; right; left; exact Hpending.
          * change
              ((let '(fr1, input) := R.record_side_input f t t0 in
                let '(st1, changed) :=
                  R.write_side_contribution observed fr1 t input in
                if changed then
                  Some (R.continue_side (R.mark_side_dirty st1 t)
                    fr1 t r c true)
                else Some (R.continue_side st1 fr1 t r c false)) =
               Some after) in Hstep.
            destruct (R.record_side_input f t t0) as [fr1 input].
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed].
            destruct changed; inversion Hstep; subst; unfold R.continue_side.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 t)
                 (R.frame_owner fr1) t &&
                 negb (R.is_materialized (R.mark_side_dirty st1 t) t))%bool;
                 cbn; right; left; exact Hpending.
            -- cbn. right. left. exact Hpending.
        + destruct (R.is_dormant st t).
          * inversion Hstep; subst. right. left. exact Hpending.
          * destruct (R.Ranking.lookup (R.ranking st) t).
            -- set (observed := R.observe st t) in *.
               destruct (R.is_materialized observed t).
               ++ inversion Hstep; subst. right. left. exact Hpending.
               ++ destruct (R.rank_lt observed (R.frame_owner f) t);
                    inversion Hstep; subst; right; left; exact Hpending.
            -- destruct (R.pure_bottom_rhs tf t &&
                 negb (R.is_materialized st t))%bool.
               ++ inversion Hstep; subst. right. left. exact Hpending.
               ++ set (observed := R.observe st t) in *.
                  destruct (R.is_materialized observed t).
                  ** inversion Hstep; subst. right. left. exact Hpending.
                  ** destruct (R.rank_lt observed (R.frame_owner f) t);
                       inversion Hstep; subst; right; left; exact Hpending.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hpending.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. right. left. exact Hpending.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead
                 (if changed then R.mark_side_dirty st1 target else st1)
                 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed].
            destruct changed; inversion Hstep; subst; unfold R.continue_dead.
            -- destruct (R.rank_lt (R.mark_side_dirty st1 target)
                 (R.frame_owner f) target &&
                 negb (R.is_materialized (R.mark_side_dirty st1 target)
                   target))%bool;
                 cbn; right; left; exact Hpending.
            -- cbn. right. left. exact Hpending.
      - destruct (R.set_value (R.flush_deferred st) f t).
        inversion Hstep; subst. right. left. exact Hpending.
      - destruct (R.queue st) as [|next rest]; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hpending.
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. right. left. exact Hpending.
          * destruct (R.rank_lt st (R.frame_owner f) next);
              inversion Hstep; subst; right; left; exact Hpending.
      - destruct c; cbn in Hpending, Hstep.
        + contradiction.
        + inversion Hstep; subst. right. left. exact Hpending.
        + destruct (R.complete_get st f t). destruct p.
          inversion Hstep; subst. right. left. exact Hpending.
        + inversion Hstep; subst. right. left. exact Hpending.
        + inversion Hstep; subst. right. left. exact Hpending.
        + inversion Hstep; subst. right. left. exact Hpending.
        + inversion Hstep; subst. right. left. exact Hpending.
    Qed.

    Lemma roots_guarded_step :
      forall tf roots before after,
        control_history tf
          (R.cfg_state before) (R.cfg_control before) ->
        roots_guarded roots before ->
        R.next_config tf before = Some after -> roots_guarded roots after.
    Proof.
      intros tf roots before after Hhistory Hroots Hstep x Hin.
      destruct (Hroots x Hin)
        as [Hsolved | [Hqueued | [Hpending | Hactive]]].
      - left. eapply next_config_preserves_solved; eauto.
      - destruct (@queued_step_scheduled tf before after x Hqueued Hstep)
          as [Hqueued' | [Hactive' | [[Hsolved' _] _]]].
        + right. left. exact Hqueued'.
        + right. right. right. exact Hactive'.
        + left. exact Hsolved'.
      - destruct (@control_pending_step tf x before after Hpending Hstep)
          as [Hsolved' | [Hpending' | Hactive']];
          [now left |right; right; left; exact Hpending'
           |right; right; right; exact Hactive'].
      - destruct (@active_step_scheduled_or_commit
          tf before after x Hactive Hstep)
          as [Hqueued | [Hactive' | Hcommit]].
        + right. left. exact Hqueued.
        + right. right. right. exact Hactive'.
        + left. destruct Hcommit as
            [st [fr [direct [k [st' [fr'
              [-> [Hset [-> ->]]]]]]]]].
          cbn in Hhistory, Hactive.
          destruct Hactive as [_ | Hactive].
          * eapply set_value_solved;
              [exact Hset |exact (proj1 (proj1 Hhistory))].
          * eapply set_value_solved; [exact Hset |].
            eapply (@continuation_history_active_solved
              tf st k (R.frame_owner fr));
              [exact (proj2 Hhistory) |exact Hactive].
    Qed.

    Record invariant
      (tf : R.ConstraintSystem.system) (roots : list V.t)
      (c : R.config) : Prop := {
      invariant_reachable : Sem.steps tf (R.initial_config roots) c;
      invariant_history :
        control_history tf (R.cfg_state c) (R.cfg_control c);
      invariant_get_consistent :
        control_get_consistent (R.cfg_state c) (R.cfg_control c);
      invariant_aggregate :
        forall target,
          queued (R.cfg_state c) target \/
          control_active target (R.cfg_control c) \/
          aggregate_bounded (R.cfg_state c) target;
      invariant_summaries :
        forall owner,
          Sem.solved (R.cfg_state c) owner ->
          queued (R.cfg_state c) owner \/
          control_active owner (R.cfg_control c) \/
          summary_valid tf (R.cfg_state c) owner;
      invariant_roots : roots_guarded roots c;
    }.

    Lemma initial_aggregate_bounded :
      forall target, aggregate_bounded R.empty_state target.
    Proof.
      intros target. unfold aggregate_bounded, R.aggregate,
        R.lookup_map, R.sigma_value. cbn.
      rewrite ML.lookup_empty, ML.values_empty, ML.lookup_empty.
      cbn. apply DL.leq_refl.
    Qed.

    Lemma initial_invariant :
      forall tf roots, invariant tf roots (R.initial_config roots).
    Proof.
      intros tf roots. constructor.
      - constructor.
      - exact I.
      - exact I.
      - intros target. right. right. apply initial_aggregate_bounded.
      - intros owner [value Hlookup].
        unfold R.semantic_lookup in Hlookup. cbn in Hlookup.
        rewrite ML.lookup_empty, SL.empty_spec in Hlookup. discriminate.
      - apply initial_roots_guarded.
    Qed.

    Lemma invariant_step :
      forall tf roots before after,
        step_spawned before ->
        invariant tf roots before ->
        R.next_config tf before = Some after -> invariant tf roots after.
    Proof.
      intros tf roots before after Hspawn Hinv Hstep.
      pose proof (invariant_reachable Hinv) as Hreachable.
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      pose proof (Termination.reachable_control_ordered Hreachable) as Hordered.
      constructor.
      - eapply Termination.steps_append_one; eauto.
      - eapply next_config_control_history; eauto using invariant_history.
      - eapply next_config_control_get_consistent; eauto using
          invariant_get_consistent, invariant_history.
      - intros target. eapply next_config_aggregate_guarded; eauto using
          invariant_aggregate.
      - intros owner Hsolved. eapply next_config_summary_guarded; eauto using
          invariant_get_consistent, invariant_history, invariant_summaries.
      - eapply roots_guarded_step; eauto using invariant_history,
          invariant_roots.
    Qed.

    Lemma invariant_steps :
      forall tf roots first final,
        invariant tf roots first ->
        Sem.steps tf first final -> spawned_path tf first final -> invariant tf roots final.
    Proof.
      intros tf roots first final Hinv Hsteps. revert Hinv.
      induction Hsteps as [first |first next final Hstep Htail IH]; intros Hinv Hspawn.
      - exact Hinv.
      - apply IH.
        + eapply invariant_step; [|exact Hinv |exact Hstep].
          exact (Hspawn first next (@Sem.StepsRefl tf first) Hstep Htail).
        + intros before after Hprefix Hnext Hsuffix.
          apply (Hspawn before after); [|exact Hnext |exact Hsuffix].
          eapply Sem.StepsStep; eassumption.
    Qed.

    Lemma terminal_invariant :
      forall tf roots final,
        spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
        Sem.terminates_to tf roots final ->
        invariant tf roots (Sem.terminal_config final).
    Proof.
      intros tf roots final Hspawn [Hsteps _]. eapply invariant_steps.
      - apply initial_invariant.
      - exact Hsteps.
      - exact Hspawn.
    Qed.

    Theorem terminal_state_correct :
      forall tf roots final,
        spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
        Sem.terminates_to tf roots final ->
        Sem.correct_final_state tf roots final.
    Proof.
      intros tf roots final Hspawn Hterminates.
      pose proof (@terminal_invariant tf roots final Hspawn Hterminates) as Hinv.
      destruct Hterminates as [_ Hquiet].
      assert (Hnotqueued : forall x, ~ queued final x).
      { intros x. now apply quiescent_not_queued. }
      assert (Haggregate : forall target,
        D.leq (R.aggregate final target) (R.sigma_value final target) = true).
      { intros target. destruct (invariant_aggregate Hinv target)
          as [Hqueued | [Hactive | Hbounded]].
        - contradiction (Hnotqueued target Hqueued).
        - contradiction.
        - exact Hbounded. }
      intros owner Hin.
      assert (Hsolved : Sem.solved final owner).
      { destruct (invariant_roots Hinv owner Hin)
          as [Hsolved | [Hqueued | [Hpending | Hactive]]].
        - exact Hsolved.
        - contradiction (Hnotqueued owner Hqueued).
        - contradiction.
        - contradiction. }
      split; [exact Hsolved |].
      destruct (invariant_summaries Hinv Hsolved)
        as [Hqueued | [Hactive | Hsummary]].
      - contradiction (Hnotqueued owner Hqueued).
      - contradiction.
      - eapply summary_post_solution; eauto.
    Qed.

    Theorem solve_fuel_tracked_correct :
      forall fuel tf roots final,
        spawned_path tf (R.initial_config roots) (Sem.terminal_config final) ->
        R.solve_fuel fuel tf roots = Some final ->
        Sem.correct_final_state tf roots final.
    Proof.
      intros fuel tf roots final Hspawn Hsolve.
      apply terminal_state_correct; [exact Hspawn |].
      exact (@successful_run_terminates_to fuel tf roots final Hsolve).
    Qed.

    Lemma rhs_trace_spawn_closed : forall st body direct reads effects,
      rhs_trace body direct reads effects ->
      reads_agree st reads ->
      forall result, Sem.observes_at (R.sigma_value st) body result ->
      forall target, In target (Sem.observed_spawns result) -> spawned target.
    Proof.
      intros st body direct reads effects Htrace. induction Htrace;
        intros Hagree result [Hobs Hreads] target' Hin;
        inversion Hobs; subst; cbn in *.
      - contradiction.
      - assert (Hvalue : value = value0).
        { pose proof (Hreads target value0 (or_introl eq_refl)) as Hvalue0.
          assert (Hseen : R.sigma_value st target = value).
          { pose proof (@semantic_lookup_solved st target
              (ex_intro _ value (Hagree target value (or_introl eq_refl)))) as Hlookup.
            rewrite (Hagree target value (or_introl eq_refl)) in Hlookup.
            now inversion Hlookup. }
          rewrite Hseen in Hvalue0. symmetry. exact Hvalue0. }
        subst value0. eapply IHHtrace.
        + intros read v Hread. apply Hagree. right. exact Hread.
        + split; [eassumption |].
          intros read v Hread. apply Hreads. right. exact Hread.
        + exact Hin.
      - eapply IHHtrace; [exact Hagree |split; eassumption |exact Hin].
      - destruct Hin as [<- | Hin]; [assumption |].
        eapply IHHtrace; [exact Hagree |split; eassumption |exact Hin].
    Qed.

  End Correctness.

  Lemma numerical_spawned_path tf first final :
    spawned_path (fun _ => True) tf first final.
  Proof. intros before after Hprefix Hstep Hsuffix.
    unfold step_spawned. destruct (R.cfg_control before); try exact I.
    destruct r; exact I.
  Qed.

  Theorem solve_fuel_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> Sem.correct_final_state tf roots final.
  Proof. intros. eapply (@solve_fuel_tracked_correct (fun _ => True));
    [apply numerical_spawned_path |eassumption]. Qed.


  Lemma demanded_steps tf roots demands first final :
    invariant (fun _ => True) tf roots first ->
    roots_guarded demands first -> Sem.steps tf first final -> roots_guarded demands final.
  Proof.
    intros Hinv Hguard Hsteps. revert Hinv Hguard.
    induction Hsteps as [first |first next final Hstep Htail IH]; intros Hinv Hguard.
    - exact Hguard.
    - apply IH.
      + eapply (@invariant_step (fun _ => True)); [|exact Hinv |exact Hstep].
        unfold step_spawned. destruct (R.cfg_control first); try exact I. destruct r; exact I.
      + eapply roots_guarded_step; [exact (invariant_history Hinv) |exact Hguard |exact Hstep].
  Qed.

  Lemma remember_dormant_demanded st target :
    Sem.solved (R.remember_dormant st target) target.
  Proof.
    unfold Sem.solved, Sem.StateSpec.solved, R.semantic_lookup, R.remember_dormant; cbn.
    destruct (M.lookup (R.sigma st) target) as [value |] eqn:Hlookup.
    - now exists value.
    - assert (S.mem target (S.add target (R.dormant_bottom st)) = true) as Hmem
        by (apply SL.add_spec; now left).
      rewrite Hmem. now exists D.bottom.
  Qed.

  Lemma spawn_demanded tf st fr target next k after :
    R.next_config tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} = Some after ->
    roots_guarded [target] after.
  Proof.
    intros Hstep x [<- |Hfalse]; [|contradiction].
    cbn -[R.observe R.is_dormant R.is_materialized R.rank_lt R.materialize
      R.enqueue R.remember_dormant R.pure_bottom_rhs R.Ranking.lookup R.ranking] in Hstep.
    destruct (R.is_dormant st target) eqn:Hdormant.
    - inversion Hstep; subst. left. now apply solved_dormant.
    - destruct (R.Ranking.lookup (R.ranking st) target).
      + destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
        * inversion Hstep; subst. left. now apply materialized_solved.
        * destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
          -- inversion Hstep; subst. right. right. right. now left.
          -- inversion Hstep; subst. left. apply materialize_solved_correctness.
      + destruct (R.pure_bottom_rhs tf target && negb (R.is_materialized st target))%bool.
        * inversion Hstep; subst. left. apply remember_dormant_demanded.
        * destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
          -- inversion Hstep; subst. left. now apply materialized_solved.
          -- destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
             ++ inversion Hstep; subst. right. right. right. now left.
             ++ inversion Hstep; subst. left. apply materialize_solved_correctness.
  Qed.

  Lemma successful_spawned_path tf roots final : Sem.terminates_to tf roots final ->
    spawned_path (Sem.solved final) tf (R.initial_config roots) (Sem.terminal_config final).
  Proof.
    intros [Hrun Hquiet] [st control] after Hprefix Hstep Hsuffix.
    unfold step_spawned; cbn. destruct control; try exact I. destruct r; try exact I.
    assert (Hinv : invariant (fun _ => True) tf roots {|R.cfg_state := st;
      R.cfg_control := R.RunRhs f (R.ConstraintSystem.Spawn t r) c|}).
    { eapply invariant_steps; [apply initial_invariant |exact Hprefix |apply numerical_spawned_path]. }
    assert (Hafter : invariant (fun _ => True) tf roots after).
    { eapply (@invariant_step (fun _ => True)); [|exact Hinv |exact Hstep]. exact I. }
    pose proof (@demanded_steps tf roots [t] after (Sem.terminal_config final)
      Hafter (@spawn_demanded tf st f t r c after Hstep) Hsuffix t (or_introl eq_refl)) as Hguard.
    destruct Hguard as [Hsolved |[Hqueued |[Hpending |Hactive]]]; try contradiction.
    - exact Hsolved.
    - exfalso. exact (@quiescent_not_queued final t Hquiet Hqueued).
  Qed.

  Theorem successful_run_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> Spec.correct_final_state tf roots final.
  Proof.
    intros fuel tf roots final Hrun.
    pose proof (@successful_run_terminates_to fuel tf roots final Hrun) as Hterm.
    pose proof (@terminal_invariant (Sem.solved final) tf roots final
      (successful_spawned_path Hterm) Hterm) as Hinv.
    destruct Hterm as [_ Hquiet].
    assert (Hnotqueued : forall x, ~ queued final x).
    { intros x. now apply quiescent_not_queued. }
    assert (Haggregate : forall target,
      D.leq (R.aggregate final target) (R.sigma_value final target) = true).
    { intros target. destruct (invariant_aggregate Hinv target) as [Hqueued |[Hactive |Hbounded]];
      [contradiction (Hnotqueued target Hqueued) |contradiction |exact Hbounded]. }
    split.
    - intros owner Hin. exact (proj1 (@solve_fuel_correct fuel tf roots final Hrun owner Hin)).
    - intros owner Hsolved.
      destruct (invariant_summaries Hinv Hsolved) as [Hqueued |[Hactive |Hsummary]];
        [contradiction (Hnotqueued owner Hqueued) |contradiction |].
      destruct Hsummary as [Hsolved' [direct [reads [effects [Htrace [Hreads [Heffects Hdirect]]]]]]].
      assert (Hagree : reads_agree final reads) by (eapply guarded_reads_agree; eassumption).
      split.
      + exists direct, reads, effects. exact (rhs_trace_replay Htrace Hagree).
      + split.
        * eapply summary_post_solution; [exact Hquiet |exact Haggregate |].
          split; [exact Hsolved' |]. exists direct, reads, effects. exact (conj Htrace (conj Hreads (conj Heffects Hdirect))).
        * exact (@rhs_trace_spawn_closed (Sem.solved final) final (tf owner) direct reads effects Htrace Hagree).
  Qed.

End Make.

Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Features : DirtyReadRestarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (OSL : ORDINARY_UPDATE_SOUND_LAWS V D U)
  (SSL : SIDE_UPDATE_SOUND_LAWS V D SU)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Include Make V D U SU S M Rk Features Laws DL OSL SSL SL ML.
End FirstDiscovery.

Module FixedRank
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (SU : SIDE_UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed)
  (Features : DirtyReadRestarting.FEATURES)
  (DL : DOMAIN_LAWS D)
  (OSL : ORDINARY_UPDATE_SOUND_LAWS V D U)
  (SSL : SIDE_UPDATE_SOUND_LAWS V D SU)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).
  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Include Make V D U SU S M Rk Features Laws DL OSL SSL SL ML.
End FixedRank.
