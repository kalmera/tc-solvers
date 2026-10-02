From Stdlib Require Import
  Bool List Lia Arith.PeanoNat Sorting.Sorted Sorting.Permutation
  Wellfounded Wf_nat
  Relations.Relation_Operators
  Wellfounded.Inverse_Image
  Wellfounded.Lexicographic_Product
  Wellfounded.List_Extension.
From TcSolvers Require Import
  common.Assumptions
  common.ConstraintSemantics
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.narrowing_fixed_point.Base.

Import ListNotations.
Set Implicit Arguments.

(** Proof-only interpretation of the Restarting machine. *)
Module Semantics.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : Base.FEATURES).

  Module R := Base.Make V D U S M Rk Features.
  Module ConstraintSyntax.
    Definition rhs := R.ConstraintSystem.rhs.
    Definition Ret := R.ConstraintSystem.Ret.
    Definition Get := R.ConstraintSystem.Get.
    Definition Side := R.ConstraintSystem.Side.
    Definition Spawn := R.ConstraintSystem.Spawn.
    Definition system := V.t -> rhs.
  End ConstraintSyntax.
  Module ConstraintSemantics :=
    ConstraintSemantics.Make V D ConstraintSyntax.
  Include ConstraintSemantics.

  Lemma rhs_observes_spawns_supported : forall supported body result,
    rhs_supported supported body -> rhs_observes body result ->
    forall target, List.In target (observed_spawns result) -> supported target.
  Proof.
    intros supported body result Hsupported Hobs. revert Hsupported.
    induction Hobs; intros Hsupported observed Hin;
      inversion Hsupported; subst; cbn in Hin.
    - contradiction.
    - eapply IHHobs; [apply H2 |exact Hin].
    - eapply IHHobs; eassumption.
    - destruct Hin as [<- | Hin]; [exact H1 |].
      eapply IHHobs; eassumption.
  Qed.

  Definition step
    (tf : R.ConstraintSystem.system) (before after : R.config) : Prop :=
    R.next_config tf before = Some after.

  Inductive steps
    (tf : R.ConstraintSystem.system) : R.config -> R.config -> Prop :=
  | StepsRefl : forall c, steps tf c c
  | StepsStep : forall first next final,
      step tf first next ->
      steps tf next final ->
      steps tf first final.

  Definition quiescent (st : R.state) : Prop :=
    R.queue_peek (R.queue st) = None.

  Definition terminal_config (st : R.state) : R.config :=
    {| R.cfg_state := st; R.cfg_control := R.RunLoop |}.

  Definition terminates_to
    (tf : R.ConstraintSystem.system)
    (initial : list V.t) (final : R.state) : Prop :=
    steps tf (R.initial_config initial) (terminal_config final) /\
    quiescent final.

  Lemma observes_at_deterministic : forall values body left right,
    observes_at values body left -> observes_at values body right -> left = right.
  Proof.
    intros values body left right [Hleft Hleftreads]. revert right Hleftreads.
    induction Hleft; intros right Hleftreads [Hright Hrightreads];
      inversion Hright; subst; cbn in *.
    - reflexivity.
    - assert (Heq : value = value0).
      { rewrite (Hleftreads target value (or_introl eq_refl)),
          (Hrightreads target value0 (or_introl eq_refl)). reflexivity. }
      subst value0.
      assert (Htail : result = result0).
      { apply IHHleft.
        - intros observed v Hin. apply Hleftreads. right; exact Hin.
        - split; [exact H2 |].
          intros observed v Hin. apply Hrightreads. right; exact Hin. }
      subst result0. reflexivity.
    - assert (Htail : result = result0) by
        (apply IHHleft; [exact Hleftreads |split; assumption]).
      subst result0. reflexivity.
    - assert (Htail : result = result0) by
        (apply IHHleft; [exact Hleftreads |split; assumption]).
      subst result0. reflexivity.
  Qed.

  Definition solved (st : R.state) (x : V.t) : Prop :=
    exists value, M.lookup (R.sigma st) x = Some value.

  Definition state_valuation (st : R.state) : valuation :=
    R.sigma_value st.

  Definition rhs_eval (st : R.state) :=
    rhs_eval_with (fun target => M.lookup (R.sigma st) target).

  Definition side_effects_below
    (st : R.state) (effects : list (V.t * D.t)) : Prop :=
    forall target value,
      List.In (target, value) effects ->
      D.leq value (R.sigma_value st target) = true.

  (** Numerical replay bounds; public owner_post_solution also requires spawn closure. *)
  Definition rhs_post_solution
    (st : R.state) (owner : V.t)
    (body : R.ConstraintSystem.rhs) : Prop :=
    forall direct reads effects,
      rhs_eval st body direct reads effects ->
      D.leq direct (R.sigma_value st owner) = true /\
      side_effects_below st effects.

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

(** Internal total-correctness proof for the Restarting machine.  The
    reviewer-facing results are re-stated in [solvers.slr.narrowing_fixed_point.Theorems].

    The machine uses an executable
    stable partial-rank policy.  The rank and queue foundation stays in the
    same functor as the Restarting-specific termination argument. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (Features : Base.FEATURES)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Sem := Semantics.Make V D U S M Rk Features.
  Module R := Sem.R.

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

  Lemma rank_extends_with_controlled :
    forall st controlled, rank_extends st (R.with_controlled st controlled).
  Proof. intros. apply rank_extends_same_ranking. reflexivity. Qed.

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

  Lemma rank_valid_with_controlled :
    forall st controlled,
      rank_valid st -> rank_valid (R.with_controlled st controlled).
  Proof. intros st controlled Hvalid. exact Hvalid. Qed.

  Lemma rank_valid_materialize :
    forall st x, rank_valid st -> rank_valid (R.materialize st x).
  Proof.
    intros st x Hvalid. unfold R.materialize.
    destruct (M.lookup (R.sigma st) x); exact Hvalid.
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
  }.

  Lemma empty_state_data_ranked : state_data_ranked R.empty_state.
  Proof.
    constructor; cbn.
    - apply empty_queue_ranked.
    - apply empty_set_table_ranked.
    - apply empty_set_table_ranked.
  Qed.

  Lemma state_data_ranked_preserved :
    forall before after,
      rank_extends before after ->
      R.queue after = R.queue before ->
      R.readers after = R.readers before ->
      R.last_targets after = R.last_targets before ->
      state_data_ranked before -> state_data_ranked after.
  Proof.
    intros before after Hextends Hqueue Hreaders Htargets
      [Hqueue_ranked Hreaders_ranked Htargets_ranked].
    constructor.
    - intros x Hin. apply ranked_extended with before; [exact Hextends |].
      apply Hqueue_ranked. now rewrite <- Hqueue.
    - rewrite Hreaders. now apply set_table_ranked_extended with before.
    - rewrite Htargets. now apply set_table_ranked_extended with before.
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
    - exact Hdata.
  Qed.

  Lemma state_data_ranked_with_queue :
    forall st queue,
      state_data_ranked st ->
      list_ranked st queue ->
      state_data_ranked (R.with_queue st queue).
  Proof.
    intros st queue [Hold Hreaders Htargets] Hqueue.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_enqueue :
    forall st x,
      state_data_ranked st -> ranked st x ->
      state_data_ranked (R.enqueue st x).
  Proof.
    intros st x [Hqueue Hreaders Htargets] Hx.
    constructor; cbn.
    - now apply enqueue_ranked.
    - exact Hreaders.
    - exact Htargets.
  Qed.

  Lemma state_data_ranked_enqueue_all :
    forall st xs,
      state_data_ranked st -> list_ranked st xs ->
      state_data_ranked (R.enqueue_all st xs).
  Proof.
    intros st xs [Hqueue Hreaders Htargets] Hxs.
    constructor; cbn.
    - now apply enqueue_all_ranked.
    - exact Hreaders.
    - exact Htargets.
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
    - exact Hdata.
  Qed.

  Lemma state_data_ranked_with_readers :
    forall st readers,
      state_data_ranked st ->
      set_table_ranked st readers ->
      state_data_ranked (R.with_readers st readers).
  Proof.
    intros st readers [Hqueue Hreaders Htargets] Hnext.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_last_targets :
    forall st targets,
      state_data_ranked st ->
      set_table_ranked st targets ->
      state_data_ranked (R.with_last_targets st targets).
  Proof.
    intros st targets [Hqueue Hreaders Hold] Hnext.
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_sigma :
    forall st sigma,
      state_data_ranked st -> state_data_ranked (R.with_sigma st sigma).
  Proof.
    intros st sigma [Hqueue Hreaders Htargets].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_contributions :
    forall st contributions,
      state_data_ranked st ->
      state_data_ranked (R.with_contributions st contributions).
  Proof.
    intros st contributions [Hqueue Hreaders Htargets].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_cells_and_resets :
    forall st cells resets,
      state_data_ranked st ->
      state_data_ranked (R.with_cells_and_resets st cells resets).
  Proof.
    intros st cells resets [Hqueue Hreaders Htargets].
    constructor; cbn; assumption.
  Qed.

  Lemma state_data_ranked_with_controlled :
    forall st controlled,
      state_data_ranked st ->
      state_data_ranked (R.with_controlled st controlled).
  Proof.
    intros st controlled [Hqueue Hreaders Htargets].
    constructor; cbn; assumption.
  Qed.

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
        | apply rank_valid_with_controlled
        | apply rank_valid_materialize
        | apply rank_valid_enqueue
        | apply rank_valid_enqueue_all
        | eapply rank_valid_observe; [|reflexivity] ];
      try exact Hvalid;
      eauto 5 using rank_valid_continue_side, rank_valid_continue_dead,
        rank_valid_write_side_contribution, rank_valid_set_value,
        rank_valid_observe.
    apply rank_valid_continue_side;
      apply rank_valid_register_reset;
      apply rank_valid_with_contributions;
      apply rank_valid_promote_side_target;
      eapply rank_valid_observe; [exact Hvalid | reflexivity].
    apply rank_valid_continue_dead;
      apply rank_valid_register_reset;
      apply rank_valid_with_contributions;
      apply rank_valid_promote_side_target;
      exact Hvalid.
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
        | eapply rank_extends_trans; [|apply rank_extends_with_controlled]
        | eapply rank_extends_trans; [|apply rank_extends_materialize]
        | eapply rank_extends_trans; [|apply rank_extends_enqueue]
        | eapply rank_extends_trans; [|apply rank_extends_enqueue_all]
        | eapply rank_extends_observe; reflexivity
        | apply rank_extends_refl ];
      eauto 5 using rank_extends_trans, rank_extends_observe,
        rank_extends_write_side_contribution,
        rank_extends_continue_side, rank_extends_continue_dead,
        rank_extends_set_value, rank_extends_reset_registered_cells.
    eapply rank_extends_trans.
    { eapply rank_extends_observe. reflexivity. }
    eapply rank_extends_trans.
    { apply rank_extends_promote_side_target. }
    eapply rank_extends_trans.
    { apply rank_extends_with_contributions. }
    eapply rank_extends_trans.
    { apply rank_extends_register_reset. }
    apply rank_extends_continue_side.
    eapply rank_extends_trans.
    { apply rank_extends_promote_side_target. }
    eapply rank_extends_trans.
    { apply rank_extends_with_contributions. }
    eapply rank_extends_trans.
    { apply rank_extends_register_reset. }
    apply rank_extends_continue_dead.
    all: apply rank_extends_reset_registered_cells.
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
    all: try (apply state_data_ranked_observe; exact Hdata).
    all: try (apply state_data_ranked_materialize; exact Hdata).

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
      | Hcomplete : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_complete_get_after_observe;
          [exact Hdata | exact (proj1 Hcontrol) | exact Hcomplete]
      end.
    all: try (apply state_data_ranked_materialize;
      apply state_data_ranked_enqueue;
      [apply state_data_ranked_observe; exact Hdata
      |eapply observe_ranks_variable; reflexivity]).
    all: try (apply state_data_ranked_publish_targets;
      [exact Hdata | exact (proj1 Hcontrol)]).
    all: try (apply state_data_ranked_reset_registered_cells; exact Hdata).


    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- state_data_ranked ?next =>
          eapply state_data_ranked_set_value; [exact Hdata | exact Hset]
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
    apply state_data_ranked_continue_side.
    { apply state_data_ranked_register_reset.
      apply state_data_ranked_with_contributions.
      apply state_data_ranked_promote_side_target.
      apply state_data_ranked_observe. exact Hdata. }
    eapply ranked_extended.
    { eapply rank_extends_trans.
      { apply rank_extends_promote_side_target. }
      eapply rank_extends_trans.
      { apply rank_extends_with_contributions. }
      apply rank_extends_register_reset. }
    eapply observe_ranks_variable. reflexivity.
    apply state_data_ranked_continue_dead.
    { apply state_data_ranked_register_reset.
      apply state_data_ranked_with_contributions.
      apply state_data_ranked_promote_side_target. exact Hdata. }
    eapply ranked_extended.
    { eapply rank_extends_trans.
      { apply rank_extends_promote_side_target. }
      eapply rank_extends_trans.
      { apply rank_extends_with_contributions. }
      apply rank_extends_register_reset. }
    apply (proj1 (proj2 Hcontrol)). now left.
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
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr),
        Hcontrol0 : frame_ranked ?before ?fr /\ continuation_ranked ?before ?k
        |- frame_ranked ?next ?next_fr /\ continuation_ranked _ ?k =>
          split;
          [change (frame_ranked next next_fr); eapply frame_ranked_set_value;
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
    all: try exact Hcontrol.
    split; [eapply observe_ranks_variable; reflexivity | exact I].
    split; [exact (proj1 Hcontrol) |]; split;
      [intros x Hin; inversion Hin | exact (proj2 Hcontrol)].
    apply control_ranked_continue_side.
    { eapply frame_ranked_write_side_contribution.
      { eapply record_side_input_ranked.
        { eapply frame_ranked_extended;
          [eapply rank_extends_observe; reflexivity |exact (proj1 Hcontrol)]. }
        { eapply observe_ranks_variable. reflexivity. }
        exact Hcase0. }
      exact Hcase1. }
    { eapply ranked_extended.
      { eapply rank_extends_write_side_contribution. exact Hcase1. }
      eapply observe_ranks_variable. reflexivity. }
    eapply continuation_ranked_extended.
    { eapply rank_extends_trans.
      { eapply rank_extends_observe. reflexivity. }
      eapply rank_extends_write_side_contribution. exact Hcase1. }
    exact (proj2 Hcontrol).
    split;
      [eapply frame_ranked_extended;
       [exact Hextends |exact (proj1 Hcontrol)]
      |eapply continuation_ranked_extended;
       [exact Hextends |exact (proj2 (proj2 Hcontrol))]].
    apply control_ranked_continue_dead.
    { eapply frame_ranked_write_side_contribution;
      [exact (proj1 Hcontrol) |exact Hcase1]. }
    { eapply ranked_extended;
      [eapply rank_extends_write_side_contribution; exact Hcase1
      |apply (proj1 (proj2 Hcontrol)); now left]. }
    { eapply list_ranked_extended;
      [eapply rank_extends_write_side_contribution; exact Hcase1
      |intros x Hin; apply (proj1 (proj2 Hcontrol)); now right]. }
    eapply continuation_ranked_extended;
      [eapply rank_extends_write_side_contribution; exact Hcase1
      |exact (proj2 (proj2 Hcontrol))].
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
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- queue_distinct ?next =>
          eapply queue_distinct_set_value; [exact Hdistinct |exact Hset]
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
    eapply queue_distinct_complete_get; [|exact Hcase1].
    destruct (R.is_materialized (R.observe st t) t).
    { apply queue_distinct_observe. exact Hdistinct. }
    apply enqueue_distinct. apply queue_distinct_observe. exact Hdistinct.
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
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- queue_ordered ?next =>
          eapply queue_ordered_set_value;
          [exact Hvalid |exact Hdata |exact Hordered |exact Hset]
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
    eapply queue_ordered_complete_get; [|exact Hcase1].
    destruct (R.is_materialized (R.observe st t) t).
    { apply queue_ordered_observe; [exact Hdata |exact Hordered]. }
    apply enqueue_ordered.
    { eapply rank_valid_observe; [exact Hvalid |reflexivity]. }
    { exact (data_queue_ranked (state_data_ranked_observe t Hdata)). }
    { apply queue_ordered_observe; [exact Hdata |exact Hordered]. }
    eapply observe_ranks_variable. reflexivity.
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

  Definition supported (support : list V.t) (x : V.t) : Prop :=
    List.In x support.

  Definition ranking_generated (support : list V.t) (st : R.state) : Prop :=
    RankFinite.generated support (R.ranking st).

  Definition map_keys_supported {A : Type}
    (support : list V.t) (table : M.t A) : Prop :=
    forall x value, M.lookup table x = Some value -> supported support x.

  Definition set_supported (support : list V.t) (values : S.t) : Prop :=
    forall x, S.mem x values = true -> supported support x.

  Definition queue_supported
    (support : list V.t) (queue : R.work_queue) : Prop :=
    forall x, List.In x queue -> supported support x.

  Definition set_table_supported
    (support : list V.t) (table : M.t S.t) : Prop :=
    map_keys_supported support table /\
    forall outer values inner,
      M.lookup table outer = Some values ->
      S.mem inner values = true ->
      supported support inner.

  Definition frame_supported
    (support : list V.t) (fr : R.frame) : Prop :=
    supported support (R.frame_owner fr) /\
    map_keys_supported support (R.frame_local_side fr) /\
    set_supported support (R.frame_previous_targets fr) /\
    set_supported support (R.frame_current_targets fr) /\
    supported support (R.frame_min_scope fr) /\
    match R.frame_max_read fr with
    | Some x => supported support x
    | None => True
    end.

  Fixpoint continuation_supported
    (support : list V.t) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop => True
    | R.KSeedLoop roots => Forall (supported support) roots
    | R.KAfterGet fr target next rest =>
        frame_supported support fr /\
        supported support target /\
        (forall value, Sem.rhs_supported (supported support) (next value)) /\
        continuation_supported support rest
    | R.KAfterSide fr next rest
    | R.KAfterSpawn fr next rest =>
        frame_supported support fr /\
        Sem.rhs_supported (supported support) next /\
        continuation_supported support rest
    | R.KDead fr _ pending rest =>
        frame_supported support fr /\
        Forall (supported support) pending /\
        continuation_supported support rest
    | R.KDrain fr rest =>
        frame_supported support fr /\ continuation_supported support rest
    end.

  Definition control_supported
    (support : list V.t) (control : R.control) : Prop :=
    match control with
    | R.RunLoop => True
    | R.RunSeeds roots | R.RunSeedLoop roots =>
        Forall (supported support) roots
    | R.StartEpisode owner k =>
        supported support owner /\ continuation_supported support k
    | R.RunRhs fr body k =>
        frame_supported support fr /\
        Sem.rhs_supported (supported support) body /\
        continuation_supported support k
    | R.RunDead fr _ pending k =>
        frame_supported support fr /\
        Forall (supported support) pending /\
        continuation_supported support k
    | R.RunCommit fr _ k | R.RunDrain fr k =>
        frame_supported support fr /\ continuation_supported support k
    | R.Return k => continuation_supported support k
    end.

  Record state_supported (support : list V.t) (st : R.state) : Prop := {
    state_ranking_generated : ranking_generated support st;
    state_queue_supported : queue_supported support (R.queue st);
    state_readers_supported : set_table_supported support (R.readers st);
    state_targets_supported : set_table_supported support (R.last_targets st);
  }.

  Definition config_supported (support : list V.t) (c : R.config) : Prop :=
    state_supported support (R.cfg_state c) /\
    control_supported support (R.cfg_control c).

  Lemma rhs_supported_get_inv :
    forall support target next,
      Sem.rhs_supported support (R.ConstraintSystem.Get target next) ->
      support target /\ forall value, Sem.rhs_supported support (next value).
  Proof. intros. inversion H; subst; auto. Qed.

  Lemma rhs_supported_side_inv :
    forall support target value next,
      Sem.rhs_supported support (R.ConstraintSystem.Side target value next) ->
      support target /\ Sem.rhs_supported support next.
  Proof. intros. inversion H; subst; auto. Qed.

  Lemma rhs_supported_spawn_inv :
    forall support target next,
      Sem.rhs_supported support (R.ConstraintSystem.Spawn target next) ->
      support target /\ Sem.rhs_supported support next.
  Proof. intros. inversion H; subst; auto. Qed.

  Lemma map_keys_supported_empty :
    forall A support, map_keys_supported support (M.empty A).
  Proof.
    intros A support x value Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma map_keys_supported_update :
    forall A support (table : M.t A) x value,
      supported support x ->
      map_keys_supported support table ->
      map_keys_supported support (M.update table x value).
  Proof.
    intros A support table x value Hx Htable observed old Hlookup.
    destruct (V.eq_dec observed x) as [-> |Hneq]; auto.
    rewrite ML.lookup_update_other in Hlookup by exact Hneq.
    now apply (Htable observed old).
  Qed.

  Lemma set_supported_empty :
    forall support, set_supported support S.empty.
  Proof.
    intros support x Hmem. rewrite SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma set_supported_add :
    forall support values x,
      supported support x ->
      set_supported support values ->
      set_supported support (S.add x values).
  Proof.
    intros support values x Hx Hvalues observed Hmem.
    apply SL.add_spec in Hmem. destruct Hmem as [-> |Hmem]; auto.
  Qed.

  Lemma set_elements_supported :
    forall support values,
      set_supported support values ->
      Forall (supported support) (S.elements values).
  Proof.
    intros support values Hvalues. rewrite Forall_forall.
    intros x Hin. apply Hvalues, SL.mem_spec. exact Hin.
  Qed.

  Lemma set_table_supported_empty :
    forall support, set_table_supported support (M.empty S.t).
  Proof.
    intros support. split; [apply map_keys_supported_empty |].
    intros outer values inner Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma lookup_set_supported :
    forall support table outer,
      set_table_supported support table ->
      set_supported support (R.lookup_set table outer).
  Proof.
    intros support table outer [_ Hmembers] inner Hmem.
    unfold R.lookup_set in Hmem.
    destruct (M.lookup table outer) as [values |] eqn:Hlookup.
    - eapply Hmembers; eauto.
    - rewrite SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma set_table_supported_update :
    forall support table outer values,
      supported support outer ->
      set_supported support values ->
      set_table_supported support table ->
      set_table_supported support (M.update table outer values).
  Proof.
    intros support table outer values Houter Hvalues [Hkeys Hmembers].
    split; [now apply map_keys_supported_update |].
    intros key current inner Hlookup Hmem.
    destruct (V.eq_dec key outer) as [-> |Hneq].
    - rewrite ML.lookup_update_same in Hlookup.
      injection Hlookup as ->. now apply Hvalues.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      eapply Hmembers; eauto.
  Qed.

  Lemma queue_supported_insert :
    forall support order x queue,
      supported support x ->
      queue_supported support queue ->
      queue_supported support (R.queue_insert order x queue).
  Proof.
    intros support order x queue Hx Hqueue observed Hin.
    apply queue_insert_members in Hin. destruct Hin as [-> |Hin]; auto.
  Qed.

  Lemma queue_supported_insert_all :
    forall support order xs queue,
      Forall (supported support) xs ->
      queue_supported support queue ->
      queue_supported support (R.queue_insert_all order xs queue).
  Proof.
    intros support order xs queue Hxs Hqueue observed Hin.
    apply queue_insert_all_members in Hin. destruct Hin as [Hin |Hin].
    - now apply (proj1 (Forall_forall _ _) Hxs).
    - now apply Hqueue.
  Qed.

  Lemma queue_supported_pop :
    forall support queue owner rest,
      queue_supported support queue ->
      R.queue_pop queue = Some (owner, rest) ->
      supported support owner /\ queue_supported support rest.
  Proof.
    intros support [|head tail] owner rest Hqueue Hpop;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. split.
    - apply Hqueue. now left.
    - intros x Hin. apply Hqueue. now right.
  Qed.

  Lemma empty_state_supported :
    forall support, state_supported support R.empty_state.
  Proof.
    intros support. constructor; cbn.
    - apply RankFinite.generated_empty.
    - intros x Hin. contradiction.
    - apply set_table_supported_empty.
    - apply set_table_supported_empty.
  Qed.

  Lemma initial_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots),
      config_supported (Sem.support finite) (R.initial_config roots).
  Proof.
    intros tf roots finite. split; cbn.
    - apply empty_state_supported.
    - rewrite Forall_forall. exact (Sem.initial_supported finite).
  Qed.

  Lemma state_supported_core_view :
    forall support before after,
      state_supported support before ->
      R.ranking after = R.ranking before ->
      R.queue after = R.queue before ->
      R.readers after = R.readers before ->
      R.last_targets after = R.last_targets before ->
      state_supported support after.
  Proof.
    intros support before after Hbefore Hranking Hqueue Hreaders Htargets.
    destruct Hbefore. constructor.
    - unfold ranking_generated in *. now rewrite Hranking.
    - now rewrite Hqueue.
    - now rewrite Hreaders.
    - now rewrite Htargets.
  Qed.

  Lemma state_supported_with_queue :
    forall support st queue,
      state_supported support st ->
      queue_supported support queue ->
      state_supported support (R.with_queue st queue).
  Proof.
    intros support st queue Hstate Hqueue. destruct Hstate.
    constructor; cbn; assumption.
  Qed.

  Lemma state_supported_with_readers :
    forall support st readers,
      state_supported support st ->
      set_table_supported support readers ->
      state_supported support (R.with_readers st readers).
  Proof.
    intros support st readers Hstate Hreaders. destruct Hstate.
    constructor; cbn; assumption.
  Qed.

  Lemma state_supported_with_last_targets :
    forall support st targets,
      state_supported support st ->
      set_table_supported support targets ->
      state_supported support (R.with_last_targets st targets).
  Proof.
    intros support st targets Hstate Htargets. destruct Hstate.
    constructor; cbn; assumption.
  Qed.

  Lemma state_supported_observe :
    forall support st x,
      supported support x ->
      state_supported support st ->
      state_supported support (R.observe st x).
  Proof.
    intros support st x Hx Hstate. unfold R.observe.
    destruct (R.Ranking.observe (R.ranking st) x)
      as [ranking rank] eqn:Hobserve.
    destruct Hstate. constructor; cbn; try assumption.
    unfold ranking_generated in *.
    eapply RankFinite.generated_observe; eauto.
  Qed.

  Lemma state_supported_materialize :
    forall support st x,
      state_supported support st ->
      state_supported support (R.materialize st x).
  Proof.
    intros support st x Hstate. unfold R.materialize.
    destruct (M.lookup (R.sigma st) x); [exact Hstate |].
    eapply state_supported_core_view; eauto; reflexivity.
  Qed.

  Lemma state_supported_promote_controlled :
    forall support st x,
      state_supported support st ->
      state_supported support (R.promote_controlled st x).
  Proof.
    intros support st x Hstate.
    eapply state_supported_core_view; eauto; reflexivity.
  Qed.

  Lemma state_supported_promote_side_target :
    forall support st fr target,
      state_supported support st ->
      state_supported support (R.promote_side_target st fr target).
  Proof.
    intros support st fr target Hstate.
    unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr));
      auto using state_supported_promote_controlled.
  Qed.

  Lemma state_supported_register_reset :
    forall support st source target scope phase,
      state_supported support st ->
      state_supported support
        (R.register_reset st source target scope phase).
  Proof.
    intros support st source target scope phase Hstate.
    unfold R.register_reset.
    repeat match goal with
      | |- context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | |- context [match ?value with _ => _ end] =>
          destruct value eqn:?
      end;
      eapply state_supported_core_view; eauto; reflexivity.
  Qed.

  Lemma state_supported_enqueue :
    forall support st x,
      supported support x ->
      state_supported support st ->
      state_supported support (R.enqueue st x).
  Proof.
    intros support st x Hx Hstate. apply state_supported_with_queue.
    - exact Hstate.
    - apply queue_supported_insert; [exact Hx |].
      exact (state_queue_supported Hstate).
  Qed.

  Lemma state_supported_enqueue_all :
    forall support st xs,
      Forall (supported support) xs ->
      state_supported support st ->
      state_supported support (R.enqueue_all st xs).
  Proof.
    intros support st xs Hxs Hstate. apply state_supported_with_queue.
    - exact Hstate.
    - apply queue_supported_insert_all; [exact Hxs |].
      exact (state_queue_supported Hstate).
  Qed.

  Lemma frame_supported_with_phase :
    forall support fr phase,
      frame_supported support fr ->
      frame_supported support (R.with_frame_phase fr phase).
  Proof.
    intros support fr phase Hfr. unfold frame_supported in *.
    cbn. tauto.
  Qed.

  Lemma frame_supported_with_read :
    forall support fr minimum maximum,
      frame_supported support fr ->
      supported support minimum ->
      option_rect (fun _ => Prop) (supported support) True maximum ->
      frame_supported support (R.with_frame_read fr minimum maximum).
  Proof.
    intros support fr minimum [maximum |] Hfr Hminimum Hmaximum;
      unfold frame_supported in *; cbn in *; tauto.
  Qed.

  Lemma frame_supported_with_side :
    forall support fr target input,
      frame_supported support fr ->
      supported support target ->
      frame_supported support (R.with_frame_side fr target input).
  Proof.
    intros support fr target input
      [Howner [Hlocal [Hprevious [Hcurrent [Hminimum Hmaximum]]]]] Htarget.
    repeat split; cbn; auto using map_keys_supported_update,
      set_supported_add.
  Qed.

  Lemma fresh_frame_supported :
    forall support st owner phase,
      supported support owner ->
      state_supported support st ->
      frame_supported support (R.fresh_frame st owner phase).
  Proof.
    intros support st owner phase Howner Hstate.
    repeat split; cbn; auto using map_keys_supported_empty,
      set_supported_empty.
    now apply lookup_set_supported, state_targets_supported.
  Qed.

  Lemma record_side_input_supported :
    forall support fr target raw,
      frame_supported support fr ->
      supported support target ->
      frame_supported support (fst (R.record_side_input fr target raw)).
  Proof.
    intros support fr target raw Hfr Htarget.
    unfold R.record_side_input. now apply frame_supported_with_side.
  Qed.

  Lemma state_supported_complete_get :
    forall support st fr target next next_fr value,
      state_supported support st ->
      frame_supported support fr ->
      supported support target ->
      R.complete_get st fr target = (next, next_fr, value) ->
      state_supported support next /\ frame_supported support next_fr.
  Proof.
    intros support st fr target next next_fr value Hstate Hfr Htarget Hget.
    pose proof (proj1 Hfr) as Howner.
    destruct Hfr as
      [Howner0 [Hlocal [Hprevious_targets [Hcurrent [Hmin Hmax]]]]].
    assert (Hfr : frame_supported support fr) by
      (repeat split; assumption).
    unfold R.complete_get in Hget.
    destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Howner_target;
      destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hminimum;
      destruct (R.frame_max_read fr) as [previous |] eqn:Hmaximum;
      try destruct (R.rank_lt st previous target) eqn:Hprevious;
      inversion Hget; subst; clear Hget; split.
    all: try (apply state_supported_materialize;
      apply state_supported_with_readers;
      [apply state_supported_promote_controlled; exact Hstate |];
      apply set_table_supported_update;
      [exact Htarget |apply set_supported_add;
       [exact Howner |apply lookup_set_supported;
        exact (state_readers_supported Hstate)]
      |exact (state_readers_supported Hstate)]).
    all: try (apply state_supported_materialize;
      apply state_supported_with_readers;
      [exact Hstate |];
      apply set_table_supported_update;
      [exact Htarget |apply set_supported_add;
       [exact Howner |apply lookup_set_supported;
        exact (state_readers_supported Hstate)]
      |exact (state_readers_supported Hstate)]).
    all: apply frame_supported_with_read; try exact Hfr; cbn;
      try exact Htarget; assumption.
  Qed.

  Lemma state_supported_write_side_contribution :
    forall support st fr target input next changed,
      state_supported support st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      state_supported support next.
  Proof.
    intros support st fr target input next changed Hstate Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted.
    destruct (U.update true target
      (R.side_phase
        (R.stored_side_cell promoted (R.frame_owner fr) target))
      (R.stored_contribution promoted (R.frame_owner fr) target)
      input) as [phase contribution] eqn:Hupdate.
    inversion Hwrite; subst; clear Hwrite.
    apply state_supported_register_reset.
    eapply state_supported_core_view with
      (before := R.promote_side_target st fr target).
    - now apply state_supported_promote_side_target.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma state_supported_publish_targets :
    forall support st fr,
      state_supported support st ->
      frame_supported support fr ->
      state_supported support (R.publish_targets st fr).
  Proof.
    intros support st fr Hstate Hfr. unfold R.publish_targets.
    apply state_supported_with_last_targets; [exact Hstate |].
    apply set_table_supported_update.
    - exact (proj1 Hfr).
    - exact (proj1 (proj2 (proj2 (proj2 Hfr)))).
    - exact (state_targets_supported Hstate).
  Qed.

  Lemma state_supported_set_value :
    forall support st fr direct next next_fr,
      state_supported support st ->
      frame_supported support fr ->
      R.set_value st fr direct = (next, next_fr) ->
      state_supported support next.
  Proof.
    intros support st fr direct next next_fr Hstate Hfr Hset.
    unfold R.set_value in Hset.
    repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn; try exact Hstate.
    all: apply state_supported_with_readers.
    all: try (apply state_supported_enqueue_all;
      [apply set_elements_supported; apply lookup_set_supported;
       exact (state_readers_supported Hstate)
      |eapply state_supported_core_view; eauto; reflexivity]).
    all: apply set_table_supported_update.
    all: try exact (proj1 Hfr).
    all: try apply set_supported_empty.
    all: exact (state_readers_supported Hstate).
  Qed.

  Lemma frame_supported_set_value :
    forall support st fr direct next next_fr,
      frame_supported support fr ->
      R.set_value st fr direct = (next, next_fr) ->
      frame_supported support next_fr.
  Proof.
    intros support st fr direct next next_fr Hfr Hset.
    unfold R.set_value in Hset.
    repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end;
      inversion Hset; subst; cbn;
      auto using frame_supported_with_phase.
  Qed.

  Lemma state_supported_reset_registered_cells :
    forall support st owner,
      state_supported support st ->
      state_supported support (R.reset_registered_cells st owner).
  Proof.
    intros support st owner Hstate.
    unfold R.reset_registered_cells.
    destruct Features.restart_side_phases;
      [eapply state_supported_core_view; eauto; reflexivity |exact Hstate].
  Qed.

  Lemma state_supported_continue_side :
    forall support st fr target body k changed,
      state_supported support st ->
      supported support target ->
      state_supported support
        (R.cfg_state (R.continue_side st fr target body k changed)).
  Proof.
    intros support st fr target body k changed Hstate Htarget.
    unfold R.continue_side.
    repeat match goal with
      | |- context [if ?condition then _ else _] => destruct condition
      end; cbn; auto using state_supported_enqueue.
  Qed.

  Lemma control_supported_continue_side :
    forall support st fr target body k changed,
      frame_supported support fr ->
      supported support target ->
      Sem.rhs_supported (supported support) body ->
      continuation_supported support k ->
      control_supported support
        (R.cfg_control (R.continue_side st fr target body k changed)).
  Proof.
    intros support st fr target body k changed Hfr Htarget Hbody Hk.
    destruct changed eqn:Hchanged.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))) eqn:Hcondition;
        unfold R.continue_side; rewrite Hcondition; cbn; tauto.
    - unfold R.continue_side. cbn. tauto.
  Qed.

  Lemma state_supported_continue_dead :
    forall support st fr direct target remaining k changed,
      state_supported support st ->
      supported support target ->
      state_supported support
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros support st fr direct target remaining k changed Hstate Htarget.
    unfold R.continue_dead.
    repeat match goal with
      | |- context [if ?condition then _ else _] => destruct condition
      end; cbn; auto using state_supported_enqueue.
  Qed.

  Lemma control_supported_continue_dead :
    forall support st fr direct target remaining k changed,
      frame_supported support fr ->
      supported support target ->
      Forall (supported support) remaining ->
      continuation_supported support k ->
      control_supported support
        (R.cfg_control
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros support st fr direct target remaining k changed
      Hfr Htarget Hremaining Hk.
    destruct changed eqn:Hchanged.
    - destruct (andb (R.rank_lt st (R.frame_owner fr) target)
        (negb (R.is_materialized st target))) eqn:Hcondition;
        unfold R.continue_dead; rewrite Hcondition; cbn; tauto.
    - unfold R.continue_dead. cbn. tauto.
  Qed.

  Lemma state_supported_add_reader_materialize :
    forall support st readers fr target,
      state_supported support st ->
      set_table_supported support readers ->
      frame_supported support fr ->
      supported support target ->
      state_supported support
        (R.materialize
          (R.with_readers st
            (M.update readers target
              (S.add (R.frame_owner fr)
                (R.lookup_set readers target))))
          target).
  Proof.
    intros support st readers fr target Hstate Hreaders Hfr Htarget.
    apply state_supported_materialize.
    apply state_supported_with_readers; [exact Hstate |].
    apply set_table_supported_update.
    - exact Htarget.
    - apply set_supported_add.
      + exact (proj1 Hfr).
      + now apply lookup_set_supported.
    - exact Hreaders.
  Qed.

  Lemma next_config_state_supported :
    forall tf support before after,
      config_supported support before ->
      R.next_config tf before = Some after ->
      state_supported support (R.cfg_state after).
  Proof.
    intros tf support [st control] after [Hstate Hcontrol] Hstep.
    cbn in Hstep. destruct control; cbn in Hstep, Hcontrol;
      repeat match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hstate.
    all: try (apply state_supported_observe;
      [inversion Hcontrol; assumption |exact Hstate]).
    all: try (apply state_supported_materialize; exact Hstate).

    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?rest)
        |- state_supported ?support (R.with_queue ?before ?rest) =>
          apply state_supported_with_queue;
          [exact Hstate |exact (proj2
            (queue_supported_pop (state_queue_supported Hstate) Hpop))]
      end.

    all: try match goal with
      | Hget : R.complete_get ?before ?fr ?target =
          (?next, ?next_fr, ?value)
        |- state_supported ?support ?next =>
          eapply (proj1 (state_supported_complete_get
            Hstate (proj1 Hcontrol) _ Hget));
          [inversion Hcontrol; subst; assumption]
      end.

    all: try match goal with
      | Hget : R.complete_get
          (if R.is_materialized (R.observe ?before ?target) ?target
           then R.observe ?before ?target
           else R.enqueue (R.observe ?before ?target) ?target)
          ?fr ?target = (?next, ?next_fr, ?value)
        |- state_supported ?support ?next =>
          assert (Htarget : supported support target) by
            (destruct Hcontrol as [_ [Hbody _]];
             exact (proj1 (rhs_supported_get_inv Hbody)));
          eapply (proj1 (state_supported_complete_get
            _ (proj1 Hcontrol) Htarget Hget));
          destruct (R.is_materialized (R.observe before target) target);
          [apply state_supported_observe |apply state_supported_enqueue];
          auto using state_supported_observe
      end.

    all: try match goal with
      | Hwrite : R.write_side_contribution (R.observe ?before ?target)
          ?recorded ?target ?input = (?next, ?changed)
        |- state_supported ?support
          (R.cfg_state
            (R.continue_side ?next ?recorded ?target ?body ?k ?changed)) =>
          assert (Htarget : supported support target) by
            (destruct Hcontrol as [_ [Hrhs _]];
             exact (proj1 (rhs_supported_side_inv Hrhs)));
          apply state_supported_continue_side; [|exact Htarget];
          eapply state_supported_write_side_contribution; [|exact Hwrite];
          now apply state_supported_observe
      end.

    all: try match goal with
      | Hwrite : R.write_side_contribution ?before ?fr ?target D.bottom =
          (?next, ?changed)
        |- state_supported ?support
          (R.cfg_state
            (R.continue_dead ?next ?fr ?direct ?target ?rest ?k ?changed)) =>
          pose proof (proj1 (proj2 Hcontrol)) as Hpending;
          inversion Hpending; subst;
          apply state_supported_continue_dead; [|assumption];
          eapply state_supported_write_side_contribution; eauto
      end.
    all: try (apply state_supported_publish_targets;
      [exact Hstate |exact (proj1 Hcontrol)]).


    all: try match goal with
      | Hset : R.set_value ?before ?fr ?direct = (?next, ?next_fr)
        |- state_supported ?support ?next =>
          eapply state_supported_set_value;
          [exact Hstate |exact (proj1 Hcontrol) |exact Hset]
      end.
    all: try (apply state_supported_reset_registered_cells; exact Hstate).
    all: try (apply state_supported_materialize;
      apply state_supported_enqueue;
      [destruct Hcontrol as [_ [Hbody _]];
       exact (proj1 (rhs_supported_spawn_inv Hbody))
      |apply state_supported_observe;
       [destruct Hcontrol as [_ [Hbody _]];
        exact (proj1 (rhs_supported_spawn_inv Hbody))
       |exact Hstate]]).
    all: try assert (Htarget : supported support t) by
      first
        [destruct Hcontrol as [_ [Hbody _]];
         exact (proj1 (rhs_supported_get_inv Hbody))
        |destruct Hcontrol as [_ [Hbody _]];
         exact (proj1 (rhs_supported_spawn_inv Hbody))
        |exact (proj1 (proj2 Hcontrol))].
    all: try (apply state_supported_observe; [exact Htarget |exact Hstate]).

    all: try match goal with
      | |- state_supported ?support
          (R.materialize
            (R.with_readers ?base
              (M.update ?old_readers ?target
                (S.add (R.frame_owner ?fr)
                  (R.lookup_set ?old_readers ?target)))) ?target) =>
          assert (Hbase : state_supported support base) by
            first
              [exact Hstate
              |apply state_supported_observe; [exact Htarget |exact Hstate]
              |apply state_supported_enqueue;
               [exact Htarget |apply state_supported_observe;
                [exact Htarget |exact Hstate]]
              |apply state_supported_promote_controlled;
               apply state_supported_observe;
               [exact Htarget |exact Hstate]
              |apply state_supported_promote_controlled;
               apply state_supported_enqueue;
               [exact Htarget |apply state_supported_observe;
                [exact Htarget |exact Hstate]]];
          assert (Hreaders : set_table_supported support old_readers) by
            first
              [exact (state_readers_supported Hstate)
              |exact (state_readers_supported
                (@state_supported_observe support st target Htarget Hstate))];
          eapply state_supported_add_reader_materialize;
          [exact Hbase |exact Hreaders |exact (proj1 Hcontrol) |exact Htarget]
      end.
    all: try (eapply state_supported_add_reader_materialize;
      [apply state_supported_promote_controlled; exact Hstate
      |exact (state_readers_supported Hstate)
      |exact (proj1 Hcontrol)
      |exact Htarget]).
    all: try match type of Hcontrol with
      | frame_supported ?support0 ?fr0 /\
          Sem.rhs_supported (supported ?support0)
            (R.ConstraintSystem.Side ?target ?raw ?body) /\ _ =>
          assert (Htarget0 : supported support0 target) by
            (destruct Hcontrol as [_ [Hrhs _]];
             exact (proj1 (rhs_supported_side_inv Hrhs)));
          apply state_supported_continue_side; [|exact Htarget0];
          eapply state_supported_write_side_contribution with
            (st := R.observe st target)
            (fr := R.with_frame_side fr0 target
              (R.accumulated_side_input fr0 target raw));
          [apply state_supported_observe; [exact Htarget0 |exact Hstate]
          |reflexivity]
      end.

    all: try match goal with
      | |- state_supported ?support
          (R.cfg_state
            (R.continue_dead ?next ?frame0 ?direct ?target0 ?rest ?k ?changed)) =>
          pose proof (proj1 (proj2 Hcontrol)) as Hpending;
          inversion Hpending; subst;
          apply state_supported_continue_dead; [|assumption];
          eapply state_supported_write_side_contribution with
            (st := st) (fr := frame0);
          [exact Hstate |reflexivity]
      end.
  Qed.

  Lemma next_config_control_supported :
    forall tf support before after,
      (forall owner,
        supported support owner ->
        Sem.rhs_supported (supported support) (tf owner)) ->
      config_supported support before ->
      R.next_config tf before = Some after ->
      control_supported support (R.cfg_control after).
  Proof.
    intros tf support [st control] after Htf [Hstate Hcontrol] Hstep.
    pose proof (@next_config_state_supported tf support
      {| R.cfg_state := st; R.cfg_control := control |} after
      (conj Hstate Hcontrol) Hstep) as Hstate_after.
    cbn -[R.complete_get R.write_side_contribution R.set_value
      R.continue_side R.continue_dead R.fresh_frame
      R.materialize R.publish_targets R.reset_registered_cells] in Hstep.
    destruct control;
      cbn -[R.complete_get R.write_side_contribution R.set_value
        R.continue_side R.continue_dead R.fresh_frame
        R.materialize R.publish_targets R.reset_registered_cells] in Hstep;
      cbn in Hcontrol;
      repeat match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact I; try tauto.

    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?owner, ?rest)
        |- supported ?support ?owner /\ True =>
          split;
          [exact (proj1
            (queue_supported_pop (state_queue_supported Hstate) Hpop))
          |exact I]
      end.

    all: try match goal with
      | Hroots : Forall (supported ?support) (?root :: ?remaining)
        |- supported ?support ?root /\
           continuation_supported ?support (R.KSeedLoop ?remaining) =>
          inversion Hroots; subst; cbn; tauto
      end.

    all: try match goal with
      | Howner : supported ?support ?owner /\
          continuation_supported ?support ?k
        |- frame_supported ?support
             (R.fresh_frame (R.materialize ?st ?owner) ?owner ?phase) /\
           Sem.rhs_supported (supported ?support) (?system ?owner) /\
           continuation_supported ?support ?k =>
          destruct Howner as [Howner Hk]; repeat split;
          [apply fresh_frame_supported;
           [exact Howner |apply state_supported_materialize; exact Hstate]
          |now apply Htf
          |exact Hk]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Ret ?direct) /\
          continuation_supported ?support ?k
        |- frame_supported ?support ?fr /\
           Forall (supported ?support)
             (S.elements (R.frame_previous_targets ?fr)) /\
           continuation_supported ?support ?k =>
          repeat split;
          [exact (proj1 Hcontrol0)
          |apply set_elements_supported;
           exact (proj1 (proj2 (proj2 (proj1 Hcontrol0))))
          |exact (proj2 (proj2 Hcontrol0))]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Get ?target ?next) /\
          continuation_supported ?support ?k
        |- supported ?support ?target /\
           frame_supported ?support ?fr /\
           supported ?support ?target /\
           (forall value, Sem.rhs_supported (supported ?support) (?next value)) /\
           continuation_supported ?support ?k =>
          pose proof (rhs_supported_get_inv (proj1 (proj2 Hcontrol0)))
            as [Htarget Hnext]; tauto
      end.

    all: try match goal with
      | Hget : R.complete_get ?before ?fr ?target =
          (?next_st, ?next_fr, ?value),
        Hcontrol0 : frame_supported ?support ?fr /\ _ /\ _
        |- frame_supported ?support ?next_fr /\ _ =>
          split;
          [eapply (proj2 (state_supported_complete_get
             _ (proj1 Hcontrol0) _ Hget));
           first
             [exact (proj1 (rhs_supported_get_inv
                (proj1 (proj2 Hcontrol0))))
             |exact (proj1 (proj2 Hcontrol0))]
          |]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Get ?target ?next) /\
          continuation_supported ?support ?k
        |- Sem.rhs_supported (supported ?support) (?next ?value) /\
           continuation_supported ?support ?k =>
          pose proof (rhs_supported_get_inv (proj1 (proj2 Hcontrol0)))
            as [_ Hnext]; split; [apply Hnext |exact (proj2 (proj2 Hcontrol0))]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Side ?target ?raw ?body) /\
          continuation_supported ?support ?k,
        Hrecord : R.record_side_input ?fr ?target ?raw = (?recorded, ?input),
        Hwrite : R.write_side_contribution (R.observe ?st ?target)
          ?recorded ?target ?input = (?next_st, ?changed)
        |- control_supported ?support
          (R.cfg_control
            (R.continue_side ?next_st ?recorded ?target ?body ?k ?changed)) =>
          pose proof (rhs_supported_side_inv (proj1 (proj2 Hcontrol0)))
            as [Htarget Hbody];
          apply control_supported_continue_side;
          [rewrite <- Hrecord; now apply record_side_input_supported
          |exact Htarget |exact Hbody |exact (proj2 (proj2 Hcontrol0))]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Spawn ?target ?body) /\
          continuation_supported ?support ?k
        |- _ =>
          pose proof (rhs_supported_spawn_inv (proj1 (proj2 Hcontrol0)))
            as [Htarget Hbody]
      end.
    all: try tauto.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Forall (supported ?support) (?target :: ?remaining) /\
          continuation_supported ?support ?k,
        Hwrite : R.write_side_contribution ?st ?fr ?target D.bottom =
          (?next_st, ?changed)
        |- control_supported ?support
          (R.cfg_control
            (R.continue_dead ?next_st ?fr ?direct
              ?target ?remaining ?k ?changed)) =>
          pose proof (proj1 (proj2 Hcontrol0)) as Hpending;
          inversion Hpending as [|? ? Htarget Hremaining];
          apply control_supported_continue_dead;
          [exact (proj1 Hcontrol0)
          |exact Htarget |exact Hremaining |exact (proj2 (proj2 Hcontrol0))]
      end.

    all: try match goal with
      | Hset : R.set_value ?st ?fr ?direct = (?next_st, ?next_fr),
        Hcontrol0 : frame_supported ?support ?fr /\
          continuation_supported ?support ?k
        |- frame_supported ?support ?next_fr /\
           continuation_supported ?support ?k =>
          split; [eapply frame_supported_set_value; eauto |tauto]
      end.

    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?st) = Some (?owner, ?rest),
        Hcontrol0 : frame_supported ?support ?fr /\
          continuation_supported ?support ?k
        |- supported ?support ?owner /\
           frame_supported ?support ?fr /\
           continuation_supported ?support ?k =>
          pose proof (queue_supported_pop
            (state_queue_supported Hstate) Hpop) as [Howner _]; tauto
      end.
    all: try exact Hcontrol.
    all: try tauto.
    all: try (inversion Hcontrol; subst; tauto).

    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?st0) = Some (?owner, ?rest)
        |- supported ?support ?owner /\ _ =>
          pose proof (queue_supported_pop
            (state_queue_supported Hstate) Hpop) as [Howner Hrest];
          split; [exact Howner |assumption]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Forall _ (?x :: ?xs) /\ continuation_supported ?support ?k
        |- frame_supported ?support ?fr /\
           Forall _ ?xs /\ continuation_supported ?support ?k =>
          destruct Hcontrol0 as [Hfr [Hxs Hk]];
          inversion Hxs; subst; tauto
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          continuation_supported ?support ?k,
        Hpeek : R.queue_peek (R.queue ?st0) = Some ?peek,
        Hpop : R.queue_pop (R.queue ?st0) = Some (?head, ?rest)
        |- supported ?support ?peek /\ frame_supported ?support ?fr /\
           continuation_supported ?support ?k =>
          assert (Hsame : peek = head) by
            (eapply queue_peek_pop_same; eauto);
          subst peek;
          pose proof (queue_supported_pop
            (state_queue_supported Hstate) Hpop) as [Hhead Hrest];
          tauto
      end.

    all: try match goal with
      | Hcontrol0 : supported ?support ?owner /\
          continuation_supported ?support ?k
        |- frame_supported ?support
             (R.fresh_frame ?st0 ?owner ?phase) /\
           Sem.rhs_supported (supported ?support) (?system ?owner) /\
           continuation_supported ?support ?k =>
          destruct Hcontrol0 as [Howner Hk]; split;
          [apply fresh_frame_supported;
           [exact Howner |exact Hstate_after]
          |split; [apply Htf; exact Howner |exact Hk]]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Ret ?value) /\
          continuation_supported ?support ?k
        |- frame_supported ?support ?fr /\
           Forall (supported ?support)
             (S.elements (R.frame_previous_targets ?fr)) /\
           continuation_supported ?support ?k =>
          destruct Hcontrol0 as [Hfr [_ Hk]]; split; [exact Hfr |];
          split;
          [apply set_elements_supported;
           exact (proj1 (proj2 (proj2 Hfr)))
          |exact Hk]
      end.
    all: try tauto.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Side ?target ?raw ?body) /\
          continuation_supported ?support ?k
        |- control_supported ?support
          (R.cfg_control
            (R.continue_side ?next_st
              (R.with_frame_side ?fr ?target
                (R.accumulated_side_input ?fr ?target ?raw))
              ?target ?body ?k ?changed)) =>
          destruct Hcontrol0 as [Hfr [Hrhs Hk]];
          pose proof (rhs_supported_side_inv Hrhs) as [Htarget Hbody];
          apply control_supported_continue_side;
          [apply frame_supported_with_side; assumption
          |exact Htarget |exact Hbody |exact Hk]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          continuation_supported ?support ?k
        |- frame_supported ?support
             (R.fresh_frame ?st0 (R.frame_owner ?fr) ?phase) /\
           Sem.rhs_supported (supported ?support)
             (?system (R.frame_owner ?fr)) /\
           continuation_supported ?support ?k =>
          destruct Hcontrol0 as [Hfr Hk]; split;
          [apply fresh_frame_supported;
           [exact (proj1 Hfr) |exact Hstate_after]
          |split; [apply Htf; exact (proj1 Hfr) |exact Hk]]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          supported ?support ?target /\
          (forall value,
            Sem.rhs_supported (supported ?support) (?next value)) /\
          continuation_supported ?support ?k
        |- Sem.rhs_supported (supported ?support) (?next ?value) /\
           continuation_supported ?support ?k =>
          destruct Hcontrol0 as [_ [_ [Hnext Hk]]];
          split; [apply Hnext |exact Hk]
      end.
    Unshelve.
    all: try exact Hstate.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Get ?target ?next) /\ _
        |- supported ?support ?target =>
          exact (proj1
            (rhs_supported_get_inv (proj1 (proj2 Hcontrol0))))
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Get ?target ?next) /\ _,
        Hstate0 : state_supported ?support ?st0
        |- state_supported ?support
          (if R.is_materialized (R.observe ?st0 ?target) ?target
           then R.observe ?st0 ?target
           else R.enqueue (R.observe ?st0 ?target) ?target) =>
          pose proof
            (rhs_supported_get_inv (proj1 (proj2 Hcontrol0)))
            as [Htarget _];
          destruct (R.is_materialized (R.observe st0 target) target);
          cbn;
          [apply state_supported_observe; assumption
          |apply state_supported_enqueue;
           [exact Htarget |apply state_supported_observe; assumption]]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          Sem.rhs_supported (supported ?support)
            (R.ConstraintSystem.Ret ?value) /\
          continuation_supported ?support ?k
        |- frame_supported ?support ?fr /\
           Forall (supported ?support) [] /\
           continuation_supported ?support ?k =>
          destruct Hcontrol0 as [Hfr [_ Hk]];
          split; [exact Hfr |split; [constructor |exact Hk]]
      end.

    all: try match goal with
      | Hcontrol0 : frame_supported ?support ?fr /\
          supported ?support ?target /\ _
        |- supported ?support ?target =>
          exact (proj1 (proj2 Hcontrol0))
      end.
    all: tauto.
  Qed.

  Theorem next_config_supported :
    forall tf support before after,
      (forall owner,
        supported support owner ->
        Sem.rhs_supported (supported support) (tf owner)) ->
      config_supported support before ->
      R.next_config tf before = Some after ->
      config_supported support after.
  Proof.
    intros tf support before after Htf Hsupported Hstep. split.
    - eapply next_config_state_supported; eauto.
    - eapply next_config_control_supported; eauto.
  Qed.

  Lemma steps_supported :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      config_supported (Sem.support finite) before ->
      Sem.steps tf before after ->
      config_supported (Sem.support finite) after.
  Proof.
    intros tf roots finite before after Hsupported Hsteps.
    induction Hsteps.
    - exact Hsupported.
    - apply IHHsteps. eapply next_config_supported; eauto.
      exact (Sem.system_supported finite).
  Qed.

  Theorem reachable_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots) after,
      Sem.steps tf (R.initial_config roots) after ->
      config_supported (Sem.support finite) after.
  Proof.
    intros tf roots finite after Hsteps.
    eapply steps_supported; eauto. apply initial_config_supported.
  Qed.

  Theorem reachable_rank_bound :
    forall tf roots (finite : Sem.finite_system tf roots) after x rank,
      Sem.steps tf (R.initial_config roots) after ->
      R.Ranking.lookup (R.ranking (R.cfg_state after)) x = Some rank ->
      rank < RankFinite.bound (Sem.support finite).
  Proof.
    intros tf roots finite after x rank Hsteps Hlookup.
    eapply RankFinite.generated_lookup_bound.
    - exact (configuration_rank_valid
        (reachable_configuration_ranked Hsteps)).
    - exact (state_ranking_generated
        (proj1 (reachable_config_supported finite Hsteps))).
    - exact Hlookup.
  Qed.

  (** The outer termination budget counts finite-support variables whose
      stable rank has not yet been revealed. *)
  Fixpoint unobserved_budget
    (support : list V.t) (st : R.state) : nat :=
    match support with
    | [] => 0
    | x :: rest =>
        match R.Ranking.lookup (R.ranking st) x with
        | Some _ => unobserved_budget rest st
        | None => S (unobserved_budget rest st)
        end
    end.

  Lemma unobserved_budget_nonincreasing :
    forall support before after,
      rank_extends before after ->
      unobserved_budget support after <= unobserved_budget support before.
  Proof.
    induction support as [|x rest IH]; intros before after Hextends.
    - reflexivity.
    - pose proof (IH before after Hextends) as Htail.
      cbn.
      destruct (R.Ranking.lookup (R.ranking before) x)
        as [before_rank |] eqn:Hbefore;
      destruct (R.Ranking.lookup (R.ranking after) x)
        as [after_rank |] eqn:Hafter; cbn in *; try lia.
      pose proof (Hextends x before_rank Hbefore). congruence.
  Qed.

  Lemma unobserved_budget_strict :
    forall support before after x,
      NoDup support ->
      List.In x support ->
      rank_extends before after ->
      R.Ranking.lookup (R.ranking before) x = None ->
      (exists rank,
        R.Ranking.lookup (R.ranking after) x = Some rank) ->
      unobserved_budget support after < unobserved_budget support before.
  Proof.
    induction support as [|y rest IH];
      intros before after x Hnodup Hin Hextends Hbefore [rank Hafter].
    - contradiction.
    - inversion Hnodup as [|? ? Hnotin Hrest]; subst.
      destruct Hin as [<- | Hin].
      + pose proof
          (@unobserved_budget_nonincreasing rest before after Hextends)
          as Htail.
        cbn. rewrite Hbefore, Hafter. cbn. lia.
      + pose proof
          (IH before after x Hrest Hin Hextends Hbefore
            (ex_intro _ rank Hafter)) as Htail.
        cbn.
        destruct (R.Ranking.lookup (R.ranking before) y)
          as [before_rank |] eqn:Hy_before;
        destruct (R.Ranking.lookup (R.ranking after) y)
          as [after_rank |] eqn:Hy_after; cbn in *; try lia.
        pose proof (Hextends y before_rank Hy_before). congruence.
  Qed.

  Lemma observe_fresh_decreases_unobserved_budget :
    forall support st x,
      NoDup support ->
      List.In x support ->
      R.Ranking.lookup (R.ranking st) x = None ->
      unobserved_budget support (R.observe st x) <
        unobserved_budget support st.
  Proof.
    intros support st x Hnodup Hin Hfresh.
    eapply (@unobserved_budget_strict support st (R.observe st x) x);
      eauto using rank_extends_observe.
    apply observe_ranks_variable with (st := st). reflexivity.
  Qed.

  Theorem next_config_unobserved_budget :
    forall support tf before after,
      R.next_config tf before = Some after ->
      unobserved_budget support (R.cfg_state after) =
        unobserved_budget support (R.cfg_state before) \/
      unobserved_budget support (R.cfg_state after) <
        unobserved_budget support (R.cfg_state before).
  Proof.
    intros support tf before after Hstep.
    pose proof (@unobserved_budget_nonincreasing support
      (R.cfg_state before) (R.cfg_state after)
      (@next_config_rank_extends tf before after Hstep)).
    lia.
  Qed.

  Lemma rank_extends_lookup_reflect_on_support :
    forall support before after,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      forall x rank,
        List.In x support ->
        R.Ranking.lookup (R.ranking after) x = Some rank ->
        R.Ranking.lookup (R.ranking before) x = Some rank.
  Proof.
    intros support before after Hnodup Hextends Hbudget
      x rank Hin Hafter.
    destruct (R.Ranking.lookup (R.ranking before) x)
      as [old_rank |] eqn:Hbefore.
    - pose proof (Hextends x old_rank Hbefore) as Hold_after.
      rewrite Hafter in Hold_after. now inversion Hold_after.
    - exfalso.
      pose proof (@unobserved_budget_strict support before after x
        Hnodup Hin Hextends Hbefore (ex_intro _ rank Hafter)).
      lia.
  Qed.

  Lemma rank_extends_lookup_iff_on_support :
    forall support before after,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      forall x rank,
        List.In x support ->
        (R.Ranking.lookup (R.ranking before) x = Some rank <->
         R.Ranking.lookup (R.ranking after) x = Some rank).
  Proof.
    intros support before after Hnodup Hextends Hbudget x rank Hin.
    split; [apply Hextends |].
    now apply (@rank_extends_lookup_reflect_on_support
      support before after Hnodup Hextends Hbudget x rank Hin).
  Qed.

  Module SeedMeasure.
    Fixpoint continuation_seed_measure (k : R.continuation) : nat :=
      match k with
      | R.KLoop => 0
      | R.KSeedLoop roots => 2 * length roots + 2
      | R.KAfterGet _ _ _ rest
      | R.KAfterSide _ _ rest
      | R.KAfterSpawn _ _ rest
      | R.KDead _ _ _ rest
      | R.KDrain _ rest => continuation_seed_measure rest
      end.

    Definition seed_measure (control : R.control) : nat :=
      match control with
      | R.RunLoop => 0
      | R.RunSeeds roots => 2 * length roots + 1
      | R.RunSeedLoop roots => 2 * length roots + 2
      | R.StartEpisode _ rest
      | R.RunRhs _ _ rest
      | R.RunDead _ _ _ rest
      | R.RunCommit _ _ rest
      | R.RunDrain _ rest
      | R.Return rest => continuation_seed_measure rest
      end.

    Theorem next_config_seed_measure_nonincreasing :
      forall tf before after,
        R.next_config tf before = Some after ->
        seed_measure (R.cfg_control after) <=
        seed_measure (R.cfg_control before).
    Proof.
      intros tf [st control] after Hstep. cbn in Hstep.
      destruct control; cbn in Hstep;
        repeat match type of Hstep with
          | context [match ?subject with _ => _ end] =>
              destruct subject eqn:?Hcase
          | context [if ?condition then _ else _] =>
              destruct condition eqn:?Hcase
          end;
        try discriminate; inversion Hstep; subst; cbn;
        try reflexivity; try lia.

    all: try match goal with
        | |- seed_measure (R.cfg_control
            (R.continue_side _ _ _ _ _ ?changed)) <= _ =>
            unfold R.continue_side; destruct changed;
            [destruct (_ && _)%bool |]; cbn; lia
        | |- seed_measure (R.cfg_control
            (R.continue_dead _ _ _ _ _ _ ?changed)) <= _ =>
            unfold R.continue_dead; destruct changed;
            [destruct (_ && _)%bool |]; cbn; lia
        end.
    Qed.

    Theorem run_seeds_step_strict :
      forall tf st roots after,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds roots |} =
          Some after ->
        seed_measure (R.cfg_control after) <
        seed_measure (R.RunSeeds roots).
    Proof.
      intros tf st roots after Hstep. cbn in Hstep.
      destruct roots as [|root remaining].
      - inversion Hstep; subst; cbn; lia.
      - destruct (R.is_materialized (R.observe st root) root);
          inversion Hstep; subst; cbn; lia.
    Qed.

    Theorem empty_seed_loop_step_strict :
      forall tf st roots after,
        R.queue_pop (R.queue st) = None ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop roots |} =
          Some after ->
        seed_measure (R.cfg_control after) <
        seed_measure (R.RunSeedLoop roots).
    Proof.
      intros tf st roots after Hempty Hstep. cbn in Hstep.
      rewrite Hempty in Hstep. inversion Hstep; subst; cbn; lia.
    Qed.
  End SeedMeasure.

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

  Definition higher_count
    (st : R.state) (support : list V.t) (owner : V.t) : nat :=
    length (filter (fun x => R.rank_lt st owner x) support).

  Lemma higher_count_mono :
    forall st support owner target,
      R.rank_lt st owner target = true ->
      higher_count st support target <= higher_count st support owner.
  Proof.
    intros st support owner target Hbefore.
    pose proof (@rank_lt_true_ranked st owner target Hbefore)
      as [Howner Htarget_ranked].
    unfold higher_count.
    induction support as [|x support IH]; [cbn; lia |].
    cbn. destruct (R.rank_lt st target x) eqn:Htarget.
    - assert (Howner_x : R.rank_lt st owner x = true).
      { eapply rank_lt_trans.
        - exact Howner.
        - exact Htarget_ranked.
        - exact (proj2 (@rank_lt_true_ranked st target x Htarget)).
        - exact Hbefore.
        - exact Htarget. }
      rewrite Howner_x. cbn. lia.
    - destruct (R.rank_lt st owner x); cbn; lia.
  Qed.

  Lemma higher_count_strict :
    forall st support owner target,
      R.rank_lt st owner target = true ->
      List.In target support ->
      higher_count st support target < higher_count st support owner.
  Proof.
    intros st support owner target Hbefore Hin.
    pose proof (@rank_lt_true_ranked st owner target Hbefore)
      as [Howner Htarget_ranked].
    unfold higher_count.
    induction support as [|x support IH]; [contradiction |].
    cbn in Hin. cbn. destruct Hin as [-> | Hin].
    - rewrite (rank_lt_irrefl Htarget_ranked), Hbefore. cbn.
      pose proof (@higher_count_mono st support owner target Hbefore)
        as Hmono.
      unfold higher_count in Hmono. lia.
    - destruct (R.rank_lt st target x) eqn:Htarget.
      + assert (Howner_x : R.rank_lt st owner x = true).
        { eapply rank_lt_trans.
          - exact Howner.
          - exact Htarget_ranked.
          - exact (proj2 (@rank_lt_true_ranked st target x Htarget)).
          - exact Hbefore.
          - exact Htarget. }
        rewrite Howner_x. cbn. specialize (IH Hin). lia.
      + destruct (R.rank_lt st owner x); cbn;
          specialize (IH Hin); lia.
  Qed.

  Theorem higher_count_induction :
    forall st support (P : V.t -> Prop),
      (forall owner,
        (forall target,
          List.In target support ->
          R.rank_lt st owner target = true ->
          P target) ->
        P owner) ->
      forall owner, P owner.
  Proof.
    intros st support P Hstep.
    apply (well_founded_induction_type
      (well_founded_ltof V.t (higher_count st support))).
    intros owner IH. apply Hstep.
    intros target Hsupported Hhigher. apply IH.
    unfold ltof. now apply higher_count_strict.
  Qed.

  Lemma rank_lt_stable_on_support :
    forall support before after,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      forall x y,
        List.In x support ->
        List.In y support ->
        R.rank_lt before x y = R.rank_lt after x y.
  Proof.
    intros support before after Hnodup Hextends Hbudget x y Hx Hy.
    assert (Hlookup_x :
      R.Ranking.lookup (R.ranking before) x =
      R.Ranking.lookup (R.ranking after) x).
    { destruct (R.Ranking.lookup (R.ranking before) x)
        as [xrank |] eqn:Hbefore_x.
      - now rewrite (Hextends x xrank Hbefore_x).
      - destruct (R.Ranking.lookup (R.ranking after) x)
          as [xrank |] eqn:Hafter_x; [|reflexivity].
        pose proof (@rank_extends_lookup_reflect_on_support support
          before after Hnodup Hextends Hbudget x xrank Hx Hafter_x).
        congruence. }
    assert (Hlookup_y :
      R.Ranking.lookup (R.ranking before) y =
      R.Ranking.lookup (R.ranking after) y).
    { destruct (R.Ranking.lookup (R.ranking before) y)
        as [yrank |] eqn:Hbefore_y.
      - now rewrite (Hextends y yrank Hbefore_y).
      - destruct (R.Ranking.lookup (R.ranking after) y)
          as [yrank |] eqn:Hafter_y; [|reflexivity].
        pose proof (@rank_extends_lookup_reflect_on_support support
          before after Hnodup Hextends Hbudget y yrank Hy Hafter_y).
        congruence. }
    unfold R.rank_lt, R.ranking_lt. now rewrite Hlookup_x, Hlookup_y.
  Qed.

  Lemma higher_count_stable :
    forall support before after owner,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      List.In owner support ->
      higher_count before support owner = higher_count after support owner.
  Proof.
    intros support before after owner Hnodup Hextends Hbudget Howner.
    unfold higher_count. f_equal. apply filter_ext_in.
    intros x Hx. now apply (@rank_lt_stable_on_support support
      before after Hnodup Hextends Hbudget owner x Howner Hx).
  Qed.

  Inductive rhs_child :
    R.ConstraintSystem.rhs -> R.ConstraintSystem.rhs -> Prop :=
  | RhsGetChild :
      forall target next value,
        rhs_child (next value) (R.ConstraintSystem.Get target next)
  | RhsSideChild :
      forall target value next,
        rhs_child next (R.ConstraintSystem.Side target value next)
  | RhsSpawnChild :
      forall target next,
        rhs_child next (R.ConstraintSystem.Spawn target next).

  Theorem rhs_child_well_founded : well_founded rhs_child.
  Proof.
    unfold well_founded. intro body.
    induction body using R.ConstraintSystem.rhs_ind.
    - constructor. intros child Hchild. inversion Hchild.
    - constructor. intros child Hchild.
      inversion Hchild; subst. apply H.
    - constructor. intros child Hchild.
      inversion Hchild; subst. exact IHbody.
    - constructor. intros child Hchild.
      inversion Hchild; subst. exact IHbody.
  Qed.

  Inductive local_work : Type :=
  | WorkEval : R.ConstraintSystem.rhs -> local_work
  | WorkAfterGet : V.t -> (D.t -> R.ConstraintSystem.rhs) -> local_work
  | WorkDead : nat -> local_work
  | WorkCommit : local_work
  | WorkDrain : local_work
  | WorkFinish : local_work.

  Inductive local_work_lt : local_work -> local_work -> Prop :=
  | WorkGetSuspend :
      forall target next,
        local_work_lt (WorkAfterGet target next)
          (WorkEval (R.ConstraintSystem.Get target next))
  | WorkGetResume :
      forall target next value,
        local_work_lt (WorkEval (next value)) (WorkAfterGet target next)
  | WorkGetDirect :
      forall target next value,
        local_work_lt (WorkEval (next value))
          (WorkEval (R.ConstraintSystem.Get target next))
  | WorkSideNext :
      forall target value next,
        local_work_lt (WorkEval next)
          (WorkEval (R.ConstraintSystem.Side target value next))
  | WorkSpawnNext :
      forall target next,
        local_work_lt (WorkEval next)
          (WorkEval (R.ConstraintSystem.Spawn target next))
  | WorkRetDead :
      forall direct pending,
        local_work_lt (WorkDead pending)
          (WorkEval (R.ConstraintSystem.Ret direct))
  | WorkDeadNext :
      forall pending, local_work_lt (WorkDead pending) (WorkDead (S pending))
  | WorkDeadCommit : local_work_lt WorkCommit (WorkDead 0)
  | WorkCommitDrain : local_work_lt WorkDrain WorkCommit
  | WorkDrainFinish : local_work_lt WorkFinish WorkDrain.

  Lemma work_finish_accessible : Acc local_work_lt WorkFinish.
  Proof. constructor. intros work Hwork. inversion Hwork. Qed.

  Lemma work_drain_accessible : Acc local_work_lt WorkDrain.
  Proof.
    constructor. intros work Hwork.
    inversion Hwork; subst. exact work_finish_accessible.
  Qed.

  Lemma work_commit_accessible : Acc local_work_lt WorkCommit.
  Proof.
    constructor. intros work Hwork.
    inversion Hwork; subst. exact work_drain_accessible.
  Qed.

  Lemma work_dead_accessible :
    forall pending, Acc local_work_lt (WorkDead pending).
  Proof.
    induction pending as [|pending IH].
    - constructor. intros work Hwork.
      inversion Hwork; subst. exact work_commit_accessible.
    - constructor. intros work Hwork.
      inversion Hwork; subst. exact IH.
  Qed.

  Definition work_eval_accessible :
    forall body, Acc local_work_lt (WorkEval body).
  Proof.
    apply (R.ConstraintSystem.rhs_rect
      (fun body => Acc local_work_lt (WorkEval body))).
    - intros direct. constructor. intros work Hwork.
      inversion Hwork; subst. apply work_dead_accessible.
    - intros target next Hnext.
      assert (Hafter : Acc local_work_lt (WorkAfterGet target next)).
      { constructor. intros work Hwork.
        inversion Hwork; subst. apply Hnext. }
      constructor. intros work Hwork.
      inversion Hwork; subst; [exact Hafter |apply Hnext].
    - intros target value next Hnext.
      constructor. intros work Hwork.
      inversion Hwork; subst. exact Hnext.
    - intros target next Hnext.
      constructor. intros work Hwork.
      inversion Hwork; subst. exact Hnext.
  Defined.

  Lemma work_after_get_accessible :
    forall target next, Acc local_work_lt (WorkAfterGet target next).
  Proof.
    intros target next. eapply Acc_inv.
    - apply work_eval_accessible.
    - constructor.
  Qed.

  Theorem local_work_lt_well_founded : well_founded local_work_lt.
  Proof.
    intros work. destruct work.
    - apply work_eval_accessible.
    - apply work_after_get_accessible.
    - apply work_dead_accessible.
    - apply work_commit_accessible.
    - apply work_drain_accessible.
    - apply work_finish_accessible.
  Qed.

  Definition owner_work := (V.t * local_work)%type.

  Definition owner_work_lt
    (st : R.state) (support : list V.t) : owner_work -> owner_work -> Prop :=
    fun left right =>
      slexprod nat local_work lt local_work_lt
        (higher_count st support (fst left), snd left)
        (higher_count st support (fst right), snd right).

  Theorem owner_work_lt_well_founded :
    forall st support, well_founded (owner_work_lt st support).
  Proof.
    intros st support. unfold owner_work_lt.
    apply wf_inverse_image. apply wf_slexprod.
    - apply PeanoNat.Nat.lt_wf_0.
    - apply local_work_lt_well_founded.
  Qed.

  Lemma owner_work_nested :
    forall st support owner target current child,
      R.rank_lt st owner target = true ->
      List.In target support ->
      owner_work_lt st support (target, child) (owner, current).
  Proof.
    intros st support owner target current child Hhigher Hsupported.
    unfold owner_work_lt. cbn. apply left_slex.
    now apply higher_count_strict.
  Qed.

  Lemma owner_work_local :
    forall st support owner before after,
      local_work_lt after before ->
      owner_work_lt st support (owner, after) (owner, before).
  Proof.
    intros st support owner before after Hlocal.
    unfold owner_work_lt. cbn. now apply right_slex.
  Qed.

  Definition work_forest_lt
    (st : R.state) (support : list V.t) :
    list owner_work -> list owner_work -> Prop :=
    list_ext owner_work (owner_work_lt st support).

  Theorem work_forest_lt_well_founded :
    forall st support, well_founded (work_forest_lt st support).
  Proof.
    intros st support. unfold work_forest_lt.
    apply wf_list_ext, owner_work_lt_well_founded.
  Qed.

  Fixpoint continuation_work
    (k : R.continuation) : list owner_work :=
    match k with
    | R.KLoop | R.KSeedLoop _ => []
    | R.KAfterGet fr target next rest =>
        (R.frame_owner fr, WorkAfterGet target next) ::
        continuation_work rest
    | R.KAfterSide fr next rest
    | R.KAfterSpawn fr next rest =>
        (R.frame_owner fr, WorkEval next) :: continuation_work rest
    | R.KDead fr _ pending rest =>
        (R.frame_owner fr, WorkDead (length pending)) ::
        continuation_work rest
    | R.KDrain fr rest =>
        (R.frame_owner fr, WorkDrain) :: continuation_work rest
    end.

  Definition control_work
    (tf : R.ConstraintSystem.system) (control : R.control) : list owner_work :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => []
    | R.StartEpisode owner k =>
        (owner, WorkEval (tf owner)) :: continuation_work k
    | R.RunRhs fr body k =>
        (R.frame_owner fr, WorkEval body) :: continuation_work k
    | R.RunDead fr _ pending k =>
        (R.frame_owner fr, WorkDead (length pending)) ::
        continuation_work k
    | R.RunCommit fr _ k =>
        (R.frame_owner fr, WorkCommit) :: continuation_work k
    | R.RunDrain fr k =>
        (R.frame_owner fr, WorkDrain) :: continuation_work k
    | R.Return k => continuation_work k
    end.

  Lemma continuation_work_supported :
    forall support k,
      continuation_supported support k ->
      Forall (fun work => supported support (fst work))
        (continuation_work k).
  Proof.
    intros support k. induction k; cbn; intros Hsupported.
    - constructor.
    - constructor.
    - destruct Hsupported as [Hfr [_ [_ Hrest]]].
      constructor; [exact (proj1 Hfr) |auto].
    - destruct Hsupported as [Hfr [_ Hrest]].
      constructor; [exact (proj1 Hfr) |auto].
    - destruct Hsupported as [Hfr [_ Hrest]].
      constructor; [exact (proj1 Hfr) |auto].
    - destruct Hsupported as [Hfr [_ Hrest]].
      constructor; [exact (proj1 Hfr) |auto].
    - destruct Hsupported as [Hfr Hrest].
      constructor; [exact (proj1 Hfr) |auto].
  Qed.

  Lemma control_work_supported :
    forall tf support control,
      control_supported support control ->
      Forall (fun work => supported support (fst work))
        (control_work tf control).
  Proof.
    intros tf support control Hsupported.
    destruct control; cbn in *.
    - constructor.
    - constructor.
    - constructor.
    - destruct Hsupported as [Howner Hrest].
      constructor; [exact Howner |now apply continuation_work_supported].
    - destruct Hsupported as [Hfr [_ Hrest]].
      constructor; [exact (proj1 Hfr) |now apply continuation_work_supported].
    - destruct Hsupported as [Hfr [_ Hrest]].
      constructor; [exact (proj1 Hfr) |now apply continuation_work_supported].
    - destruct Hsupported as [Hfr Hrest].
      constructor; [exact (proj1 Hfr) |now apply continuation_work_supported].
    - destruct Hsupported as [Hfr Hrest].
      constructor; [exact (proj1 Hfr) |now apply continuation_work_supported].
    - now apply continuation_work_supported.
  Qed.

  Theorem reachable_control_work_supported :
    forall tf roots (finite : Sem.finite_system tf roots) c,
      Sem.steps tf (R.initial_config roots) c ->
      Forall
        (fun work => supported (Sem.support finite) (fst work))
        (control_work tf (R.cfg_control c)).
  Proof.
    intros tf roots finite c Hsteps. apply control_work_supported.
    exact (proj2 (reachable_config_supported finite Hsteps)).
  Qed.

  Lemma owner_work_lt_stable :
    forall support before after left right,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      supported support (fst left) ->
      supported support (fst right) ->
      (owner_work_lt before support left right <->
       owner_work_lt after support left right).
  Proof.
    intros support before after [left_owner left_work]
      [right_owner right_work] Hnodup Hextends Hbudget Hleft Hright.
    unfold owner_work_lt. cbn in *.
    rewrite (@higher_count_stable support before after left_owner
      Hnodup Hextends Hbudget Hleft).
    rewrite (@higher_count_stable support before after right_owner
      Hnodup Hextends Hbudget Hright).
    tauto.
  Qed.

  Lemma work_forest_lt_stable :
    forall support before after left right,
      NoDup support ->
      rank_extends before after ->
      unobserved_budget support after = unobserved_budget support before ->
      Forall (fun work => supported support (fst work)) left ->
      Forall (fun work => supported support (fst work)) right ->
      (work_forest_lt before support left right <->
       work_forest_lt after support left right).
  Proof.
    intros support before after left right Hnodup Hextends Hbudget
      Hleft Hright. split; intros Hrelation.
    - inversion Hrelation as [current replacements prefix suffix Hsmaller];
        subst left right.
      rewrite Forall_forall in Hleft, Hright, Hsmaller.
      constructor. apply Forall_forall. intros work Hin.
      assert (Hwork : supported support (fst work)).
      { apply Hleft. apply in_or_app. right.
        apply in_or_app. now left. }
      assert (Hcurrent : supported support (fst current)).
      { apply Hright. apply in_or_app. right.
        now left. }
      apply (proj1 (@owner_work_lt_stable support before after work current
        Hnodup Hextends Hbudget Hwork Hcurrent)).
      now apply Hsmaller.
    - inversion Hrelation as [current replacements prefix suffix Hsmaller];
        subst left right.
      rewrite Forall_forall in Hleft, Hright, Hsmaller.
      constructor. apply Forall_forall. intros work Hin.
      assert (Hwork : supported support (fst work)).
      { apply Hleft. apply in_or_app. right.
        apply in_or_app. now left. }
      assert (Hcurrent : supported support (fst current)).
      { apply Hright. apply in_or_app. right.
        now left. }
      apply (proj2 (@owner_work_lt_stable support before after work current
        Hnodup Hextends Hbudget Hwork Hcurrent)).
      now apply Hsmaller.
  Qed.

  Lemma work_forest_replace_head :
    forall st support current replacements rest,
      Forall (fun work => owner_work_lt st support work current)
        replacements ->
      work_forest_lt st support
        (replacements ++ rest) (current :: rest).
  Proof.
    intros st support current replacements rest Hsmaller.
    unfold work_forest_lt.
    replace (replacements ++ rest)
      with ([] ++ replacements ++ rest) by reflexivity.
    replace (current :: rest)
      with ([] ++ current :: rest) by reflexivity.
    now constructor.
  Qed.

  Lemma work_forest_remove_head :
    forall st support current rest,
      work_forest_lt st support rest (current :: rest).
  Proof.
    intros st support current rest.
    exact (@work_forest_replace_head st support current [] rest
      (Forall_nil _)).
  Qed.

  Lemma work_forest_local :
    forall st support owner before after rest,
      local_work_lt after before ->
      work_forest_lt st support
        ((owner, after) :: rest) ((owner, before) :: rest).
  Proof.
    intros st support owner before after rest Hlocal.
    apply (@work_forest_replace_head st support
      (owner, before) [(owner, after)] rest).
    constructor; [now apply owner_work_local |constructor].
  Qed.

  Lemma work_forest_nested :
    forall st support owner target before child residual rest,
      R.rank_lt st owner target = true ->
      List.In target support ->
      local_work_lt residual before ->
      work_forest_lt st support
        ((target, child) :: (owner, residual) :: rest)
        ((owner, before) :: rest).
  Proof.
    intros st support owner target before child residual rest
      Hhigher Htarget Hlocal.
    apply (@work_forest_replace_head st support
      (owner, before) [(target, child); (owner, residual)] rest).
    constructor.
    - now apply owner_work_nested.
    - constructor; [now apply owner_work_local |constructor].
  Qed.

  Lemma complete_get_owner :
    forall st fr target st' fr' value,
      R.complete_get st fr target = (st', fr', value) ->
      R.frame_owner fr' = R.frame_owner fr.
  Proof.
    intros st fr target st' fr' value Hget.
    unfold R.complete_get in Hget. inversion Hget. reflexivity.
  Qed.

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

  Definition reset_table_ranked
    (st : R.state) (table : R.reset_table) : Prop :=
    forall scope ids source target,
      M.lookup table scope = Some ids ->
      List.In (source, target) ids ->
      R.rank_lt st scope target = true.

  Lemma reset_table_ranked_extended :
    forall before after table,
      rank_extends before after ->
      reset_table_ranked before table ->
      reset_table_ranked after table.
  Proof.
    intros before after table Hextends Hranked scope ids source target
      Hlookup Hin.
    pose proof (Hranked scope ids source target Hlookup Hin) as Hlt.
    pose proof (@rank_lt_true_ranked before scope target Hlt)
      as [Hscope Htarget].
    rewrite <- (@rank_lt_stable before after scope target
      Hextends Hscope Htarget). exact Hlt.
  Qed.

  Lemma remove_cell_id_in :
    forall id ids candidate,
      List.In candidate (R.remove_cell_id id ids) ->
      List.In candidate ids.
  Proof.
    intros id ids. induction ids as [|head rest IH];
      intros candidate Hin; cbn in *; [contradiction |].
    destruct (R.cell_id_eq_dec id head).
    - right. now apply IH.
    - destruct Hin as [-> | Hin]; [now left |right; now apply IH].
  Qed.

  Lemma add_cell_id_in :
    forall id ids candidate,
      List.In candidate (R.add_cell_id id ids) ->
      candidate = id \/ List.In candidate ids.
  Proof.
    intros id ids candidate Hin. unfold R.add_cell_id in Hin.
    destruct (List.in_dec R.cell_id_eq_dec id ids).
    - now right.
    - cbn in Hin. destruct Hin as [-> | Hin]; auto.
  Qed.

  Lemma reset_table_ranked_remove :
    forall st table scope id,
      reset_table_ranked st table ->
      reset_table_ranked st (R.remove_registration table scope id).
  Proof.
    intros st table scope id Hrank observed ids source target Hlookup Hin.
    unfold R.remove_registration in Hlookup.
    destruct (V.eq_dec observed scope) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hlookup.
      injection Hlookup as Hids. subst ids.
      unfold R.lookup_reset_ids in Hin.
      destruct (M.lookup table scope) as [old |] eqn:Hold;
        cbn in Hin; [|contradiction].
      exact (Hrank scope old source target Hold
        (@remove_cell_id_in id old (source, target) Hin)).
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      eapply Hrank; eauto.
  Qed.

  Lemma reset_table_ranked_add :
    forall st table scope source target,
      reset_table_ranked st table ->
      R.rank_lt st scope target = true ->
      reset_table_ranked st
        (R.add_registration table scope (source, target)).
  Proof.
    intros st table scope source target Hrank Hhigher
      observed ids source' target' Hlookup Hin.
    unfold R.add_registration in Hlookup.
    destruct (V.eq_dec observed scope) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hlookup.
      injection Hlookup as Hids. subst ids.
      apply add_cell_id_in in Hin. destruct Hin as [Heq | Hin].
      + injection Heq as -> ->. exact Hhigher.
      + unfold R.lookup_reset_ids in Hin.
        destruct (M.lookup table scope) as [old |] eqn:Hold;
          cbn in Hin; [|contradiction].
        eapply Hrank; eauto.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      eapply Hrank; eauto.
  Qed.

  Lemma reset_table_ranked_register :
    forall st source target scope phase,
      reset_table_ranked st (R.reset_at_close st) ->
      reset_table_ranked (R.register_reset st source target scope phase)
        (R.reset_at_close
          (R.register_reset st source target scope phase)).
  Proof.
    intros st source target scope phase Hrank.
    unfold R.register_reset. cbn.
    destruct (R.stored_side_cell st source target)
      as [old_phase old_scope]. cbn.
    destruct Features.restart_side_phases.
    - destruct (R.rank_lt st scope target) eqn:Hhigher; cbn.
      + destruct (R.same_scope old_scope (Some scope)).
        * exact Hrank.
        * destruct old_scope as [previous |].
          -- apply reset_table_ranked_add;
               [now apply reset_table_ranked_remove |exact Hhigher].
          -- now apply reset_table_ranked_add.
      + destruct (R.same_scope old_scope None).
        * exact Hrank.
        * destruct old_scope as [previous |].
          -- now apply reset_table_ranked_remove.
          -- exact Hrank.
    - cbn. destruct (R.same_scope old_scope None).
      + exact Hrank.
      + destruct old_scope as [previous |].
        * now apply reset_table_ranked_remove.
        * exact Hrank.
  Qed.

  Lemma reset_table_ranked_clear :
    forall st table scope,
      reset_table_ranked st table ->
      reset_table_ranked st (M.update table scope []).
  Proof.
    intros st table scope Hrank observed ids source target Hlookup Hin.
    destruct (V.eq_dec observed scope) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hlookup.
      injection Hlookup as Hids. subst ids. contradiction.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      eapply Hrank; eauto.
  Qed.

  Definition state_resets_ranked (st : R.state) : Prop :=
    reset_table_ranked st (R.reset_at_close st).

  Lemma empty_state_resets_ranked :
    state_resets_ranked R.empty_state.
  Proof.
    intros scope ids source target Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma state_resets_ranked_view :
    forall before after,
      rank_extends before after ->
      R.reset_at_close after = R.reset_at_close before ->
      state_resets_ranked before ->
      state_resets_ranked after.
  Proof.
    intros before after Hextends Hresets Hranked.
    unfold state_resets_ranked. rewrite Hresets.
    now apply reset_table_ranked_extended with before.
  Qed.

  Lemma state_resets_ranked_promote_side_target :
    forall st fr target,
      state_resets_ranked st ->
      state_resets_ranked (R.promote_side_target st fr target).
  Proof.
    intros st fr target Hranked. unfold R.promote_side_target.
    destruct (R.rank_lt st target (R.frame_owner fr)).
    - exact Hranked.
    - eapply state_resets_ranked_view;
        [apply rank_extends_promote_controlled |reflexivity |exact Hranked].
  Qed.

  Lemma state_resets_ranked_write_side_contribution :
    forall st fr target input next changed,
      state_resets_ranked st ->
      R.write_side_contribution st fr target input = (next, changed) ->
      state_resets_ranked next.
  Proof.
    intros st fr target input next changed Hranked Hwrite.
    unfold R.write_side_contribution in Hwrite.
    remember (R.promote_side_target st fr target) as promoted.
    destruct (U.update true target
      (R.side_phase
        (R.stored_side_cell promoted (R.frame_owner fr) target))
      (R.stored_contribution promoted (R.frame_owner fr) target)
      input) as [phase contribution] eqn:Hupdate.
    inversion Hwrite; subst; clear Hwrite.
    apply reset_table_ranked_register.
    eapply state_resets_ranked_view with
      (before := R.promote_side_target st fr target).
    - apply rank_extends_with_contributions.
    - reflexivity.
    - now apply state_resets_ranked_promote_side_target.
  Qed.

  Lemma state_resets_ranked_continue_side :
    forall st fr target body k changed,
      state_resets_ranked st ->
      state_resets_ranked
        (R.cfg_state (R.continue_side st fr target body k changed)).
  Proof.
    intros st fr target body k changed Hranked.
    unfold R.continue_side. destruct changed.
    - destruct (_ && _)%bool; cbn.
      + exact Hranked.
      + eapply state_resets_ranked_view with (before := st);
          [apply rank_extends_enqueue |reflexivity |exact Hranked].
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_continue_dead :
    forall st fr direct target remaining k changed,
      state_resets_ranked st ->
      state_resets_ranked
        (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed)).
  Proof.
    intros st fr direct target remaining k changed Hranked.
    unfold R.continue_dead. destruct changed.
    - destruct (_ && _)%bool; cbn.
      + exact Hranked.
      + eapply state_resets_ranked_view with (before := st);
          [apply rank_extends_enqueue |reflexivity |exact Hranked].
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_reset_registered_cells :
    forall st owner,
      state_resets_ranked st ->
      state_resets_ranked (R.reset_registered_cells st owner).
  Proof.
    intros st owner Hranked. unfold R.reset_registered_cells.
    destruct Features.restart_side_phases.
    - cbn. apply reset_table_ranked_clear. exact Hranked.
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_complete_get :
    forall st fr target next next_fr value,
      state_resets_ranked st ->
      R.complete_get st fr target = (next, next_fr, value) ->
      state_resets_ranked next.
  Proof.
    intros st fr target next next_fr value Hranked Hget.
    eapply state_resets_ranked_view with (before := st).
    - exact (@rank_extends_complete_get
        st fr target next next_fr value Hget).
    - unfold R.complete_get in Hget.
      repeat match type of Hget with
        | context [if ?condition then _ else _] => destruct condition eqn:?
        end;
        unfold R.materialize in Hget;
        destruct (M.lookup _ target);
        inversion Hget; subst; cbn; reflexivity.
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_set_value :
    forall st fr direct next next_fr,
      state_resets_ranked st ->
      R.set_value st fr direct = (next, next_fr) ->
      state_resets_ranked next.
  Proof.
    intros st fr direct next next_fr Hranked Hset.
    eapply state_resets_ranked_view with (before := st).
    - exact (@rank_extends_set_value st fr direct next next_fr Hset).
    - unfold R.set_value in Hset.
      repeat match type of Hset with
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?
        end;
        inversion Hset; subst; cbn; reflexivity.
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_observe :
    forall st x,
      state_resets_ranked st -> state_resets_ranked (R.observe st x).
  Proof.
    intros st x Hranked.
    eapply state_resets_ranked_view with (before := st).
    - eapply rank_extends_observe. reflexivity.
    - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
      reflexivity.
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_materialize :
    forall st x,
      state_resets_ranked st -> state_resets_ranked (R.materialize st x).
  Proof.
    intros st x Hranked.
    eapply state_resets_ranked_view with (before := st).
    - apply rank_extends_materialize.
    - unfold R.materialize. destruct (M.lookup (R.sigma st) x);
        reflexivity.
    - exact Hranked.
  Qed.

  Lemma state_resets_ranked_enqueue :
    forall st x,
      state_resets_ranked st -> state_resets_ranked (R.enqueue st x).
  Proof.
    intros st x Hranked.
    eapply state_resets_ranked_view with (before := st);
      [apply rank_extends_enqueue |reflexivity |exact Hranked].
  Qed.

  Lemma state_resets_ranked_get_base :
    forall st target,
      state_resets_ranked st ->
      state_resets_ranked
        (if R.is_materialized (R.observe st target) target
         then R.observe st target
         else R.enqueue (R.observe st target) target).
  Proof.
    intros st target Hranked.
    pose proof (state_resets_ranked_observe target Hranked) as Hobserved.
    destruct (R.is_materialized (R.observe st target) target).
    - exact Hobserved.
    - now apply state_resets_ranked_enqueue.
  Qed.

  Lemma next_config_resets_ranked :
    forall tf before after,
      state_resets_ranked (R.cfg_state before) ->
      R.next_config tf before = Some after ->
      state_resets_ranked (R.cfg_state after).
  Proof.
    intros tf [st control] after Hranked Hstep.
    cbn -[R.complete_get R.write_side_contribution R.set_value
      R.continue_side R.continue_dead R.fresh_frame
      R.materialize R.publish_targets R.reset_registered_cells] in Hstep.
    destruct control;
      cbn -[R.complete_get R.write_side_contribution R.set_value
        R.continue_side R.continue_dead R.fresh_frame
        R.materialize R.publish_targets R.reset_registered_cells] in Hstep;
      repeat match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hranked.
    all: try (apply state_resets_ranked_observe; exact Hranked).
    all: try (apply state_resets_ranked_materialize; exact Hranked).
    all: try (apply state_resets_ranked_materialize;
      apply state_resets_ranked_enqueue;
      apply state_resets_ranked_observe; exact Hranked).
    all: try (apply state_resets_ranked_reset_registered_cells;
      exact Hranked).

    all: try match goal with
      | Hget : R.complete_get ?base ?fr ?target = (?next, ?next_fr, ?value)
        |- state_resets_ranked ?next =>
          eapply state_resets_ranked_complete_get;
          [first [apply state_resets_ranked_get_base; exact Hranked
                 |exact Hranked]
          |exact Hget]
      end.

    all: try match goal with
      | Hwrite : R.write_side_contribution ?base ?fr ?target ?input =
          (?next, ?changed)
        |- state_resets_ranked
          (R.cfg_state (R.continue_side ?next ?fr ?target ?body ?k ?changed)) =>
          apply state_resets_ranked_continue_side;
          eapply state_resets_ranked_write_side_contribution;
          [apply state_resets_ranked_observe; exact Hranked |exact Hwrite]
      | Hwrite : R.write_side_contribution ?base ?fr ?target ?input =
          (?next, ?changed)
        |- state_resets_ranked
          (R.cfg_state
            (R.continue_dead ?next ?fr ?direct ?target ?rest ?k ?changed)) =>
          apply state_resets_ranked_continue_dead;
          eapply state_resets_ranked_write_side_contribution;
          [exact Hranked |exact Hwrite]
      end.

    all: try match goal with
      | Hset : R.set_value ?base ?fr ?direct = (?next, ?next_fr)
        |- state_resets_ranked ?next =>
          change (state_resets_ranked next); eapply state_resets_ranked_set_value; [exact Hranked |exact Hset]
      end.
    all: eapply state_resets_ranked_complete_get; eauto.
  Qed.

  Lemma steps_resets_ranked :
    forall tf before after,
      state_resets_ranked (R.cfg_state before) ->
      Sem.steps tf before after ->
      state_resets_ranked (R.cfg_state after).
  Proof.
    intros tf before after Hranked Hsteps. induction Hsteps.
    - exact Hranked.
    - apply IHHsteps. eapply next_config_resets_ranked; eauto.
  Qed.

  Theorem reachable_resets_ranked :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      state_resets_ranked (R.cfg_state after).
  Proof.
    intros tf roots after Hsteps. eapply steps_resets_ranked; eauto.
    apply empty_state_resets_ranked.
  Qed.

  Module Credits.
    Definition domain_equivalent (left right : D.t) : Prop :=
      D.leq left right = true /\ D.leq right left = true.

    Lemma domain_equivalent_refl :
      forall value, domain_equivalent value value.
    Proof. intros. split; apply DL.leq_refl. Qed.

    Lemma domain_equivalent_sym :
      forall left right,
        domain_equivalent left right -> domain_equivalent right left.
    Proof. intros left right [Hlr Hrl]. split; assumption. Qed.

    Lemma domain_equivalent_trans :
      forall first second third,
        domain_equivalent first second ->
        domain_equivalent second third ->
        domain_equivalent first third.
    Proof.
      intros first second third [H12 H21] [H23 H32].
      split; eapply DL.leq_trans; eauto.
    Qed.

    Lemma join_congruent :
      forall left left' right right',
        domain_equivalent left left' ->
        domain_equivalent right right' ->
        domain_equivalent (D.join left right) (D.join left' right').
    Proof.
      intros left left' right right' [Hleft Hleft'] [Hright Hright'].
      split; apply DL.join_least.
      - eapply DL.leq_trans; [exact Hleft |apply DL.join_upper_left].
      - eapply DL.leq_trans; [exact Hright |apply DL.join_upper_right].
      - eapply DL.leq_trans; [exact Hleft' |apply DL.join_upper_left].
      - eapply DL.leq_trans; [exact Hright' |apply DL.join_upper_right].
    Qed.

    Lemma join_bottom_left :
      forall value, domain_equivalent (D.join D.bottom value) value.
    Proof.
      intros value. split.
      - apply DL.join_least; [apply DL.bottom_least |apply DL.leq_refl].
      - apply DL.join_upper_right.
    Qed.

    Lemma join_swap :
      forall left right rest,
        domain_equivalent
          (D.join left (D.join right rest))
          (D.join right (D.join left rest)).
    Proof.
      intros left right rest. split; apply DL.join_least.
      - eapply DL.leq_trans; [apply DL.join_upper_left |].
        apply DL.join_upper_right.
      - apply DL.join_least.
        + apply DL.join_upper_left.
        + eapply DL.leq_trans; [apply DL.join_upper_right |].
          apply DL.join_upper_right.
      - eapply DL.leq_trans; [apply DL.join_upper_left |].
        apply DL.join_upper_right.
      - apply DL.join_least.
        + apply DL.join_upper_left.
        + eapply DL.leq_trans; [apply DL.join_upper_right |].
          apply DL.join_upper_right.
    Qed.

    Lemma join_values_permutation :
      forall values values',
        Permutation values values' ->
        domain_equivalent (R.join_values values) (R.join_values values').
    Proof.
      intros values values' Hperm. induction Hperm; cbn.
      - apply domain_equivalent_refl.
      - apply join_congruent;
          [apply domain_equivalent_refl |exact IHHperm].
      - apply join_swap.
      - eapply domain_equivalent_trans; eauto.
    Qed.

    Lemma lookup_map_update_same :
      forall A (table : M.t (M.t A)) outer inner value,
        M.lookup
          (R.lookup_map (R.update_map table outer inner value) outer) inner =
        Some value.
    Proof.
      intros. unfold R.update_map, R.lookup_map.
      rewrite ML.lookup_update_same. apply ML.lookup_update_same.
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

    Lemma aggregate_register_reset :
      forall st source target scope phase observed,
        R.aggregate (R.register_reset st source target scope phase) observed =
        R.aggregate st observed.
    Proof.
      intros. unfold R.register_reset.
      destruct (R.stored_side_cell st source target)
        as [old_phase old_reset]. cbn.
      destruct Features.restart_side_phases; cbn;
        destruct (R.rank_lt st scope target); cbn;
        destruct (R.same_scope old_reset (Some scope)); cbn;
        try destruct old_reset; cbn; reflexivity.
    Qed.

    Lemma aggregate_row_update_equivalent :
      forall st source target value,
        domain_equivalent value (R.stored_contribution st source target) ->
        domain_equivalent
          (R.aggregate
            (R.with_contributions st
              (R.update_map (R.contributions st) target source value))
            target)
          (R.aggregate st target).
    Proof.
      intros st source target value Hequivalent.
      unfold R.aggregate. cbn. unfold R.update_map, R.lookup_map.
      rewrite ML.lookup_update_same.
      set (row := R.lookup_map (R.contributions st) target) in *.
      destruct (ML.values_update row source value)
        as [rest [Hupdated Hprevious]].
      pose proof (join_values_permutation Hupdated) as Hnew.
      destruct (M.lookup row source) as [previous |] eqn:Hlookup.
      - pose proof (join_values_permutation Hprevious) as Hold.
        unfold R.stored_contribution in Hequivalent.
        fold row in Hequivalent. rewrite Hlookup in Hequivalent.
        eapply domain_equivalent_trans; [exact Hnew |].
        eapply domain_equivalent_trans.
        + cbn. apply join_congruent;
            [exact Hequivalent |apply domain_equivalent_refl].
        + apply domain_equivalent_sym. exact Hold.
      - pose proof (join_values_permutation Hprevious) as Hold.
        unfold R.stored_contribution in Hequivalent.
        fold row in Hequivalent. rewrite Hlookup in Hequivalent.
        eapply domain_equivalent_trans; [exact Hnew |].
        eapply domain_equivalent_trans.
        + cbn. apply join_congruent;
            [exact Hequivalent |apply domain_equivalent_refl].
        + eapply domain_equivalent_trans;
            [apply join_bottom_left |apply domain_equivalent_sym; exact Hold].
    Qed.

    Lemma aggregate_promote_side_target :
      forall st fr target,
        R.aggregate (R.promote_side_target st fr target) target =
        R.aggregate st target.
    Proof.
      intros. unfold R.promote_side_target, R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Definition side_cell_credit
      (st : R.state) (source target : V.t) : nat :=
      UL.remaining_changes
        (R.side_phase (R.stored_side_cell st source target))
        (R.stored_contribution st source target).

    Definition ordinary_credit (st : R.state) (fr : R.frame) : nat :=
      UL.remaining_changes
        (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr)).

    Lemma side_cell_credit_promote_side_target :
      forall st fr source target,
        side_cell_credit (R.promote_side_target st fr target) source target =
        side_cell_credit st source target.
    Proof.
      intros. unfold side_cell_credit, R.promote_side_target,
        R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma side_cell_credit_after_update :
      forall st source target scope phase value,
        side_cell_credit
          (R.register_reset
            (R.with_contributions st
              (R.update_map (R.contributions st) target source value))
            source target scope phase)
          source target =
        UL.remaining_changes phase value.
    Proof.
      intros. unfold side_cell_credit, R.register_reset.
      destruct
        (R.stored_side_cell
          (R.with_contributions st
            (R.update_map (R.contributions st) target source value))
          source target) as [old_phase old_scope]. cbn.
      destruct Features.restart_side_phases; cbn;
        destruct (R.rank_lt st scope target); cbn;
        destruct (R.same_scope old_scope (Some scope)); cbn;
        try destruct old_scope;
        unfold R.stored_side_cell, R.stored_contribution; cbn;
        rewrite !lookup_map_update_same; reflexivity.
    Qed.

    Lemma write_side_credit_nonincreasing :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        side_cell_credit next (R.frame_owner fr) target <=
        side_cell_credit st (R.frame_owner fr) target.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      set (cell := R.stored_side_cell base (R.frame_owner fr) target) in *.
      set (old := R.stored_contribution base (R.frame_owner fr) target) in *.
      destruct (U.update true target (R.side_phase cell) old input)
        as [phase value] eqn:Hupdate.
      cbn in Hwrite. inversion Hwrite; subst; clear Hwrite.
      rewrite side_cell_credit_after_update.
      rewrite <- (side_cell_credit_promote_side_target
        st fr (R.frame_owner fr) target).
      subst base cell old.
      pose proof (UL.remaining_changes_nonincreasing
        true target
        (R.side_phase
          (R.stored_side_cell (R.promote_side_target st fr target)
            (R.frame_owner fr) target))
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) input) as Hcredit.
      now rewrite Hupdate in Hcredit.
    Qed.

    Lemma write_side_changed_credit_decreases :
      forall st fr target input next,
        R.write_side_contribution st fr target input = (next, true) ->
        side_cell_credit next (R.frame_owner fr) target <
        side_cell_credit st (R.frame_owner fr) target.
    Proof.
      intros st fr target input next Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      set (cell := R.stored_side_cell base (R.frame_owner fr) target) in *.
      set (old := R.stored_contribution base (R.frame_owner fr) target) in *.
      destruct (U.update true target (R.side_phase cell) old input)
        as [phase value] eqn:Hupdate.
      cbn in Hwrite.
      set (updated := R.with_contributions base
        (R.update_map (R.contributions base)
          target (R.frame_owner fr) value)) in Hwrite.
      set (registered := R.register_reset updated (R.frame_owner fr) target
        (R.frame_min_scope fr) phase) in Hwrite.
      remember (negb (R.equivalent
        (R.aggregate registered target) (R.aggregate base target)))
        as actual_changed eqn:Hchanged in Hwrite.
      change ((registered, actual_changed) = (next, true)) in Hwrite.
      injection Hwrite as Hstate Htrue. subst next.
      assert (Hchanged_value : negb (R.equivalent
        (R.aggregate registered target) (R.aggregate base target)) = true).
      { rewrite <- Hchanged. exact Htrue. }
      assert (Houtput : ~ domain_equivalent value old).
      { intro Hequivalent.
        assert (Haggregate : domain_equivalent
          (R.aggregate registered target) (R.aggregate base target)).
        { subst registered updated. rewrite aggregate_register_reset.
          now apply aggregate_row_update_equivalent. }
        assert (Hboolean : R.equivalent
          (R.aggregate registered target) (R.aggregate base target) = true).
        { unfold R.equivalent. apply Bool.andb_true_iff. exact Haggregate. }
        rewrite Hboolean in Hchanged_value. discriminate. }
      subst registered updated. rewrite side_cell_credit_after_update.
      rewrite <- (side_cell_credit_promote_side_target
        st fr (R.frame_owner fr) target).
      subst base cell old.
      pose proof (@UL.update_change_consumes true target
        (R.side_phase
          (R.stored_side_cell (R.promote_side_target st fr target)
            (R.frame_owner fr) target))
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) input) as Hcredit.
      rewrite Hupdate in Hcredit. apply Hcredit. exact Houtput.
    Qed.

    Lemma lookup_cell_update_other :
      forall A (cells : M.t (M.t A))
        source target updated_source updated_target value,
        (source, target) <> (updated_source, updated_target) ->
        M.lookup
          (R.lookup_map
            (R.update_map cells updated_source updated_target value)
            source) target =
        M.lookup (R.lookup_map cells source) target.
    Proof.
      intros A cells source target updated_source updated_target value Hneq.
      destruct (V.eq_dec source updated_source) as [-> | Hsource].
      - assert (Htarget : target <> updated_target).
        { intro Heq. apply Hneq. now f_equal. }
        unfold R.update_map, R.lookup_map.
        rewrite ML.lookup_update_same.
        now apply ML.lookup_update_other.
      - rewrite lookup_update_map_other by exact Hsource. reflexivity.
    Qed.

    Lemma stored_side_cell_write_other :
      forall st fr target input next changed source observed,
        R.write_side_contribution st fr target input = (next, changed) ->
        (source, observed) <> (R.frame_owner fr, target) ->
        R.stored_side_cell next source observed =
        R.stored_side_cell st source observed.
    Proof.
      intros st fr target input next changed source observed Hwrite Hother.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [phase value].
      cbn in Hwrite. inversion Hwrite; subst; clear Hwrite.
      unfold R.register_reset.
      destruct (R.stored_side_cell
        (R.with_contributions base
          (R.update_map (R.contributions base)
            target (R.frame_owner fr) value))
        (R.frame_owner fr) target) as [old_phase old_scope]. cbn.
      destruct Features.restart_side_phases; cbn;
        destruct (R.rank_lt base (R.frame_min_scope fr) target); cbn;
        destruct (R.same_scope old_scope (Some (R.frame_min_scope fr)));
        cbn; try destruct old_scope; cbn;
        unfold R.stored_side_cell; cbn;
        rewrite (@lookup_cell_update_other R.side_cell
          (R.side_cells base) source observed (R.frame_owner fr) target
          _ Hother);
        subst base; unfold R.promote_side_target, R.promote_controlled;
        destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma stored_contribution_write_other :
      forall st fr target input next changed source observed,
        R.write_side_contribution st fr target input = (next, changed) ->
        (source, observed) <> (R.frame_owner fr, target) ->
        R.stored_contribution next source observed =
        R.stored_contribution st source observed.
    Proof.
      intros st fr target input next changed source observed Hwrite Hother.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [phase value].
      cbn in Hwrite. inversion Hwrite; subst; clear Hwrite.
      unfold R.stored_contribution, R.register_reset.
      destruct (R.stored_side_cell
        (R.with_contributions base
          (R.update_map (R.contributions base)
            target (R.frame_owner fr) value))
        (R.frame_owner fr) target) as [old_phase old_scope]. cbn.
      destruct Features.restart_side_phases; cbn;
        destruct (R.rank_lt base (R.frame_min_scope fr) target); cbn;
        destruct (R.same_scope old_scope (Some (R.frame_min_scope fr)));
        cbn; try destruct old_scope; cbn;
        assert (Hswap : (observed, source) <>
          (target, R.frame_owner fr)) by
          (intro Heq; apply Hother; inversion Heq; reflexivity);
        rewrite (@lookup_cell_update_other D.t (R.contributions base)
          observed source target (R.frame_owner fr) value Hswap);
        subst base; unfold R.promote_side_target, R.promote_controlled;
        destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma side_cell_credit_write_other :
      forall st fr target input next changed source observed,
        R.write_side_contribution st fr target input = (next, changed) ->
        (source, observed) <> (R.frame_owner fr, target) ->
        side_cell_credit next source observed =
        side_cell_credit st source observed.
    Proof.
      intros st fr target input next changed source observed Hwrite Hother.
      unfold side_cell_credit.
      rewrite (stored_side_cell_write_other Hwrite Hother).
      rewrite (stored_contribution_write_other Hwrite Hother).
      reflexivity.
    Qed.

    Fixpoint source_side_credit
      (support : list V.t) (st : R.state) (source : V.t) : nat :=
      match support with
      | [] => 0
      | target :: rest =>
          side_cell_credit st source target +
          source_side_credit rest st source
      end.

    Lemma source_side_credit_write_nonincreasing :
      forall support st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        source_side_credit support next (R.frame_owner fr) <=
        source_side_credit support st (R.frame_owner fr).
    Proof.
      intros support. induction support as [|observed rest IH];
        intros st fr target input next changed Hwrite; cbn; [lia |].
      destruct (V.eq_dec observed target) as [-> | Hneq].
      - pose proof (write_side_credit_nonincreasing Hwrite).
        pose proof (IH _ _ _ _ _ _ Hwrite). lia.
      - rewrite (side_cell_credit_write_other Hwrite)
          by (intro Heq; inversion Heq; contradiction).
        pose proof (IH _ _ _ _ _ _ Hwrite). lia.
    Qed.

    Lemma source_side_credit_write_decreases :
      forall support st fr target input next,
        List.In target support ->
        R.write_side_contribution st fr target input = (next, true) ->
        source_side_credit support next (R.frame_owner fr) <
        source_side_credit support st (R.frame_owner fr).
    Proof.
      intros support. induction support as [|observed rest IH];
        intros st fr target input next Hin Hwrite; [contradiction |].
      cbn. destruct Hin as [Heq | Hin].
      - subst observed.
        pose proof (write_side_changed_credit_decreases Hwrite).
        pose proof (source_side_credit_write_nonincreasing rest Hwrite).
        lia.
      - destruct (V.eq_dec observed target) as [-> | Hneq].
        + pose proof (write_side_changed_credit_decreases Hwrite).
          pose proof (source_side_credit_write_nonincreasing rest Hwrite).
          lia.
        + rewrite (side_cell_credit_write_other Hwrite)
            by (intro Heq; inversion Heq; contradiction).
          pose proof (IH _ _ _ _ _ Hin Hwrite). lia.
    Qed.

    Lemma source_side_credit_write_other_source :
      forall support st fr target input next changed source,
        R.write_side_contribution st fr target input = (next, changed) ->
        source <> R.frame_owner fr ->
        source_side_credit support next source =
        source_side_credit support st source.
    Proof.
      intros support. induction support as [|observed rest IH];
        intros st fr target input next changed source Hwrite Hneq;
        cbn; [reflexivity |].
      rewrite (side_cell_credit_write_other Hwrite)
        by (intro Heq; inversion Heq; contradiction).
      now rewrite (IH _ _ _ _ _ _ _ Hwrite Hneq).
    Qed.

    Fixpoint total_side_credit_for
      (targets sources : list V.t) (st : R.state) : nat :=
      match sources with
      | [] => 0
      | source :: rest =>
          source_side_credit targets st source +
          total_side_credit_for targets rest st
      end.

    Definition total_side_credit
      (support : list V.t) (st : R.state) : nat :=
      total_side_credit_for support support st.

    Lemma total_side_credit_for_write_nonincreasing :
      forall targets sources st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        total_side_credit_for targets sources next <=
        total_side_credit_for targets sources st.
    Proof.
      intros targets sources. induction sources as [|source rest IH];
        intros st fr target input next changed Hwrite; cbn; [lia |].
      destruct (V.eq_dec source (R.frame_owner fr)) as [-> | Hneq].
      - pose proof (source_side_credit_write_nonincreasing targets Hwrite).
        pose proof (IH _ _ _ _ _ _ Hwrite). lia.
      - rewrite (source_side_credit_write_other_source targets Hwrite Hneq).
        pose proof (IH _ _ _ _ _ _ Hwrite). lia.
    Qed.

    Lemma total_side_credit_for_write_decreases :
      forall targets sources st fr target input next,
        List.In (R.frame_owner fr) sources ->
        List.In target targets ->
        R.write_side_contribution st fr target input = (next, true) ->
        total_side_credit_for targets sources next <
        total_side_credit_for targets sources st.
    Proof.
      intros targets sources. induction sources as [|source rest IH];
        intros st fr target input next Hsource Htarget Hwrite;
        [contradiction |].
      cbn. destruct Hsource as [Heq | Hsource].
      - subst source.
        pose proof (source_side_credit_write_decreases
          targets Htarget Hwrite).
        pose proof (total_side_credit_for_write_nonincreasing
          targets rest Hwrite). lia.
      - destruct (V.eq_dec source (R.frame_owner fr)) as [-> | Hneq].
        + pose proof (source_side_credit_write_decreases
            targets Htarget Hwrite).
          pose proof (total_side_credit_for_write_nonincreasing
            targets rest Hwrite). lia.
        + rewrite (source_side_credit_write_other_source
            targets Hwrite Hneq).
          pose proof (IH _ _ _ _ _ Hsource Htarget Hwrite). lia.
    Qed.

    Lemma total_side_credit_write_nonincreasing :
      forall support st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        total_side_credit support next <= total_side_credit support st.
    Proof.
      intros support st fr target input next changed Hwrite.
      unfold total_side_credit.
      eapply total_side_credit_for_write_nonincreasing. exact Hwrite.
    Qed.

    Lemma total_side_credit_write_decreases :
      forall support st fr target input next,
        List.In (R.frame_owner fr) support ->
        List.In target support ->
        R.write_side_contribution st fr target input = (next, true) ->
        total_side_credit support next < total_side_credit support st.
    Proof.
      intros support st fr target input next Hsource Htarget Hwrite.
      unfold total_side_credit.
      eapply total_side_credit_for_write_decreases; eassumption.
    Qed.

    Fixpoint reset_cells_other
      (ids : list R.side_cell_id) (cells : R.side_cell_table)
      (source target : V.t) :
      ~ List.In (source, target) ids ->
      M.lookup (R.lookup_map (R.reset_cells ids cells) source) target =
      M.lookup (R.lookup_map cells source) target.
    Proof.
      destruct ids as [|[updated_source updated_target] rest];
        intros Hnotin; cbn; [reflexivity |].
      assert (Hhead :
        (source, target) <> (updated_source, updated_target)).
      { intro Heq. apply Hnotin. left. symmetry. exact Heq. }
      assert (Hrest : ~ List.In (source, target) rest).
      { intro Hin. apply Hnotin. right. exact Hin. }
      rewrite (reset_cells_other rest _ source target Hrest).
      now apply lookup_cell_update_other.
    Defined.

    Lemma side_cell_credit_reset_unchanged :
      forall st scope source target,
        ~ List.In (source, target)
          (R.lookup_reset_ids (R.reset_at_close st) scope) ->
        side_cell_credit
          (R.reset_registered_cells st scope) source target =
        side_cell_credit st source target.
    Proof.
      intros st scope source target Hnotin.
      unfold side_cell_credit, R.reset_registered_cells.
      destruct Features.restart_side_phases; cbn; [|reflexivity].
      unfold R.stored_side_cell, R.stored_contribution. cbn.
      rewrite reset_cells_other by exact Hnotin. reflexivity.
    Qed.

    Lemma reset_credit_change_target_higher :
      forall st scope source target,
        state_resets_ranked st ->
        side_cell_credit
          (R.reset_registered_cells st scope) source target <>
        side_cell_credit st source target ->
        R.rank_lt st scope target = true.
    Proof.
      intros st scope source target Hranked Hchanged.
      destruct (List.in_dec R.cell_id_eq_dec (source, target)
        (R.lookup_reset_ids (R.reset_at_close st) scope))
        as [Hin | Hnotin].
      2: { exfalso. apply Hchanged.
           now apply side_cell_credit_reset_unchanged. }
      unfold R.lookup_reset_ids in Hin.
      destruct (M.lookup (R.reset_at_close st) scope)
        as [ids |] eqn:Hlookup; cbn in Hin; [|contradiction].
      eapply Hranked; eassumption.
    Qed.

    Lemma sigma_value_after_commit :
      forall st owner value queued readers,
        R.sigma_value
          (R.with_readers
            (R.enqueue_all
              (R.with_sigma st (M.update (R.sigma st) owner value))
              queued)
            readers) owner = value.
    Proof.
      intros. unfold R.sigma_value, R.enqueue_all. cbn.
      rewrite ML.lookup_update_same. reflexivity.
    Qed.

    Lemma set_value_credit_nonincreasing :
      forall st fr direct next next_fr,
        S.mem (R.frame_owner fr) (R.controlled st) = true ->
        R.set_value st fr direct = (next, next_fr) ->
        ordinary_credit next next_fr <= ordinary_credit st fr.
    Proof.
      intros st fr direct next next_fr Hcontrolled Hset.
      unfold R.set_value in Hset.
      set (candidate :=
        D.join direct (R.aggregate st (R.frame_owner fr))) in *.
      set (old := R.sigma_value st (R.frame_owner fr)) in *.
      destruct (R.equivalent candidate old) eqn:Hcandidate.
      - inversion Hset; subst. lia.
      - rewrite Hcontrolled in Hset.
        destruct (U.update false (R.frame_owner fr)
          (R.frame_phase fr) old candidate) as [phase value] eqn:Hupdate.
        cbn in Hset.
        destruct (R.equivalent value old) eqn:Hequivalent.
        + inversion Hset; subst. unfold ordinary_credit. cbn. fold old.
          assert (Hvalue : domain_equivalent value old).
          { unfold R.equivalent in Hequivalent.
            now apply Bool.andb_true_iff in Hequivalent. }
          rewrite <- (UL.remaining_changes_extensional phase Hvalue).
          pose proof (UL.remaining_changes_nonincreasing false
            (R.frame_owner fr) (R.frame_phase fr) old candidate) as Hcredit.
          now rewrite Hupdate in Hcredit.
        + inversion Hset; subst. unfold ordinary_credit. cbn.
          rewrite sigma_value_after_commit. fold old.
          pose proof (UL.remaining_changes_nonincreasing false
            (R.frame_owner fr) (R.frame_phase fr) old candidate) as Hcredit.
          now rewrite Hupdate in Hcredit.
    Qed.

    Lemma set_value_changed_credit_decreases :
      forall st fr direct next next_fr,
        S.mem (R.frame_owner fr) (R.controlled st) = true ->
        R.set_value st fr direct = (next, next_fr) ->
        R.equivalent
          (R.sigma_value next (R.frame_owner fr))
          (R.sigma_value st (R.frame_owner fr)) = false ->
        ordinary_credit next next_fr < ordinary_credit st fr.
    Proof.
      intros st fr direct next next_fr Hcontrolled Hset Hchanged.
      unfold R.set_value in Hset.
      set (candidate :=
        D.join direct (R.aggregate st (R.frame_owner fr))) in *.
      set (old := R.sigma_value st (R.frame_owner fr)) in *.
      destruct (R.equivalent candidate old) eqn:Hcandidate.
      - inversion Hset; subst. fold old in Hchanged.
        unfold R.equivalent in Hchanged.
        rewrite DL.leq_refl in Hchanged. cbn in Hchanged. discriminate.
      - rewrite Hcontrolled in Hset.
        destruct (U.update false (R.frame_owner fr)
          (R.frame_phase fr) old candidate) as [phase value] eqn:Hupdate.
        cbn in Hset.
        destruct (R.equivalent value old) eqn:Hequivalent.
        + inversion Hset; subst. fold old in Hchanged.
          unfold R.equivalent in Hchanged.
          rewrite DL.leq_refl in Hchanged. cbn in Hchanged. discriminate.
        + inversion Hset; subst. unfold ordinary_credit. cbn.
          rewrite sigma_value_after_commit. fold old.
          pose proof (@UL.update_change_consumes false
            (R.frame_owner fr) (R.frame_phase fr) old candidate) as Hcredit.
          rewrite Hupdate in Hcredit. apply Hcredit. intro Heq. cbn in Heq.
          unfold R.equivalent in Hequivalent.
          apply Bool.andb_false_iff in Hequivalent.
          destruct Heq as [Hleft Hright].
          destruct Hequivalent as [Hfalse |Hfalse];
            [rewrite Hleft in Hfalse |rewrite Hright in Hfalse]; discriminate.
    Qed.
  End Credits.

  Module ScopeBounds.
    Definition source_not_below_scope
      (st : R.state) (scope source : V.t) : Prop :=
      source = scope \/ R.rank_lt st scope source = true.

    Definition reset_sources_bounded (st : R.state) : Prop :=
      forall scope ids source target,
        M.lookup (R.reset_at_close st) scope = Some ids ->
        List.In (source, target) ids ->
        source_not_below_scope st scope source.

    Definition frame_scope_bounded (st : R.state) (fr : R.frame) : Prop :=
      source_not_below_scope st
        (R.frame_min_scope fr) (R.frame_owner fr).

    Fixpoint continuation_scopes_bounded
      (st : R.state) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          frame_scope_bounded st fr /\ continuation_scopes_bounded st rest
      end.

    Definition control_scopes_bounded
      (st : R.state) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
      | R.StartEpisode _ k => continuation_scopes_bounded st k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          frame_scope_bounded st fr /\ continuation_scopes_bounded st k
      | R.Return k => continuation_scopes_bounded st k
      end.

    Definition scopes_bounded (c : R.config) : Prop :=
      reset_sources_bounded (R.cfg_state c) /\
      control_scopes_bounded (R.cfg_state c) (R.cfg_control c).

    Lemma source_not_below_scope_extended :
      forall before after scope source,
        rank_extends before after ->
        source_not_below_scope before scope source ->
        source_not_below_scope after scope source.
    Proof.
      intros before after scope source Hextends [-> | Hlt].
      - now left.
      - right. pose proof (@rank_lt_true_ranked before scope source Hlt)
          as [Hscope Hsource].
        rewrite <- (@rank_lt_stable before after scope source
          Hextends Hscope Hsource). exact Hlt.
    Qed.

    Lemma reset_sources_bounded_view :
      forall before after,
        rank_extends before after ->
        R.reset_at_close after = R.reset_at_close before ->
        reset_sources_bounded before ->
        reset_sources_bounded after.
    Proof.
      intros before after Hextends Hresets Hbounded
        scope ids source target Hlookup Hin.
      rewrite Hresets in Hlookup.
      apply source_not_below_scope_extended with before; [exact Hextends |].
      eapply Hbounded; eauto.
    Qed.

    Lemma frame_scope_bounded_extended :
      forall before after fr,
        rank_extends before after ->
        frame_scope_bounded before fr -> frame_scope_bounded after fr.
    Proof.
      intros. now apply source_not_below_scope_extended with before.
    Qed.

    Lemma continuation_scopes_bounded_extended :
      forall before after k,
        rank_extends before after ->
        continuation_scopes_bounded before k ->
        continuation_scopes_bounded after k.
    Proof.
      intros before after k Hextends. induction k; cbn; intros Hbounded;
        try exact I.
      all: destruct Hbounded as [Hframe Hrest]; split.
      all: try (now apply frame_scope_bounded_extended with before).
      all: now apply IHk.
    Qed.

    Lemma reset_sources_bounded_remove :
      forall st (table : R.reset_table) scope id,
        (forall observed ids source target,
          M.lookup table observed = Some ids ->
          List.In (source, target) ids ->
          source_not_below_scope st observed source) ->
        forall observed ids source target,
          M.lookup (R.remove_registration table scope id) observed = Some ids ->
          List.In (source, target) ids ->
          source_not_below_scope st observed source.
    Proof.
      intros st table scope id Hbounded observed ids source target
        Hlookup Hin.
      unfold R.remove_registration in Hlookup.
      destruct (V.eq_dec observed scope) as [-> | Hneq].
      - rewrite ML.lookup_update_same in Hlookup.
        injection Hlookup as Hids. subst ids.
        unfold R.lookup_reset_ids in Hin.
        destruct (M.lookup table scope) as [old |] eqn:Hold;
          cbn in Hin; [|contradiction].
        exact (Hbounded scope old source target Hold
          (@remove_cell_id_in id old (source, target) Hin)).
      - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        eapply Hbounded; eauto.
    Qed.

    Lemma reset_sources_bounded_add :
      forall st (table : R.reset_table) scope source target,
        (forall observed ids source' target',
          M.lookup table observed = Some ids ->
          List.In (source', target') ids ->
          source_not_below_scope st observed source') ->
        source_not_below_scope st scope source ->
        forall observed ids source' target',
          M.lookup (R.add_registration table scope (source, target)) observed =
            Some ids ->
          List.In (source', target') ids ->
          source_not_below_scope st observed source'.
    Proof.
      intros st table scope source target Hbounded Hsource
        observed ids source' target' Hlookup Hin.
      unfold R.add_registration in Hlookup.
      destruct (V.eq_dec observed scope) as [-> | Hneq].
      - rewrite ML.lookup_update_same in Hlookup.
        injection Hlookup as Hids. subst ids.
        apply add_cell_id_in in Hin. destruct Hin as [Heq | Hin].
        + injection Heq as -> ->. exact Hsource.
        + unfold R.lookup_reset_ids in Hin.
          destruct (M.lookup table scope) as [old |] eqn:Hold;
            cbn in Hin; [|contradiction].
          eapply Hbounded; eauto.
      - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        eapply Hbounded; eauto.
    Qed.

    Lemma reset_sources_bounded_register :
      forall st source target scope phase,
        reset_sources_bounded st ->
        source_not_below_scope st scope source ->
        reset_sources_bounded
          (R.register_reset st source target scope phase).
    Proof.
      intros st source target scope phase Hbounded Hsource.
      unfold reset_sources_bounded in *.
      unfold R.register_reset. cbn.
      destruct (R.stored_side_cell st source target)
        as [old_phase old_scope]. cbn.
      destruct Features.restart_side_phases.
      - destruct (R.rank_lt st scope target); cbn.
        + destruct (R.same_scope old_scope (Some scope)).
          * exact Hbounded.
          * destruct old_scope as [previous |].
            -- eapply reset_sources_bounded_add.
               ++ eapply reset_sources_bounded_remove. exact Hbounded.
               ++ exact Hsource.
            -- now apply reset_sources_bounded_add.
        + destruct (R.same_scope old_scope None).
          * exact Hbounded.
          * destruct old_scope as [previous |].
            -- now apply reset_sources_bounded_remove.
            -- exact Hbounded.
      - cbn. destruct (R.same_scope old_scope None).
        + exact Hbounded.
        + destruct old_scope as [previous |].
          * now apply reset_sources_bounded_remove.
          * exact Hbounded.
    Qed.

    Lemma reset_sources_bounded_clear :
      forall st scope,
        reset_sources_bounded st ->
        reset_sources_bounded (R.reset_registered_cells st scope).
    Proof.
      intros st scope Hbounded.
      unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; [|exact Hbounded].
      intros observed ids source target Hlookup Hin. cbn in Hlookup.
      destruct (V.eq_dec observed scope) as [-> | Hneq].
      - rewrite ML.lookup_update_same in Hlookup.
        injection Hlookup as Hids. subst ids. contradiction.
      - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        eapply Hbounded; eauto.
    Qed.

    Lemma frame_scope_fresh :
      forall st owner phase,
        frame_scope_bounded st (R.fresh_frame st owner phase).
    Proof. intros. left. reflexivity. Qed.

    Lemma frame_scope_phase :
      forall st fr phase,
        frame_scope_bounded st fr ->
        frame_scope_bounded st (R.with_frame_phase fr phase).
    Proof. intros. exact H. Qed.

    Lemma frame_scope_side :
      forall st fr target input,
        frame_scope_bounded st fr ->
        frame_scope_bounded st (R.with_frame_side fr target input).
    Proof. intros. exact H. Qed.

    Lemma frame_scope_read :
      forall st fr minimum maximum,
        frame_scope_bounded st fr ->
        (minimum = R.frame_min_scope fr \/
         R.rank_lt st minimum (R.frame_min_scope fr) = true) ->
        frame_scope_bounded st (R.with_frame_read fr minimum maximum).
    Proof.
      intros st fr minimum maximum Hbounded Hminimum.
      unfold frame_scope_bounded, source_not_below_scope in *.
      cbn. destruct Hminimum as [-> | Hminimum].
      - exact Hbounded.
      - right. destruct Hbounded as [Heq | Hbounded].
        + now rewrite Heq.
        + pose proof (@rank_lt_true_ranked st minimum
            (R.frame_min_scope fr) Hminimum) as [Hmin Hscope].
          pose proof (@rank_lt_true_ranked st (R.frame_min_scope fr)
            (R.frame_owner fr) Hbounded) as [_ Howner].
          exact (@rank_lt_trans st minimum (R.frame_min_scope fr)
            (R.frame_owner fr) Hmin Hscope Howner Hminimum Hbounded).
    Qed.

    Lemma complete_get_scope :
      forall st fr target next next_fr value,
        frame_scope_bounded st fr ->
        R.complete_get st fr target = (next, next_fr, value) ->
        frame_scope_bounded next next_fr.
    Proof.
      intros st fr target next next_fr value Hbounded Hget.
      assert (Hlocal : frame_scope_bounded st
        (snd (fst (R.complete_get st fr target)))).
      { unfold R.complete_get. cbn.
        apply frame_scope_read; [exact Hbounded |].
        destruct (R.rank_lt st target (R.frame_min_scope fr)) eqn:Hlt.
        - right. exact Hlt.
        - left. reflexivity. }
      rewrite Hget in Hlocal. cbn in Hlocal.
      eapply frame_scope_bounded_extended; [|exact Hlocal].
      eapply rank_extends_complete_get. exact Hget.
    Qed.

    Lemma reset_sources_bounded_observe :
      forall st x,
        reset_sources_bounded st ->
        reset_sources_bounded (R.observe st x).
    Proof.
      intros st x Hbounded. eapply reset_sources_bounded_view.
      - eapply rank_extends_observe. reflexivity.
      - unfold R.observe. destruct (R.Ranking.observe (R.ranking st) x).
        reflexivity.
      - exact Hbounded.
    Qed.

    Lemma reset_sources_bounded_materialize :
      forall st x,
        reset_sources_bounded st ->
        reset_sources_bounded (R.materialize st x).
    Proof.
      intros st x Hbounded. eapply reset_sources_bounded_view.
      - apply rank_extends_materialize.
      - unfold R.materialize. destruct (M.lookup (R.sigma st) x);
          reflexivity.
      - exact Hbounded.
    Qed.

    Lemma reset_sources_bounded_enqueue :
      forall st x,
        reset_sources_bounded st -> reset_sources_bounded (R.enqueue st x).
    Proof.
      intros st x Hbounded. eapply reset_sources_bounded_view;
        [apply rank_extends_enqueue |reflexivity |exact Hbounded].
    Qed.

    Lemma write_side_scopes :
      forall st fr target input next changed,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        R.write_side_contribution st fr target input = (next, changed) ->
        reset_sources_bounded next /\ frame_scope_bounded next fr.
    Proof.
      intros st fr target input next changed Hreset Hframe Hwrite.
      assert (Hextends : rank_extends st next).
      { eapply rank_extends_write_side_contribution. exact Hwrite. }
      split.
      - unfold R.write_side_contribution in Hwrite.
        remember (R.promote_side_target st fr target) as base.
        destruct (U.update true target
          (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
          (R.stored_contribution base (R.frame_owner fr) target) input)
          as [phase value].
        inversion Hwrite; subst; clear Hwrite.
        apply reset_sources_bounded_register.
        + eapply reset_sources_bounded_view with
            (before := R.promote_side_target st fr target).
          * apply rank_extends_with_contributions.
          * reflexivity.
          * unfold R.promote_side_target.
            destruct (R.rank_lt st target (R.frame_owner fr));
              [exact Hreset |].
            eapply reset_sources_bounded_view;
              [apply rank_extends_promote_controlled
              |reflexivity |exact Hreset].
        + apply source_not_below_scope_extended with st.
          * eapply rank_extends_trans with
              (second := R.promote_side_target st fr target).
            -- apply rank_extends_promote_side_target.
            -- apply rank_extends_with_contributions.
          * exact Hframe.
      - now apply frame_scope_bounded_extended with st.
    Qed.

    Lemma set_value_scope :
      forall st fr direct next next_fr,
        frame_scope_bounded st fr ->
        R.set_value st fr direct = (next, next_fr) ->
        frame_scope_bounded next next_fr.
    Proof.
      intros st fr direct next next_fr Hframe Hset.
      apply frame_scope_bounded_extended with st.
      - eapply rank_extends_set_value. exact Hset.
      - unfold R.set_value in Hset.
        repeat match type of Hset with
          | context [if ?condition then _ else _] => destruct condition eqn:?
          end;
          inversion Hset; subst; try exact Hframe;
          now apply frame_scope_phase.
    Qed.

    Lemma reset_sources_bounded_set_value :
      forall st fr direct next next_fr,
        reset_sources_bounded st ->
        R.set_value st fr direct = (next, next_fr) ->
        reset_sources_bounded next.
    Proof.
      intros st fr direct next next_fr Hreset Hset.
      eapply reset_sources_bounded_view.
      - eapply rank_extends_set_value. exact Hset.
      - unfold R.set_value in Hset.
        repeat match type of Hset with
          | context [if ?condition then _ else _] => destruct condition eqn:?
          end;
          inversion Hset; subst; cbn; reflexivity.
      - exact Hreset.
    Qed.

    Lemma reset_sources_bounded_complete_get :
      forall st fr target next next_fr value,
        reset_sources_bounded st ->
        R.complete_get st fr target = (next, next_fr, value) ->
        reset_sources_bounded next.
    Proof.
      intros st fr target next next_fr value Hreset Hget.
      eapply reset_sources_bounded_view.
      - eapply rank_extends_complete_get. exact Hget.
      - unfold R.complete_get in Hget.
        repeat match type of Hget with
          | context [if ?condition then _ else _] => destruct condition eqn:?
          end;
          unfold R.materialize in Hget;
          destruct (M.lookup _ target);
          inversion Hget; subst; cbn; reflexivity.
      - exact Hreset.
    Qed.

    Lemma control_scopes_bounded_extended :
      forall before after control,
        rank_extends before after ->
        control_scopes_bounded before control ->
        control_scopes_bounded after control.
    Proof.
      intros before after control Hextends Hbounded.
      destruct control; cbn in *; try exact I.
      - now apply continuation_scopes_bounded_extended with before.
      - destruct Hbounded as [Hframe Hk]. split.
        + now apply frame_scope_bounded_extended with before.
        + now apply continuation_scopes_bounded_extended with before.
      - destruct Hbounded as [Hframe Hk]. split.
        + now apply frame_scope_bounded_extended with before.
        + now apply continuation_scopes_bounded_extended with before.
      - destruct Hbounded as [Hframe Hk]. split.
        + now apply frame_scope_bounded_extended with before.
        + now apply continuation_scopes_bounded_extended with before.
      - destruct Hbounded as [Hframe Hk]. split.
        + now apply frame_scope_bounded_extended with before.
        + now apply continuation_scopes_bounded_extended with before.
      - now apply continuation_scopes_bounded_extended with before.
    Qed.

    Lemma reset_sources_bounded_with_queue :
      forall st queue,
        reset_sources_bounded st ->
        reset_sources_bounded (R.with_queue st queue).
    Proof.
      intros. eapply reset_sources_bounded_view;
        [apply rank_extends_with_queue |reflexivity |exact H].
    Qed.

    Lemma reset_sources_bounded_publish_targets :
      forall st fr,
        reset_sources_bounded st ->
        reset_sources_bounded (R.publish_targets st fr).
    Proof.
      intros st fr Hbounded. eapply reset_sources_bounded_view.
      - apply rank_extends_same_ranking. reflexivity.
      - reflexivity.
      - exact Hbounded.
    Qed.

    Lemma reset_sources_bounded_get_base :
      forall st target,
        reset_sources_bounded st ->
        reset_sources_bounded
          (if R.is_materialized (R.observe st target) target
           then R.observe st target
           else R.enqueue (R.observe st target) target).
    Proof.
      intros st target Hbounded.
      pose proof (reset_sources_bounded_observe target Hbounded) as Hobserved.
      destruct (R.is_materialized (R.observe st target) target).
      - exact Hobserved.
      - now apply reset_sources_bounded_enqueue.
    Qed.

    Lemma next_runloop_scopes :
      forall tf st after,
        reset_sources_bounded st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunLoop |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st after Hreset Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |];
        try discriminate.
      inversion Hstep; subst. split.
      - now apply reset_sources_bounded_with_queue.
      - exact I.
    Qed.

    Lemma next_seeds_scopes :
      forall tf st roots after,
        reset_sources_bounded st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds roots |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st roots after Hreset Hstep. destruct roots as [|root rest].
      - cbn in Hstep. inversion Hstep; subst. split; [exact Hreset |exact I].
      - cbn -[R.observe] in Hstep.
        remember (R.observe st root) as observed eqn:Hobserve.
        assert (Hreset' : reset_sources_bounded observed).
        { subst observed. now apply reset_sources_bounded_observe. }
        destruct (R.is_materialized observed root).
        + inversion Hstep; subst. split; [exact Hreset' |exact I].
        + inversion Hstep; subst. split; [exact Hreset' |exact I].
    Qed.

    Lemma next_seedloop_scopes :
      forall tf st roots after,
        reset_sources_bounded st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeedLoop roots |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st roots after Hreset Hstep. cbn in Hstep.
      destruct (R.queue_pop (R.queue st)) as [[owner rest] |].
      - inversion Hstep; subst. split.
        + now apply reset_sources_bounded_with_queue.
        + exact I.
      - inversion Hstep; subst. split; [exact Hreset |exact I].
    Qed.

    Lemma next_start_episode_scopes :
      forall tf st owner k after,
        reset_sources_bounded st ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st owner k after Hreset Hk Hstep. cbn in Hstep.
      inversion Hstep; subst. split.
      - now apply reset_sources_bounded_materialize.
      - cbn. split.
        + apply frame_scope_fresh.
        + apply continuation_scopes_bounded_extended with st;
            [apply rank_extends_materialize |exact Hk].
    Qed.

    Lemma next_runrhs_ret_scopes :
      forall tf st fr direct k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Ret direct) k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr direct k after Hreset Hframe Hk Hstep.
      cbn in Hstep. inversion Hstep; subst. split.
      - exact Hreset.
      - cbn. split; assumption.
    Qed.

    Lemma next_runrhs_get_scopes :
      forall tf st fr target kget k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Get target kget) k |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr target kget k after Hreset Hframe Hk Hstep.
      cbn -[R.observe R.complete_get R.enqueue] in Hstep.
      remember (R.observe st target) as observed eqn:Hobserve.
      assert (Hext0 : rank_extends st observed).
      { subst observed. eapply rank_extends_observe. reflexivity. }
      assert (Hreset0 : reset_sources_bounded observed).
      { subst observed. now apply reset_sources_bounded_observe. }
      pose proof (frame_scope_bounded_extended Hext0 Hframe) as Hframe0.
      pose proof (@continuation_scopes_bounded_extended
        st observed k Hext0 Hk) as Hk0.
      destruct (negb (R.is_materialized observed target) &&
        R.rank_lt observed (R.frame_owner fr) target)%bool eqn:Hdefer.
      - inversion Hstep; subst. split; [exact Hreset0 |].
        cbn. split; assumption.
      - remember
          (if R.is_materialized observed target
           then observed else R.enqueue observed target) as base eqn:Hbase.
        assert (Hext1 : rank_extends observed base).
        { subst base. destruct (R.is_materialized observed target);
            [apply rank_extends_refl |apply rank_extends_enqueue]. }
        assert (Hreset1 : reset_sources_bounded base).
        { subst base. destruct (R.is_materialized observed target);
            [exact Hreset0 |now apply reset_sources_bounded_enqueue]. }
        pose proof (frame_scope_bounded_extended Hext1 Hframe0) as Hframe1.
        pose proof (@continuation_scopes_bounded_extended
          observed base k Hext1 Hk0) as Hk1.
        destruct (R.complete_get base fr target)
          as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst. split.
        + eapply reset_sources_bounded_complete_get; eauto.
        + cbn. split.
          * eapply complete_get_scope; eauto.
          * eapply continuation_scopes_bounded_extended.
            -- eapply rank_extends_complete_get. exact Hget.
            -- exact Hk1.
    Qed.

    Lemma next_runrhs_side_scopes :
      forall tf st fr target raw body k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr
               (R.ConstraintSystem.Side target raw body) k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr target raw body k after Hreset Hframe Hk Hstep.
      cbn -[R.observe R.record_side_input R.write_side_contribution
        R.continue_side] in Hstep.
      remember (R.observe st target) as observed eqn:Hobserve.
      assert (Hext0 : rank_extends st observed).
      { subst observed. eapply rank_extends_observe. reflexivity. }
      assert (Hreset0 : reset_sources_bounded observed).
      { subst observed. now apply reset_sources_bounded_observe. }
      pose proof (frame_scope_bounded_extended Hext0 Hframe) as Hframe0.
      pose proof (@continuation_scopes_bounded_extended
        st observed k Hext0 Hk) as Hk0.
      destruct (R.record_side_input fr target raw)
        as [fr1 input] eqn:Hrecord.
      assert (Hfr1 : frame_scope_bounded observed fr1).
      { unfold R.record_side_input in Hrecord.
        inversion Hrecord; subst. now apply frame_scope_side. }
      destruct (R.write_side_contribution observed fr1 target input)
        as [next changed] eqn:Hwrite.
      pose proof (@write_side_scopes observed fr1 target input next changed
        Hreset0 Hfr1 Hwrite) as [Hreset1 Hframe1].
      assert (Hk1 : continuation_scopes_bounded next k).
      { eapply continuation_scopes_bounded_extended;
          [eapply rank_extends_write_side_contribution; exact Hwrite
          |exact Hk0]. }
      unfold R.continue_side in Hstep. destruct changed.
      - destruct (R.rank_lt next (R.frame_owner fr1) target &&
          negb (R.is_materialized next target))%bool.
        + inversion Hstep; subst. split; [exact Hreset1 |].
          cbn. split; assumption.
        + inversion Hstep; subst. split.
          * now apply reset_sources_bounded_enqueue.
          * cbn. split.
            -- now apply frame_scope_bounded_extended with next;
                 [apply rank_extends_enqueue |].
            -- now apply continuation_scopes_bounded_extended with next;
                 [apply rank_extends_enqueue |].
      - inversion Hstep; subst. split; [exact Hreset1 |].
        cbn. split; assumption.
    Qed.

    Lemma next_runrhs_spawn_scopes :
      forall tf st fr target body k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr
               (R.ConstraintSystem.Spawn target body) k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr target body k after Hreset Hframe Hk Hstep.
      cbn -[R.observe R.materialize R.enqueue] in Hstep.
      remember (R.observe st target) as observed eqn:Hobserve.
      assert (Hext0 : rank_extends st observed).
      { subst observed. eapply rank_extends_observe. reflexivity. }
      assert (Hreset0 : reset_sources_bounded observed).
      { subst observed. now apply reset_sources_bounded_observe. }
      pose proof (frame_scope_bounded_extended Hext0 Hframe) as Hframe0.
      pose proof (@continuation_scopes_bounded_extended
        st observed k Hext0 Hk) as Hk0.
      destruct (R.is_materialized observed target).
      - inversion Hstep; subst. split; [exact Hreset0 |].
        cbn. split; assumption.
      - destruct (R.rank_lt observed (R.frame_owner fr) target).
        + inversion Hstep; subst. split; [exact Hreset0 |].
          cbn. split; assumption.
        + inversion Hstep; subst. split.
          * apply reset_sources_bounded_materialize.
            now apply reset_sources_bounded_enqueue.
          * cbn. split.
            -- eapply frame_scope_bounded_extended.
               ++ eapply rank_extends_trans;
                    [apply rank_extends_enqueue |apply rank_extends_materialize].
               ++ exact Hframe0.
            -- eapply continuation_scopes_bounded_extended.
               ++ eapply rank_extends_trans;
                    [apply rank_extends_enqueue |apply rank_extends_materialize].
               ++ exact Hk0.
    Qed.

    Lemma next_runrhs_scopes :
      forall tf st fr body k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr body k after Hreset Hframe Hk Hstep.
      destruct body.
      - eapply next_runrhs_ret_scopes; eauto.
      - eapply next_runrhs_get_scopes; eauto.
      - eapply next_runrhs_side_scopes; eauto.
      - eapply next_runrhs_spawn_scopes; eauto.
    Qed.

    Lemma next_rundead_scopes :
      forall tf st fr direct pending k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr direct pending k after Hreset Hframe Hk Hstep.
      destruct pending as [|target remaining].
      - cbn -[R.publish_targets] in Hstep. inversion Hstep; subst. split.
        + now apply reset_sources_bounded_publish_targets.
        + cbn. split.
          * apply frame_scope_bounded_extended with st;
              [apply rank_extends_same_ranking; reflexivity |exact Hframe].
          * apply continuation_scopes_bounded_extended with st;
              [apply rank_extends_same_ranking; reflexivity |exact Hk].
      - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        + inversion Hstep; subst. split; [exact Hreset |].
          cbn. split; assumption.
        + destruct (R.write_side_contribution st fr target D.bottom)
            as [next changed] eqn:Hwrite.
          pose proof (@write_side_scopes st fr target D.bottom next changed
            Hreset Hframe Hwrite) as [Hreset1 Hframe1].
          assert (Hk1 : continuation_scopes_bounded next k).
          { eapply continuation_scopes_bounded_extended;
              [eapply rank_extends_write_side_contribution; exact Hwrite
              |exact Hk]. }
          unfold R.continue_dead in Hstep. destruct changed.
          * destruct (R.rank_lt next (R.frame_owner fr) target &&
              negb (R.is_materialized next target))%bool.
            -- inversion Hstep; subst. split; [exact Hreset1 |].
               cbn. split; assumption.
            -- inversion Hstep; subst. split.
               ++ now apply reset_sources_bounded_enqueue.
               ++ cbn. split.
                  ** now apply frame_scope_bounded_extended with next;
                       [apply rank_extends_enqueue |].
                  ** now apply continuation_scopes_bounded_extended with next;
                       [apply rank_extends_enqueue |].
          * inversion Hstep; subst. split; [exact Hreset1 |].
            cbn. split; assumption.
    Qed.

    Lemma next_runcommit_scopes :
      forall tf st fr direct k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit fr direct k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr direct k after Hreset Hframe Hk Hstep.
      cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
      inversion Hstep; subst.
      split.
      - change (reset_sources_bounded next).
        eapply reset_sources_bounded_set_value; eauto.
      - cbn. split.
        + change (frame_scope_bounded next next_fr).
          eapply set_value_scope; eauto.
        + eapply continuation_scopes_bounded_extended with st.
          * eapply rank_extends_trans;
              [eapply rank_extends_set_value; exact Hset
              |apply rank_extends_refl].
          * exact Hk.
    Qed.

    Lemma clear_return_scopes :
      forall st owner k,
        reset_sources_bounded st ->
        continuation_scopes_bounded st k ->
        scopes_bounded
          {| R.cfg_state := R.reset_registered_cells st owner;
             R.cfg_control := R.Return k |}.
    Proof.
      intros st owner k Hreset Hk. split.
      - now apply reset_sources_bounded_clear.
      - cbn. apply continuation_scopes_bounded_extended with st.
        + apply rank_extends_reset_registered_cells.
        + exact Hk.
    Qed.

    Lemma next_rundrain_scopes :
      forall tf st fr k after,
        reset_sources_bounded st ->
        frame_scope_bounded st fr ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} =
          Some after ->
        scopes_bounded after.
    Proof.
      intros tf st fr k after Hreset Hframe Hk Hstep.
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      - destruct (V.eq_dec next (R.frame_owner fr)).
        + destruct (R.queue_pop (R.queue st)) as [[head rest] |];
            try discriminate.
          inversion Hstep; subst. split.
          * now apply reset_sources_bounded_with_queue.
          * cbn. split.
            -- apply frame_scope_fresh.
            -- now apply continuation_scopes_bounded_extended with st;
                 [apply rank_extends_with_queue |].
        + destruct (R.rank_lt st (R.frame_owner fr) next).
          * destruct (R.queue_pop (R.queue st)) as [[head rest] |];
              try discriminate.
            inversion Hstep; subst. split.
            -- now apply reset_sources_bounded_with_queue.
            -- cbn. split.
               ++ now apply frame_scope_bounded_extended with st;
                    [apply rank_extends_with_queue |].
               ++ now apply continuation_scopes_bounded_extended with st;
                    [apply rank_extends_with_queue |].
          * inversion Hstep; subst. now apply clear_return_scopes.
      - inversion Hstep; subst. now apply clear_return_scopes.
    Qed.

    Lemma next_return_scopes :
      forall tf st k after,
        reset_sources_bounded st ->
        continuation_scopes_bounded st k ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
        scopes_bounded after.
    Proof.
      intros tf st k after Hreset Hcontrol Hstep.
      destruct k.
      - cbn in Hstep. inversion Hstep; subst. split; assumption.
      - cbn in Hstep. inversion Hstep; subst. split; assumption.
      - cbn -[R.complete_get] in Hstep.
        cbn in Hcontrol. destruct Hcontrol as [Hframe Hrest].
        destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst. split.
        + eapply reset_sources_bounded_complete_get; eauto.
        + cbn. split.
          * eapply complete_get_scope; eauto.
          * eapply continuation_scopes_bounded_extended.
            -- eapply rank_extends_complete_get. exact Hget.
            -- exact Hrest.
      - cbn in Hstep. inversion Hstep; subst.
        cbn in Hcontrol. destruct Hcontrol as [Hframe Hrest].
        split; [exact Hreset |]. cbn. split; assumption.
      - cbn in Hstep. inversion Hstep; subst.
        cbn in Hcontrol. destruct Hcontrol as [Hframe Hrest].
        split; [exact Hreset |]. cbn. split; assumption.
      - cbn in Hstep. inversion Hstep; subst.
        cbn in Hcontrol. destruct Hcontrol as [Hframe Hrest].
        split; [exact Hreset |]. cbn. split; assumption.
      - cbn in Hstep. inversion Hstep; subst.
        cbn in Hcontrol. destruct Hcontrol as [Hframe Hrest].
        split; [exact Hreset |]. cbn. split; assumption.
    Qed.

    Lemma next_config_scopes_bounded :
      forall tf before after,
        scopes_bounded before ->
        R.next_config tf before = Some after ->
        scopes_bounded after.
    Proof.
      intros tf [st control] after [Hreset Hcontrol] Hstep.
      cbn in Hreset, Hcontrol. destruct control.
      - eapply next_runloop_scopes; eauto.
      - eapply next_seeds_scopes; eauto.
      - eapply next_seedloop_scopes; eauto.
      - eapply next_start_episode_scopes; eauto.
      - destruct Hcontrol as [Hframe Hk].
        eapply next_runrhs_scopes; eauto.
      - destruct Hcontrol as [Hframe Hk].
        eapply next_rundead_scopes; eauto.
      - destruct Hcontrol as [Hframe Hk].
        eapply next_runcommit_scopes; eauto.
      - destruct Hcontrol as [Hframe Hk].
        eapply next_rundrain_scopes; eauto.
      - eapply next_return_scopes; eauto.
    Qed.

    Theorem reachable_scopes_bounded :
      forall tf roots c,
        Sem.steps tf (R.initial_config roots) c ->
        scopes_bounded c.
    Proof.
      intros tf roots c Hsteps.
      assert (Hinitial : scopes_bounded (R.initial_config roots)).
      { split.
        - intros scope ids source target Hlookup.
          cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
        - exact I. }
      revert Hinitial. induction Hsteps; intros Hbounded.
      - exact Hbounded.
      - apply IHHsteps. eapply next_config_scopes_bounded; eauto.
    Qed.
  End ScopeBounds.

  Lemma reset_above_preserves_source_cell :
    forall st scope source target,
      ScopeBounds.reset_sources_bounded st ->
      R.rank_lt st source scope = true ->
      Credits.side_cell_credit
        (R.reset_registered_cells st scope) source target =
      Credits.side_cell_credit st source target.
  Proof.
    intros st scope source target Hbounded Habove.
    apply Credits.side_cell_credit_reset_unchanged. intro Hin.
    unfold R.lookup_reset_ids in Hin.
    destruct (M.lookup (R.reset_at_close st) scope)
      as [ids |] eqn:Hlookup; cbn in Hin; [|contradiction].
    pose proof (Hbounded scope ids source target Hlookup Hin)
      as [Heq | Hbelow].
    - subst scope.
      pose proof (proj1 (@rank_lt_true_ranked st source source Habove)) as Hr.
      rewrite (rank_lt_irrefl Hr) in Habove. discriminate.
    - pose proof (@rank_lt_true_ranked st source scope Habove)
        as [Hsource Hscope].
      rewrite (@rank_lt_asymmetric st source scope Hsource Hscope Habove)
        in Hbelow. discriminate.
  Qed.

  Lemma reset_above_preserves_source_credit :
    forall support st scope source,
      ScopeBounds.reset_sources_bounded st ->
      R.rank_lt st source scope = true ->
      Credits.source_side_credit support
        (R.reset_registered_cells st scope) source =
      Credits.source_side_credit support st source.
  Proof.
    intros support. induction support as [|target rest IH];
      intros st scope source Hbounded Habove; cbn; [reflexivity |].
    rewrite (@reset_above_preserves_source_cell
      st scope source target Hbounded Habove).
    rewrite (@IH st scope source Hbounded Habove). reflexivity.
  Qed.

  Module ReaderOrder.
    Definition controlled_mono (before after : R.state) : Prop :=
      forall x,
        S.mem x (R.controlled before) = true ->
        S.mem x (R.controlled after) = true.

    Lemma controlled_mono_same :
      forall before after,
        R.controlled after = R.controlled before ->
        controlled_mono before after.
    Proof.
      intros before after Heq. unfold controlled_mono.
      intros x Hmem. rewrite Heq. exact Hmem.
    Qed.

    Lemma controlled_mono_promote :
      forall st x, controlled_mono st (R.promote_controlled st x).
    Proof.
      intros st x observed Hmem. cbn. apply SL.add_spec. now right.
    Qed.

    Lemma controlled_mono_observe :
      forall st x, controlled_mono st (R.observe st x).
    Proof.
      intros. apply controlled_mono_same. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
    Qed.

    Lemma controlled_mono_materialize :
      forall st x, controlled_mono st (R.materialize st x).
    Proof.
      intros. apply controlled_mono_same. unfold R.materialize.
      destruct (M.lookup (R.sigma st) x); reflexivity.
    Qed.

    Lemma controlled_mono_enqueue :
      forall st x, controlled_mono st (R.enqueue st x).
    Proof. intros. apply controlled_mono_same. reflexivity. Qed.

    Lemma controlled_mono_with_queue :
      forall st queue, controlled_mono st (R.with_queue st queue).
    Proof. intros. apply controlled_mono_same. reflexivity. Qed.

    Lemma controlled_mono_publish_targets :
      forall st fr, controlled_mono st (R.publish_targets st fr).
    Proof. intros. apply controlled_mono_same. reflexivity. Qed.

    Lemma controlled_mono_reset_registered :
      forall st owner,
        controlled_mono st (R.reset_registered_cells st owner).
    Proof.
      intros. apply controlled_mono_same. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma controlled_mono_write_side :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        controlled_mono st next.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [next_phase contribution].
      inversion Hwrite; subst; clear Hwrite.
      unfold base, R.promote_side_target.
      destruct (R.rank_lt st target (R.frame_owner fr)).
      - apply controlled_mono_same. reflexivity.
      - exact (controlled_mono_promote st (R.frame_owner fr)).
    Qed.

    Definition reader_edges_ordered (st : R.state) : Prop :=
      forall target source,
        S.mem source (R.lookup_set (R.readers st) target) = true ->
        R.rank_lt st source target = true \/
        S.mem target (R.controlled st) = true.

    Lemma reader_edges_ordered_same :
      forall before after,
        reader_edges_ordered before ->
        rank_extends before after ->
        R.readers after = R.readers before ->
        controlled_mono before after ->
        reader_edges_ordered after.
    Proof.
      intros before after Hordered Hextends Hreaders Hcontrolled
        target source Hmem.
      unfold R.lookup_set in Hmem. rewrite Hreaders in Hmem.
      destruct (Hordered target source Hmem) as [Hrank | Hknown].
      - left. pose proof (@rank_lt_true_ranked before source target Hrank)
          as [Hsource Htarget].
        rewrite <- (@rank_lt_stable before after source target
          Hextends Hsource Htarget). exact Hrank.
      - right. now apply Hcontrolled.
    Qed.

    Lemma reader_edges_ordered_observe :
      forall st target,
        reader_edges_ordered st ->
        reader_edges_ordered (R.observe st target).
    Proof.
      intros st target Hordered. eapply reader_edges_ordered_same.
      - exact Hordered.
      - eapply rank_extends_observe. reflexivity.
      - unfold R.observe.
        destruct (R.Ranking.observe (R.ranking st) target). reflexivity.
      - apply controlled_mono_observe.
    Qed.

    Lemma reader_edges_ordered_promote :
      forall st target,
        reader_edges_ordered st ->
        reader_edges_ordered (R.promote_controlled st target).
    Proof.
      intros st target Hordered. eapply reader_edges_ordered_same.
      - exact Hordered.
      - apply rank_extends_promote_controlled.
      - reflexivity.
      - apply controlled_mono_promote.
    Qed.

    Lemma reader_edges_ordered_materialize :
      forall st target,
        reader_edges_ordered st ->
        reader_edges_ordered (R.materialize st target).
    Proof.
      intros st target Hordered. eapply reader_edges_ordered_same.
      - exact Hordered.
      - apply rank_extends_materialize.
      - unfold R.materialize.
        destruct (M.lookup (R.sigma st) target); reflexivity.
      - apply controlled_mono_materialize.
    Qed.

    Lemma reader_edges_ordered_enqueue :
      forall st target,
        reader_edges_ordered st -> reader_edges_ordered (R.enqueue st target).
    Proof.
      intros st target Hordered. eapply reader_edges_ordered_same;
        [exact Hordered |apply rank_extends_enqueue |reflexivity |
         apply controlled_mono_enqueue].
    Qed.

    Lemma reader_edges_ordered_with_queue :
      forall st queue,
        reader_edges_ordered st ->
        reader_edges_ordered (R.with_queue st queue).
    Proof.
      intros st queue Hordered. eapply reader_edges_ordered_same;
        [exact Hordered |apply rank_extends_with_queue |reflexivity |
         apply controlled_mono_with_queue].
    Qed.

    Lemma reader_edges_ordered_complete_get :
      forall st fr target next next_fr value,
        reader_edges_ordered st ->
        R.complete_get st fr target = (next, next_fr, value) ->
        reader_edges_ordered next.
    Proof.
      intros st fr target next next_fr value Hordered Hget.
      unfold R.complete_get in Hget.
      set (owner := R.frame_owner fr) in *.
      set (st1 := if R.rank_lt st owner target
        then st else R.promote_controlled st target) in *.
      assert (Hst1 : reader_edges_ordered st1).
      { subst st1. destruct (R.rank_lt st owner target);
          auto using reader_edges_ordered_promote. }
      assert (Hnew : R.rank_lt st1 owner target = true \/
        S.mem target (R.controlled st1) = true).
      { subst st1. destruct (R.rank_lt st owner target) eqn:Hhigher.
        - now left.
        - right. cbn. apply SL.add_spec. now left. }
      set (new_readers := M.update (R.readers st1) target
        (S.add owner (R.lookup_set (R.readers st1) target))).
      assert (Hupdated : reader_edges_ordered
        (R.with_readers st1 new_readers)).
      { intros observed source Hmem. unfold R.lookup_set in Hmem. cbn in Hmem.
        subst new_readers.
        destruct (V.eq_dec observed target) as [-> | Hneq].
        - rewrite ML.lookup_update_same in Hmem.
          apply SL.add_spec in Hmem. destruct Hmem as [-> | Hmem].
          + exact Hnew.
          + now apply Hst1.
        - rewrite ML.lookup_update_other in Hmem by exact Hneq.
          now apply Hst1. }
      inversion Hget; subst next next_fr value.
      apply reader_edges_ordered_materialize. exact Hupdated.
    Qed.

    Lemma write_side_readers :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        R.readers next = R.readers st.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [next_phase contribution].
      inversion Hwrite; subst. unfold base, R.promote_side_target.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma reader_edges_ordered_write_side :
      forall st fr target input next changed,
        reader_edges_ordered st ->
        R.write_side_contribution st fr target input = (next, changed) ->
        reader_edges_ordered next.
    Proof.
      intros st fr target input next changed Hordered Hwrite.
      eapply reader_edges_ordered_same.
      - exact Hordered.
      - eapply rank_extends_write_side_contribution. exact Hwrite.
      - eapply write_side_readers. exact Hwrite.
      - eapply controlled_mono_write_side. exact Hwrite.
    Qed.

    Lemma reader_edges_ordered_reset_registered :
      forall st owner,
        reader_edges_ordered st ->
        reader_edges_ordered (R.reset_registered_cells st owner).
    Proof.
      intros st owner Hordered. eapply reader_edges_ordered_same.
      - exact Hordered.
      - apply rank_extends_reset_registered_cells.
      - unfold R.reset_registered_cells.
        destruct Features.restart_side_phases; reflexivity.
      - apply controlled_mono_reset_registered.
    Qed.

    Lemma reader_edges_ordered_publish_targets :
      forall st fr,
        reader_edges_ordered st ->
        reader_edges_ordered (R.publish_targets st fr).
    Proof.
      intros st fr Hordered. eapply reader_edges_ordered_same.
      - exact Hordered.
      - apply rank_extends_same_ranking. reflexivity.
      - reflexivity.
      - apply controlled_mono_publish_targets.
    Qed.

    Lemma reader_edges_ordered_set_value :
      forall st fr direct next next_fr,
        reader_edges_ordered st ->
        R.set_value st fr direct = (next, next_fr) ->
        reader_edges_ordered next.
    Proof.
      intros st fr direct next next_fr Hordered Hset.
      assert (Hfst : reader_edges_ordered (fst (R.set_value st fr direct))).
      { unfold R.set_value.
        destruct (R.equivalent
          (D.join direct (R.aggregate st (R.frame_owner fr)))
          (R.sigma_value st (R.frame_owner fr)));
          [exact Hordered |].
        destruct (if S.mem (R.frame_owner fr) (R.controlled st)
          then U.update false (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr)))
          else (R.frame_phase fr,
            D.join direct (R.aggregate st (R.frame_owner fr))))
          as [phase value].
        cbn. destruct (R.equivalent value
          (R.sigma_value st (R.frame_owner fr)));
          [exact Hordered |].
        intros observed source Hmem.
        unfold R.lookup_set in Hmem. cbn in Hmem.
        destruct (V.eq_dec observed (R.frame_owner fr)) as [-> | Hneq].
        - rewrite ML.lookup_update_same in Hmem.
          rewrite SL.empty_spec in Hmem. discriminate.
        - rewrite ML.lookup_update_other in Hmem by exact Hneq.
          now apply Hordered. }
      rewrite Hset in Hfst. exact Hfst.
    Qed.

    Lemma run_rhs_reader_edges_ordered :
      forall tf st fr body k after,
        reader_edges_ordered st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} =
          Some after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      intros tf st fr body k after Hordered Hstep.
      destruct body as [direct | target next | target raw next | target next].
      - cbn in Hstep. inversion Hstep; subst. exact Hordered.
      - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
        set (st0 := R.observe st target) in *.
        assert (Hst0 : reader_edges_ordered st0).
        { subst st0. now apply reader_edges_ordered_observe. }
        destruct (negb (R.is_materialized st0 target) &&
          R.rank_lt st0 (R.frame_owner fr) target)%bool.
        + inversion Hstep; subst. exact Hst0.
        + set (st1 := if R.is_materialized st0 target
            then st0 else R.enqueue st0 target) in *.
          assert (Hst1 : reader_edges_ordered st1).
          { subst st1. destruct (R.is_materialized st0 target);
              auto using reader_edges_ordered_enqueue. }
          destruct (R.complete_get st1 fr target)
            as [[st2 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          eapply reader_edges_ordered_complete_get; eauto.
      - cbn -[R.observe R.record_side_input R.write_side_contribution
          R.continue_side] in Hstep.
        set (st0 := R.observe st target) in *.
        assert (Hst0 : reader_edges_ordered st0).
        { subst st0. now apply reader_edges_ordered_observe. }
        destruct (R.record_side_input fr target raw) as [fr1 input].
        destruct (R.write_side_contribution st0 fr1 target input)
          as [st1 changed] eqn:Hwrite.
        assert (Hst1 : reader_edges_ordered st1).
        { eapply reader_edges_ordered_write_side; eauto. }
        unfold R.continue_side in Hstep.
        destruct changed;
          try destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
            negb (R.is_materialized st1 target))%bool;
          inversion Hstep; subst;
          auto using reader_edges_ordered_enqueue.
      - cbn -[R.observe R.materialize R.enqueue] in Hstep.
        set (st0 := R.observe st target) in *.
        assert (Hst0 : reader_edges_ordered st0).
        { subst st0. now apply reader_edges_ordered_observe. }
        destruct (R.is_materialized st0 target).
        + inversion Hstep; subst. exact Hst0.
        + destruct (R.rank_lt st0 (R.frame_owner fr) target).
          * inversion Hstep; subst. exact Hst0.
          * inversion Hstep; subst. apply reader_edges_ordered_materialize.
            now apply reader_edges_ordered_enqueue.
    Qed.

    Lemma run_dead_reader_edges_ordered :
      forall tf st fr direct pending k after,
        reader_edges_ordered st ->
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      intros tf st fr direct pending k after Hordered Hstep.
      destruct pending as [|target remaining].
      - cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
        now apply reader_edges_ordered_publish_targets.
      - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        + inversion Hstep; subst. exact Hordered.
        + destruct (R.write_side_contribution st fr target D.bottom)
            as [st1 changed] eqn:Hwrite.
          assert (Hst1 : reader_edges_ordered st1).
          { eapply reader_edges_ordered_write_side; eauto. }
          unfold R.continue_dead in Hstep.
          destruct changed;
            try destruct (R.rank_lt st1 (R.frame_owner fr) target &&
              negb (R.is_materialized st1 target))%bool;
            inversion Hstep; subst;
            auto using reader_edges_ordered_enqueue.
    Qed.

    Lemma run_drain_reader_edges_ordered :
      forall tf st fr k after,
        reader_edges_ordered st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} =
          Some after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      intros tf st fr k after Hordered Hstep.
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [queued |].
      - destruct (V.eq_dec queued (R.frame_owner fr)).
        + destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
            try discriminate. inversion Hstep; subst.
          now apply reader_edges_ordered_with_queue.
        + destruct (R.rank_lt st (R.frame_owner fr) queued).
          * destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
              try discriminate. inversion Hstep; subst.
            now apply reader_edges_ordered_with_queue.
          * inversion Hstep; subst.
            now apply reader_edges_ordered_reset_registered.
      - inversion Hstep; subst.
        now apply reader_edges_ordered_reset_registered.
    Qed.

    Lemma return_reader_edges_ordered :
      forall tf st k after,
        reader_edges_ordered st ->
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      intros tf st k after Hordered Hstep.
      destruct k as
        [|remaining |fr target next rest |fr next rest |fr next rest
         |fr direct pending rest |fr rest];
        cbn -[R.complete_get] in Hstep;
        try (inversion Hstep; subst; exact Hordered).
      destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      inversion Hstep; subst. eapply reader_edges_ordered_complete_get; eauto.
    Qed.

    Theorem next_config_reader_edges_ordered :
      forall tf before after,
        reader_edges_ordered (R.cfg_state before) ->
        R.next_config tf before = Some after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      intros tf [st control] after Hordered Hstep.
      destruct control as
        [|roots |remaining |owner k |fr body k |fr direct pending k
         |fr direct k |fr k |k].
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[popped rest] |]; try discriminate.
        inversion Hstep; subst. now apply reader_edges_ordered_with_queue.
      - destruct roots as [|root roots]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. exact Hordered.
        + assert (Hobserved : reader_edges_ordered (R.observe st root))
            by (now apply reader_edges_ordered_observe).
          destruct (R.is_materialized (R.observe st root) root);
            inversion Hstep; subst; exact Hobserved.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[popped rest] |].
        + inversion Hstep; subst. now apply reader_edges_ordered_with_queue.
        + inversion Hstep; subst. exact Hordered.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        now apply reader_edges_ordered_materialize.
      - eapply run_rhs_reader_edges_ordered; eauto.
      - eapply run_dead_reader_edges_ordered; eauto.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. eapply reader_edges_ordered_set_value; eauto.
      - eapply run_drain_reader_edges_ordered; eauto.
      - eapply return_reader_edges_ordered; eauto.
    Qed.

    Theorem reachable_reader_edges_ordered :
      forall tf roots after,
        Sem.steps tf (R.initial_config roots) after ->
        reader_edges_ordered (R.cfg_state after).
    Proof.
      assert (Hpreserved : forall tf before after,
        reader_edges_ordered (R.cfg_state before) ->
        Sem.steps tf before after ->
        reader_edges_ordered (R.cfg_state after)).
      { intros system before final Hordered Hsteps. induction Hsteps.
        - exact Hordered.
        - apply IHHsteps. eapply next_config_reader_edges_ordered; eauto. }
      intros tf roots after Hsteps. eapply Hpreserved; [|exact Hsteps].
      intros target source Hmem. unfold R.lookup_set in Hmem. cbn in Hmem.
      rewrite ML.lookup_empty in Hmem. rewrite SL.empty_spec in Hmem.
      discriminate.
    Qed.

  End ReaderOrder.

  Lemma set_value_new_queue_cause :
    forall st fr direct next next_fr queued,
      R.set_value st fr direct = (next, next_fr) ->
      ~ List.In queued (R.queue st) ->
      List.In queued (R.queue next) ->
      R.equivalent
        (R.sigma_value next (R.frame_owner fr))
        (R.sigma_value st (R.frame_owner fr)) = false /\
      S.mem queued
        (R.lookup_set (R.readers st) (R.frame_owner fr)) = true.
  Proof.
    intros st fr direct next next_fr queued Hset Hnot Hin.
    unfold R.set_value in Hset.
    destruct (R.equivalent
      (D.join direct (R.aggregate st (R.frame_owner fr)))
      (R.sigma_value st (R.frame_owner fr))); [congruence |].
    destruct (if S.mem (R.frame_owner fr) (R.controlled st)
      then U.update false (R.frame_owner fr) (R.frame_phase fr)
        (R.sigma_value st (R.frame_owner fr))
        (D.join direct (R.aggregate st (R.frame_owner fr)))
      else (R.frame_phase fr,
        D.join direct (R.aggregate st (R.frame_owner fr))))
      as [phase value].
    cbn in Hset.
    destruct (R.equivalent value
      (R.sigma_value st (R.frame_owner fr))) eqn:Hchanged;
      [congruence |].
    inversion Hset; subst; clear Hset. split.
    - unfold R.sigma_value. cbn.
      rewrite ML.lookup_update_same. exact Hchanged.
    - apply SL.mem_spec. unfold R.enqueue_all in Hin. cbn in Hin.
      apply queue_insert_all_members in Hin.
      destruct Hin as [Hin | Hin]; [exact Hin |contradiction].
  Qed.

  Lemma continue_side_new_queue :
    forall st fr target next k changed queued,
      ~ List.In queued (R.queue st) ->
      List.In queued
        (R.queue (R.cfg_state
          (R.continue_side st fr target next k changed))) ->
      changed = true /\ queued = target.
  Proof.
    intros st fr target next k changed queued Hnot Hin.
    unfold R.continue_side in Hin.
    destruct changed; [|cbn in Hin; contradiction].
    destruct (R.rank_lt st (R.frame_owner fr) target &&
      negb (R.is_materialized st target))%bool; cbn in Hin.
    - contradiction.
    - unfold R.enqueue in Hin. cbn in Hin.
      apply queue_insert_members in Hin.
      destruct Hin as [Heq | Hin]; [now split |contradiction].
  Qed.

  Lemma continue_dead_new_queue :
    forall st fr direct target remaining k changed queued,
      ~ List.In queued (R.queue st) ->
      List.In queued
        (R.queue (R.cfg_state
          (R.continue_dead st fr direct target remaining k changed))) ->
      changed = true /\ queued = target.
  Proof.
    intros st fr direct target remaining k changed queued Hnot Hin.
    unfold R.continue_dead in Hin.
    destruct changed; [|cbn in Hin; contradiction].
    destruct (R.rank_lt st (R.frame_owner fr) target &&
      negb (R.is_materialized st target))%bool; cbn in Hin.
    - contradiction.
    - unfold R.enqueue in Hin. cbn in Hin.
      apply queue_insert_members in Hin.
      destruct Hin as [Heq | Hin]; [now split |contradiction].
  Qed.

  Definition reachable_step
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (after before : R.config) : Prop :=
    Sem.steps tf (R.initial_config roots) before /\ Sem.step tf before after.

  Inductive work_step_kind
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (before after : R.config) : Prop :=
  | WorkStepDecrease :
      work_forest_lt (R.cfg_state after) support
        (control_work tf (R.cfg_control after))
        (control_work tf (R.cfg_control before)) ->
      work_step_kind support tf before after
  | WorkStepAdministrative :
      control_work tf (R.cfg_control after) =
      control_work tf (R.cfg_control before) ->
      work_step_kind support tf before after
  | WorkStepSeed :
      (exists roots, R.cfg_control before = R.RunSeeds roots) ->
      work_step_kind support tf before after
  | WorkStepQueueStart :
      (R.cfg_control before = R.RunLoop \/
       exists roots, R.cfg_control before = R.RunSeedLoop roots) ->
      work_step_kind support tf before after
  | WorkStepOrdinaryRerun :
      (exists fr k,
        R.cfg_control before = R.RunDrain fr k /\
        exists fr',
          R.frame_owner fr' = R.frame_owner fr /\
          R.cfg_control after =
            R.RunRhs fr' (tf (R.frame_owner fr)) k) ->
      work_step_kind support tf before after
  | WorkStepDrainNested :
      (exists fr k target,
        R.cfg_control before = R.RunDrain fr k /\
        R.rank_lt (R.cfg_state after) (R.frame_owner fr) target = true /\
        R.cfg_control after = R.StartEpisode target (R.KDrain fr k)) ->
      work_step_kind support tf before after.

  Lemma run_rhs_work_kind :
    forall tf support st fr body k after,
      Sem.rhs_supported (supported support) body ->
      R.next_config tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} =
        Some after ->
      work_step_kind support tf
        {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} after.
  Proof.
    intros tf support st fr body k after Hbody Hstep.
    destruct body as [direct | target next | target raw next | target next].
    - cbn in Hstep. inversion Hstep; subst.
      apply WorkStepDecrease. cbn.
      apply work_forest_local. constructor.
    - pose proof (rhs_supported_get_inv Hbody) as [Htarget Hnext].
      cbn -[R.observe R.complete_get R.enqueue] in Hstep.
      set (st0 := R.observe st target) in *.
      destruct (negb (R.is_materialized st0 target) &&
        R.rank_lt st0 (R.frame_owner fr) target)%bool eqn:Hnested.
      + apply Bool.andb_true_iff in Hnested.
        destruct Hnested as [_ Hhigher].
        inversion Hstep; subst. apply WorkStepDecrease. cbn.
        eapply work_forest_nested; eauto. constructor.
      + set (st1 := if R.is_materialized st0 target
          then st0 else R.enqueue st0 target) in *.
        destruct (R.complete_get st1 fr target)
          as [[st2 fr1] value] eqn:Hget.
        pose proof (complete_get_owner Hget) as Howner.
        inversion Hstep; subst. apply WorkStepDecrease. cbn.
        rewrite Howner. apply work_forest_local. constructor.
    - pose proof (rhs_supported_side_inv Hbody) as [Htarget Hnext].
      cbn -[R.observe R.record_side_input R.write_side_contribution
        R.continue_side] in Hstep.
      set (st0 := R.observe st target) in *.
      destruct (R.record_side_input fr target raw)
        as [fr1 input] eqn:Hrecord.
      pose proof (record_side_input_owner Hrecord) as Howner.
      destruct (R.write_side_contribution st0 fr1 target input)
        as [st1 changed].
      unfold R.continue_side in Hstep. destruct changed.
      + destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
          negb (R.is_materialized st1 target))%bool eqn:Hnested.
        * apply Bool.andb_true_iff in Hnested.
          destruct Hnested as [Hhigher _]. rewrite Howner in Hhigher.
          inversion Hstep; subst. apply WorkStepDecrease. cbn.
          rewrite Howner. eapply work_forest_nested; eauto. constructor.
        * inversion Hstep; subst. apply WorkStepDecrease. cbn.
          rewrite Howner. apply work_forest_local. constructor.
      + inversion Hstep; subst. apply WorkStepDecrease. cbn.
        rewrite Howner. apply work_forest_local. constructor.
    - pose proof (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
      cbn -[R.observe R.materialize R.enqueue] in Hstep.
      set (st0 := R.observe st target) in *.
      destruct (R.is_materialized st0 target).
      + inversion Hstep; subst. apply WorkStepDecrease. cbn.
        apply work_forest_local. constructor.
      + destruct (R.rank_lt st0 (R.frame_owner fr) target) eqn:Hhigher.
        * inversion Hstep; subst. apply WorkStepDecrease. cbn.
          eapply work_forest_nested; eauto. constructor.
        * inversion Hstep; subst. apply WorkStepDecrease. cbn.
          apply work_forest_local. constructor.
  Qed.

  Lemma run_dead_work_kind :
    forall tf support st fr direct pending k after,
      Forall (supported support) pending ->
      R.next_config tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
      work_step_kind support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunDead fr direct pending k |} after.
  Proof.
    intros tf support st fr direct pending k after Hpending Hstep.
    destruct pending as [|target remaining].
    - cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
      apply WorkStepDecrease. cbn. apply work_forest_local. constructor.
    - inversion Hpending as [|? ? Htarget Hremaining]; subst.
      cbn -[R.write_side_contribution R.continue_dead] in Hstep.
      destruct (S.mem target (R.frame_current_targets fr)).
      + inversion Hstep; subst. apply WorkStepDecrease. cbn.
        apply work_forest_local. constructor.
      + destruct (R.write_side_contribution st fr target D.bottom)
          as [st1 changed].
        unfold R.continue_dead in Hstep. destruct changed.
        * destruct (R.rank_lt st1 (R.frame_owner fr) target &&
            negb (R.is_materialized st1 target))%bool eqn:Hnested.
          -- apply Bool.andb_true_iff in Hnested.
             destruct Hnested as [Hhigher _].
             inversion Hstep; subst. apply WorkStepDecrease. cbn.
             eapply work_forest_nested; eauto. constructor.
          -- inversion Hstep; subst. apply WorkStepDecrease. cbn.
             apply work_forest_local. constructor.
        * inversion Hstep; subst. apply WorkStepDecrease. cbn.
          apply work_forest_local. constructor.
  Qed.

  Lemma run_drain_work_kind :
    forall tf support st fr k after,
      R.next_config tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} =
        Some after ->
      work_step_kind support tf
        {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} after.
  Proof.
    intros tf support st fr k after Hstep.
    cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
    destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
    - destruct (V.eq_dec next (R.frame_owner fr)).
      + destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
          try discriminate.
        inversion Hstep; subst. apply WorkStepOrdinaryRerun.
        exists fr, k. split; [reflexivity |].
        exists
          (R.fresh_frame (R.with_queue st rest)
            (R.frame_owner fr) (R.frame_phase fr)).
        split; reflexivity.
      + destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
        * destruct (R.queue_pop (R.queue st)) as [[popped rest] |];
            try discriminate.
          inversion Hstep; subst. apply WorkStepDrainNested.
          exists fr, k, next. repeat split; assumption.
        * inversion Hstep; subst. apply WorkStepDecrease. cbn.
          apply work_forest_remove_head.
    - inversion Hstep; subst. apply WorkStepDecrease. cbn.
      apply work_forest_remove_head.
  Qed.

  Lemma return_work_kind :
    forall tf support st k after,
      R.next_config tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
      work_step_kind support tf
        {| R.cfg_state := st; R.cfg_control := R.Return k |} after.
  Proof.
    intros tf support st k after Hstep.
    destruct k as
      [|remaining |fr target next rest |fr next rest |fr next rest
       |fr direct pending rest |fr rest];
      cbn -[R.complete_get] in Hstep.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - destruct (R.complete_get st fr target)
        as [[st1 fr1] value] eqn:Hget.
      pose proof (complete_get_owner Hget) as Howner.
      inversion Hstep; subst. apply WorkStepDecrease. cbn. rewrite Howner.
      apply work_forest_local. constructor.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
  Qed.

  Theorem reachable_step_work_kind :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      reachable_step tf roots after before ->
      work_step_kind (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite [st control] after [Hreachable Hstep].
    pose proof (reachable_config_supported finite Hreachable)
      as [_ Hsupported].
    unfold Sem.step in Hstep.
    destruct control as
      [|seed_roots |remaining |owner k |fr body k |fr direct pending k
       |fr direct k |fr k |k].
    - apply WorkStepQueueStart. now left.
    - apply WorkStepSeed. now eexists.
    - cbn in Hstep. destruct (R.queue_pop (R.queue st))
        as [[queued rest] |] eqn:Hpop.
      + apply WorkStepQueueStart. right. now eexists.
      + inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - cbn -[R.materialize R.fresh_frame] in Hstep.
      inversion Hstep; subst. apply WorkStepAdministrative. reflexivity.
    - destruct Hsupported as [Hfr [Hbody Hk]].
      eapply run_rhs_work_kind; eauto.
    - destruct Hsupported as [Hfr [Hpending Hk]].
      eapply run_dead_work_kind; eauto.
    - cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
      pose proof (@set_value_owner st fr direct st1 fr1 Hset) as Howner.
      inversion Hstep; subst. apply WorkStepDecrease. cbn. rewrite Howner.
      apply work_forest_local. constructor.
    - eapply run_drain_work_kind; eauto.
    - eapply return_work_kind; eauto.
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

    Inductive steps_plus (tf : R.ConstraintSystem.system) :
      R.config -> R.config -> Prop :=
    | StepsPlus :
        forall first next final,
          Sem.step tf first next ->
          Sem.steps tf next final ->
          steps_plus tf first final.

    Lemma steps_plus_steps :
      forall tf first final,
        steps_plus tf first final -> Sem.steps tf first final.
    Proof. intros tf first final Hplus. destruct Hplus. econstructor; eauto. Qed.

    Lemma steps_nontrivial_plus :
      forall tf first final,
        Sem.steps tf first final -> first <> final -> steps_plus tf first final.
    Proof.
      intros tf first final Hsteps Hneq. destruct Hsteps.
      - contradiction.
      - econstructor; eauto.
    Qed.

    Lemma steps_append_one_plus :
      forall tf first middle final,
        Sem.steps tf first middle ->
        Sem.step tf middle final ->
        steps_plus tf first final.
    Proof.
      intros tf first middle final Hsteps Hlast. induction Hsteps.
      - econstructor; [exact Hlast |constructor].
      - econstructor; [exact H |].
        eapply steps_append_one; eauto.
    Qed.

    Lemma step_deterministic :
      forall tf before left right,
        Sem.step tf before left -> Sem.step tf before right -> left = right.
    Proof. intros tf before left right Hleft Hright. unfold Sem.step in *. congruence. Qed.

    Lemma steps_rank_extends :
      forall tf before after,
        Sem.steps tf before after ->
        rank_extends (R.cfg_state before) (R.cfg_state after).
    Proof.
      intros tf before after Hsteps. induction Hsteps.
      - apply rank_extends_refl.
      - eapply rank_extends_trans;
          [eapply next_config_rank_extends; exact H |exact IHHsteps].
    Qed.

    Definition queue_strictly_below (upper : V.t) (st : R.state) : Prop :=
      forall queued,
        List.In queued (R.queue st) ->
        R.rank_lt st queued upper = true.

    Lemma with_queue_strictly_below :
      forall st head tail,
        queue_ordered st ->
        R.queue_pop (R.queue st) = Some (head, tail) ->
        queue_strictly_below head (R.with_queue st tail).
    Proof.
      intros st head tail Hordered Hpop queued Hin. cbn in Hin.
      exact (proj2 (queue_pop_ordered Hordered Hpop) queued Hin).
    Qed.

    Lemma queue_below_trans :
      forall lower upper st,
        R.rank_lt st lower upper = true ->
        queue_strictly_below lower st ->
        queue_strictly_below upper st.
    Proof.
      intros lower upper st Hlt Hbelow queued Hin.
      pose proof (Hbelow queued Hin) as Hqueued_lower.
      pose proof (@rank_lt_true_ranked st queued lower Hqueued_lower)
        as [Hqueued Hlower].
      pose proof (@rank_lt_true_ranked st lower upper Hlt)
        as [_ Hupper].
      exact (@rank_lt_trans st queued lower upper
        Hqueued Hlower Hupper Hqueued_lower Hlt).
    Qed.

    Lemma queue_below_extended :
      forall before after upper,
        rank_extends before after ->
        ranked before upper ->
        R.queue after = R.queue before ->
        queue_strictly_below upper before ->
        queue_strictly_below upper after.
    Proof.
      intros before after upper Hextends Hupper Hqueue Hbelow queued Hin.
      assert (Hqueued_before : List.In queued (R.queue before)).
      { now rewrite <- Hqueue. }
      pose proof (Hbelow queued Hqueued_before) as Hlt.
      pose proof (@rank_lt_true_ranked before queued upper Hlt)
        as [Hqueued Hupper0].
      rewrite <- (@rank_lt_stable before after queued upper
        Hextends Hqueued Hupper0).
      exact Hlt.
    Qed.

    Definition episode_complete
      (tf : R.ConstraintSystem.system) (owner : V.t) (k : R.continuation)
      (start : R.config) : Prop :=
      exists st,
        Sem.steps tf start
          {| R.cfg_state := st; R.cfg_control := R.Return k |} /\
        queue_strictly_below owner st.

    Definition higher_episodes_complete
      (support : list V.t) (tf : R.ConstraintSystem.system)
      (roots : list V.t) (owner : V.t) : Prop :=
      forall target k start,
        List.In target support ->
        R.rank_lt (R.cfg_state start) owner target = true ->
        Sem.steps tf (R.initial_config roots) start ->
        R.cfg_control start = R.StartEpisode target k ->
        episode_complete tf target k start.

    Lemma reachable_after_steps :
      forall tf roots first final,
        Sem.steps tf (R.initial_config roots) first ->
        Sem.steps tf first final ->
        Sem.steps tf (R.initial_config roots) final.
    Proof. intros. eapply steps_transitive; eauto. Qed.

    Lemma one_step :
      forall tf before after,
        R.next_config tf before = Some after -> Sem.steps tf before after.
    Proof. intros. econstructor; [exact H |constructor]. Qed.

    Definition rhs_finishes
      (tf : R.ConstraintSystem.system) (fr : R.frame)
      (body : R.ConstraintSystem.rhs) (k : R.continuation)
      (start : R.config) : Prop :=
      exists st' fr' direct pending,
        Sem.steps tf start
          {| R.cfg_state := st';
             R.cfg_control := R.RunDead fr' direct pending k |} /\
        R.frame_owner fr' = R.frame_owner fr.

    Lemma run_rhs_finishes :
      forall support tf roots owner,
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          rhs_finishes tf fr body k
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}.
    Proof.
      intros support tf roots owner Hchildren st fr body k
        Howner Hbody Hreachable.
      revert st fr k Howner Hbody Hreachable. pattern body.
      apply (well_founded_induction_type rhs_child_well_founded).
      intros current IH st fr k Howner Hbody Hreachable. subst owner.
      destruct current as
        [direct |target next |target raw next |target next].
      - exists st, fr, direct,
          (if Features.eliminate_dead_sides
           then S.elements (R.frame_previous_targets fr) else []).
        split; [apply one_step; reflexivity |reflexivity].
      - pose proof (rhs_supported_get_inv Hbody) as [Htarget Hnext].
        set (st0 := R.observe st target).
        destruct (negb (R.is_materialized st0 target) &&
          R.rank_lt st0 (R.frame_owner fr) target)%bool eqn:Hnested.
        + apply Bool.andb_true_iff in Hnested.
          destruct Hnested as [Hfresh Hhigher].
          set (child :=
            {| R.cfg_state := st0;
               R.cfg_control :=
                 R.StartEpisode target (R.KAfterGet fr target next k) |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.RunRhs fr (R.ConstraintSystem.Get target next) k |} child).
          { unfold Sem.step, child. cbn -[R.observe R.complete_get R.enqueue].
            fold st0. rewrite Hfresh, Hhigher. reflexivity. }
          assert (Hchild_reachable :
            Sem.steps tf (R.initial_config roots) child).
          { eapply steps_append_one; eauto. }
          destruct (Hchildren target (R.KAfterGet fr target next k) child
            Htarget Hhigher Hchild_reachable eq_refl)
            as [child_st [Hchild _]].
          destruct (R.complete_get child_st fr target)
            as [[st1 fr1] value] eqn:Hget.
          set (returned :=
            {| R.cfg_state := child_st;
               R.cfg_control := R.Return (R.KAfterGet fr target next k) |}).
          set (resumed :=
            {| R.cfg_state := st1;
               R.cfg_control := R.RunRhs fr1 (next value) k |}).
          assert (Hreturn : Sem.step tf returned resumed).
          { unfold Sem.step, returned, resumed. cbn -[R.complete_get].
            now rewrite Hget. }
          assert (Hresume_reachable :
            Sem.steps tf (R.initial_config roots) resumed).
          { eapply steps_transitive; [exact Hchild_reachable |].
            eapply steps_transitive; [exact Hchild |].
            apply one_step. exact Hreturn. }
          assert (Hfr1 : R.frame_owner fr1 = R.frame_owner fr).
          { exact (@complete_get_owner child_st fr target st1 fr1 value Hget). }
          destruct (IH (next value) (RhsGetChild target next value)
            st1 fr1 k Hfr1 (Hnext value) Hresume_reachable)
            as [done_st [done_fr [done_direct
              [pending [Hdone Hdone_owner]]]]].
          exists done_st, done_fr, done_direct, pending. split.
          * eapply steps_transitive; [|exact Hdone].
            econstructor; [exact Hstep |].
            eapply steps_transitive; [exact Hchild |].
            apply one_step. exact Hreturn.
          * now rewrite Hdone_owner, Hfr1.
        + set (base := if R.is_materialized st0 target
            then st0 else R.enqueue st0 target).
          destruct (R.complete_get base fr target)
            as [[st1 fr1] value] eqn:Hget.
          set (after :=
            {| R.cfg_state := st1;
               R.cfg_control := R.RunRhs fr1 (next value) k |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.RunRhs fr (R.ConstraintSystem.Get target next) k |} after).
          { unfold Sem.step, after. cbn -[R.observe R.complete_get R.enqueue].
            fold st0. rewrite Hnested. fold base. now rewrite Hget. }
          assert (Hafter_reachable :
            Sem.steps tf (R.initial_config roots) after).
          { eapply steps_append_one; eauto. }
          assert (Hfr1 : R.frame_owner fr1 = R.frame_owner fr).
          { exact (@complete_get_owner base fr target st1 fr1 value Hget). }
          destruct (IH (next value) (RhsGetChild target next value)
            st1 fr1 k Hfr1 (Hnext value) Hafter_reachable)
            as [done_st [done_fr [done_direct
              [pending [Hdone Hdone_owner]]]]].
          exists done_st, done_fr, done_direct, pending. split.
          * econstructor; [exact Hstep |exact Hdone].
          * now rewrite Hdone_owner, Hfr1.
      - pose proof (rhs_supported_side_inv Hbody) as [Htarget Hnext].
        set (st0 := R.observe st target).
        destruct (R.record_side_input fr target raw)
          as [fr1 input] eqn:Hrecord.
        destruct (R.write_side_contribution st0 fr1 target input)
          as [st1 changed] eqn:Hwrite.
        pose proof (@record_side_input_owner fr target raw fr1 input Hrecord)
          as Hfr1.
        destruct changed.
        + destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
            negb (R.is_materialized st1 target))%bool eqn:Hnested.
          * apply Bool.andb_true_iff in Hnested.
            destruct Hnested as [Hhigher Hfresh].
            assert (Hhigher_owner :
              R.rank_lt st1 (R.frame_owner fr) target = true).
            { now rewrite <- Hfr1. }
            set (child :=
              {| R.cfg_state := st1;
                 R.cfg_control :=
                   R.StartEpisode target (R.KAfterSide fr1 next k) |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr
                   (R.ConstraintSystem.Side target raw next) k |} child).
            { unfold Sem.step, child.
              cbn -[R.observe R.record_side_input
                R.write_side_contribution R.continue_side].
              fold st0. rewrite Hrecord, Hwrite. unfold R.continue_side.
              rewrite Hhigher, Hfresh. reflexivity. }
            assert (Hchild_reachable :
              Sem.steps tf (R.initial_config roots) child).
            { eapply steps_append_one; eauto. }
            destruct (Hchildren target (R.KAfterSide fr1 next k) child
              Htarget Hhigher_owner Hchild_reachable eq_refl)
              as [child_st [Hchild _]].
            set (returned :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.Return (R.KAfterSide fr1 next k) |}).
            set (resumed :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.RunRhs fr1 next k |}).
            assert (Hreturn : Sem.step tf returned resumed).
            { unfold Sem.step, returned, resumed. reflexivity. }
            assert (Hresume_reachable :
              Sem.steps tf (R.initial_config roots) resumed).
            { eapply steps_transitive; [exact Hchild_reachable |].
              eapply steps_transitive; [exact Hchild |].
              apply one_step. exact Hreturn. }
            destruct (IH next (RhsSideChild target raw next)
              child_st fr1 k Hfr1 Hnext Hresume_reachable)
              as [done_st [done_fr [done_direct
                [pending [Hdone Hdone_owner]]]]].
            exists done_st, done_fr, done_direct, pending. split.
            -- eapply steps_transitive; [|exact Hdone].
               econstructor; [exact Hstep |].
               eapply steps_transitive; [exact Hchild |].
               apply one_step. exact Hreturn.
            -- now rewrite Hdone_owner, Hfr1.
          * set (after :=
              {| R.cfg_state := R.enqueue st1 target;
                 R.cfg_control := R.RunRhs fr1 next k |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr
                   (R.ConstraintSystem.Side target raw next) k |} after).
            { unfold Sem.step, after.
              cbn -[R.observe R.record_side_input
                R.write_side_contribution R.continue_side].
              fold st0. rewrite Hrecord, Hwrite. unfold R.continue_side.
              now rewrite Hnested. }
            assert (Hafter_reachable :
              Sem.steps tf (R.initial_config roots) after).
            { eapply steps_append_one; eauto. }
            destruct (IH next (RhsSideChild target raw next)
              (R.enqueue st1 target) fr1 k Hfr1 Hnext Hafter_reachable)
              as [done_st [done_fr [done_direct
                [pending [Hdone Hdone_owner]]]]].
            exists done_st, done_fr, done_direct, pending. split.
            -- econstructor; [exact Hstep |exact Hdone].
            -- now rewrite Hdone_owner, Hfr1.
        + set (after :=
            {| R.cfg_state := st1;
               R.cfg_control := R.RunRhs fr1 next k |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr
                 (R.ConstraintSystem.Side target raw next) k |} after).
          { unfold Sem.step, after.
            cbn -[R.observe R.record_side_input
              R.write_side_contribution R.continue_side].
            fold st0. now rewrite Hrecord, Hwrite. }
          assert (Hafter_reachable :
            Sem.steps tf (R.initial_config roots) after).
          { eapply steps_append_one; eauto. }
          destruct (IH next (RhsSideChild target raw next)
            st1 fr1 k Hfr1 Hnext Hafter_reachable)
            as [done_st [done_fr [done_direct
              [pending [Hdone Hdone_owner]]]]].
          exists done_st, done_fr, done_direct, pending. split.
          * econstructor; [exact Hstep |exact Hdone].
          * now rewrite Hdone_owner, Hfr1.
      - pose proof (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
        set (st0 := R.observe st target).
        destruct (R.is_materialized st0 target) eqn:Hmaterialized.
        + set (after :=
            {| R.cfg_state := st0;
               R.cfg_control := R.RunRhs fr next k |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr
                 (R.ConstraintSystem.Spawn target next) k |} after).
          { unfold Sem.step, after. cbn -[R.observe]. fold st0.
            now rewrite Hmaterialized. }
          assert (Hafter_reachable :
            Sem.steps tf (R.initial_config roots) after).
          { eapply steps_append_one; eauto. }
          destruct (IH next (RhsSpawnChild target next)
            st0 fr k eq_refl Hnext Hafter_reachable)
            as [done_st [done_fr [done_direct
              [pending [Hdone Hdone_owner]]]]].
          exists done_st, done_fr, done_direct, pending.
          split; [econstructor; eauto |exact Hdone_owner].
        + destruct (R.rank_lt st0 (R.frame_owner fr) target) eqn:Hhigher.
          * set (child :=
              {| R.cfg_state := st0;
                 R.cfg_control :=
                   R.StartEpisode target (R.KAfterSpawn fr next k) |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr
                   (R.ConstraintSystem.Spawn target next) k |} child).
            { unfold Sem.step, child. cbn -[R.observe]. fold st0.
              now rewrite Hmaterialized, Hhigher. }
            assert (Hchild_reachable :
              Sem.steps tf (R.initial_config roots) child).
            { eapply steps_append_one; eauto. }
            destruct (Hchildren target (R.KAfterSpawn fr next k) child
              Htarget Hhigher Hchild_reachable eq_refl)
              as [child_st [Hchild _]].
            set (returned :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.Return (R.KAfterSpawn fr next k) |}).
            set (resumed :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.RunRhs fr next k |}).
            assert (Hreturn : Sem.step tf returned resumed).
            { unfold Sem.step, returned, resumed. reflexivity. }
            assert (Hresume_reachable :
              Sem.steps tf (R.initial_config roots) resumed).
            { eapply steps_transitive; [exact Hchild_reachable |].
              eapply steps_transitive; [exact Hchild |].
              apply one_step. exact Hreturn. }
            destruct (IH next (RhsSpawnChild target next)
              child_st fr k eq_refl Hnext Hresume_reachable)
              as [done_st [done_fr [done_direct
                [pending [Hdone Hdone_owner]]]]].
            exists done_st, done_fr, done_direct, pending. split.
            -- eapply steps_transitive; [|exact Hdone].
               econstructor; [exact Hstep |].
               eapply steps_transitive; [exact Hchild |].
               apply one_step. exact Hreturn.
            -- exact Hdone_owner.
          * set (after :=
              {| R.cfg_state := R.materialize (R.enqueue st0 target) target;
                 R.cfg_control := R.RunRhs fr next k |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr
                   (R.ConstraintSystem.Spawn target next) k |} after).
            { unfold Sem.step, after. cbn -[R.observe]. fold st0.
              now rewrite Hmaterialized, Hhigher. }
            assert (Hafter_reachable :
              Sem.steps tf (R.initial_config roots) after).
            { eapply steps_append_one; eauto. }
            destruct (IH next (RhsSpawnChild target next)
              (R.materialize (R.enqueue st0 target) target)
              fr k eq_refl Hnext Hafter_reachable)
              as [done_st [done_fr [done_direct
                [pending [Hdone Hdone_owner]]]]].
            exists done_st, done_fr, done_direct, pending.
            split; [econstructor; eauto |exact Hdone_owner].
    Qed.

    Definition dead_finishes
      (tf : R.ConstraintSystem.system) (fr : R.frame) (direct : D.t)
      (pending : list V.t) (k : R.continuation)
      (start : R.config) : Prop :=
      exists st' fr',
        Sem.steps tf start
          {| R.cfg_state := st';
             R.cfg_control := R.RunCommit fr' direct k |} /\
        R.frame_owner fr' = R.frame_owner fr.

    Lemma run_dead_finishes :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr direct pending k,
          R.frame_owner fr = owner ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st;
               R.cfg_control := R.RunDead fr direct pending k |} ->
          dead_finishes tf fr direct pending k
            {| R.cfg_state := st;
               R.cfg_control := R.RunDead fr direct pending k |}.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr direct pending. revert st fr.
      induction pending as [|target remaining IH];
        intros st fr k Howner Hreachable.
      - exists (R.publish_targets st fr), fr.
        split; [apply one_step; reflexivity |reflexivity].
      - pose proof (reachable_config_supported finite Hreachable)
          as [_ Hcontrol].
        cbn in Hcontrol. destruct Hcontrol as [_ [Hpending _]].
        assert (Htarget : List.In target support).
        { rewrite Hsupport. inversion Hpending; assumption. }
        destruct (S.mem target (R.frame_current_targets fr)) eqn:Hcurrent.
        + set (after :=
            {| R.cfg_state := st;
               R.cfg_control := R.RunDead fr direct remaining k |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control :=
                 R.RunDead fr direct (target :: remaining) k |} after).
          { unfold Sem.step, after. cbn. now rewrite Hcurrent. }
          assert (Hafter_reachable :
            Sem.steps tf (R.initial_config roots) after).
          { eapply steps_append_one; eauto. }
          destruct (IH st fr k Howner Hafter_reachable)
            as [done_st [done_fr [Hdone Hdone_owner]]].
          exists done_st, done_fr.
          split; [econstructor; eauto |exact Hdone_owner].
        + destruct (R.write_side_contribution st fr target D.bottom)
            as [st1 changed] eqn:Hwrite.
          destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr) target &&
              negb (R.is_materialized st1 target))%bool eqn:Hnested.
            -- apply Bool.andb_true_iff in Hnested.
               destruct Hnested as [Hhigher Hfresh].
               assert (Hhigher_owner : R.rank_lt st1 owner target = true).
               { now rewrite <- Howner. }
               set (child :=
                 {| R.cfg_state := st1;
                    R.cfg_control :=
                      R.StartEpisode target
                        (R.KDead fr direct remaining k) |}).
               assert (Hstep : Sem.step tf
                 {| R.cfg_state := st;
                    R.cfg_control :=
                      R.RunDead fr direct (target :: remaining) k |} child).
               { unfold Sem.step, child.
                 cbn -[R.write_side_contribution R.continue_dead].
                 rewrite Hcurrent, Hwrite. unfold R.continue_dead.
                 now rewrite Hhigher, Hfresh. }
               assert (Hchild_reachable :
                 Sem.steps tf (R.initial_config roots) child).
               { eapply steps_append_one; eauto. }
               destruct (Hchildren target
                 (R.KDead fr direct remaining k) child Htarget
                 Hhigher_owner Hchild_reachable eq_refl)
                 as [child_st [Hchild _]].
               set (returned :=
                 {| R.cfg_state := child_st;
                    R.cfg_control :=
                      R.Return (R.KDead fr direct remaining k) |}).
               set (resumed :=
                 {| R.cfg_state := child_st;
                    R.cfg_control := R.RunDead fr direct remaining k |}).
               assert (Hreturn : Sem.step tf returned resumed).
               { unfold Sem.step, returned, resumed. reflexivity. }
               assert (Hresume_reachable :
                 Sem.steps tf (R.initial_config roots) resumed).
               { eapply steps_transitive; [exact Hchild_reachable |].
                 eapply steps_transitive; [exact Hchild |].
                 apply one_step. exact Hreturn. }
               destruct (IH child_st fr k Howner Hresume_reachable)
                 as [done_st [done_fr [Hdone Hdone_owner]]].
               exists done_st, done_fr. split.
               ++ eapply steps_transitive; [|exact Hdone].
                  econstructor; [exact Hstep |].
                  eapply steps_transitive; [exact Hchild |].
                  apply one_step. exact Hreturn.
               ++ exact Hdone_owner.
            -- set (after :=
                 {| R.cfg_state := R.enqueue st1 target;
                    R.cfg_control := R.RunDead fr direct remaining k |}).
               assert (Hstep : Sem.step tf
                 {| R.cfg_state := st;
                    R.cfg_control :=
                      R.RunDead fr direct (target :: remaining) k |} after).
               { unfold Sem.step, after.
                 cbn -[R.write_side_contribution R.continue_dead].
                 rewrite Hcurrent, Hwrite. unfold R.continue_dead.
                 now rewrite Hnested. }
               assert (Hafter_reachable :
                 Sem.steps tf (R.initial_config roots) after).
               { eapply steps_append_one; eauto. }
               destruct (IH (R.enqueue st1 target) fr k
                 Howner Hafter_reachable)
                 as [done_st [done_fr [Hdone Hdone_owner]]].
               exists done_st, done_fr.
               split; [econstructor; eauto |exact Hdone_owner].
          * set (after :=
              {| R.cfg_state := st1;
                 R.cfg_control := R.RunDead fr direct remaining k |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st;
                 R.cfg_control :=
                   R.RunDead fr direct (target :: remaining) k |} after).
            { unfold Sem.step, after.
              cbn -[R.write_side_contribution R.continue_dead].
              now rewrite Hcurrent, Hwrite. }
            assert (Hafter_reachable :
              Sem.steps tf (R.initial_config roots) after).
            { eapply steps_append_one; eauto. }
            destruct (IH st1 fr k Howner Hafter_reachable)
              as [done_st [done_fr [Hdone Hdone_owner]]].
            exists done_st, done_fr.
            split; [econstructor; eauto |exact Hdone_owner].
    Qed.

    Definition evaluation_reaches_commit
      (tf : R.ConstraintSystem.system) (fr : R.frame)
      (body : R.ConstraintSystem.rhs) (k : R.continuation)
      (start : R.config) : Prop :=
      exists st' fr' direct,
        Sem.steps tf start
          {| R.cfg_state := st';
             R.cfg_control := R.RunCommit fr' direct k |} /\
        R.frame_owner fr' = R.frame_owner fr.

    Definition evaluation_reaches_drain
      (tf : R.ConstraintSystem.system) (fr : R.frame)
      (body : R.ConstraintSystem.rhs) (k : R.continuation)
      (start : R.config) : Prop :=
      exists st' fr',
        Sem.steps tf start
          {| R.cfg_state := st';
             R.cfg_control := R.RunDrain fr' k |} /\
        R.frame_owner fr' = R.frame_owner fr.

    Lemma run_rhs_reaches_commit :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          evaluation_reaches_commit tf fr body k
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_finishes support tf roots owner Hchildren
        st fr body k Howner Hbody Hreachable)
        as [dead_st [dead_fr [direct [pending [Heval Heval_owner]]]]].
      assert (Hdead_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := dead_st;
           R.cfg_control := R.RunDead dead_fr direct pending k |}).
      { eapply steps_transitive; eauto. }
      assert (Hdead_owner : R.frame_owner dead_fr = owner).
      { now rewrite Heval_owner. }
      destruct (@run_dead_finishes support tf roots finite owner
        Hsupport Hchildren dead_st dead_fr direct pending k
        Hdead_owner Hdead_reachable)
        as [commit_st [commit_fr [Hdead Hcommit_owner]]].
      exists commit_st, commit_fr, direct. split.
      - eapply steps_transitive; eauto.
      - now rewrite Hcommit_owner, Heval_owner.
    Qed.

    Lemma run_rhs_reaches_drain :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          evaluation_reaches_drain tf fr body k
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_reaches_commit support tf roots finite owner
        Hsupport Hchildren st fr body k Howner Hbody Hreachable)
        as [commit_st [commit_fr [direct [Hcommit Hcommit_owner]]]].
      destruct (R.set_value commit_st commit_fr direct)
        as [drain_st drain_fr] eqn:Hset.
      exists (drain_st), drain_fr. split.
      - eapply steps_transitive; [exact Hcommit |]. apply one_step.
        unfold Sem.step. cbn -[R.set_value]. now rewrite Hset.
      - pose proof (@set_value_owner commit_st commit_fr direct
          drain_st drain_fr Hset) as Hdrain_owner.
        now rewrite Hdrain_owner, Hcommit_owner.
    Qed.

    Lemma queue_peek_some_pop :
      forall queue head,
        R.queue_peek queue = Some head ->
        exists tail, R.queue_pop queue = Some (head, tail).
    Proof.
      intros [|first rest] head Hpeek; cbn in Hpeek; try discriminate.
      inversion Hpeek; subst. exists rest. reflexivity.
    Qed.

    Lemma queue_peek_none_below :
      forall st owner,
        R.queue_peek (R.queue st) = None -> queue_strictly_below owner st.
    Proof.
      intros st owner Hpeek queued Hin.
      destruct (R.queue st); cbn in Hpeek; [contradiction |discriminate].
    Qed.

    Lemma queue_peek_lower_below :
      forall st next owner,
        queue_ordered st ->
        R.queue_peek (R.queue st) = Some next ->
        R.rank_lt st next owner = true ->
        queue_strictly_below owner st.
    Proof.
      intros st next owner Hordered Hpeek Hlower.
      destruct (@queue_peek_some_pop (R.queue st) next Hpeek)
        as [tail Hpop].
      intros queued Hin.
      pose proof (proj2 (queue_pop_ordered Hordered Hpop)) as Htail.
      destruct (R.queue st) as [|head rest] eqn:Hqueue;
        cbn in Hpop; try discriminate.
      inversion Hpop; subst head rest.
      destruct Hin as [-> |Hin]; [exact Hlower |].
      pose proof (Htail queued Hin) as Hqueued_next.
      pose proof (@rank_lt_true_ranked st queued next Hqueued_next)
        as [Hqueued Hnext].
      pose proof (@rank_lt_true_ranked st next owner Hlower)
        as [_ Howner].
      exact (@rank_lt_trans st queued next owner
        Hqueued Hnext Howner Hqueued_next Hlower).
    Qed.

    Lemma rank_lt_reverse_if_false :
      forall st left right,
        rank_valid st -> ranked st left -> ranked st right ->
        left <> right -> R.rank_lt st left right = false ->
        R.rank_lt st right left = true.
    Proof.
      intros st left right Hvalid Hleft Hright Hneq Hfalse.
      destruct (@rank_lt_total st left right Hvalid Hleft Hright Hneq)
        as [Htrue |Hreverse]; [congruence |exact Hreverse].
    Qed.

    Lemma reset_registered_cells_queue :
      forall st owner,
        R.queue (R.reset_registered_cells st owner) = R.queue st.
    Proof.
      intros st owner. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma reset_registered_cells_ranking :
      forall st owner,
        R.ranking (R.reset_registered_cells st owner) = R.ranking st.
    Proof.
      intros st owner. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma reset_registered_cells_below :
      forall st owner upper,
        queue_strictly_below upper st ->
        queue_strictly_below upper (R.reset_registered_cells st owner).
    Proof.
      intros st owner upper Hbelow queued Hin.
      rewrite reset_registered_cells_queue in Hin.
      unfold R.rank_lt, R.ranking_lt.
      rewrite reset_registered_cells_ranking. now apply Hbelow.
    Qed.

    Inductive drain_boundary
      (tf : R.ConstraintSystem.system) (owner : V.t) (k : R.continuation) :
      R.config -> Prop :=
    | DrainBoundaryReturn :
        forall st,
          queue_strictly_below owner st ->
          drain_boundary tf owner k
            {| R.cfg_state := st; R.cfg_control := R.Return k |}
    | DrainBoundaryRerun :
        forall st fr,
          R.frame_owner fr = owner ->
          queue_strictly_below owner st ->
          drain_boundary tf owner k
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr (tf owner) k |}.

    Definition drain_reaches_boundary
      (tf : R.ConstraintSystem.system) (owner : V.t) (k : R.continuation)
      (start : R.config) : Prop :=
      exists boundary,
        Sem.steps tf start boundary /\ drain_boundary tf owner k boundary.

    Lemma queue_peek_member :
      forall queue head,
        R.queue_peek queue = Some head -> List.In head queue.
    Proof.
      intros [|first rest] head Hpeek; cbn in Hpeek; try discriminate.
      inversion Hpeek; now left.
    Qed.

    Inductive executed_drain_boundary
      (tf : R.ConstraintSystem.system) (owner : V.t) (k : R.continuation)
      (start : R.config) : R.config -> Prop :=
    | ExecutedDrainReturn :
        forall st,
          Sem.steps tf start
            {| R.cfg_state := st; R.cfg_control := R.Return k |} ->
          queue_strictly_below owner st ->
          executed_drain_boundary tf owner k start
            {| R.cfg_state := st; R.cfg_control := R.Return k |}
    | ExecutedDrainRerun :
        forall before fr tail,
          Sem.steps tf start
            {| R.cfg_state := before; R.cfg_control := R.RunDrain fr k |} ->
          R.frame_owner fr = owner ->
          R.queue_pop (R.queue before) = Some (owner, tail) ->
          queue_ordered before ->
          executed_drain_boundary tf owner k start
            {| R.cfg_state := R.with_queue before tail;
               R.cfg_control :=
                 R.RunRhs
                   (R.fresh_frame (R.with_queue before tail)
                     owner (R.frame_phase fr))
                   (tf owner) k |}.

    Lemma executed_drain_steps :
      forall tf owner k start boundary,
        executed_drain_boundary tf owner k start boundary ->
        Sem.steps tf start boundary.
    Proof.
      intros tf owner k start boundary Hexecuted. destruct Hexecuted.
      - exact H.
      - eapply steps_append_one; [exact H |]. unfold Sem.step. cbn.
        destruct (R.queue before) as [|head rest] eqn:Hqueue;
          cbn in H1; try discriminate.
        inversion H1; subst head rest. cbn.
        rewrite H0. destruct (V.eq_dec owner owner);
          [reflexivity |contradiction].
    Qed.

    Lemma executed_drain_is_boundary :
      forall tf owner k start boundary,
        executed_drain_boundary tf owner k start boundary ->
        drain_boundary tf owner k boundary.
    Proof.
      intros tf owner k start boundary Hexecuted. destruct Hexecuted.
      - now apply DrainBoundaryReturn.
      - apply DrainBoundaryRerun; [reflexivity |].
        now apply with_queue_strictly_below.
    Qed.

    Lemma executed_drain_prepend :
      forall tf owner k first start boundary,
        Sem.steps tf first start ->
        executed_drain_boundary tf owner k start boundary ->
        executed_drain_boundary tf owner k first boundary.
    Proof.
      intros tf owner k first start boundary Hfirst Hexecuted.
      destruct Hexecuted.
      - apply ExecutedDrainReturn;
          [eapply steps_transitive; eauto |exact H0].
      - eapply ExecutedDrainRerun;
          [eapply steps_transitive; eauto |exact H0 |exact H1 |exact H2].
    Qed.

    Lemma run_drain_reaches_executed_boundary :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall fuel st fr k,
          R.frame_owner fr = owner ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
          (forall next rank,
            R.queue_peek (R.queue st) = Some next ->
            R.rank_lt st owner next = true ->
            R.Ranking.lookup (R.ranking st) next = Some rank ->
            rank < fuel) ->
          exists boundary,
            executed_drain_boundary tf owner k
              {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
              boundary.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren fuel.
      induction fuel using lt_wf_ind.
      intros st fr k Howner Hreachable Hbound.
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      pose proof (configuration_rank_valid Hranked) as Hvalid.
      pose proof (configuration_state_data Hranked) as Hdata.
      pose proof (configuration_control_ranked Hranked) as Hcontrol.
      pose proof (configuration_queue_ordered Hranked) as Hordered.
      destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
      - destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
        + subst next. destruct (@queue_peek_some_pop
            (R.queue st) (R.frame_owner fr) Hpeek) as [tail Hpop].
          exists
            {| R.cfg_state := R.with_queue st tail;
               R.cfg_control :=
                 R.RunRhs
                   (R.fresh_frame (R.with_queue st tail)
                     owner (R.frame_phase fr)) (tf owner) k |}.
          eapply ExecutedDrainRerun with (before := st) (fr := fr).
          * constructor.
          * exact Howner.
          * now rewrite Howner in Hpop.
          * exact Hordered.
        + assert (Hnext_ranked : ranked st next).
          { apply (data_queue_ranked Hdata).
            now apply queue_peek_member in Hpeek. }
          assert (Howner_ranked : ranked st (R.frame_owner fr)).
          { cbn in Hcontrol. exact (proj1 (proj1 Hcontrol)). }
          destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
          * destruct Hnext_ranked as [next_rank Hnext_lookup].
            assert (Hhigher_owner : R.rank_lt st owner next = true).
            { now rewrite <- Howner. }
            specialize (Hbound next next_rank eq_refl
              Hhigher_owner Hnext_lookup).
            destruct fuel as [|fuel']; [lia |].
            destruct (@queue_peek_some_pop (R.queue st) next Hpeek)
              as [tail Hpop].
            assert (Hnext_supported : List.In next support).
            { rewrite Hsupport. pose proof (reachable_config_supported
                finite Hreachable) as [Hstate _].
              apply (state_queue_supported Hstate).
              now apply queue_peek_member in Hpeek. }
            set (child :=
              {| R.cfg_state := R.with_queue st tail;
                 R.cfg_control := R.StartEpisode next (R.KDrain fr k) |}).
            assert (Hstep : Sem.step tf
              {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
              child).
            { unfold Sem.step, child. cbn -[R.fresh_frame].
              rewrite Hpeek. destruct (V.eq_dec next (R.frame_owner fr));
                [contradiction |]. rewrite Hhigher, Hpop. reflexivity. }
            assert (Hchild_reachable :
              Sem.steps tf (R.initial_config roots) child).
            { eapply steps_append_one; eauto. }
            assert (Hchild_higher :
              R.rank_lt (R.cfg_state child) owner next = true).
            { unfold child. cbn. now rewrite <- Howner. }
            destruct (Hchildren next (R.KDrain fr k) child
              Hnext_supported Hchild_higher Hchild_reachable eq_refl)
              as [child_st [Hchild Hchild_below]].
            set (returned :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.Return (R.KDrain fr k) |}).
            set (resumed :=
              {| R.cfg_state := child_st;
                 R.cfg_control := R.RunDrain fr k |}).
            assert (Hreturn : Sem.step tf returned resumed).
            { unfold Sem.step, returned, resumed. reflexivity. }
            assert (Hresume_reachable :
              Sem.steps tf (R.initial_config roots) resumed).
            { eapply steps_transitive; [exact Hchild_reachable |].
              eapply steps_transitive; [exact Hchild |].
              apply one_step. exact Hreturn. }
            assert (Hnext_lookup_child :
              R.Ranking.lookup (R.ranking child_st) next = Some next_rank).
            { apply (steps_rank_extends Hchild).
              unfold child. cbn. exact Hnext_lookup. }
            assert (Hnext_bound : forall candidate candidate_rank,
              R.queue_peek (R.queue child_st) = Some candidate ->
              R.rank_lt child_st owner candidate = true ->
              R.Ranking.lookup (R.ranking child_st) candidate =
                Some candidate_rank ->
              candidate_rank < fuel').
            { intros candidate candidate_rank Hcandidate _ Hcandidate_lookup.
              assert (Hcandidate_member : List.In candidate (R.queue child_st)).
              { now apply queue_peek_member in Hcandidate. }
              pose proof (Hchild_below candidate Hcandidate_member)
                as Hcandidate_below.
              rewrite (@rank_lt_lookup child_st candidate next
                candidate_rank next_rank Hcandidate_lookup Hnext_lookup_child)
                in Hcandidate_below.
              apply Nat.ltb_lt in Hcandidate_below. lia. }
            destruct (H fuel' ltac:(lia) child_st fr k Howner
              Hresume_reachable Hnext_bound)
              as [boundary Hexecuted].
            exists boundary. eapply executed_drain_prepend;
              [|exact Hexecuted].
            econstructor; [exact Hstep |].
            eapply steps_transitive; [exact Hchild |].
            econstructor; [exact Hreturn |constructor].
          * assert (Hlower : R.rank_lt st next owner = true).
            { pose proof (@rank_lt_reverse_if_false st
                (R.frame_owner fr) next Hvalid Howner_ranked Hnext_ranked
                (fun Heq => Hneq (eq_sym Heq)) Hhigher) as Hlower_frame.
              now rewrite Howner in Hlower_frame. }
            exists
              {| R.cfg_state := R.reset_registered_cells st owner;
                 R.cfg_control := R.Return k |}.
            apply ExecutedDrainReturn.
            -- apply one_step. unfold Sem.step. cbn.
               rewrite Hpeek. destruct (V.eq_dec next (R.frame_owner fr));
                 [contradiction |]. rewrite Hhigher, Howner. reflexivity.
            -- apply reset_registered_cells_below.
               eapply queue_peek_lower_below; eauto.
      - exists
          {| R.cfg_state := R.reset_registered_cells st owner;
             R.cfg_control := R.Return k |}.
        apply ExecutedDrainReturn.
        + apply one_step. unfold Sem.step. cbn. now rewrite Hpeek, Howner.
        + apply reset_registered_cells_below.
          now apply queue_peek_none_below.
    Qed.

    Lemma run_drain_reaches_boundary :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr k,
          R.frame_owner fr = owner ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
          drain_reaches_boundary tf owner k
            {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr k Howner Hreachable.
      destruct (@run_drain_reaches_executed_boundary support tf roots finite
        owner Hsupport Hchildren (RankFinite.bound (Sem.support finite))
        st fr k Howner Hreachable) as [boundary Hexecuted].
      - intros next rank Hpeek Hhigher Hlookup.
        eapply reachable_rank_bound; eauto.
      - exists boundary. split.
        + now apply executed_drain_steps in Hexecuted.
        + now apply executed_drain_is_boundary in Hexecuted.
    Qed.

    Lemma run_rhs_reaches_executed_boundary :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          exists boundary,
            executed_drain_boundary tf owner k
              {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
              boundary.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_reaches_drain support tf roots finite owner
        Hsupport Hchildren st fr body k Howner Hbody Hreachable)
        as [drain_st [drain_fr [Heval Heval_owner]]].
      assert (Hdrain_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain drain_fr k |}).
      { eapply steps_transitive; eauto. }
      assert (Hdrain_owner : R.frame_owner drain_fr = owner).
      { now rewrite Heval_owner. }
      destruct (@run_drain_reaches_executed_boundary support tf roots finite
        owner Hsupport Hchildren (RankFinite.bound (Sem.support finite))
        drain_st drain_fr k Hdrain_owner Hdrain_reachable)
        as [boundary Hexecuted].
      - intros next rank Hpeek Hhigher Hlookup.
        eapply reachable_rank_bound; eauto.
      - exists boundary. eapply executed_drain_prepend; eauto.
    Qed.

    Definition executed_round_boundary
      (tf : R.ConstraintSystem.system) (owner : V.t) (k : R.continuation)
      (start boundary : R.config) : Prop :=
      exists commit_st commit_fr direct drain_st drain_fr,
        Sem.steps tf start
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} /\
        R.frame_owner commit_fr = owner /\
        R.set_value commit_st commit_fr direct = (drain_st, drain_fr) /\
        R.frame_owner drain_fr = owner /\
        executed_drain_boundary tf owner k
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain drain_fr k |} boundary.

    Lemma run_rhs_reaches_executed_round_boundary :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          exists boundary,
            executed_round_boundary tf owner k
              {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
              boundary.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_reaches_commit support tf roots finite owner
        Hsupport Hchildren st fr body k Howner Hbody Hreachable)
        as [commit_st [commit_fr [direct [Hcommit Hcommit_owner]]]].
      assert (Hcommit_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}).
      { eapply steps_transitive; eauto. }
      destruct (R.set_value commit_st commit_fr direct)
        as [drain_st drain_fr] eqn:Hset.
      pose proof (@set_value_owner commit_st commit_fr direct
        drain_st drain_fr Hset) as Hdrain_commit.
      assert (Hdrain_owner : R.frame_owner drain_fr = owner).
      { now rewrite Hdrain_commit, Hcommit_owner, Howner. }
      assert (Hdrain_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain drain_fr k |}).
      { eapply steps_append_one; [exact Hcommit_reachable |].
        unfold Sem.step. cbn -[R.set_value]. now rewrite Hset. }
      destruct (@run_drain_reaches_executed_boundary support tf roots finite
        owner Hsupport Hchildren (RankFinite.bound (Sem.support finite))
        (drain_st) drain_fr k Hdrain_owner Hdrain_reachable)
        as [boundary Hexecuted].
      - intros next rank Hpeek Hhigher Hlookup.
        eapply reachable_rank_bound; eauto.
      - exists boundary. exists commit_st, commit_fr, direct, drain_st, drain_fr.
        repeat split; try assumption.
        now rewrite Hcommit_owner, Howner.
    Qed.

    Lemma executed_round_steps_plus :
      forall tf owner k st fr body boundary,
        executed_drain_boundary tf owner k
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
          boundary ->
        steps_plus tf
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
          boundary.
    Proof.
      intros tf owner k st fr body boundary Hexecuted.
      destruct Hexecuted.
      - eapply steps_nontrivial_plus; [exact H |].
        intro Heq. inversion Heq.
      - eapply steps_append_one_plus; [exact H |].
        unfold Sem.step. cbn.
        destruct (R.queue before) as [|head rest] eqn:Hqueue;
          cbn in H1; try discriminate.
        inversion H1; subst head rest. cbn. rewrite H0.
        destruct (V.eq_dec owner owner); [reflexivity |contradiction].
    Qed.

    Lemma run_rhs_reaches_boundary :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          drain_reaches_boundary tf owner k
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_reaches_drain support tf roots finite owner
        Hsupport Hchildren st fr body k Howner Hbody Hreachable)
        as [drain_st [drain_fr [Heval Heval_owner]]].
      assert (Hdrain_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain drain_fr k |}).
      { eapply steps_transitive; eauto. }
      assert (Hdrain_owner : R.frame_owner drain_fr = owner).
      { now rewrite Heval_owner. }
      destruct (@run_drain_reaches_boundary support tf roots finite owner
        Hsupport Hchildren drain_st drain_fr k Hdrain_owner Hdrain_reachable)
        as [boundary [Hdrain Hboundary]].
      exists boundary. split; [eapply steps_transitive; eauto |exact Hboundary].
    Qed.

    Lemma run_rhs_reaches_boundary_plus :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        higher_episodes_complete support tf roots owner ->
        forall st fr body k,
          R.frame_owner fr = owner ->
          Sem.rhs_supported (supported support) body ->
          Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} ->
          exists boundary,
            steps_plus tf
              {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |}
              boundary /\
            drain_boundary tf owner k boundary.
    Proof.
      intros support tf roots finite owner Hsupport Hchildren
        st fr body k Howner Hbody Hreachable.
      destruct (@run_rhs_reaches_executed_boundary
        support tf roots finite owner
        Hsupport Hchildren st fr body k Howner Hbody Hreachable)
        as [boundary Hexecuted].
      exists boundary. split.
      - now apply executed_round_steps_plus in Hexecuted.
      - now apply executed_drain_is_boundary in Hexecuted.
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
      destruct (U.update true target
        (R.side_phase
          (R.stored_side_cell (R.promote_side_target st fr target)
            (R.frame_owner fr) target))
        (R.stored_contribution (R.promote_side_target st fr target)
          (R.frame_owner fr) target) input) as [phase contribution].
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
        + destruct (R.is_materialized (R.observe st root) root);
            inversion Hstep; subst; apply sigma_extends_observe.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[owner rest] |].
        + inversion Hstep; subst. apply sigma_extends_with_queue.
        + inversion Hstep; subst. apply sigma_extends_refl.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        apply sigma_extends_materialize.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. apply sigma_extends_refl.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. unfold observed.
            apply sigma_extends_observe.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base fr target)
              as [[next_st next_fr] read] eqn:Hget.
            inversion Hstep; subst.
            eapply sigma_extends_trans with (middle := base).
            -- unfold base, observed. destruct (R.is_materialized
                 (R.observe st target) target).
               ++ apply sigma_extends_observe.
               ++ eapply sigma_extends_trans with
                    (middle := R.observe st target);
                    [exact (@sigma_extends_observe st target)
                    |exact (@sigma_extends_enqueue (R.observe st target) target)].
            -- eapply sigma_extends_complete_get; exact Hget.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution (R.observe st target)
            fr1 target input) as [next_st changed] eqn:Hwrite.
          inversion Hstep; subst. eapply sigma_extends_trans.
          * apply sigma_extends_observe.
          * eapply sigma_extends_trans.
            -- eapply sigma_extends_write_side_contribution; exact Hwrite.
            -- apply sigma_extends_continue_side.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. unfold observed. apply sigma_extends_observe.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. unfold observed.
               apply sigma_extends_observe.
            -- inversion Hstep; subst. eapply sigma_extends_trans.
               ++ unfold observed. apply sigma_extends_observe.
               ++ eapply sigma_extends_trans;
                    [apply sigma_extends_enqueue |apply sigma_extends_materialize].
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          apply sigma_extends_same. reflexivity.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. apply sigma_extends_refl.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [next_st changed] eqn:Hwrite.
            inversion Hstep; subst. eapply sigma_extends_trans.
            -- eapply sigma_extends_write_side_contribution; exact Hwrite.
            -- apply sigma_extends_continue_dead.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [next_st next_fr] eqn:Hset.
        inversion Hstep; subst. eapply sigma_extends_set_value; exact Hset.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head rest] |];
              try discriminate. inversion Hstep; subst.
            apply sigma_extends_with_queue.
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

    Lemma steps_sigma_extends :
      forall tf before after,
        Sem.steps tf before after ->
        sigma_extends (R.cfg_state before) (R.cfg_state after).
    Proof.
      intros tf before after Hsteps. induction Hsteps.
      - apply sigma_extends_refl.
      - eapply sigma_extends_trans;
          [eapply next_config_sigma_extends; exact H |exact IHHsteps].
    Qed.

    Lemma step_materialized_mono :
      forall tf before after x,
        Sem.step tf before after ->
        R.is_materialized (R.cfg_state before) x = true ->
        R.is_materialized (R.cfg_state after) x = true.
    Proof.
      intros tf before after x Hstep Hmaterialized.
      unfold R.is_materialized in *.
      destruct (M.lookup (R.sigma (R.cfg_state before)) x)
        as [value |] eqn:Hlookup; [|discriminate].
      destruct (@next_config_sigma_extends tf before after Hstep
        x value Hlookup)
        as [next_value Hnext]. now rewrite Hnext.
    Qed.

    Fixpoint unmaterialized_count
      (support : list V.t) (st : R.state) : nat :=
      match support with
      | [] => 0
      | x :: rest =>
          (if R.is_materialized st x then 0 else 1) +
          unmaterialized_count rest st
      end.

    Lemma unmaterialized_count_step_nonincreasing :
      forall support tf before after,
        Sem.step tf before after ->
        unmaterialized_count support (R.cfg_state after) <=
        unmaterialized_count support (R.cfg_state before).
    Proof.
      intros support. induction support as [|x rest IH];
        intros tf before after Hstep; cbn; [lia |].
      specialize (IH tf before after Hstep).
      destruct (R.is_materialized (R.cfg_state before) x) eqn:Hbefore.
      - rewrite (@step_materialized_mono tf before after x Hstep Hbefore).
        lia.
      - destruct (R.is_materialized (R.cfg_state after) x); lia.
    Qed.

    Lemma unmaterialized_count_steps_nonincreasing :
      forall support tf before after,
        Sem.steps tf before after ->
        unmaterialized_count support (R.cfg_state after) <=
        unmaterialized_count support (R.cfg_state before).
    Proof.
      intros support tf before after Hsteps. induction Hsteps; [lia |].
      pose proof (unmaterialized_count_step_nonincreasing support H) as Hfirst.
      lia.
    Qed.

    Lemma unmaterialized_count_update_other :
      forall support st target value,
        ~ List.In target support ->
        unmaterialized_count support
          (R.with_sigma st (M.update (R.sigma st) target value)) =
        unmaterialized_count support st.
    Proof.
      intros support. induction support as [|x rest IH];
        intros st target value Hnotin; [reflexivity |].
      cbn. assert (Hneq : x <> target).
      { intro Heq. apply Hnotin. now left. }
      assert (Hrest : ~ List.In target rest).
      { intro Hin. apply Hnotin. now right. }
      unfold R.is_materialized. cbn.
      rewrite ML.lookup_update_other by exact Hneq.
      now rewrite (IH st target value Hrest).
    Qed.

    Lemma unmaterialized_count_materialize_decreases :
      forall support st target,
        NoDup support -> List.In target support ->
        R.is_materialized st target = false ->
        unmaterialized_count support (R.materialize st target) <
        unmaterialized_count support st.
    Proof.
      intros support. induction support as [|x rest IH];
        intros st target Hnodup Hin Hfresh; [contradiction |].
      inversion Hnodup as [|? ? Hnotin Hrest]; subst. cbn in Hin. cbn.
      destruct Hin as [-> |Hin].
      - rewrite Hfresh. unfold R.materialize, R.is_materialized in *.
        destruct (M.lookup (R.sigma st) target); try discriminate.
        cbn. rewrite ML.lookup_update_same. cbn.
        rewrite (@unmaterialized_count_update_other rest st target D.bottom
          Hnotin). lia.
      - assert (Hneq : x <> target).
        { intro Heq. subst. contradiction. }
        unfold R.is_materialized in Hfresh.
        destruct (M.lookup (R.sigma st) target) eqn:Htarget;
          try discriminate.
        assert (Hfresh0 : R.is_materialized st target = false).
        { unfold R.is_materialized. now rewrite Htarget. }
        specialize (IH st target Hrest Hin Hfresh0).
        unfold R.materialize in IH |- *. rewrite Htarget in IH |- *.
        cbn. unfold R.is_materialized. cbn.
        rewrite ML.lookup_update_other by exact Hneq. lia.
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
        remember (R.observe st target) as observed eqn:Hobserve.
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
        + apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
          cbn. split; [exact (proj2 Hguard) |exact Hordered0].
        + remember (if R.is_materialized observed target
            then observed else R.enqueue observed target) as base.
          destruct (R.complete_get base fr target)
            as [[next_st next_fr] value] eqn:Hget.
          inversion Hstep; subst. cbn. rewrite (complete_get_owner Hget).
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
        unfold R.continue_side in Hstep. destruct changed.
        + destruct (R.rank_lt next_st (R.frame_owner fr1) target &&
            negb (R.is_materialized next_st target))%bool eqn:Hguard.
          * apply Bool.andb_true_iff in Hguard. inversion Hstep; subst.
            cbn. split; [exact (proj1 Hguard) |]. rewrite Howner.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
          * inversion Hstep; subst. cbn. rewrite Howner.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
        + inversion Hstep; subst. cbn. rewrite Howner.
          eapply continuation_below_extended; eauto. exact (proj1 Hfr).
      - cbn -[R.observe R.materialize R.enqueue] in Hstep.
        remember (R.observe st target) as observed eqn:Hobserve.
        assert (Hext0 : rank_extends st observed).
        { subst. exact (@rank_extends_observe st target
            (R.observe st target) eq_refl). }
        assert (Hordered0 :
          continuation_below observed (R.frame_owner fr) k).
        { eapply continuation_below_extended; eauto. exact (proj1 Hfr). }
        destruct (R.is_materialized observed target).
        + inversion Hstep; subst. exact Hordered0.
        + destruct (R.rank_lt observed (R.frame_owner fr) target) eqn:Hlt.
          * inversion Hstep; subst. cbn. split; assumption.
          * inversion Hstep; subst.
            eapply continuation_below_extended; eauto. exact (proj1 Hfr).
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
          * destruct (R.rank_lt next_st (R.frame_owner fr) target &&
              negb (R.is_materialized next_st target))%bool eqn:Hguard.
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
      destruct (R.set_value st fr direct) as [next_st next_fr] eqn:Hset.
      inversion Hstep; subst. cbn.
      rewrite (@set_value_owner st fr direct next_st next_fr Hset).
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
        + destruct (R.is_materialized (R.observe st root) root);
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

    Fixpoint continuation_contains (owner : V.t) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => False
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          owner = R.frame_owner fr \/ continuation_contains owner rest
      end.

    Definition control_contains (owner : V.t) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
      | R.StartEpisode current k =>
          owner = current \/ continuation_contains owner k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          owner = R.frame_owner fr \/ continuation_contains owner k
      | R.Return k => continuation_contains owner k
      end.

    Fixpoint continuation_containsb
      (owner : V.t) (k : R.continuation) : bool :=
      match k with
      | R.KLoop | R.KSeedLoop _ => false
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          if V.eq_dec owner (R.frame_owner fr)
          then true else continuation_containsb owner rest
      end.

    Definition control_containsb (owner : V.t) (control : R.control) : bool :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => false
      | R.StartEpisode current k =>
          if V.eq_dec owner current then true else continuation_containsb owner k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          if V.eq_dec owner (R.frame_owner fr)
          then true else continuation_containsb owner k
      | R.Return k => continuation_containsb owner k
      end.

    Lemma continuation_containsb_spec :
      forall owner k,
        continuation_containsb owner k = true <-> continuation_contains owner k.
    Proof.
      intros owner k. induction k; cbn.
      all: try (split; [discriminate |contradiction]).
      all: destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq];
        cbn.
      all: try (split; [intro; now left |intro; reflexivity]).
      all: rewrite IHk; tauto.
    Qed.

    Lemma control_containsb_spec :
      forall owner control,
        control_containsb owner control = true <-> control_contains owner control.
    Proof.
      intros owner control. destruct control; cbn.
      - split; [discriminate |contradiction].
      - split; [discriminate |contradiction].
      - split; [discriminate |contradiction].
      - destruct (V.eq_dec owner t) as [Heq |Hneq]; cbn.
        + split; [intro; now left |intro; reflexivity].
        + rewrite continuation_containsb_spec. tauto.
      - destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; cbn.
        + split; [intro; now left |intro; reflexivity].
        + rewrite continuation_containsb_spec. tauto.
      - destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; cbn.
        + split; [intro; now left |intro; reflexivity].
        + rewrite continuation_containsb_spec. tauto.
      - destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; cbn.
        + split; [intro; now left |intro; reflexivity].
        + rewrite continuation_containsb_spec. tauto.
      - destruct (V.eq_dec owner (R.frame_owner f)) as [Heq |Hneq]; cbn.
        + split; [intro; now left |intro; reflexivity].
        + rewrite continuation_containsb_spec. tauto.
      - apply continuation_containsb_spec.
    Qed.

    Inductive active_prefix
      (owner : V.t) (tf : R.ConstraintSystem.system) :
      R.config -> R.config -> Prop :=
    | ActivePrefixRefl : forall c, active_prefix owner tf c c
    | ActivePrefixStep :
        forall first next final,
          control_contains owner (R.cfg_control first) ->
          Sem.step tf first next ->
          active_prefix owner tf next final ->
          active_prefix owner tf first final.

    Lemma active_prefix_steps :
      forall owner tf first final,
        active_prefix owner tf first final -> Sem.steps tf first final.
    Proof.
      intros owner tf first final Hprefix. induction Hprefix;
        [constructor |econstructor; eauto].
    Qed.

    Lemma active_prefix_initial_contains :
      forall owner tf first final,
        active_prefix owner tf first final ->
        control_contains owner (R.cfg_control final) ->
        control_contains owner (R.cfg_control first).
    Proof. intros owner tf first final Hprefix Hfinal. destruct Hprefix; assumption. Qed.

    Definition owner_commitb (owner : V.t) (c : R.config) : bool :=
      match R.cfg_control c with
      | R.RunCommit fr _ _ =>
          if V.eq_dec (R.frame_owner fr) owner then true else false
      | _ => false
      end.

    Inductive until_owner_commit
      (owner : V.t) (tf : R.ConstraintSystem.system) :
      R.config -> R.config -> Prop :=
    | UntilOwnerCommitDone :
        forall c,
          owner_commitb owner c = true -> until_owner_commit owner tf c c
    | UntilOwnerCommitStep :
        forall first next final,
          owner_commitb owner first = false ->
          Sem.step tf first next ->
          until_owner_commit owner tf next final ->
          until_owner_commit owner tf first final.

    Lemma until_owner_commit_steps :
      forall owner tf first final,
        until_owner_commit owner tf first final -> Sem.steps tf first final.
    Proof. intros owner tf first final H; induction H; [constructor |econstructor; eauto]. Qed.

    Lemma until_owner_commit_final :
      forall owner tf first final,
        until_owner_commit owner tf first final -> owner_commitb owner final = true.
    Proof. intros owner tf first final H; induction H; assumption. Qed.

    Lemma owner_commitb_contains :
      forall owner c,
        owner_commitb owner c = true -> control_contains owner (R.cfg_control c).
    Proof.
      intros owner [st control] Hcommit. destruct control; try discriminate.
      cbn in Hcommit |- *. destruct (V.eq_dec (R.frame_owner f) owner);
        [now left |discriminate].
    Qed.

    Lemma active_prefix_to_first_owner_commit :
      forall owner tf first final,
        active_prefix owner tf first final -> owner_commitb owner final = true ->
        exists commit,
          until_owner_commit owner tf first commit /\
          active_prefix owner tf first commit.
    Proof.
      intros owner tf first final Hprefix. induction Hprefix; intros Hfinal.
      - exists c. split; [now apply UntilOwnerCommitDone |constructor].
      - destruct (owner_commitb owner first) eqn:Hfirst.
        + exists first. split; [now apply UntilOwnerCommitDone |constructor].
        + destruct (IHHprefix Hfinal) as [commit [Huntil Hactive]].
          exists commit. split; [econstructor; eauto |econstructor; eauto].
    Qed.

    Lemma active_prefix_trans :
      forall owner tf first middle final,
        active_prefix owner tf first middle ->
        control_contains owner (R.cfg_control middle) ->
        active_prefix owner tf middle final ->
        active_prefix owner tf first final.
    Proof.
      intros owner tf first middle final Hfirst Hmiddle Hlast.
      induction Hfirst; [exact Hlast |econstructor; eauto].
    Qed.

    Lemma active_prefix_snoc :
      forall owner tf first middle final,
        active_prefix owner tf first middle ->
        control_contains owner (R.cfg_control middle) ->
        Sem.step tf middle final -> active_prefix owner tf first final.
    Proof.
      intros. eapply active_prefix_trans; [exact H |exact H0 |].
      econstructor; [exact H0 |exact H1 |constructor].
    Qed.

    Fixpoint continuation_above
      (owner : V.t) (base k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => False
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          (R.frame_owner fr = owner /\ rest = base) \/
          continuation_above owner base rest
      end.

    Definition episode_active_control
      (owner : V.t) (base : R.continuation) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
      | R.StartEpisode current k =>
          (current = owner /\ k = base) \/ continuation_above owner base k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          (R.frame_owner fr = owner /\ k = base) \/
          continuation_above owner base k
      | R.Return k => continuation_above owner base k
      end.

    Lemma continuation_above_after_get :
      forall owner base fr target next k,
        ((R.frame_owner fr = owner /\ k = base) \/
         continuation_above owner base k) ->
        continuation_above owner base (R.KAfterGet fr target next k).
    Proof. cbn. auto. Qed.

    Lemma continuation_above_after_side :
      forall owner base fr next k,
        ((R.frame_owner fr = owner /\ k = base) \/
         continuation_above owner base k) ->
        continuation_above owner base (R.KAfterSide fr next k).
    Proof. cbn. auto. Qed.

    Lemma continuation_above_after_spawn :
      forall owner base fr next k,
        ((R.frame_owner fr = owner /\ k = base) \/
         continuation_above owner base k) ->
        continuation_above owner base (R.KAfterSpawn fr next k).
    Proof. cbn. auto. Qed.

    Lemma continuation_above_dead :
      forall owner base fr direct pending k,
        ((R.frame_owner fr = owner /\ k = base) \/
         continuation_above owner base k) ->
        continuation_above owner base (R.KDead fr direct pending k).
    Proof. cbn. auto. Qed.

    Lemma continuation_above_drain :
      forall owner base fr k,
        ((R.frame_owner fr = owner /\ k = base) \/
         continuation_above owner base k) ->
        continuation_above owner base (R.KDrain fr k).
    Proof. cbn. auto. Qed.

    Lemma episode_active_control_step :
      forall tf before after owner base,
        Sem.step tf before after ->
        episode_active_control owner base (R.cfg_control before) ->
        episode_active_control owner base (R.cfg_control after) \/
        R.cfg_control after = R.Return base.
    Proof.
      intros tf [st control] after owner base Hstep Hactive.
      unfold Sem.step in Hstep. destruct control as
        [|roots |remaining |current k |fr body k |fr direct pending k
         |fr direct k |fr k |k]; try contradiction.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        now left.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. now left.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. left. cbn. right.
            now apply continuation_above_after_get.
          * set (base_st := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base_st fr target)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. left.
            pose proof (@complete_get_owner base_st fr target
              st1 fr1 value Hget) as Howner.
            cbn in Hactive |- *. now rewrite Howner.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw)
            as [fr1 input] eqn:Hrecord.
          pose proof (@record_side_input_owner fr target raw fr1 input Hrecord)
            as Howner.
          destruct (R.write_side_contribution (R.observe st target)
            fr1 target input) as [st1 changed].
          unfold R.continue_side in Hstep. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool;
              inversion Hstep; subst; left; cbn in Hactive |- *;
              rewrite Howner; auto using continuation_above_after_side.
          * inversion Hstep; subst. left. cbn in Hactive |- *.
            now rewrite Howner.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. now left.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. left. cbn. right.
               now apply continuation_above_after_spawn.
            -- inversion Hstep; subst. now left.
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst. now left.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. now left.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed].
            unfold R.continue_dead in Hstep. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool.
               ++ inversion Hstep; subst. left. cbn. right.
                  now apply continuation_above_dead.
               ++ inversion Hstep; subst. now left.
            -- inversion Hstep; subst. now left.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. left.
        pose proof (@set_value_owner st fr direct st1 fr1 Hset) as Howner.
        cbn in Hactive |- *. now rewrite Howner.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst. now left.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst. left. cbn. right.
               now apply continuation_above_drain.
            -- inversion Hstep; subst. cbn in Hactive.
               destruct Hactive as [[Howner Hbase] |Habove].
               ++ right. now subst.
               ++ now left.
        + inversion Hstep; subst. cbn in Hactive.
          destruct Hactive as [[Howner Hbase] |Habove].
          * right. now subst.
          * now left.
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep, Hactive; try contradiction.
        + destruct (R.complete_get st fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst. left.
          pose proof (@complete_get_owner st fr target st1 fr1 value Hget)
            as Howner. cbn.
          destruct Hactive as [[Hframe Hbase] |Habove].
          * left. now rewrite Howner.
          * now right.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. now left.
    Qed.

    Lemma continuation_above_contains :
      forall owner base k,
        continuation_above owner base k -> continuation_contains owner k.
    Proof.
      intros owner base k. induction k; cbn; intros Habove;
        try contradiction.
      all: destruct Habove as [[Howner Hbase] |Habove].
      all: try (left; symmetry; exact Howner).
      all: right; auto.
    Qed.

    Lemma episode_active_contains :
      forall owner base control,
        episode_active_control owner base control -> control_contains owner control.
    Proof.
      intros owner base control. destruct control; cbn; intros Hactive;
        try contradiction.
      all: try (destruct Hactive as [[Howner Hbase] |Habove];
        [left; symmetry; exact Howner
        |right; exact (@continuation_above_contains owner base _ Habove)]).
      exact (@continuation_above_contains owner base _ Hactive).
    Qed.

    Lemma steps_to_episode_boundary :
      forall owner base tf first final,
        Sem.steps tf first final ->
        episode_active_control owner base (R.cfg_control first) ->
        (exists exit,
          active_prefix owner tf first exit /\
          R.cfg_control exit = R.Return base) \/
        (active_prefix owner tf first final /\
         episode_active_control owner base (R.cfg_control final)).
    Proof.
      intros owner base tf first final Hsteps. induction Hsteps as
        [c |before next after Hstep Htail IH]; intros Hactive.
      - right. split; [constructor |exact Hactive].
      - destruct (@episode_active_control_step
          tf before next owner base Hstep Hactive) as [Hnext |Hexit].
        + destruct (IH Hnext) as
            [[exit [Hprefix Hexit]] |[Hprefix Hfinal]].
          * left. exists exit. split.
            -- econstructor;
                 [exact (@episode_active_contains owner base
                    (R.cfg_control before) Hactive)
                 |exact Hstep |exact Hprefix].
            -- exact Hexit.
          * right. split.
            -- econstructor;
                 [exact (@episode_active_contains owner base
                    (R.cfg_control before) Hactive)
                 |exact Hstep |exact Hprefix].
            -- exact Hfinal.
        + left. exists next. split.
          * econstructor;
              [exact (@episode_active_contains owner base
                 (R.cfg_control before) Hactive)
              |exact Hstep |constructor].
          * exact Hexit.
    Qed.

    Lemma active_prefix_episode_active :
      forall owner base tf first final,
        active_prefix owner tf first final ->
        episode_active_control owner base (R.cfg_control first) ->
        ~ continuation_contains owner base ->
        control_contains owner (R.cfg_control final) ->
        episode_active_control owner base (R.cfg_control final).
    Proof.
      intros owner base tf first final Hprefix. induction Hprefix;
        intros Hactive Hbase Hfinal; [exact Hactive |].
      destruct (@episode_active_control_step
        tf first next owner base H0 Hactive) as [Hnext |Hexit].
      - eapply IHHprefix; eauto.
      - pose proof (@active_prefix_initial_contains owner tf next final
          Hprefix Hfinal) as Hnext_contains.
        rewrite Hexit in Hnext_contains. cbn in Hnext_contains. contradiction.
    Qed.

    Inductive active_prefix_plus
      (owner : V.t) (tf : R.ConstraintSystem.system) :
      R.config -> R.config -> Prop :=
    | ActivePrefixPlus :
        forall first next final,
          control_contains owner (R.cfg_control first) ->
          Sem.step tf first next ->
          active_prefix owner tf next final ->
          active_prefix_plus owner tf first final.

    Lemma active_prefix_plus_prefix :
      forall owner tf first final,
        active_prefix_plus owner tf first final -> active_prefix owner tf first final.
    Proof. intros owner tf first final H; destruct H; econstructor; eauto. Qed.

    Lemma steps_plus_to_episode_boundary :
      forall owner base tf first final,
        steps_plus tf first final ->
        episode_active_control owner base (R.cfg_control first) ->
        (exists exit,
          active_prefix_plus owner tf first exit /\
          R.cfg_control exit = R.Return base) \/
        (active_prefix_plus owner tf first final /\
         episode_active_control owner base (R.cfg_control final)).
    Proof.
      intros owner base tf first final Hplus Hactive.
      destruct Hplus as [first next final Hstep Htail].
      destruct (@episode_active_control_step
        tf first next owner base Hstep Hactive) as [Hnext |Hexit].
      - destruct (@steps_to_episode_boundary owner base tf next final
          Htail Hnext) as [[exit [Hprefix Hexit]] |[Hprefix Hfinal]].
        + left. exists exit. split.
          * econstructor;
              [exact (@episode_active_contains owner base
                 (R.cfg_control first) Hactive)
              |exact Hstep |exact Hprefix].
          * exact Hexit.
        + right. split.
          * econstructor;
              [exact (@episode_active_contains owner base
                 (R.cfg_control first) Hactive)
              |exact Hstep |exact Hprefix].
          * exact Hfinal.
      - left. exists next. split.
        + econstructor;
            [exact (@episode_active_contains owner base
               (R.cfg_control first) Hactive)
            |exact Hstep |constructor].
        + exact Hexit.
    Qed.

    Lemma steps_first_inactive :
      forall owner tf first final,
        Sem.steps tf first final ->
        control_contains owner (R.cfg_control first) ->
        (exists inactive,
          active_prefix owner tf first inactive /\
          ~ control_contains owner (R.cfg_control inactive)) \/
        (active_prefix owner tf first final /\
         control_contains owner (R.cfg_control final)).
    Proof.
      intros owner tf first final Hsteps. induction Hsteps as
        [c |before next after Hstep Htail IH]; intros Hactive.
      - right. split; [constructor |exact Hactive].
      - destruct (control_containsb owner (R.cfg_control next)) eqn:Hnext.
        + apply control_containsb_spec in Hnext.
          destruct (IH Hnext) as
            [[inactive [Hprefix Hinactive]] |[Hprefix Hfinal]].
          * left. exists inactive. split; [econstructor; eauto |exact Hinactive].
          * right. split; [econstructor; eauto |exact Hfinal].
        + left. exists next. split.
          * econstructor; [exact Hactive |exact Hstep |constructor].
          * intro Hcontains. apply control_containsb_spec in Hcontains.
            congruence.
    Qed.

    Lemma active_prefix_last_step :
      forall owner tf first final,
        active_prefix owner tf first final ->
        control_contains owner (R.cfg_control first) ->
        ~ control_contains owner (R.cfg_control final) ->
        exists before,
          active_prefix owner tf first before /\
          control_contains owner (R.cfg_control before) /\
          Sem.step tf before final.
    Proof.
      intros owner tf first final Hprefix. induction Hprefix;
        intros Hfirst Hfinal; [contradiction |].
      destruct Hprefix.
      - exists first. split; [constructor |split; assumption].
      - destruct (IHHprefix H1 Hfinal)
          as [before [Hbefore [Hcontains Hlast]]].
        exists before. split; [econstructor; eauto |now split].
    Qed.

    Lemma step_loses_owner_at_boundary :
      forall tf roots before after owner,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_contains owner (R.cfg_control before) ->
        ~ control_contains owner (R.cfg_control after) ->
        exists st k,
          after = {| R.cfg_state := st; R.cfg_control := R.Return k |} /\
          queue_strictly_below owner st.
    Proof.
      intros tf roots [st control] after owner Hreachable Hstep Hbefore Hafter.
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      unfold Sem.step in Hstep. destruct control as
        [|seed_roots |remaining |current k |fr body k |fr direct pending k
         |fr direct k |fr k |k]; try contradiction.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        cbn in Hbefore, Hafter. tauto.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. cbn in Hbefore, Hafter. tauto.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. cbn in Hbefore, Hafter. tauto.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base fr target)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst.
            pose proof (@complete_get_owner base fr target st1 fr1 value Hget)
              as Howner. cbn in Hbefore, Hafter. rewrite Howner in Hafter.
            tauto.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw)
            as [fr1 input] eqn:Hrecord.
          pose proof (@record_side_input_owner fr target raw fr1 input Hrecord)
            as Howner.
          destruct (R.write_side_contribution (R.observe st target)
            fr1 target input) as [st1 changed].
          unfold R.continue_side in Hstep. destruct changed;
            try destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool;
            inversion Hstep; subst; cbn in Hbefore, Hafter;
            rewrite Howner in Hafter; tauto.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target);
            try destruct (R.rank_lt observed (R.frame_owner fr) target);
            inversion Hstep; subst; cbn in Hbefore, Hafter; tauto.
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          cbn in Hbefore, Hafter. tauto.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. cbn in Hbefore, Hafter. tauto.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed].
            unfold R.continue_dead in Hstep. destruct changed;
              try destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool;
              inversion Hstep; subst; cbn in Hbefore, Hafter; tauto.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst.
        pose proof (@set_value_owner st fr direct st1 fr1 Hset) as Howner.
        cbn in Hbefore, Hafter. rewrite Howner in Hafter. tauto.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
        + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst.
            cbn in Hbefore, Hafter. tauto.
          * destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst.
               cbn in Hbefore, Hafter. tauto.
            -- inversion Hstep; subst. cbn in Hbefore, Hafter.
               assert (Howner : owner = R.frame_owner fr) by tauto.
               subst owner. exists (R.reset_registered_cells st
                 (R.frame_owner fr)), k. split; [reflexivity |].
               apply reset_registered_cells_below.
               pose proof (configuration_rank_valid Hranked) as Hvalid.
               pose proof (configuration_state_data Hranked) as Hdata.
               pose proof (configuration_control_ranked Hranked) as Hcontrol.
               pose proof (configuration_queue_ordered Hranked) as Hordered.
               assert (Hnext_ranked : ranked st next).
               { apply (data_queue_ranked Hdata).
                 now apply queue_peek_member in Hpeek. }
               assert (Hframe_ranked : ranked st (R.frame_owner fr)).
               { cbn in Hcontrol. exact (proj1 (proj1 Hcontrol)). }
               assert (Hlower : R.rank_lt st next (R.frame_owner fr) = true).
               { exact (@rank_lt_reverse_if_false st (R.frame_owner fr) next
                   Hvalid Hframe_ranked Hnext_ranked
                   (fun Heq => Hneq (eq_sym Heq)) Hhigher). }
               eapply queue_peek_lower_below; eauto.
        + inversion Hstep; subst. cbn in Hbefore, Hafter.
          assert (Howner : owner = R.frame_owner fr) by tauto.
          subst owner. exists (R.reset_registered_cells st
            (R.frame_owner fr)), k. split; [reflexivity |].
          apply reset_registered_cells_below.
          now apply queue_peek_none_below.
      - destruct k as
          [|seed_remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep, Hbefore, Hafter;
          try contradiction.
        + destruct (R.complete_get st fr target)
            as [[st1 fr1] value] eqn:Hget.
          inversion Hstep; subst.
          pose proof (@complete_get_owner st fr target st1 fr1 value Hget)
            as Howner. exfalso. apply Hafter. cbn. now rewrite Howner.
        + inversion Hstep; subst. exfalso. apply Hafter. exact Hbefore.
        + inversion Hstep; subst. exfalso. apply Hafter. exact Hbefore.
        + inversion Hstep; subst. exfalso. apply Hafter. exact Hbefore.
        + inversion Hstep; subst. exfalso. apply Hafter. exact Hbefore.
    Qed.

    Lemma continuation_contains_below :
      forall st upper k owner,
        continuation_below st upper k ->
        continuation_contains owner k ->
        R.rank_lt st owner upper = true.
    Proof.
      intros st upper k. revert upper.
      induction k; intros upper owner Hbelow Hcontains; cbn in *;
        try contradiction.
      all: destruct Hbelow as [Htop Hbelow].
      all: destruct Hcontains as [-> |Hcontains]; [exact Htop |].
      all: pose proof (IHk (R.frame_owner f) owner Hbelow Hcontains)
        as Hinner.
      all: pose proof (@rank_lt_true_ranked
        st owner (R.frame_owner f) Hinner) as [Howner Hframe].
      all: pose proof (@rank_lt_true_ranked
        st (R.frame_owner f) upper Htop) as [_ Hupper].
      all: exact (@rank_lt_trans st owner (R.frame_owner f) upper
        Howner Hframe Hupper Hinner Htop).
    Qed.

    Lemma active_owner_commit_shape :
      forall tf roots owner base c,
        Sem.steps tf (R.initial_config roots) c ->
        episode_active_control owner base (R.cfg_control c) ->
        owner_commitb owner c = true ->
        exists st fr direct,
          c =
            {| R.cfg_state := st;
               R.cfg_control := R.RunCommit fr direct base |} /\
          R.frame_owner fr = owner.
    Proof.
      intros tf roots owner base [st control] Hreachable Hactive Hcommit.
      destruct control; try discriminate.
      unfold owner_commitb in Hcommit. cbn in Hcommit.
      destruct (V.eq_dec (R.frame_owner f) owner)
        as [Howner |Hneq]; [|discriminate].
      cbn in Hactive.
      destruct Hactive as [[Howner' Hbase] |Habove].
      - subst c. exists st, f, t. split; [reflexivity |exact Howner].
      - pose proof (@reachable_control_ordered tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit f t c |} Hreachable)
          as Hordered.
        cbn in Hordered.
        pose proof (@continuation_contains_below st
          (R.frame_owner f) c owner Hordered
          (@continuation_above_contains owner base c Habove)) as Hfalse.
        rewrite Howner in Hfalse.
        pose proof (proj1 (@rank_lt_true_ranked st owner owner Hfalse))
          as Hranked.
        rewrite (@rank_lt_irrefl st owner Hranked) in Hfalse. discriminate.
    Qed.

    Lemma active_exit_is_boundary :
      forall tf roots owner st fr body k exit,
        R.frame_owner fr = owner ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr body k |} ->
        active_prefix owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr body k |} exit ->
        R.cfg_control exit = R.Return k ->
        exists exit_st,
          exit =
            {| R.cfg_state := exit_st;
               R.cfg_control := R.Return k |} /\
          queue_strictly_below owner exit_st.
    Proof.
      intros tf roots owner st fr body k exit
        Hframe Hreachable Hprefix Hexit.
      assert (Hordered : continuation_below st owner k).
      { pose proof (@reachable_control_ordered tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr body k |} Hreachable)
          as Hcontrol.
        cbn in Hcontrol. now rewrite Hframe in Hcontrol. }
      assert (Hexit_inactive :
        ~ control_contains owner (R.cfg_control exit)).
      { rewrite Hexit. cbn. intro Hcontains.
        pose proof (@continuation_contains_below st owner k owner
          Hordered Hcontains) as Hlt.
        pose proof (proj1 (@rank_lt_true_ranked st owner owner Hlt))
          as Hranked.
        rewrite (@rank_lt_irrefl st owner Hranked) in Hlt. discriminate. }
      assert (Hstart_contains :
        control_contains owner (R.RunRhs fr body k)).
      { cbn. left. symmetry. exact Hframe. }
      destruct (@active_prefix_last_step owner tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr body k |}
        exit Hprefix Hstart_contains Hexit_inactive)
        as [before [Hbefore [Hcontains Hlast]]].
      assert (Hbefore_reachable :
        Sem.steps tf (R.initial_config roots) before).
      { eapply steps_transitive; [exact Hreachable |].
        now apply active_prefix_steps in Hbefore. }
      destruct (@step_loses_owner_at_boundary tf roots before exit owner
        Hbefore_reachable Hlast Hcontains Hexit_inactive)
        as [exit_st [exit_k [Hexit_shape Hbelow]]].
      destruct exit as [actual_st actual_control].
      cbn in Hexit. subst actual_control.
      inversion Hexit_shape; subst exit_st exit_k.
      exists actual_st. split; [reflexivity |exact Hbelow].
    Qed.

    Lemma source_credit_write :
      forall support root st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        Credits.source_side_credit support next root <=
        Credits.source_side_credit support st root.
    Proof.
      intros support root st fr target input next changed Hwrite.
      destruct (V.eq_dec root (R.frame_owner fr)) as [-> |Hneq].
      - exact (@Credits.source_side_credit_write_nonincreasing
          support st fr target input next changed Hwrite).
      - rewrite (@Credits.source_side_credit_write_other_source
          support st fr target input next changed root Hwrite Hneq). lia.
    Qed.

    Lemma source_credit_ext :
      forall support left right source,
        R.side_cells left = R.side_cells right ->
        R.contributions left = R.contributions right ->
        Credits.source_side_credit support left source =
        Credits.source_side_credit support right source.
    Proof.
      intros support. induction support as [|target rest IH];
        intros left right source Hcells Hcontributions;
        cbn; [reflexivity |].
      unfold Credits.side_cell_credit,
        R.stored_side_cell, R.stored_contribution.
      rewrite Hcells, Hcontributions.
      now rewrite (@IH left right source Hcells Hcontributions).
    Qed.

    Lemma source_credit_observe :
      forall support st target source,
        Credits.source_side_credit support (R.observe st target) source =
        Credits.source_side_credit support st source.
    Proof.
      intros. apply source_credit_ext;
        unfold R.observe;
        destruct (R.Ranking.observe (R.ranking st) target); reflexivity.
    Qed.

    Lemma source_credit_materialize :
      forall support st target source,
        Credits.source_side_credit support (R.materialize st target) source =
        Credits.source_side_credit support st source.
    Proof.
      intros. apply source_credit_ext;
        unfold R.materialize;
        destruct (M.lookup (R.sigma st) target); reflexivity.
    Qed.

    Lemma source_credit_enqueue :
      forall support st target source,
        Credits.source_side_credit support (R.enqueue st target) source =
        Credits.source_side_credit support st source.
    Proof. intros. apply source_credit_ext; reflexivity. Qed.

    Lemma source_credit_with_queue :
      forall support st queue source,
        Credits.source_side_credit support (R.with_queue st queue) source =
        Credits.source_side_credit support st source.
    Proof. intros. apply source_credit_ext; reflexivity. Qed.

    Lemma source_credit_publish_targets :
      forall support st fr source,
        Credits.source_side_credit support (R.publish_targets st fr) source =
        Credits.source_side_credit support st source.
    Proof. intros. apply source_credit_ext; reflexivity. Qed.

    Lemma source_credit_complete_get :
      forall support st fr target next next_fr value source,
        R.complete_get st fr target = (next, next_fr, value) ->
        Credits.source_side_credit support next source =
        Credits.source_side_credit support st source.
    Proof.
      intros support st fr target next next_fr value source Hget.
      unfold R.complete_get in Hget.
      set (st1 := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (minimum := if R.rank_lt st target (R.frame_min_scope fr)
        then target else R.frame_min_scope fr) in *.
      set (maximum := match R.frame_max_read fr with
        | None => Some target
        | Some previous =>
            if R.rank_lt st previous target then Some target
            else Some previous
        end) in *.
      set (st2 := R.with_readers st1
        (M.update (R.readers st1) target
          (S.add (R.frame_owner fr) (R.lookup_set (R.readers st1) target))))
        in *.
      inversion Hget; subst next next_fr value; clear Hget.
      rewrite source_credit_materialize. subst st2 st1.
      apply source_credit_ext; unfold R.promote_controlled;
        destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
    Qed.

    Lemma source_credit_set_value :
      forall support st fr direct next next_fr source,
        R.set_value st fr direct = (next, next_fr) ->
        Credits.source_side_credit support next source =
        Credits.source_side_credit support st source.
    Proof.
      intros support st fr direct next next_fr source Hset.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; subst; apply source_credit_ext; reflexivity.
    Qed.

    Lemma source_credit_step_nonincreasing :
      forall support tf roots root before after,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_contains root (R.cfg_control before) ->
        control_contains root (R.cfg_control after) ->
        Credits.source_side_credit support (R.cfg_state after) root <=
        Credits.source_side_credit support (R.cfg_state before) root.
    Proof.
      intros support tf roots root [st control] after
        Hreachable Hstep Hbefore Hafter.
      unfold Sem.step in Hstep.
      destruct control as
        [|seed_roots |remaining |owner k |fr body k
         |fr direct pending k |fr direct k |fr k |k];
        try contradiction.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        cbn -[Credits.source_side_credit R.materialize].
        rewrite source_credit_materialize. lia.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. cbn. lia.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. cbn.
            subst observed. rewrite source_credit_observe. lia.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base fr target)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. cbn -[Credits.source_side_credit].
            rewrite (@source_credit_complete_get
              support base fr target st1 fr1 value root Hget).
            subst base. destruct (R.is_materialized observed target).
            -- subst observed. rewrite source_credit_observe. lia.
            -- rewrite source_credit_enqueue. subst observed.
               rewrite source_credit_observe. lia.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.record_side_input fr target raw)
            as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 target input)
            as [st1 changed] eqn:Hwrite.
          unfold R.continue_side in Hstep. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool;
              inversion Hstep; subst; cbn;
              try rewrite source_credit_enqueue;
              pose proof (@source_credit_write support root observed fr1
                target input st1 true Hwrite) as Hcredit;
              subst observed; rewrite source_credit_observe in Hcredit;
              exact Hcredit.
          * inversion Hstep; subst; cbn.
            pose proof (@source_credit_write support root observed fr1
              target input st1 false Hwrite) as Hcredit.
            subst observed. now rewrite source_credit_observe in Hcredit.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. cbn. subst observed.
            rewrite source_credit_observe. lia.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. cbn. subst observed.
               rewrite source_credit_observe. lia.
            -- inversion Hstep; subst.
               cbn -[Credits.source_side_credit R.materialize R.enqueue].
               rewrite source_credit_materialize, source_credit_enqueue.
               subst observed. rewrite source_credit_observe. lia.
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          cbn -[Credits.source_side_credit R.publish_targets].
          rewrite source_credit_publish_targets. lia.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. cbn. lia.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed] eqn:Hwrite.
            unfold R.continue_dead in Hstep. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool;
                inversion Hstep; subst; cbn;
                try rewrite source_credit_enqueue;
                exact (@source_credit_write support root st fr target
                  D.bottom st1 true Hwrite).
            -- inversion Hstep; subst; cbn.
               exact (@source_credit_write support root st fr target
                 D.bottom st1 false Hwrite).
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. cbn -[Credits.source_side_credit].
        rewrite (@source_credit_set_value
          support st fr direct st1 fr1 root Hset). lia.
      - cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst.
            cbn -[Credits.source_side_credit].
            rewrite source_credit_with_queue. lia.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst.
               cbn -[Credits.source_side_credit].
               rewrite source_credit_with_queue. lia.
            -- inversion Hstep; subst.
               cbn -[Credits.source_side_credit R.reset_registered_cells].
               pose proof (@reachable_control_ordered tf roots
                 {| R.cfg_state := st;
                    R.cfg_control := R.RunDrain fr k |} Hreachable)
                 as Hordered.
               cbn in Hbefore, Hafter, Hordered.
               assert (Habove :
                 R.rank_lt st root (R.frame_owner fr) = true).
               { eapply continuation_contains_below; eauto. }
               rewrite (@reset_above_preserves_source_credit support st
                 (R.frame_owner fr) root
                 (proj1 (@ScopeBounds.reachable_scopes_bounded tf roots
                   {| R.cfg_state := st;
                      R.cfg_control := R.RunDrain fr k |} Hreachable))
                 Habove). lia.
        + inversion Hstep; subst.
          cbn -[Credits.source_side_credit R.reset_registered_cells].
          pose proof (@reachable_control_ordered tf roots
            {| R.cfg_state := st;
               R.cfg_control := R.RunDrain fr k |} Hreachable) as Hordered.
          cbn in Hbefore, Hafter, Hordered.
          assert (Habove :
            R.rank_lt st root (R.frame_owner fr) = true).
          { eapply continuation_contains_below; eauto. }
          rewrite (@reset_above_preserves_source_credit support st
            (R.frame_owner fr) root
            (proj1 (@ScopeBounds.reachable_scopes_bounded tf roots
              {| R.cfg_state := st;
                 R.cfg_control := R.RunDrain fr k |} Hreachable)) Habove).
          lia.
      - destruct k as
          [|seed_remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep;
          try (inversion Hstep; subst; cbn; lia).
        destruct (R.complete_get st fr target)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst. cbn -[Credits.source_side_credit].
        rewrite (@source_credit_complete_get
          support st fr target st1 fr1 value root Hget). lia.
    Qed.

    Definition promotion_reserve (st : R.state) (owner : V.t) : nat :=
      if S.mem owner (R.controlled st) then 0 else 1.

    Lemma complete_get_preserves_controlled :
      forall st fr target next next_fr value owner,
        R.complete_get st fr target = (next, next_fr, value) ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled next) = true.
    Proof.
      intros st fr target next next_fr value owner Hget Hmember.
      unfold R.complete_get in Hget.
      destruct (R.rank_lt st (R.frame_owner fr) target);
        inversion Hget; subst; cbn.
      all: unfold R.materialize; destruct (M.lookup _ target); cbn.
      all: try exact Hmember.
      all: apply SL.add_spec; now right.
    Qed.

    Lemma set_value_preserves_controlled :
      forall st fr direct next next_fr owner,
        R.set_value st fr direct = (next, next_fr) ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled next) = true.
    Proof.
      intros st fr direct next next_fr owner Hset Hmember.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; subst; exact Hmember.
    Qed.

    Lemma controlled_step_monotone :
      forall tf before after owner,
        Sem.step tf before after ->
        S.mem owner (R.controlled (R.cfg_state before)) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true.
    Proof.
      intros tf [st control] after owner Hstep Hmember.
      unfold Sem.step in Hstep.
      destruct control as
        [|roots |remaining |current k |fr body k
         |fr direct pending k |fr direct k |fr k |k].
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[head tail] |]; try discriminate.
        inversion Hstep; subst. exact Hmember.
      - destruct roots as [|root rest]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. exact Hmember.
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst;
            apply (@ReaderOrder.controlled_mono_observe st root owner Hmember).
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[head tail] |]; inversion Hstep; subst; exact Hmember.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        apply (@ReaderOrder.controlled_mono_materialize st current owner Hmember).
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. exact Hmember.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hobserved : S.mem owner (R.controlled observed) = true).
          { subst observed. exact
              (@ReaderOrder.controlled_mono_observe st target owner Hmember). }
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. exact Hobserved.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            assert (Hbase : S.mem owner (R.controlled base) = true).
            { subst base. destruct (R.is_materialized observed target);
                [exact Hobserved |exact
                  (@ReaderOrder.controlled_mono_enqueue
                    observed target owner Hobserved)]. }
            destruct (R.complete_get base fr target)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst.
            eapply complete_get_preserves_controlled; eauto.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hobserved : S.mem owner (R.controlled observed) = true).
          { subst observed. exact
              (@ReaderOrder.controlled_mono_observe st target owner Hmember). }
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution observed fr1 target input)
            as [st1 changed] eqn:Hwrite.
          assert (Hwritten : S.mem owner (R.controlled st1) = true).
          { exact (@ReaderOrder.controlled_mono_write_side
              observed fr1 target input st1 changed Hwrite owner Hobserved). }
          unfold R.continue_side in Hstep. destruct changed;
            try destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool;
            inversion Hstep; subst;
            try exact Hwritten;
            exact (@ReaderOrder.controlled_mono_enqueue
              st1 target owner Hwritten).
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hobserved : S.mem owner (R.controlled observed) = true).
          { subst observed. exact
              (@ReaderOrder.controlled_mono_observe st target owner Hmember). }
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. exact Hobserved.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. exact Hobserved.
            -- inversion Hstep; subst.
               exact (@ReaderOrder.controlled_mono_materialize
                 (R.enqueue observed target) target owner
                 (@ReaderOrder.controlled_mono_enqueue
                   observed target owner Hobserved)).
      - destruct pending as [|target remaining].
        + cbn in Hstep. inversion Hstep; subst. exact Hmember.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. exact Hmember.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed] eqn:Hwrite.
            assert (Hwritten : S.mem owner (R.controlled st1) = true).
            { exact (@ReaderOrder.controlled_mono_write_side
                st fr target D.bottom st1 changed Hwrite owner Hmember). }
            unfold R.continue_dead in Hstep. destruct changed;
              try destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool;
              inversion Hstep; subst;
              try exact Hwritten;
              exact (@ReaderOrder.controlled_mono_enqueue
                st1 target owner Hwritten).
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. eapply set_value_preserves_controlled; eauto.
      - cbn -[R.reset_registered_cells] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst. exact Hmember.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst. exact Hmember.
            -- inversion Hstep; subst.
               exact (@ReaderOrder.controlled_mono_reset_registered
                 st (R.frame_owner fr) owner Hmember).
        + inversion Hstep; subst.
          exact (@ReaderOrder.controlled_mono_reset_registered
            st (R.frame_owner fr) owner Hmember).
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep;
          try (inversion Hstep; subst; exact Hmember).
        destruct (R.complete_get st fr target)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst. eapply complete_get_preserves_controlled; eauto.
    Qed.

    Lemma controlled_steps_monotone :
      forall tf before after owner,
        Sem.steps tf before after ->
        S.mem owner (R.controlled (R.cfg_state before)) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true.
    Proof.
      intros tf before after owner Hsteps Hmember. induction Hsteps.
      - exact Hmember.
      - apply IHHsteps. eapply controlled_step_monotone; eauto.
    Qed.

    Lemma promotion_reserve_step_nonincreasing :
      forall tf before after owner,
        Sem.step tf before after ->
        promotion_reserve (R.cfg_state after) owner <=
        promotion_reserve (R.cfg_state before) owner.
    Proof.
      intros tf before after owner Hstep. unfold promotion_reserve.
      destruct (S.mem owner (R.controlled (R.cfg_state before))) eqn:Hbefore.
      - rewrite (@controlled_step_monotone tf before after owner Hstep Hbefore).
        lia.
      - destruct (S.mem owner (R.controlled (R.cfg_state after))); lia.
    Qed.

    Lemma promotion_reserve_steps_nonincreasing :
      forall tf before after owner,
        Sem.steps tf before after ->
        promotion_reserve (R.cfg_state after) owner <=
        promotion_reserve (R.cfg_state before) owner.
    Proof.
      intros tf before after owner Hsteps. induction Hsteps; [lia |].
      pose proof (@promotion_reserve_step_nonincreasing
        tf first next owner H) as Hfirst. lia.
    Qed.

    Fixpoint target_side_credit
      (support : list V.t) (st : R.state) (target : V.t) : nat :=
      match support with
      | [] => 0
      | source :: rest =>
          Credits.side_cell_credit st source target +
          target_side_credit rest st target
      end.

    Lemma target_side_credit_write_nonincreasing :
      forall support st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        target_side_credit support next target <=
        target_side_credit support st target.
    Proof.
      intros support. induction support as [|source rest IH];
        intros st fr target input next changed Hwrite; cbn; [lia |].
      destruct (V.eq_dec source (R.frame_owner fr)) as [-> |Hother].
      - pose proof (@Credits.write_side_credit_nonincreasing
          st fr target input next changed Hwrite) as Hhead.
        pose proof (@IH st fr target input next changed Hwrite) as Htail.
        lia.
      - rewrite (@Credits.side_cell_credit_write_other st fr target input
          next changed source target Hwrite)
          by (intro Heq; inversion Heq; contradiction).
        pose proof (@IH st fr target input next changed Hwrite). lia.
    Qed.

    Lemma target_side_credit_write_decreases :
      forall support st fr target input next,
        List.In (R.frame_owner fr) support ->
        R.write_side_contribution st fr target input = (next, true) ->
        target_side_credit support next target <
        target_side_credit support st target.
    Proof.
      intros support. induction support as [|source rest IH];
        intros st fr target input next Hsource Hwrite; [contradiction |].
      cbn in Hsource |- *.
      destruct (V.eq_dec source (R.frame_owner fr)) as [-> |Hother].
      - pose proof (@Credits.write_side_changed_credit_decreases
          st fr target input next Hwrite) as Hhead.
        pose proof (@target_side_credit_write_nonincreasing
          rest st fr target input next true Hwrite) as Htail. lia.
      - rewrite (@Credits.side_cell_credit_write_other st fr target input
          next true source target Hwrite)
          by (intro Heq; inversion Heq; contradiction).
        assert (Hin : List.In (R.frame_owner fr) rest) by tauto.
        pose proof (@IH st fr target input next Hin Hwrite). lia.
    Qed.

    Lemma target_side_credit_write_other_target :
      forall support st fr written input next changed target,
        R.write_side_contribution st fr written input = (next, changed) ->
        target <> written ->
        target_side_credit support next target =
        target_side_credit support st target.
    Proof.
      intros support. induction support as [|source rest IH];
        intros st fr written input next changed target Hwrite Hneq;
        cbn; [reflexivity |].
      rewrite (@Credits.side_cell_credit_write_other st fr written input
        next changed source target Hwrite)
        by (intro Heq; inversion Heq; contradiction).
      now rewrite (@IH st fr written input next changed target Hwrite Hneq).
    Qed.

    Lemma target_side_credit_ext :
      forall support left right target,
        R.side_cells left = R.side_cells right ->
        R.contributions left = R.contributions right ->
        target_side_credit support left target =
        target_side_credit support right target.
    Proof.
      intros support. induction support as [|source rest IH];
        intros left right target Hcells Hcontributions;
        cbn; [reflexivity |].
      unfold Credits.side_cell_credit,
        R.stored_side_cell, R.stored_contribution.
      rewrite Hcells, Hcontributions.
      now rewrite (@IH left right target Hcells Hcontributions).
    Qed.

    Lemma reset_above_preserves_target_credit :
      forall support st scope target,
        state_resets_ranked st ->
        R.rank_lt st target scope = true ->
        target_side_credit support
          (R.reset_registered_cells st scope) target =
        target_side_credit support st target.
    Proof.
      intros support st scope target Hranked Habove.
      induction support as [|source rest IH]; cbn; [reflexivity |].
      assert (Hcell :
        Credits.side_cell_credit
          (R.reset_registered_cells st scope) source target =
        Credits.side_cell_credit st source target).
      { destruct (Nat.eq_dec
          (Credits.side_cell_credit
            (R.reset_registered_cells st scope) source target)
          (Credits.side_cell_credit st source target)); [assumption |].
        exfalso.
        pose proof (@Credits.reset_credit_change_target_higher
          st scope source target Hranked n) as Hhigher.
        pose proof (@rank_lt_true_ranked st target scope Habove)
          as [Htarget Hscope].
        rewrite (@rank_lt_asymmetric st target scope
          Htarget Hscope Habove) in Hhigher. discriminate. }
      now rewrite Hcell, IH.
    Qed.

    Lemma reset_drain_preserves_target_credit :
      forall support tf roots st fr k root,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunDrain fr k |} ->
        continuation_contains root k ->
        target_side_credit support
          (R.reset_registered_cells st (R.frame_owner fr)) root =
        target_side_credit support st root.
    Proof.
      intros support tf roots st fr k root Hreachable Hcontains.
      pose proof (@reachable_control_ordered tf roots
        {| R.cfg_state := st;
           R.cfg_control := R.RunDrain fr k |} Hreachable) as Hordered.
      cbn in Hordered.
      assert (Habove : R.rank_lt st root (R.frame_owner fr) = true).
      { eapply continuation_contains_below; eauto. }
      apply reset_above_preserves_target_credit.
      - exact (@reachable_resets_ranked tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunDrain fr k |} Hreachable).
      - exact Habove.
    Qed.

    Lemma target_credit_observe :
      forall support st observed target,
        target_side_credit support (R.observe st observed) target =
        target_side_credit support st target.
    Proof.
      intros. apply target_side_credit_ext; unfold R.observe;
        destruct (R.Ranking.observe (R.ranking st) observed); reflexivity.
    Qed.

    Lemma target_credit_materialize :
      forall support st materialized target,
        target_side_credit support (R.materialize st materialized) target =
        target_side_credit support st target.
    Proof.
      intros. apply target_side_credit_ext; unfold R.materialize;
        destruct (M.lookup (R.sigma st) materialized); reflexivity.
    Qed.

    Lemma target_credit_enqueue :
      forall support st queued target,
        target_side_credit support (R.enqueue st queued) target =
        target_side_credit support st target.
    Proof. intros. apply target_side_credit_ext; reflexivity. Qed.

    Lemma target_credit_with_queue :
      forall support st queue target,
        target_side_credit support (R.with_queue st queue) target =
        target_side_credit support st target.
    Proof. intros. apply target_side_credit_ext; reflexivity. Qed.

    Lemma target_credit_publish_targets :
      forall support st fr target,
        target_side_credit support (R.publish_targets st fr) target =
        target_side_credit support st target.
    Proof. intros. apply target_side_credit_ext; reflexivity. Qed.

    Lemma target_credit_complete_get :
      forall support st fr read next next_fr value target,
        R.complete_get st fr read = (next, next_fr, value) ->
        target_side_credit support next target =
        target_side_credit support st target.
    Proof.
      intros support st fr read next next_fr value target Hget.
      unfold R.complete_get in Hget.
      set (st1 := if R.rank_lt st (R.frame_owner fr) read
        then st else R.promote_controlled st read) in *.
      set (minimum := if R.rank_lt st read (R.frame_min_scope fr)
        then read else R.frame_min_scope fr) in *.
      set (maximum := match R.frame_max_read fr with
        | None => Some read
        | Some previous =>
            if R.rank_lt st previous read then Some read else Some previous
        end) in *.
      set (st2 := R.with_readers st1
        (M.update (R.readers st1) read
          (S.add (R.frame_owner fr) (R.lookup_set (R.readers st1) read)))) in *.
      inversion Hget; subst next next_fr value; clear Hget.
      rewrite target_credit_materialize. subst st2 st1.
      apply target_side_credit_ext; unfold R.promote_controlled;
        destruct (R.rank_lt st (R.frame_owner fr) read); reflexivity.
    Qed.

    Lemma target_credit_set_value :
      forall support st fr direct next next_fr target,
        R.set_value st fr direct = (next, next_fr) ->
        target_side_credit support next target =
        target_side_credit support st target.
    Proof.
      intros support st fr direct next next_fr target Hset.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; subst; apply target_side_credit_ext; reflexivity.
    Qed.

    Lemma target_credit_step_nonincreasing :
      forall support tf roots root before after,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_contains root (R.cfg_control before) ->
        control_contains root (R.cfg_control after) ->
        target_side_credit support (R.cfg_state after) root <=
        target_side_credit support (R.cfg_state before) root.
    Proof.
      intros support tf roots root [st control] after
        Hreachable Hstep Hbefore Hafter.
      unfold Sem.step in Hstep.
      destruct control as
        [|seed_roots |remaining |owner k |fr body k
         |fr direct pending k |fr direct k |fr k |k];
        try contradiction.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst.
        cbn -[target_side_credit R.materialize].
        rewrite target_credit_materialize. lia.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. cbn. lia.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. cbn. subst observed.
            rewrite target_credit_observe. lia.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base fr target)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. cbn -[target_side_credit].
            rewrite (@target_credit_complete_get
              support base fr target st1 fr1 value root Hget).
            subst base. destruct (R.is_materialized observed target).
            -- subst observed. rewrite target_credit_observe. lia.
            -- rewrite target_credit_enqueue. subst observed.
               rewrite target_credit_observe. lia.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution observed fr1 target input)
            as [st1 changed] eqn:Hwrite.
          unfold R.continue_side in Hstep. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool;
              inversion Hstep; subst; cbn;
              try rewrite target_credit_enqueue.
            all: destruct (V.eq_dec root target) as [-> |Hneq].
            all: try (pose proof (@target_side_credit_write_nonincreasing
              support observed fr1 target input st1 true Hwrite) as Hcredit;
              subst observed; rewrite target_credit_observe in Hcredit;
              exact Hcredit).
            all: rewrite (@target_side_credit_write_other_target support
              observed fr1 target input st1 true root Hwrite Hneq).
            all: subst observed; rewrite target_credit_observe; lia.
          * inversion Hstep; subst. cbn.
            destruct (V.eq_dec root target) as [-> |Hneq].
            -- pose proof (@target_side_credit_write_nonincreasing support
                 observed fr1 target input st1 false Hwrite) as Hcredit.
               subst observed. now rewrite target_credit_observe in Hcredit.
            -- rewrite (@target_side_credit_write_other_target support
                 observed fr1 target input st1 false root Hwrite Hneq).
               subst observed. rewrite target_credit_observe. lia.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. cbn. subst observed.
            rewrite target_credit_observe. lia.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. cbn. subst observed.
               rewrite target_credit_observe. lia.
            -- inversion Hstep; subst. cbn -[target_side_credit].
               rewrite target_credit_materialize, target_credit_enqueue.
               subst observed. rewrite target_credit_observe. lia.
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
          cbn -[target_side_credit R.publish_targets].
          rewrite target_credit_publish_targets. lia.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. cbn. lia.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed] eqn:Hwrite.
            unfold R.continue_dead in Hstep. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool;
                inversion Hstep; subst; cbn;
                try rewrite target_credit_enqueue.
               all: destruct (V.eq_dec root target) as [-> |Hneq].
               all: try (eapply target_side_credit_write_nonincreasing;
                 exact Hwrite).
               all: rewrite (@target_side_credit_write_other_target support
                 st fr target D.bottom st1 true root Hwrite Hneq); lia.
            -- inversion Hstep; subst. cbn.
               destruct (V.eq_dec root target) as [-> |Hneq].
               ++ eapply target_side_credit_write_nonincreasing; exact Hwrite.
               ++ rewrite (@target_side_credit_write_other_target support
                    st fr target D.bottom st1 false root Hwrite Hneq). lia.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. cbn -[target_side_credit].
        rewrite (@target_credit_set_value
          support st fr direct st1 fr1 root Hset). lia.
      - cbn -[R.reset_registered_cells] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst.
            cbn -[target_side_credit]. rewrite target_credit_with_queue. lia.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst.
               cbn -[target_side_credit].
               rewrite target_credit_with_queue. lia.
            -- inversion Hstep; subst. cbn in Hafter.
               cbn -[target_side_credit R.reset_registered_cells].
               rewrite (@reset_drain_preserves_target_credit support tf roots
                 st fr k root Hreachable Hafter). lia.
        + inversion Hstep; subst. cbn in Hafter.
          cbn -[target_side_credit R.reset_registered_cells].
          rewrite (@reset_drain_preserves_target_credit support tf roots
            st fr k root Hreachable Hafter). lia.
      - destruct k as
          [|seed_remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep;
          try (inversion Hstep; subst; cbn; lia).
        destruct (R.complete_get st fr target)
          as [[st1 fr1] value] eqn:Hget.
        inversion Hstep; subst. cbn -[target_side_credit].
        rewrite (@target_credit_complete_get
          support st fr target st1 fr1 value root Hget). lia.
    Qed.

    Lemma active_prefix_source_credit_nonincreasing :
      forall support tf roots owner first final,
        Sem.steps tf (R.initial_config roots) first ->
        active_prefix owner tf first final ->
        control_contains owner (R.cfg_control final) ->
        Credits.source_side_credit support (R.cfg_state final) owner <=
        Credits.source_side_credit support (R.cfg_state first) owner.
    Proof.
      intros support tf roots owner first final Hreachable Hprefix.
      induction Hprefix; intros Hfinal; [lia |].
      assert (Hnext : control_contains owner (R.cfg_control next)).
      { destruct Hprefix; [exact Hfinal |exact H1]. }
      pose proof (@source_credit_step_nonincreasing support tf roots owner
        first next Hreachable H0 H Hnext) as Hfirst.
      assert (Hnext_reachable : Sem.steps tf (R.initial_config roots) next).
      { eapply steps_append_one; eauto. }
      specialize (IHHprefix Hnext_reachable Hfinal). lia.
    Qed.

    Lemma active_prefix_target_credit_nonincreasing :
      forall support tf roots owner first final,
        Sem.steps tf (R.initial_config roots) first ->
        active_prefix owner tf first final ->
        control_contains owner (R.cfg_control final) ->
        target_side_credit support (R.cfg_state final) owner <=
        target_side_credit support (R.cfg_state first) owner.
    Proof.
      intros support tf roots owner first final Hreachable Hprefix.
      induction Hprefix; intros Hfinal; [lia |].
      assert (Hnext : control_contains owner (R.cfg_control next)).
      { destruct Hprefix; [exact Hfinal |exact H1]. }
      pose proof (@target_credit_step_nonincreasing support tf roots owner
        first next Hreachable H0 H Hnext) as Hfirst.
      assert (Hnext_reachable : Sem.steps tf (R.initial_config roots) next).
      { eapply steps_append_one; eauto. }
      specialize (IHHprefix Hnext_reachable Hfinal). lia.
    Qed.

    Fixpoint continuation_frame
      (owner : V.t) (k : R.continuation) : option R.frame :=
      match k with
      | R.KLoop | R.KSeedLoop _ => None
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          if V.eq_dec (R.frame_owner fr) owner
          then Some fr else continuation_frame owner rest
      end.

    Definition control_frame
      (owner : V.t) (control : R.control) : option R.frame :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => None
      | R.StartEpisode current k =>
          if V.eq_dec current owner then None else continuation_frame owner k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          if V.eq_dec (R.frame_owner fr) owner
          then Some fr else continuation_frame owner k
      | R.Return k => continuation_frame owner k
      end.

    Definition active_ordinary_credit
      (st : R.state) (control : R.control) (owner : V.t) : nat :=
      if S.mem owner (R.controlled st) then
        match control_frame owner control with
        | Some fr => Credits.ordinary_credit st fr
        | None => 0
        end
      else 0.

    Lemma promotion_reserve_equal_membership :
      forall before after owner,
        promotion_reserve after owner = promotion_reserve before owner ->
        S.mem owner (R.controlled after) =
        S.mem owner (R.controlled before).
    Proof.
      intros before after owner Hequal. unfold promotion_reserve in Hequal.
      destruct (S.mem owner (R.controlled after));
        destruct (S.mem owner (R.controlled before)); congruence.
    Qed.

    Lemma active_ordinary_credit_run_rhs :
      forall st owner fr body k,
        R.frame_owner fr = owner ->
        active_ordinary_credit st (R.RunRhs fr body k) owner =
        if S.mem owner (R.controlled st)
        then Credits.ordinary_credit st fr else 0.
    Proof.
      intros st owner fr body k Howner.
      unfold active_ordinary_credit, control_frame.
      destruct (S.mem owner (R.controlled st));
        [destruct (V.eq_dec (R.frame_owner fr) owner) |]; congruence.
    Qed.

    Lemma set_value_controlled :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        R.controlled next = R.controlled st.
    Proof.
      intros st fr direct next next_fr Hset. unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; reflexivity.
    Qed.

    Lemma active_ordinary_credit_set_value_nonincreasing :
      forall st fr direct next next_fr body k,
        S.mem (R.frame_owner fr) (R.controlled st) = true ->
        R.set_value st fr direct = (next, next_fr) ->
        active_ordinary_credit next
          (R.RunRhs next_fr body k) (R.frame_owner fr) <=
        active_ordinary_credit st
          (R.RunRhs fr body k) (R.frame_owner fr).
    Proof.
      intros st fr direct next next_fr body k Hcontrolled Hset.
      pose proof (@set_value_owner st fr direct next next_fr Hset) as Howner.
      rewrite (@active_ordinary_credit_run_rhs next
        (R.frame_owner fr) next_fr body k Howner),
        (@active_ordinary_credit_run_rhs st
          (R.frame_owner fr) fr body k eq_refl), Hcontrolled.
      assert (Hcontrolled' :
        S.mem (R.frame_owner fr) (R.controlled next) = true).
      { rewrite (@set_value_controlled st fr direct next next_fr Hset).
        exact Hcontrolled. }
      rewrite Hcontrolled'.
      eapply Credits.set_value_credit_nonincreasing; eauto.
    Qed.

    Lemma active_ordinary_credit_set_value_decreases :
      forall st fr direct next next_fr body k,
        S.mem (R.frame_owner fr) (R.controlled st) = true ->
        R.set_value st fr direct = (next, next_fr) ->
        R.equivalent
          (R.sigma_value next (R.frame_owner fr))
          (R.sigma_value st (R.frame_owner fr)) = false ->
        active_ordinary_credit next
          (R.RunRhs next_fr body k) (R.frame_owner fr) <
        active_ordinary_credit st
          (R.RunRhs fr body k) (R.frame_owner fr).
    Proof.
      intros st fr direct next next_fr body k Hcontrolled Hset Hchanged.
      pose proof (@set_value_owner st fr direct next next_fr Hset) as Howner.
      rewrite (@active_ordinary_credit_run_rhs next
        (R.frame_owner fr) next_fr body k Howner),
        (@active_ordinary_credit_run_rhs st
          (R.frame_owner fr) fr body k eq_refl), Hcontrolled.
      assert (Hcontrolled' :
        S.mem (R.frame_owner fr) (R.controlled next) = true).
      { rewrite (@set_value_controlled st fr direct next next_fr Hset).
        exact Hcontrolled. }
      rewrite Hcontrolled'.
      eapply Credits.set_value_changed_credit_decreases; eauto.
    Qed.

    Definition owner_round_measure
      (support : list V.t) (first_round : nat)
      (owner : V.t) (c : R.config) :
      nat * (nat * (nat * (nat * (nat * nat)))) :=
      (first_round,
       (unmaterialized_count support (R.cfg_state c),
        (promotion_reserve (R.cfg_state c) owner,
         (Credits.source_side_credit support (R.cfg_state c) owner,
          (target_side_credit support (R.cfg_state c) owner,
           active_ordinary_credit
             (R.cfg_state c) (R.cfg_control c) owner))))).

    Definition owner_round_measure_lt
      (support : list V.t) (owner : V.t)
      (left right : nat * R.config) : Prop :=
      Relation_Operators.slexprod
        nat (nat * (nat * (nat * (nat * nat)))) lt
        (Relation_Operators.slexprod
          nat (nat * (nat * (nat * nat))) lt
          (Relation_Operators.slexprod
            nat (nat * (nat * nat)) lt
            (Relation_Operators.slexprod
              nat (nat * nat) lt
              (Relation_Operators.slexprod nat nat lt lt))))
        (owner_round_measure support (fst left) owner (snd left))
        (owner_round_measure support (fst right) owner (snd right)).

    Lemma owner_round_measure_lt_well_founded :
      forall support owner, well_founded (owner_round_measure_lt support owner).
    Proof.
      intros support owner. unfold owner_round_measure_lt.
      apply wf_inverse_image. repeat apply wf_slexprod;
        apply Nat.lt_wf_0.
    Qed.

    Lemma first_round_decreases :
      forall support owner before after,
        owner_round_measure_lt support owner (0, after) (1, before).
    Proof.
      intros. unfold owner_round_measure_lt, owner_round_measure. cbn.
      apply Relation_Operators.left_slex. lia.
    Qed.

    Lemma positive_round_decreases :
      forall support owner first before after,
        0 < first ->
        owner_round_measure_lt support owner (0, after) (first, before).
    Proof.
      intros support owner first before after Hpositive.
      unfold owner_round_measure_lt, owner_round_measure. cbn.
      apply Relation_Operators.left_slex. exact Hpositive.
    Qed.

    Definition round_payment
      (support : list V.t) (owner : V.t)
      (before after : R.config) : Prop :=
      unmaterialized_count support (R.cfg_state after) <
        unmaterialized_count support (R.cfg_state before) \/
      unmaterialized_count support (R.cfg_state after) =
        unmaterialized_count support (R.cfg_state before) /\
      (promotion_reserve (R.cfg_state after) owner <
         promotion_reserve (R.cfg_state before) owner \/
       promotion_reserve (R.cfg_state after) owner =
         promotion_reserve (R.cfg_state before) owner /\
       (Credits.source_side_credit support (R.cfg_state after) owner <
          Credits.source_side_credit support (R.cfg_state before) owner \/
        Credits.source_side_credit support (R.cfg_state after) owner =
          Credits.source_side_credit support (R.cfg_state before) owner /\
        (target_side_credit support (R.cfg_state after) owner <
           target_side_credit support (R.cfg_state before) owner \/
         target_side_credit support (R.cfg_state after) owner =
           target_side_credit support (R.cfg_state before) owner /\
         active_ordinary_credit
             (R.cfg_state after) (R.cfg_control after) owner <
           active_ordinary_credit
             (R.cfg_state before) (R.cfg_control before) owner))).

    Lemma round_payment_decreases :
      forall support owner before after,
        round_payment support owner before after ->
        owner_round_measure_lt support owner (0, after) (0, before).
    Proof.
      intros support owner before after Hpayment.
      unfold owner_round_measure_lt, owner_round_measure. cbn.
      apply Relation_Operators.right_slex.
      destruct Hpayment as
        [Hmaterialized |
         [Hmaterialized
          [Hpromoted |
           [Hpromoted
            [Hsource |
             [Hsource [Htarget |[Htarget Hordinary]]]]]]]].
      - apply Relation_Operators.left_slex. exact Hmaterialized.
      - rewrite Hmaterialized. apply Relation_Operators.right_slex.
        apply Relation_Operators.left_slex. exact Hpromoted.
      - rewrite Hmaterialized, Hpromoted.
        apply Relation_Operators.right_slex.
        apply Relation_Operators.right_slex.
        apply Relation_Operators.left_slex. exact Hsource.
      - rewrite Hmaterialized, Hpromoted, Hsource.
        apply Relation_Operators.right_slex.
        apply Relation_Operators.right_slex.
        apply Relation_Operators.right_slex.
        apply Relation_Operators.left_slex. exact Htarget.
      - rewrite Hmaterialized, Hpromoted, Hsource, Htarget.
        repeat apply Relation_Operators.right_slex. exact Hordinary.
    Qed.

    Definition materialized_mono (before after : R.state) : Prop :=
      forall x,
        R.is_materialized before x = true ->
        R.is_materialized after x = true.

    Lemma sigma_extends_materialized_mono :
      forall before after,
        sigma_extends before after -> materialized_mono before after.
    Proof.
      intros before after Hextends x Hmaterialized.
      unfold R.is_materialized in *.
      destruct (M.lookup (R.sigma before) x) as [value |] eqn:Hlookup;
        [|discriminate].
      destruct (Hextends x value Hlookup) as [next Hnext].
      now rewrite Hnext.
    Qed.

    Fixpoint continuation_owners_materialized
      (st : R.state) (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => True
      | R.KAfterGet fr _ _ rest
      | R.KAfterSide fr _ rest
      | R.KAfterSpawn fr _ rest
      | R.KDead fr _ _ rest
      | R.KDrain fr rest =>
          R.is_materialized st (R.frame_owner fr) = true /\
          continuation_owners_materialized st rest
      end.

    Definition control_owners_materialized
      (st : R.state) (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
      | R.StartEpisode _ k | R.Return k =>
          continuation_owners_materialized st k
      | R.RunRhs fr _ k
      | R.RunDead fr _ _ k
      | R.RunCommit fr _ k
      | R.RunDrain fr k =>
          R.is_materialized st (R.frame_owner fr) = true /\
          continuation_owners_materialized st k
      end.

    Lemma continuation_owners_materialized_mono :
      forall before after k,
        materialized_mono before after ->
        continuation_owners_materialized before k ->
        continuation_owners_materialized after k.
    Proof.
      intros before after k Hmono. induction k; cbn; intuition.
    Qed.

    Lemma control_owners_materialized_mono :
      forall before after control,
        materialized_mono before after ->
        control_owners_materialized before control ->
        control_owners_materialized after control.
    Proof.
      intros before after control Hmono. destruct control; cbn; intuition;
        eauto using continuation_owners_materialized_mono.
    Qed.

    Lemma materialize_self :
      forall st owner,
        R.is_materialized (R.materialize st owner) owner = true.
    Proof.
      intros st owner. unfold R.materialize.
      destruct (M.lookup (R.sigma st) owner) eqn:Hlookup.
      - unfold R.is_materialized. rewrite Hlookup. reflexivity.
      - unfold R.is_materialized. cbn. rewrite ML.lookup_update_same.
        reflexivity.
    Qed.

    Lemma next_config_owners_materialized :
      forall tf before after,
        R.next_config tf before = Some after ->
        control_owners_materialized
          (R.cfg_state before) (R.cfg_control before) ->
        control_owners_materialized
          (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf [st control] after Hstep Howners.
      pose proof (sigma_extends_materialized_mono
        (@next_config_sigma_extends tf
          {| R.cfg_state := st; R.cfg_control := control |} after Hstep))
        as Hmono.
      destruct control as
        [|roots |remaining |owner k |fr body k
         |fr direct pending k |fr direct k |fr k |k]; cbn in Howners.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[head tail] |]; try discriminate.
        inversion Hstep; subst. exact I.
      - destruct roots as [|root rest]; cbn -[R.observe] in Hstep.
        + inversion Hstep; subst. exact I.
        + destruct (R.is_materialized (R.observe st root) root);
            inversion Hstep; subst; exact I.
      - cbn in Hstep. destruct (R.queue_pop (R.queue st))
          as [[head tail] |]; inversion Hstep; subst; exact I.
      - cbn -[R.materialize] in Hstep. inversion Hstep; subst. cbn. split.
        + apply materialize_self.
        + eapply continuation_owners_materialized_mono; eauto.
      - destruct Howners as [Hcurrent Hrest]. destruct body.
        + cbn in Hstep. inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st t) in *.
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner fr) t)%bool.
          * inversion Hstep; subst. cbn. split;
              eauto using continuation_owners_materialized_mono.
          * set (base := if R.is_materialized observed t
              then observed else R.enqueue observed t) in *.
            destruct (R.complete_get base fr t)
              as [[next next_fr] value] eqn:Hget.
            inversion Hstep; subst. cbn. split.
            -- rewrite (complete_get_owner Hget). apply Hmono. exact Hcurrent.
            -- eapply continuation_owners_materialized_mono; eauto.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st t) in *.
          destruct (R.record_side_input fr t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [next changed] eqn:Hwrite.
          pose proof (@record_side_input_owner fr t t0 fr1 input Hrecord)
            as Howner.
          unfold R.continue_side in Hstep. destruct changed;
            try destruct (R.rank_lt next (R.frame_owner fr1) t &&
              negb (R.is_materialized next t))%bool;
            inversion Hstep; subst; cbn; split;
            eauto using continuation_owners_materialized_mono.
          all: rewrite Howner; apply Hmono; exact Hcurrent.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st t) in *.
          destruct (R.is_materialized observed t);
            try destruct (R.rank_lt observed (R.frame_owner fr) t);
            inversion Hstep; subst; cbn; split;
            eauto using continuation_owners_materialized_mono.
      - destruct Howners as [Hcurrent Hrest].
        destruct pending as [|target remaining].
        + cbn in Hstep. inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. cbn. split;
              eauto using continuation_owners_materialized_mono.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [next changed] eqn:Hwrite.
            unfold R.continue_dead in Hstep. destruct changed;
              try destruct (R.rank_lt next (R.frame_owner fr) target &&
                negb (R.is_materialized next target))%bool;
              inversion Hstep; subst; cbn; split;
              eauto using continuation_owners_materialized_mono.
      - destruct Howners as [Hcurrent Hrest].
        cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
        inversion Hstep; subst. cbn. split.
        + rewrite (@set_value_owner st fr direct next next_fr Hset).
          apply Hmono. exact Hcurrent.
        + eapply continuation_owners_materialized_mono; eauto.
      - destruct Howners as [Hcurrent Hrest].
        cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate. inversion Hstep; subst. cbn. split;
              eauto using continuation_owners_materialized_mono.
          * destruct (R.rank_lt st (R.frame_owner fr) next).
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst. cbn. split;
                 eauto using continuation_owners_materialized_mono.
            -- inversion Hstep; subst. cbn.
               eapply continuation_owners_materialized_mono; eauto.
        + inversion Hstep; subst. cbn.
          eapply continuation_owners_materialized_mono; eauto.
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep, Howners.
        + inversion Hstep; subst. exact I.
        + inversion Hstep; subst. exact I.
        + destruct Howners as [Hcurrent Hrest].
          destruct (R.complete_get st fr target)
            as [[next_st next_fr] value] eqn:Hget.
          inversion Hstep; subst. cbn. split.
          * rewrite (complete_get_owner Hget). apply Hmono. exact Hcurrent.
          * eapply continuation_owners_materialized_mono; eauto.
        + destruct Howners as [Hcurrent Hrest].
          inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
        + destruct Howners as [Hcurrent Hrest].
          inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
        + destruct Howners as [Hcurrent Hrest].
          inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
        + destruct Howners as [Hcurrent Hrest].
          inversion Hstep; subst. cbn. split;
            eauto using continuation_owners_materialized_mono.
    Qed.

    Lemma steps_owners_materialized :
      forall tf before after,
        control_owners_materialized
          (R.cfg_state before) (R.cfg_control before) ->
        Sem.steps tf before after ->
        control_owners_materialized
          (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf before after Howners Hsteps. induction Hsteps;
        [exact Howners |].
      apply IHHsteps. eapply next_config_owners_materialized; eauto.
    Qed.

    Theorem reachable_owners_materialized :
      forall tf roots after,
        Sem.steps tf (R.initial_config roots) after ->
        control_owners_materialized
          (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf roots after Hsteps. eapply steps_owners_materialized; eauto.
      exact I.
    Qed.

    Lemma continuation_frame_owner :
      forall owner k fr,
        continuation_frame owner k = Some fr -> R.frame_owner fr = owner.
    Proof.
      intros owner k. induction k; intros fr Hframe;
        cbn [continuation_frame] in Hframe; try discriminate.
      all: destruct (V.eq_dec (R.frame_owner f) owner).
      all: try (inversion Hframe; subst; reflexivity).
      all: eapply IHk; eauto.
    Qed.

    Lemma control_frame_owner :
      forall owner control fr,
        control_frame owner control = Some fr -> R.frame_owner fr = owner.
    Proof.
      intros owner control fr Hframe. destruct control;
        cbn [control_frame] in Hframe; try discriminate.
      - destruct (V.eq_dec t owner); [discriminate |].
        eapply continuation_frame_owner; eauto.
      - destruct (V.eq_dec (R.frame_owner f) owner);
          [inversion Hframe; subst; reflexivity |].
        eapply continuation_frame_owner; eauto.
      - destruct (V.eq_dec (R.frame_owner f) owner);
          [inversion Hframe; subst; reflexivity |].
        eapply continuation_frame_owner; eauto.
      - destruct (V.eq_dec (R.frame_owner f) owner);
          [inversion Hframe; subst; reflexivity |].
        eapply continuation_frame_owner; eauto.
      - destruct (V.eq_dec (R.frame_owner f) owner);
          [inversion Hframe; subst; reflexivity |].
        eapply continuation_frame_owner; eauto.
      - eapply continuation_frame_owner; eauto.
    Qed.

    Lemma continuation_frame_materialized :
      forall st owner k fr,
        continuation_owners_materialized st k ->
        continuation_frame owner k = Some fr ->
        R.is_materialized st owner = true.
    Proof.
      intros st owner k. induction k; intros fr Howners Hframe;
        cbn [continuation_frame] in Hframe; try discriminate.
      all: destruct Howners as [Hcurrent Hrest].
      all: destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
      all: try (rewrite <- Heq; exact Hcurrent).
      all: eapply IHk; eauto.
    Qed.

    Lemma control_frame_materialized :
      forall st owner control fr,
        control_owners_materialized st control ->
        control_frame owner control = Some fr ->
        R.is_materialized st owner = true.
    Proof.
      intros st owner control fr Howners Hframe. destruct control;
        cbn [control_frame] in Howners, Hframe; try discriminate.
      - destruct (V.eq_dec t owner); [discriminate |].
        eapply continuation_frame_materialized; eauto.
      - destruct Howners as [Hcurrent Hrest].
        destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
        + rewrite <- Heq. exact Hcurrent.
        + eapply continuation_frame_materialized; eauto.
      - destruct Howners as [Hcurrent Hrest].
        destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
        + rewrite <- Heq. exact Hcurrent.
        + eapply continuation_frame_materialized; eauto.
      - destruct Howners as [Hcurrent Hrest].
        destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
        + rewrite <- Heq. exact Hcurrent.
        + eapply continuation_frame_materialized; eauto.
      - destruct Howners as [Hcurrent Hrest].
        destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
        + rewrite <- Heq. exact Hcurrent.
        + eapply continuation_frame_materialized; eauto.
      - eapply continuation_frame_materialized; eauto.
    Qed.

    Lemma materialize_sigma_value_materialized :
      forall st target owner,
        R.is_materialized st owner = true ->
        R.sigma_value (R.materialize st target) owner = R.sigma_value st owner.
    Proof.
      intros st target owner Howner.
      unfold R.materialize, R.is_materialized, R.sigma_value in *.
      destruct (M.lookup (R.sigma st) target) eqn:Htarget; [reflexivity |].
      destruct (M.lookup (R.sigma st) owner) eqn:Hlookup;
        [|discriminate]. cbn.
      destruct (V.eq_dec owner target) as [-> |Hneq].
      - rewrite Hlookup in Htarget. discriminate.
      - rewrite ML.lookup_update_other by exact Hneq. now rewrite Hlookup.
    Qed.

    Lemma complete_get_preserves_owner_credit_view :
      forall st fr target next next_fr value owner,
        R.complete_get st fr target = (next, next_fr, value) ->
        R.is_materialized st owner = true ->
        R.sigma_value next owner = R.sigma_value st owner /\
        R.frame_phase next_fr = R.frame_phase fr.
    Proof.
      intros st fr target next next_fr value owner Hget Hmaterialized.
      unfold R.complete_get in Hget.
      set (st1 := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (minimum := if R.rank_lt st target (R.frame_min_scope fr)
        then target else R.frame_min_scope fr) in *.
      set (maximum := match R.frame_max_read fr with
        | None => Some target
        | Some previous =>
            if R.rank_lt st previous target then Some target else Some previous
        end) in *.
      set (next0 := R.with_readers st1
        (M.update (R.readers st1) target
          (S.add (R.frame_owner fr) (R.lookup_set (R.readers st1) target)))) in *.
      inversion Hget; subst next next_fr value; clear Hget. split.
      - assert (Hnext0 : R.is_materialized next0 owner = true).
        { subst next0 st1. unfold R.promote_controlled, R.is_materialized.
          destruct (R.rank_lt st (R.frame_owner fr) target);
            cbn; exact Hmaterialized. }
        rewrite (@materialize_sigma_value_materialized
          next0 target owner Hnext0).
        subst next0 st1. unfold R.promote_controlled, R.sigma_value.
        destruct (R.rank_lt st (R.frame_owner fr) target); reflexivity.
      - reflexivity.
    Qed.

    Lemma active_ordinary_credit_same :
      forall before after before_control after_control owner before_fr after_fr,
        S.mem owner (R.controlled before) = true ->
        S.mem owner (R.controlled after) = true ->
        control_frame owner before_control = Some before_fr ->
        control_frame owner after_control = Some after_fr ->
        R.frame_phase after_fr = R.frame_phase before_fr ->
        R.sigma_value after owner = R.sigma_value before owner ->
        active_ordinary_credit after after_control owner =
        active_ordinary_credit before before_control owner.
    Proof.
      intros before after before_control after_control owner before_fr after_fr
        Hbefore Hafter Hbefore_frame Hafter_frame Hphase Hsigma.
      unfold active_ordinary_credit.
      rewrite Hbefore, Hafter, Hbefore_frame, Hafter_frame.
      unfold Credits.ordinary_credit.
      pose proof (@control_frame_owner owner before_control before_fr
        Hbefore_frame) as Hbefore_owner.
      pose proof (@control_frame_owner owner after_control after_fr
        Hafter_frame) as Hafter_owner.
      now rewrite Hphase, Hbefore_owner, Hafter_owner, Hsigma.
    Qed.

    Lemma active_ordinary_credit_same_le :
      forall before after before_control after_control owner before_fr after_fr,
        S.mem owner (R.controlled before) = true ->
        S.mem owner (R.controlled after) = true ->
        control_frame owner before_control = Some before_fr ->
        control_frame owner after_control = Some after_fr ->
        R.frame_phase after_fr = R.frame_phase before_fr ->
        R.sigma_value after owner = R.sigma_value before owner ->
        active_ordinary_credit after after_control owner <=
        active_ordinary_credit before before_control owner.
    Proof.
      intros. erewrite active_ordinary_credit_same; eauto.
    Qed.

    Lemma write_side_sigma_value :
      forall st fr target input next changed owner,
        R.write_side_contribution st fr target input = (next, changed) ->
        R.sigma_value next owner = R.sigma_value st owner.
    Proof.
      intros st fr target input next changed owner Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input).
      inversion Hwrite; subst. unfold base, R.promote_side_target,
        R.promote_controlled, R.sigma_value.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma write_side_sigma :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        R.sigma next = R.sigma st.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input).
      inversion Hwrite; subst. unfold base, R.promote_side_target,
        R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Lemma set_value_other_sigma_value :
      forall st fr direct next next_fr owner,
        R.set_value st fr direct = (next, next_fr) ->
        owner <> R.frame_owner fr ->
        R.sigma_value next owner = R.sigma_value st owner.
    Proof.
      intros st fr direct next next_fr owner Hset Hneq.
      unfold R.set_value in Hset.
      repeat match type of Hset with
      | context [if ?condition then _ else _] => destruct condition
      | context [match ?subject with _ => _ end] => destruct subject
      end;
      inversion Hset; subst; unfold R.sigma_value; cbn;
      try reflexivity;
      rewrite ML.lookup_update_other by exact Hneq; reflexivity.
    Qed.

    Lemma materialized_solved :
      forall st owner,
        R.is_materialized st owner = true -> Sem.solved st owner.
    Proof.
      intros st owner Hmaterialized. unfold R.is_materialized in Hmaterialized.
      destruct (M.lookup (R.sigma st) owner) as [value |] eqn:Hlookup;
        [now exists value |discriminate].
    Qed.

    Lemma solved_materialized :
      forall st owner,
        Sem.solved st owner -> R.is_materialized st owner = true.
    Proof.
      intros st owner [value Hlookup]. unfold R.is_materialized.
      now rewrite Hlookup.
    Qed.

    Theorem reachable_control_frame_solved :
      forall tf roots c owner fr,
        Sem.steps tf (R.initial_config roots) c ->
        control_frame owner (R.cfg_control c) = Some fr ->
        Sem.solved (R.cfg_state c) owner.
    Proof.
      intros tf roots c owner fr Hsteps Hframe. apply materialized_solved.
      eapply control_frame_materialized; [|exact Hframe].
      exact (reachable_owners_materialized Hsteps).
    Qed.

    Lemma observe_sigma :
      forall st target, R.sigma (R.observe st target) = R.sigma st.
    Proof.
      intros. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) target). reflexivity.
    Qed.

    Lemma enqueue_sigma :
      forall st target, R.sigma (R.enqueue st target) = R.sigma st.
    Proof. reflexivity. Qed.

    Lemma publish_targets_sigma :
      forall st fr, R.sigma (R.publish_targets st fr) = R.sigma st.
    Proof. reflexivity. Qed.

    Lemma reset_registered_cells_sigma :
      forall st owner,
        R.sigma (R.reset_registered_cells st owner) = R.sigma st.
    Proof.
      intros. unfold R.reset_registered_cells.
      destruct Features.restart_side_phases; reflexivity.
    Qed.

    Lemma record_side_input_phase :
      forall fr target raw next input,
        R.record_side_input fr target raw = (next, input) ->
        R.frame_phase next = R.frame_phase fr.
    Proof.
      intros fr target raw next input Hrecord.
      unfold R.record_side_input in Hrecord. inversion Hrecord. reflexivity.
    Qed.

    Lemma active_ordinary_start_episode_nonincreasing :
      forall tf st current k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.StartEpisode current k |} =
          Some after ->
        control_frame owner (R.StartEpisode current k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.StartEpisode current k) owner.
    Proof.
      intros tf st current k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      cbn in Hstep. inversion Hstep; subst.
      assert (Hneq : current <> owner).
      { intro Heq. subst current. cbn [control_frame] in Hbefore_frame.
        destruct (V.eq_dec owner owner); [discriminate |contradiction]. }
      eapply active_ordinary_credit_same_le
        with (before_fr := before_fr) (after_fr := after_fr); eauto.
      - cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
        destruct (V.eq_dec current owner); [contradiction |].
        cbn in Hafter_frame.
        destruct (V.eq_dec current owner); [contradiction |]. congruence.
      - unfold R.materialize.
        destruct (M.lookup (R.sigma st) current) eqn:Hlookup;
          [reflexivity |].
        unfold R.sigma_value. cbn.
        rewrite ML.lookup_update_other by exact (not_eq_sym Hneq).
        reflexivity.
    Qed.

    Lemma active_ordinary_runrhs_ret_nonincreasing :
      forall tf st fr direct k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Ret direct) k |} =
          Some after ->
        control_frame owner
          (R.RunRhs fr (R.ConstraintSystem.Ret direct) k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st
          (R.RunRhs fr (R.ConstraintSystem.Ret direct) k) owner.
    Proof.
      intros tf st fr direct k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      cbn in Hstep. inversion Hstep; subst.
      eapply active_ordinary_credit_same_le
        with (before_fr := before_fr) (after_fr := after_fr); eauto;
        try reflexivity.
      cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
      congruence.
    Qed.

    Lemma active_ordinary_runrhs_get_nonincreasing :
      forall tf st fr target next k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} =
          Some after ->
        control_frame owner
          (R.RunRhs fr (R.ConstraintSystem.Get target next) k) =
          Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        Sem.solved st owner ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st
          (R.RunRhs fr (R.ConstraintSystem.Get target next) k) owner.
    Proof.
      intros tf st fr target next k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after Hsolved.
      cbn -[R.observe R.complete_get R.enqueue] in Hstep.
      remember (R.observe st target) as observed.
      assert (Hsolved_observed : Sem.solved observed owner).
      { destruct Hsolved as [value Hlookup]. exists value. subst observed.
        rewrite observe_sigma. exact Hlookup. }
      destruct (negb (R.is_materialized observed target) &&
        R.rank_lt observed (R.frame_owner fr) target)%bool eqn:Hrecursive.
      - inversion Hstep; subst.
        assert (Htarget : target <> owner).
        { intro Heq. subst target.
          destruct Hsolved_observed as [value Hlookup].
          unfold R.is_materialized in Hrecursive.
          rewrite Hlookup in Hrecursive. discriminate. }
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto.
        + cbn [R.cfg_control control_frame continuation_frame]
            in Hbefore_frame, Hafter_frame.
          destruct (V.eq_dec target owner); [contradiction |].
          destruct (V.eq_dec (R.frame_owner fr) owner); congruence.
        + cbn. unfold R.sigma_value. rewrite observe_sigma. reflexivity.
      - remember (if R.is_materialized observed target
          then observed else R.enqueue observed target) as base.
        destruct (R.complete_get base fr target)
          as [[next_st next_fr] value] eqn:Hget.
        inversion Hstep; subst.
        set (base := if R.is_materialized (R.observe st target) target
          then R.observe st target
          else R.enqueue (R.observe st target) target) in Hget.
        assert (Hsolved_base : Sem.solved base owner).
        { subst base. destruct (R.is_materialized (R.observe st target) target);
            [exact Hsolved_observed |].
          destruct Hsolved_observed as [current Hlookup]. exists current.
          rewrite enqueue_sigma. exact Hlookup. }
        destruct (@complete_get_preserves_owner_credit_view
          base fr target next_st next_fr value owner Hget
          (solved_materialized Hsolved_base)) as [Hsigma Hphase].
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto.
        + cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          pose proof (@complete_get_owner
            base fr target next_st next_fr value Hget) as Howner_get.
          destruct (V.eq_dec (R.frame_owner fr) owner);
            destruct (V.eq_dec (R.frame_owner next_fr) owner); congruence.
        + cbn. rewrite Hsigma. subst base.
          destruct (R.is_materialized (R.observe st target) target);
            unfold R.sigma_value; rewrite ?enqueue_sigma, observe_sigma;
            reflexivity.
    Qed.

    Lemma active_ordinary_runrhs_side_nonincreasing :
      forall tf st fr target raw next k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Side target raw next) k |} =
          Some after ->
        control_frame owner
          (R.RunRhs fr (R.ConstraintSystem.Side target raw next) k) =
          Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st
          (R.RunRhs fr (R.ConstraintSystem.Side target raw next) k) owner.
    Proof.
      intros tf st fr target raw next k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      cbn -[R.observe R.record_side_input
        R.write_side_contribution R.continue_side] in Hstep.
      remember (R.observe st target) as observed.
      destruct (R.record_side_input fr target raw) as [fr1 input] eqn:Hrecord.
      destruct (R.write_side_contribution observed fr1 target input)
        as [next_st changed] eqn:Hwrite.
      pose proof (@record_side_input_phase
        fr target raw fr1 input Hrecord) as Hphase.
      pose proof (@record_side_input_owner
        fr target raw fr1 input Hrecord) as Howner.
      pose proof (@write_side_sigma
        observed fr1 target input next_st changed Hwrite) as Hsigma.
      unfold R.continue_side in Hstep. destruct changed;
        try destruct (R.rank_lt next_st (R.frame_owner fr1) target &&
          negb (R.is_materialized next_st target))%bool;
        inversion Hstep; subst.
      all: eapply active_ordinary_credit_same_le
        with (before_fr := before_fr) (after_fr := after_fr); eauto.
      all: try (cbn; unfold R.sigma_value;
        rewrite ?enqueue_sigma, Hsigma, observe_sigma; reflexivity).
      all: cbn [R.cfg_control control_frame continuation_frame]
        in Hbefore_frame, Hafter_frame.
      all: rewrite Howner in Hafter_frame.
      all: destruct (V.eq_dec target owner);
        destruct (V.eq_dec (R.frame_owner fr) owner); try congruence.
      all: inversion Hbefore_frame; inversion Hafter_frame; subst.
      all: exact Hphase.
    Qed.

    Lemma active_ordinary_runrhs_spawn_nonincreasing :
      forall tf st fr target next k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} =
          Some after ->
        control_frame owner
          (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k) =
          Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        Sem.solved st owner ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st
          (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k) owner.
    Proof.
      intros tf st fr target next k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after Hsolved.
      cbn -[R.observe R.materialize R.enqueue] in Hstep.
      remember (R.observe st target) as observed.
      assert (Hsolved_observed : Sem.solved observed owner).
      { destruct Hsolved as [value Hlookup]. exists value. subst observed.
        rewrite observe_sigma. exact Hlookup. }
      destruct (R.is_materialized observed target) eqn:Hmaterialized.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        + cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          congruence.
        + cbn. unfold R.sigma_value. rewrite observe_sigma. reflexivity.
      - destruct (R.rank_lt observed (R.frame_owner fr) target) eqn:Hhigher.
        + inversion Hstep; subst.
          assert (Htarget : target <> owner).
          { intro Heq. subst target.
            destruct Hsolved_observed as [value Hlookup].
            unfold R.is_materialized in Hmaterialized.
            rewrite Hlookup in Hmaterialized. discriminate. }
          eapply active_ordinary_credit_same_le
            with (before_fr := before_fr) (after_fr := after_fr);
            try eassumption.
          * cbn [R.cfg_control control_frame continuation_frame]
              in Hbefore_frame, Hafter_frame.
            destruct (V.eq_dec target owner); [contradiction |].
            destruct (V.eq_dec (R.frame_owner fr) owner); congruence.
          * cbn. unfold R.sigma_value. rewrite observe_sigma. reflexivity.
        + inversion Hstep; subst.
          eapply active_ordinary_credit_same_le
            with (before_fr := before_fr) (after_fr := after_fr); eauto.
          * cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
            congruence.
          * cbn. assert (Hsolved_enqueue :
              Sem.solved (R.enqueue (R.observe st target) target) owner).
            { destruct Hsolved_observed as [value Hlookup]. exists value.
              rewrite enqueue_sigma. exact Hlookup. }
            rewrite (@materialize_sigma_value_materialized
              (R.enqueue (R.observe st target) target) target owner
              (solved_materialized Hsolved_enqueue)).
            unfold R.sigma_value. rewrite enqueue_sigma, observe_sigma.
            reflexivity.
    Qed.

    Lemma active_ordinary_runrhs_nonincreasing :
      forall tf st fr body k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body k |} =
          Some after ->
        control_frame owner (R.RunRhs fr body k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        Sem.solved st owner ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.RunRhs fr body k) owner.
    Proof.
      intros tf st fr body k after owner before_fr after_fr Hstep
        Hbefore Hafter Hcontrolled Hcontrolled_after Hsolved.
      destruct body.
      - eapply active_ordinary_runrhs_ret_nonincreasing; eauto.
      - eapply active_ordinary_runrhs_get_nonincreasing; eauto.
      - eapply active_ordinary_runrhs_side_nonincreasing; eauto.
      - eapply active_ordinary_runrhs_spawn_nonincreasing; eauto.
    Qed.

    Lemma active_ordinary_rundead_nonincreasing :
      forall tf st fr direct pending k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
        control_frame owner (R.RunDead fr direct pending k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.RunDead fr direct pending k) owner.
    Proof.
      intros tf st fr direct pending k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      destruct pending as [|target remaining].
      - cbn -[R.publish_targets] in Hstep. inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        + cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          congruence.
      - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
        destruct (S.mem target (R.frame_current_targets fr)).
        + inversion Hstep; subst.
          eapply active_ordinary_credit_same_le
            with (before_fr := before_fr) (after_fr := after_fr); eauto;
            try reflexivity.
          cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          congruence.
        + destruct (R.write_side_contribution st fr target D.bottom)
            as [next changed] eqn:Hwrite.
          pose proof (@write_side_sigma
            st fr target D.bottom next changed Hwrite) as Hsigma.
          unfold R.continue_dead in Hstep. destruct changed;
            try destruct (R.rank_lt next (R.frame_owner fr) target &&
              negb (R.is_materialized next target))%bool;
            inversion Hstep; subst.
          all: eapply active_ordinary_credit_same_le
            with (before_fr := before_fr) (after_fr := after_fr); eauto.
          all: try (cbn; unfold R.sigma_value;
            rewrite ?enqueue_sigma, Hsigma; reflexivity).
          all: cbn [R.cfg_control control_frame continuation_frame]
            in Hbefore_frame, Hafter_frame.
          all: destruct (V.eq_dec target owner);
            destruct (V.eq_dec (R.frame_owner fr) owner); try congruence.
    Qed.

    Lemma active_ordinary_runcommit_nonincreasing :
      forall tf st fr direct k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
          Some after ->
        control_frame owner (R.RunCommit fr direct k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.RunCommit fr direct k) owner.
    Proof.
      intros tf st fr direct k after owner before_fr after_fr Hstep
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      cbn -[R.set_value] in Hstep.
      destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
      inversion Hstep; subst.
      pose proof (@set_value_owner st fr direct next next_fr Hset) as Howner.
      destruct (V.eq_dec (R.frame_owner fr) owner) as [Hcurrent |Hnested].
      - cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
        destruct (V.eq_dec (R.frame_owner fr) owner); [|contradiction].
        destruct (V.eq_dec (R.frame_owner next_fr) owner); [|congruence].
        inversion Hbefore_frame; inversion Hafter_frame; subst.
        unfold active_ordinary_credit. cbn.
        cbn in Hcontrolled_after. rewrite Hcontrolled, Hcontrolled_after.
        destruct (V.eq_dec
          (R.frame_owner after_fr) (R.frame_owner before_fr)); [|congruence].
        destruct (V.eq_dec
          (R.frame_owner before_fr) (R.frame_owner before_fr));
          [|contradiction].
        eapply Credits.set_value_credit_nonincreasing; eauto.
      - eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto.
        + cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          destruct (V.eq_dec (R.frame_owner fr) owner); [contradiction |].
          destruct (V.eq_dec (R.frame_owner next_fr) owner); [congruence |].
          congruence.
        + cbn. eapply set_value_other_sigma_value; eauto.
    Qed.

    Lemma continuation_frame_contains :
      forall owner k fr,
        continuation_frame owner k = Some fr ->
        continuation_contains owner k.
    Proof.
      intros owner k. induction k; intros fr Hframe;
        cbn [continuation_frame] in Hframe; try discriminate.
      all: destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
      all: try (left; symmetry; exact Heq).
      all: right; eapply IHk; eauto.
    Qed.

    Lemma continuation_frame_none_below_self :
      forall st owner k,
        continuation_below st owner k ->
        continuation_frame owner k = None.
    Proof.
      intros st owner k Hbelow.
      destruct (continuation_frame owner k) as [fr |] eqn:Hframe;
        [|reflexivity].
      pose proof (@continuation_contains_below st owner k owner Hbelow
        (@continuation_frame_contains owner k fr Hframe)) as Hlt.
      pose proof (proj1 (@rank_lt_true_ranked st owner owner Hlt)) as Hranked.
      rewrite (@rank_lt_irrefl st owner Hranked) in Hlt. discriminate.
    Qed.

    Lemma return_below_frame_phase :
      forall st fr k owner before_fr after_fr,
        continuation_below st (R.frame_owner fr) k ->
        control_frame owner (R.RunDrain fr k) = Some before_fr ->
        control_frame owner (R.Return k) = Some after_fr ->
        R.frame_phase after_fr = R.frame_phase before_fr.
    Proof.
      intros st fr k owner before_fr after_fr Hbelow Hbefore Hafter.
      cbn [control_frame] in Hbefore, Hafter.
      destruct (V.eq_dec (R.frame_owner fr) owner) as [Heq |Hneq].
      - subst owner. rewrite (@continuation_frame_none_below_self
          st (R.frame_owner fr) k Hbelow) in Hafter. discriminate.
      - congruence.
    Qed.

    Lemma active_ordinary_rundrain_nonincreasing :
      forall tf st fr k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} =
          Some after ->
        continuation_below st (R.frame_owner fr) k ->
        control_frame owner (R.RunDrain fr k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.RunDrain fr k) owner.
    Proof.
      intros tf st fr k after owner before_fr after_fr Hstep Hbelow
        Hbefore_frame Hafter_frame Hcontrolled Hcontrolled_after.
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
      destruct (R.queue_peek (R.queue st)) as [next |].
      - destruct (V.eq_dec next (R.frame_owner fr)).
        + destruct (R.queue_pop (R.queue st)) as [[head tail] |];
            try discriminate.
          inversion Hstep; subst.
          eapply active_ordinary_credit_same_le
            with (before_fr := before_fr) (after_fr := after_fr);
            try eassumption; try reflexivity.
          cbn [R.cfg_control control_frame] in Hbefore_frame, Hafter_frame.
          cbn in Hafter_frame.
          destruct (V.eq_dec (R.frame_owner fr) owner).
          * inversion Hbefore_frame; inversion Hafter_frame; subst.
            reflexivity.
          * congruence.
        + destruct (R.rank_lt st (R.frame_owner fr) next).
          * destruct (R.queue_pop (R.queue st)) as [[head tail] |];
              try discriminate.
            inversion Hstep; subst.
            eapply active_ordinary_credit_same_le
              with (before_fr := before_fr) (after_fr := after_fr);
              try eassumption; try reflexivity.
            cbn [R.cfg_control control_frame continuation_frame]
              in Hbefore_frame, Hafter_frame.
            destruct (V.eq_dec next owner);
              destruct (V.eq_dec (R.frame_owner fr) owner); try congruence.
          * inversion Hstep; subst.
            eapply active_ordinary_credit_same_le
              with (before_fr := before_fr) (after_fr := after_fr);
              try eassumption.
            -- eapply return_below_frame_phase; eauto.
            -- cbn. unfold R.sigma_value.
              rewrite reset_registered_cells_sigma. reflexivity.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr);
          try eassumption.
        + eapply return_below_frame_phase; eauto.
        + cbn. unfold R.sigma_value.
          rewrite reset_registered_cells_sigma. reflexivity.
    Qed.

    Lemma active_ordinary_return_nonincreasing :
      forall tf st k after owner before_fr after_fr,
        R.next_config tf
          {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
        control_frame owner (R.Return k) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled st) = true ->
        S.mem owner (R.controlled (R.cfg_state after)) = true ->
        Sem.solved st owner ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit st (R.Return k) owner.
    Proof.
      intros tf st k after owner before_fr after_fr Hstep Hbefore_frame
        Hafter_frame Hcontrolled Hcontrolled_after Hsolved.
      destruct k; cbn -[R.complete_get] in Hstep.
      - cbn [control_frame] in Hbefore_frame. discriminate.
      - cbn [control_frame] in Hbefore_frame. discriminate.
      - destruct (R.complete_get st f t)
          as [[next next_fr] value] eqn:Hget.
        inversion Hstep; subst.
        destruct (@complete_get_preserves_owner_credit_view
          st f t next next_fr value owner Hget
          (solved_materialized Hsolved)) as [Hsigma Hphase].
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr);
          try eassumption.
        cbn [R.cfg_control control_frame continuation_frame]
          in Hbefore_frame, Hafter_frame.
        pose proof (@complete_get_owner st f t next next_fr value Hget)
          as Howner.
        destruct (V.eq_dec (R.frame_owner f) owner);
          destruct (V.eq_dec (R.frame_owner next_fr) owner); congruence.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        cbn [R.cfg_control control_frame continuation_frame]
          in Hbefore_frame, Hafter_frame. congruence.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        cbn [R.cfg_control control_frame continuation_frame]
          in Hbefore_frame, Hafter_frame. congruence.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        cbn [R.cfg_control control_frame continuation_frame]
          in Hbefore_frame, Hafter_frame. congruence.
      - inversion Hstep; subst.
        eapply active_ordinary_credit_same_le
          with (before_fr := before_fr) (after_fr := after_fr); eauto;
          try reflexivity.
        cbn [R.cfg_control control_frame continuation_frame]
          in Hbefore_frame, Hafter_frame. congruence.
    Qed.

    Theorem reachable_active_ordinary_step_nonincreasing :
      forall tf roots before after owner before_fr after_fr,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_frame owner (R.cfg_control before) = Some before_fr ->
        control_frame owner (R.cfg_control after) = Some after_fr ->
        S.mem owner (R.controlled (R.cfg_state before)) = true ->
        active_ordinary_credit
          (R.cfg_state after) (R.cfg_control after) owner <=
        active_ordinary_credit
          (R.cfg_state before) (R.cfg_control before) owner.
    Proof.
      intros tf roots [st control] after owner before_fr after_fr Hreachable
        Hstep Hbefore_frame Hafter_frame Hcontrolled.
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      pose proof (reachable_control_ordered Hreachable) as Hordered.
      assert (Hcontrolled_after :
        S.mem owner (R.controlled (R.cfg_state after)) = true).
      { eapply controlled_step_monotone; eauto. }
      assert (Hsolved : Sem.solved st owner).
      { exact (@reachable_control_frame_solved tf roots
          {| R.cfg_state := st; R.cfg_control := control |}
          owner before_fr Hreachable Hbefore_frame). }
      unfold Sem.step in Hstep. destruct control.
      - cbn [control_frame] in Hbefore_frame. discriminate.
      - cbn [control_frame] in Hbefore_frame. discriminate.
      - cbn [control_frame] in Hbefore_frame. discriminate.
      - eapply active_ordinary_start_episode_nonincreasing; eauto.
      - eapply active_ordinary_runrhs_nonincreasing; eauto.
      - eapply active_ordinary_rundead_nonincreasing; eauto.
      - eapply active_ordinary_runcommit_nonincreasing; eauto.
      - destruct Hranked as [_ _ Hcontrol _ _]. cbn in Hcontrol, Hordered.
        destruct Hcontrol as [_ Hcontinuation].
        eapply active_ordinary_rundrain_nonincreasing; eauto.
      - eapply active_ordinary_return_nonincreasing; eauto.
    Qed.

    Lemma continuation_contains_frame_exists :
      forall owner k,
        continuation_contains owner k ->
        exists fr, continuation_frame owner k = Some fr.
    Proof.
      intros owner k. induction k; cbn [continuation_frame];
        intros Hcontains; try contradiction.
      all: destruct Hcontains as [Howner |Hcontains].
      all: destruct (V.eq_dec (R.frame_owner f) owner) as [Heq |Hneq].
      all: try (exists f; reflexivity).
      all: try (exfalso; apply Hneq; symmetry; exact Howner).
      all: apply IHk in Hcontains; exact Hcontains.
    Qed.

    Lemma frame_or_continuation_contains_frame :
      forall owner fr k,
        owner = R.frame_owner fr \/ continuation_contains owner k ->
        exists found,
          (if V.eq_dec (R.frame_owner fr) owner
           then Some fr else continuation_frame owner k) = Some found.
    Proof.
      intros owner fr k Hcontains.
      destruct (V.eq_dec (R.frame_owner fr) owner) as [Heq |Hneq].
      - exists fr. reflexivity.
      - destruct Hcontains as [Howner |Htail].
        + exfalso. apply Hneq. symmetry. exact Howner.
        + now apply continuation_contains_frame_exists.
    Qed.

    Lemma control_contains_frame_or_start :
      forall owner control,
        control_contains owner control ->
        (exists fr, control_frame owner control = Some fr) \/
        (exists k, control = R.StartEpisode owner k).
    Proof.
      intros owner control Hcontains. destruct control;
        cbn [control_contains control_frame] in Hcontains |- *;
        try contradiction.
      - destruct (V.eq_dec t owner) as [-> |Hneq].
        + right. eauto.
        + left. destruct Hcontains as [Heq |Htail].
          * exfalso. apply Hneq. symmetry. exact Heq.
          * now apply continuation_contains_frame_exists.
      - left. now apply frame_or_continuation_contains_frame.
      - left. now apply frame_or_continuation_contains_frame.
      - left. now apply frame_or_continuation_contains_frame.
      - left. now apply frame_or_continuation_contains_frame.
      - left. now apply continuation_contains_frame_exists.
    Qed.

    Lemma active_frame_cannot_start_same_owner :
      forall tf roots before after_st after_k owner before_fr,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before
          {| R.cfg_state := after_st;
             R.cfg_control := R.StartEpisode owner after_k |} ->
        control_frame owner (R.cfg_control before) = Some before_fr ->
        False.
    Proof.
      intros tf roots [st control] after_st after_k owner before_fr
        Hreachable Hstep Hframe.
      assert (Hmaterialized : R.is_materialized st owner = true).
      { eapply control_frame_materialized; [|exact Hframe].
        exact (reachable_owners_materialized Hreachable). }
      assert (Hmaterialized_after :
        R.is_materialized after_st owner = true).
      { exact (@step_materialized_mono tf
          {| R.cfg_state := st; R.cfg_control := control |}
          {| R.cfg_state := after_st;
             R.cfg_control := R.StartEpisode owner after_k |}
          owner Hstep Hmaterialized). }
      unfold Sem.step in Hstep. destruct control as
        [|seed_roots |remaining |current k |fr body k
         |fr direct pending k |fr direct k |fr k |k].
      - cbn [control_frame] in Hframe. discriminate.
      - cbn [control_frame] in Hframe. discriminate.
      - cbn [control_frame] in Hframe. discriminate.
      - cbn in Hstep. inversion Hstep.
      - destruct body as [direct |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep.
        + cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool eqn:Hnested.
          * inversion Hstep; subst.
            apply Bool.andb_true_iff in Hnested. destruct Hnested as [Hfresh _].
            apply Bool.negb_true_iff in Hfresh.
            rewrite Hmaterialized_after in Hfresh. discriminate.
          * set (base := if R.is_materialized observed target
              then observed else R.enqueue observed target) in *.
            destruct (R.complete_get base fr target) as [[next_st next_fr] value].
            inversion Hstep.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution observed fr1 target input)
            as [next_st changed].
          unfold R.continue_side in Hstep. destruct changed.
          * destruct (R.rank_lt next_st (R.frame_owner fr1) target &&
              negb (R.is_materialized next_st target))%bool eqn:Hnested.
            -- inversion Hstep; subst.
               apply Bool.andb_true_iff in Hnested.
               destruct Hnested as [_ Hfresh].
               apply Bool.negb_true_iff in Hfresh.
               rewrite Hmaterialized_after in Hfresh. discriminate.
            -- inversion Hstep.
          * inversion Hstep.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target) eqn:Htarget.
          * inversion Hstep.
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst.
               rewrite Hmaterialized_after in Htarget. discriminate.
            -- inversion Hstep.
      - destruct pending as [|target remaining].
        + cbn in Hstep. inversion Hstep.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [next_st changed].
            unfold R.continue_dead in Hstep. destruct changed.
            -- destruct (R.rank_lt next_st (R.frame_owner fr) target &&
                negb (R.is_materialized next_st target))%bool eqn:Hnested.
               ++ inversion Hstep; subst.
                  apply Bool.andb_true_iff in Hnested.
                  destruct Hnested as [_ Hfresh].
                  apply Bool.negb_true_iff in Hfresh.
                  rewrite Hmaterialized_after in Hfresh. discriminate.
               ++ inversion Hstep.
            -- inversion Hstep.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct). inversion Hstep.
      - pose proof (@reachable_control_ordered tf roots
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
          Hreachable) as Hordered.
        cbn in Hordered.
        cbn -[R.reset_registered_cells R.fresh_frame] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |].
        + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
          * destruct (R.queue_pop (R.queue st)); [destruct p |]; inversion Hstep.
          * destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
            -- destruct (R.queue_pop (R.queue st)) as [[head tail] |];
                 try discriminate. inversion Hstep; subst.
               cbn [control_frame] in Hframe.
               destruct (V.eq_dec (R.frame_owner fr) owner) as [Htop |Hbelow].
               ++ apply Hneq. now rewrite Htop.
               ++ change (control_frame owner (R.RunDrain fr k) =
                    Some before_fr) in Hframe.
                  cbn [control_frame] in Hframe.
                  destruct (V.eq_dec (R.frame_owner fr) owner);
                    [contradiction |].
                  pose proof (@continuation_frame_contains
                    owner k before_fr Hframe) as Hcontains.
                  pose proof (@continuation_contains_below st
                    (R.frame_owner fr) k owner Hordered Hcontains) as Howner_lt.
                  pose proof (@rank_lt_true_ranked st owner
                    (R.frame_owner fr) Howner_lt) as [Howner_rank Hframe_rank].
                  pose proof (@rank_lt_true_ranked st
                    (R.frame_owner fr) owner Hhigher) as [_ Howner_rank'].
                  pose proof (@rank_lt_trans st owner (R.frame_owner fr) owner
                    Howner_rank Hframe_rank Howner_rank'
                    Howner_lt Hhigher) as Hfalse.
                  rewrite (@rank_lt_irrefl st owner Howner_rank) in Hfalse.
                  discriminate.
            -- inversion Hstep.
        + inversion Hstep.
      - destruct k; cbn -[R.complete_get] in Hstep; try inversion Hstep.
    Qed.

    Lemma active_step_frame_exists :
      forall tf roots before after owner before_fr,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_frame owner (R.cfg_control before) = Some before_fr ->
        control_contains owner (R.cfg_control after) ->
        exists after_fr,
          control_frame owner (R.cfg_control after) = Some after_fr.
    Proof.
      intros tf roots before [after_st after_control] owner before_fr
        Hreachable Hstep Hbefore Hcontains.
      destruct (@control_contains_frame_or_start owner after_control Hcontains)
        as [[after_fr Hframe] |[after_k Hstart]].
      - eauto.
      - subst after_control. exfalso.
        eapply active_frame_cannot_start_same_owner; eauto.
    Qed.

    Lemma owner_frame_credit_step :
      forall tf roots before after owner owner_fr,
        Sem.steps tf (R.initial_config roots) before ->
        Sem.step tf before after ->
        control_contains owner (R.cfg_control before) ->
        control_contains owner (R.cfg_control after) ->
        control_frame owner (R.cfg_control before) = Some owner_fr ->
        S.mem owner (R.controlled (R.cfg_state before)) = true ->
        exists owner_fr',
          control_frame owner (R.cfg_control after) = Some owner_fr' /\
          active_ordinary_credit
              (R.cfg_state after) (R.cfg_control after) owner <=
            active_ordinary_credit
              (R.cfg_state before) (R.cfg_control before) owner.
    Proof.
      intros tf roots before after owner owner_fr Hreachable Hstep
        Hbefore_contains Hafter_contains Hbefore_frame Hcontrolled.
      destruct (@active_step_frame_exists tf roots before after owner owner_fr
        Hreachable Hstep Hbefore_frame Hafter_contains)
        as [after_fr Hafter_frame].
      exists after_fr. split; [exact Hafter_frame |].
      eapply reachable_active_ordinary_step_nonincreasing; eauto.
    Qed.

    Lemma active_prefix_owner_credit_nonincreasing :
      forall tf roots owner first final owner_fr,
        Sem.steps tf (R.initial_config roots) first ->
        active_prefix owner tf first final ->
        control_contains owner (R.cfg_control final) ->
        control_frame owner (R.cfg_control first) = Some owner_fr ->
        S.mem owner (R.controlled (R.cfg_state first)) = true ->
        active_ordinary_credit
            (R.cfg_state final) (R.cfg_control final) owner <=
          active_ordinary_credit
            (R.cfg_state first) (R.cfg_control first) owner.
    Proof.
      intros tf roots owner first final owner_fr Hreachable Hprefix.
      revert owner_fr Hreachable. induction Hprefix;
        intros owner_fr Hreachable Hfinal Hframe Hcontrolled; [lia |].
      assert (Hnext_contains :
        control_contains owner (R.cfg_control next)).
      { destruct Hprefix; [exact Hfinal |exact H1]. }
      destruct (@owner_frame_credit_step tf roots first next owner owner_fr
        Hreachable H0 H Hnext_contains Hframe Hcontrolled)
        as [next_fr [Hnext_frame Hfirst_credit]].
      assert (Hnext_reachable : Sem.steps tf (R.initial_config roots) next).
      { eapply steps_append_one; eauto. }
      assert (Hnext_controlled :
        S.mem owner (R.controlled (R.cfg_state next)) = true).
      { eapply controlled_step_monotone; eauto. }
      specialize (IHHprefix next_fr Hnext_reachable Hfinal
        Hnext_frame Hnext_controlled). lia.
    Qed.

    Lemma unmaterialized_count_sigma_ext :
      forall support before after,
        R.sigma after = R.sigma before ->
        unmaterialized_count support after =
        unmaterialized_count support before.
    Proof.
      intros support. induction support as [|x rest IH];
        intros before after Hsigma; cbn; [reflexivity |].
      unfold R.is_materialized. rewrite Hsigma, (IH before after Hsigma).
      reflexivity.
    Qed.

    Lemma enqueue_queue_strictly_below :
      forall owner target st,
        R.rank_lt st target owner = true ->
        queue_strictly_below owner st ->
        queue_strictly_below owner (R.enqueue st target).
    Proof.
      intros owner target st Htarget Hbelow queued Hin.
      unfold R.enqueue in Hin. cbn in Hin.
      apply queue_insert_members in Hin. destruct Hin as [-> |Hin];
        [exact Htarget |now apply Hbelow].
    Qed.

    Lemma complete_get_fresh_decreases :
      forall support st fr target next next_fr value,
        NoDup support -> List.In target support ->
        R.is_materialized st target = false ->
        R.complete_get (R.enqueue st target) fr target =
          (next, next_fr, value) ->
        unmaterialized_count support next < unmaterialized_count support st.
    Proof.
      intros support st fr target next next_fr value Hnodup Hin Hfresh Hget.
      unfold R.complete_get in Hget.
      destruct (R.rank_lt (R.enqueue st target) (R.frame_owner fr) target);
        inversion Hget; subst next next_fr value; clear Hget.
      all: match goal with
      | |- unmaterialized_count ?support0 (R.materialize ?pre ?target0) <
          unmaterialized_count ?support0 ?st0 =>
          assert (Hfresh_pre : R.is_materialized pre target0 = false) by
            (unfold R.is_materialized in *; cbn; exact Hfresh);
          pose proof (@unmaterialized_count_materialize_decreases
            support0 pre target0 Hnodup Hin Hfresh_pre) as Hdecrease;
          assert (Hsigma_pre : R.sigma pre = R.sigma st0) by reflexivity;
          pose proof (@unmaterialized_count_sigma_ext
            support0 st0 pre (eq_sym Hsigma_pre)) as Hcount; lia
      end.
    Qed.

    Lemma spawn_fresh_decreases :
      forall support st target,
        NoDup support -> List.In target support ->
        R.is_materialized st target = false ->
        unmaterialized_count support
          (R.materialize (R.enqueue st target) target) <
        unmaterialized_count support st.
    Proof.
      intros support st target Hnodup Hin Hfresh.
      pose proof (@unmaterialized_count_materialize_decreases support
        (R.enqueue st target) target Hnodup Hin) as Hdecrease.
      assert (Hfresh_enqueue :
        R.is_materialized (R.enqueue st target) target = false).
      { unfold R.is_materialized, R.enqueue in *. cbn. exact Hfresh. }
      specialize (Hdecrease Hfresh_enqueue).
      pose proof (@unmaterialized_count_sigma_ext support st
        (R.enqueue st target) eq_refl) as Hcount. lia.
    Qed.

    Lemma observe_queue :
      forall st target, R.queue (R.observe st target) = R.queue st.
    Proof.
      intros. unfold R.observe.
      destruct (R.Ranking.observe (R.ranking st) target). reflexivity.
    Qed.

    Lemma complete_get_queue :
      forall st fr target next next_fr value,
        R.complete_get st fr target = (next, next_fr, value) ->
        R.queue next = R.queue st.
    Proof.
      intros st fr target next next_fr value Hget.
      unfold R.complete_get in Hget.
      set (st1 := if R.rank_lt st (R.frame_owner fr) target
        then st else R.promote_controlled st target) in *.
      set (minimum := if R.rank_lt st target (R.frame_min_scope fr)
        then target else R.frame_min_scope fr) in *.
      set (maximum := match R.frame_max_read fr with
        | None => Some target
        | Some previous =>
            if R.rank_lt st previous target then Some target else Some previous
        end) in *.
      set (st2 := R.with_readers st1
        (M.update (R.readers st1) target
          (S.add (R.frame_owner fr) (R.lookup_set (R.readers st1) target)))) in *.
      inversion Hget; subst next next_fr value. subst st2 st1.
      unfold R.materialize, R.promote_controlled.
      destruct (R.rank_lt st (R.frame_owner fr) target);
        destruct (M.lookup _ target); reflexivity.
    Qed.

    Lemma write_side_queue :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        R.queue next = R.queue st.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input).
      inversion Hwrite; subst. unfold base, R.promote_side_target,
        R.promote_controlled.
      destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity.
    Qed.

    Inductive evaluation_frontier
      (support : list V.t) (owner : V.t)
      (base : R.continuation) : R.config -> Prop :=
    | EvaluationRhs :
        forall st fr body,
          R.frame_owner fr = owner ->
          evaluation_frontier support owner base
            {| R.cfg_state := st; R.cfg_control := R.RunRhs fr body base |}
    | EvaluationDead :
        forall st fr direct pending,
          R.frame_owner fr = owner ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.RunDead fr direct pending base |}
    | EvaluationCommit :
        forall st fr direct,
          R.frame_owner fr = owner ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.RunCommit fr direct base |}
    | EvaluationPendingGet :
        forall st target fr next,
          R.frame_owner fr = owner ->
          R.is_materialized st target = false ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.StartEpisode target
                 (R.KAfterGet fr target next base) |}
    | EvaluationPendingSide :
        forall st target fr next,
          R.frame_owner fr = owner ->
          R.is_materialized st target = false ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.StartEpisode target
                 (R.KAfterSide fr next base) |}
    | EvaluationPendingSpawn :
        forall st target fr next,
          R.frame_owner fr = owner ->
          R.is_materialized st target = false ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.StartEpisode target
                 (R.KAfterSpawn fr next base) |}
    | EvaluationPendingDead :
        forall st target fr direct pending,
          R.frame_owner fr = owner ->
          R.is_materialized st target = false ->
          evaluation_frontier support owner base
            {| R.cfg_state := st;
               R.cfg_control := R.StartEpisode target
                 (R.KDead fr direct pending base) |}.

    Lemma evaluation_frontier_owner_ranked :
      forall support owner base c,
        configuration_ranked c ->
        evaluation_frontier support owner base c ->
        ranked (R.cfg_state c) owner.
    Proof.
      intros support owner base c Hranked Hfront. destruct Hfront;
        destruct Hranked as [_ _ Hcontrol _ _]; cbn in Hcontrol.
      - rewrite <- H. exact (proj1 (proj1 Hcontrol)).
      - rewrite <- H. exact (proj1 (proj1 Hcontrol)).
      - rewrite <- H. exact (proj1 (proj1 Hcontrol)).
      - destruct Hcontrol as [_ [Hfr _]]. rewrite <- H.
        exact (proj1 Hfr).
      - destruct Hcontrol as [_ [Hfr _]]. rewrite <- H.
        exact (proj1 Hfr).
      - destruct Hcontrol as [_ [Hfr _]]. rewrite <- H.
        exact (proj1 Hfr).
      - destruct Hcontrol as [_ [Hfr _]]. rewrite <- H.
        exact (proj1 Hfr).
    Qed.

    Lemma observe_queue_strictly_below :
      forall st target owner,
        ranked st owner ->
        queue_strictly_below owner st ->
        queue_strictly_below owner (R.observe st target).
    Proof.
      intros st target owner Howner Hbelow.
      exact (@queue_below_extended st (R.observe st target) owner
        (@rank_extends_observe st target (R.observe st target) eq_refl) Howner
        (observe_queue st target) Hbelow).
    Qed.

    Lemma evaluation_frontier_step :
      forall support tf roots (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        forall base before after,
        Sem.steps tf (R.initial_config roots) before ->
        evaluation_frontier support owner base before ->
        queue_strictly_below owner (R.cfg_state before) ->
        owner_commitb owner before = false ->
        Sem.step tf before after ->
        unmaterialized_count support (R.cfg_state after) =
          unmaterialized_count support (R.cfg_state before) ->
        Credits.source_side_credit support (R.cfg_state after) owner =
          Credits.source_side_credit support (R.cfg_state before) owner ->
        evaluation_frontier support owner base after /\
        queue_strictly_below owner (R.cfg_state after).
    Proof.
      intros support tf roots finite owner Hsupport base before after
        Hreachable Hfront Hbelow Hnotcommit Hstep Hmaterialized Hsource.
      subst support.
      pose proof (reachable_config_supported finite Hreachable)
        as [Hstate Hcontrol].
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      pose proof (@evaluation_frontier_owner_ranked
        (Sem.support finite) owner base before Hranked Hfront) as Howner_ranked.
      assert (Hnodup : NoDup (Sem.support finite))
        by apply Sem.support_nodup.
      destruct Hfront.
      - cbn in Hcontrol. destruct Hcontrol as [Hframe [Hbody Hbase]].
        destruct body as [direct |target next |target raw next |target next].
        + unfold Sem.step in Hstep. cbn in Hstep. inversion Hstep; subst.
          split; [apply EvaluationDead; reflexivity |exact Hbelow].
        + pose proof (rhs_supported_get_inv Hbody) as [Htarget Hnext].
          unfold Sem.step in Hstep.
          cbn -[R.observe R.complete_get R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hbelow_observed : queue_strictly_below owner observed).
          { subst observed. now apply observe_queue_strictly_below. }
          assert (Howner_observed : ranked observed owner).
          { subst observed. eapply ranked_extended;
              [eapply rank_extends_observe; reflexivity |exact Howner_ranked]. }
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool eqn:Hnested.
          * inversion Hstep; subst. apply Bool.andb_true_iff in Hnested.
            destruct Hnested as [Hfresh Hhigher].
            apply Bool.negb_true_iff in Hfresh. split.
            -- apply EvaluationPendingGet; [reflexivity |exact Hfresh].
            -- exact Hbelow_observed.
          * destruct (R.is_materialized observed target) eqn:Hfresh.
            -- destruct (R.complete_get observed fr target)
                 as [[st1 fr1] value] eqn:Hget.
               inversion Hstep; subst. split.
               ++ apply EvaluationRhs. rewrite (complete_get_owner Hget).
                  reflexivity.
               ++ eapply queue_below_extended.
                  ** eapply rank_extends_complete_get; exact Hget.
                  ** exact Howner_observed.
                  ** eapply complete_get_queue; exact Hget.
                  ** exact Hbelow_observed.
            -- destruct (R.complete_get (R.enqueue observed target) fr target)
                 as [[st1 fr1] value] eqn:Hget.
               inversion Hstep; subst.
               pose proof (@complete_get_fresh_decreases
                 (Sem.support finite) observed fr target st1 fr1 value
                 Hnodup Htarget Hfresh Hget) as Hdecrease.
               pose proof (@unmaterialized_count_sigma_ext
                 (Sem.support finite) st observed (observe_sigma st target))
                 as Hobserve. cbn in Hmaterialized. lia.
        + pose proof (rhs_supported_side_inv Hbody) as [Htarget Hnext].
          unfold Sem.step in Hstep.
          cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hbelow_observed : queue_strictly_below owner observed).
          { subst observed. now apply observe_queue_strictly_below. }
          assert (Howner_observed : ranked observed owner).
          { subst observed. eapply ranked_extended;
              [eapply rank_extends_observe; reflexivity |exact Howner_ranked]. }
          destruct (R.record_side_input fr target raw)
            as [fr1 input] eqn:Hrecord.
          pose proof (record_side_input_owner Hrecord) as Howner1.
          destruct (R.write_side_contribution observed fr1 target input)
            as [st1 changed] eqn:Hwrite.
          assert (Hbelow_written : queue_strictly_below owner st1).
          { eapply queue_below_extended.
            - eapply rank_extends_write_side_contribution; exact Hwrite.
            - exact Howner_observed.
            - eapply write_side_queue; exact Hwrite.
            - exact Hbelow_observed. }
          unfold R.continue_side in Hstep. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool eqn:Hnested.
            -- inversion Hstep; subst. apply Bool.andb_true_iff in Hnested.
               destruct Hnested as [Hhigher Hfresh].
               apply Bool.negb_true_iff in Hfresh. split.
               ++ apply EvaluationPendingSide;
                    [now rewrite Howner1 |exact Hfresh].
               ++ exact Hbelow_written.
            -- inversion Hstep; subst.
               destruct (R.rank_lt st1 target (R.frame_owner fr)) eqn:Htarget_rank.
               ++ split.
                  ** apply EvaluationRhs. now rewrite Howner1.
                  ** apply enqueue_queue_strictly_below;
                       [exact Htarget_rank |exact Hbelow_written].
               ++ pose proof (@Credits.source_side_credit_write_decreases
                    (Sem.support finite) observed fr1 target input st1
                    Htarget Hwrite) as Hdecrease.
                  rewrite Howner1 in Hdecrease.
                  cbn in Hsource. rewrite source_credit_enqueue in Hsource.
                  subst observed. rewrite source_credit_observe in Hdecrease.
                  lia.
          * inversion Hstep; subst. split.
            -- apply EvaluationRhs. now rewrite Howner1.
            -- exact Hbelow_written.
        + pose proof (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
          unfold Sem.step in Hstep.
          cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          assert (Hbelow_observed : queue_strictly_below owner observed).
          { subst observed. now apply observe_queue_strictly_below. }
          destruct (R.is_materialized observed target) eqn:Hfresh.
          * inversion Hstep; subst. split;
              [apply EvaluationRhs; reflexivity |exact Hbelow_observed].
          * destruct (R.rank_lt observed (R.frame_owner fr) target).
            -- inversion Hstep; subst. split.
               ++ apply EvaluationPendingSpawn; [reflexivity |exact Hfresh].
               ++ exact Hbelow_observed.
            -- inversion Hstep; subst.
               pose proof (@spawn_fresh_decreases
                 (Sem.support finite) observed target Hnodup Htarget Hfresh)
                 as Hdecrease.
               pose proof (@unmaterialized_count_sigma_ext
                 (Sem.support finite) st observed (observe_sigma st target))
                 as Hobserve. cbn in Hmaterialized. lia.
      - cbn in Hcontrol. destruct Hcontrol as [Hframe [Hpending Hbase]].
        destruct pending as [|target remaining].
        + unfold Sem.step in Hstep. cbn -[R.publish_targets] in Hstep.
          inversion Hstep; subst. split;
            [apply EvaluationCommit; reflexivity |exact Hbelow].
        + assert (Htarget : List.In target (Sem.support finite)).
          { inversion Hpending; subst. assumption. }
          unfold Sem.step in Hstep.
          cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. split;
              [apply EvaluationDead; reflexivity |exact Hbelow].
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed] eqn:Hwrite.
            assert (Hbelow_written : queue_strictly_below owner st1).
            { eapply queue_below_extended.
              - eapply rank_extends_write_side_contribution; exact Hwrite.
              - exact Howner_ranked.
              - eapply write_side_queue; exact Hwrite.
              - exact Hbelow. }
            unfold R.continue_dead in Hstep. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool eqn:Hnested.
               ++ inversion Hstep; subst. apply Bool.andb_true_iff in Hnested.
                  destruct Hnested as [Hhigher Hfresh].
                  apply Bool.negb_true_iff in Hfresh. split.
                  ** apply EvaluationPendingDead; [reflexivity |exact Hfresh].
                  ** exact Hbelow_written.
               ++ inversion Hstep; subst.
                  destruct (R.rank_lt st1 target (R.frame_owner fr))
                    eqn:Htarget_rank.
                  ** split.
                     --- apply EvaluationDead. reflexivity.
                     --- apply enqueue_queue_strictly_below;
                           [exact Htarget_rank |exact Hbelow_written].
                  ** pose proof (@Credits.source_side_credit_write_decreases
                       (Sem.support finite) st fr target D.bottom st1
                       Htarget Hwrite) as Hdecrease.
                     cbn in Hsource. rewrite source_credit_enqueue in Hsource.
                     lia.
            -- inversion Hstep; subst. split;
                 [apply EvaluationDead; reflexivity |exact Hbelow_written].
      - unfold owner_commitb in Hnotcommit. cbn in Hnotcommit.
        rewrite H in Hnotcommit.
        destruct (V.eq_dec owner owner);
          [discriminate |contradiction].
      - unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
        inversion Hstep; subst.
        pose proof (@unmaterialized_count_materialize_decreases
          (Sem.support finite) st target Hnodup
          (proj1 Hcontrol) H0) as Hdecrease.
        cbn in Hmaterialized. lia.
      - unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
        inversion Hstep; subst.
        pose proof (@unmaterialized_count_materialize_decreases
          (Sem.support finite) st target Hnodup
          (proj1 Hcontrol) H0) as Hdecrease.
        cbn in Hmaterialized. lia.
      - unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
        inversion Hstep; subst.
        pose proof (@unmaterialized_count_materialize_decreases
          (Sem.support finite) st target Hnodup
          (proj1 Hcontrol) H0) as Hdecrease.
        cbn in Hmaterialized. lia.
      - unfold Sem.step in Hstep. cbn -[R.materialize] in Hstep.
        inversion Hstep; subst.
        pose proof (@unmaterialized_count_materialize_decreases
          (Sem.support finite) st target Hnodup
          (proj1 Hcontrol) H0) as Hdecrease.
        cbn in Hmaterialized. lia.
    Qed.

    Lemma evaluation_frontier_until_queue_below :
      forall support tf initial
        (finite : Sem.finite_system tf initial) owner,
        support = Sem.support finite ->
        forall base first final,
        Sem.steps tf (R.initial_config initial) first ->
        until_owner_commit owner tf first final ->
        active_prefix owner tf first final ->
        evaluation_frontier support owner base first ->
        queue_strictly_below owner (R.cfg_state first) ->
        unmaterialized_count support (R.cfg_state final) =
          unmaterialized_count support (R.cfg_state first) ->
        Credits.source_side_credit support (R.cfg_state final) owner =
          Credits.source_side_credit support (R.cfg_state first) owner ->
        queue_strictly_below owner (R.cfg_state final).
    Proof.
      intros support tf initial finite owner Hsupport
        base first final Hreachable Huntil.
      revert base Hreachable.
      induction Huntil as
        [c Hcommit
        |first next final Hnotcommit Hstep Huntil IH];
        intros base Hreachable Hactive Hfront Hbelow
          Hmaterialized Hsource.
      - exact Hbelow.
      - inversion Hactive as
          [|first' next' final'
            Hfirst_contains Hactive_step Htail];
          subst.
        + exact Hbelow.
        + assert (Hnext_eq : next' = next).
          { eapply step_deterministic; eauto. }
          subst next'.
          assert (Hfinal_contains :
            control_contains owner (R.cfg_control final)).
          {
            apply owner_commitb_contains.
            eapply until_owner_commit_final; eauto.
          }
          assert (Hnext_contains :
            control_contains owner (R.cfg_control next)).
          {
            pose proof Htail as Htail'.
            destruct Htail' as
              [|tail_first tail_next tail_final
                Hcontains Htail_step Htail_rest].
            - exact Hfinal_contains.
            - exact Hcontains.
          }
          assert (Hnext_reachable :
            Sem.steps tf (R.initial_config initial) next).
          { eapply steps_append_one; eauto. }
          pose proof
            (@unmaterialized_count_step_nonincreasing
              (Sem.support finite) tf first next Hstep)
            as Hmaterialized_first.
          pose proof
            (@unmaterialized_count_steps_nonincreasing
              (Sem.support finite) tf next final
              (until_owner_commit_steps Huntil))
            as Hmaterialized_rest.
          assert (Hmaterialized_step :
            unmaterialized_count
                (Sem.support finite) (R.cfg_state next) =
            unmaterialized_count
                (Sem.support finite) (R.cfg_state first))
            by lia.
          pose proof
            (@source_credit_step_nonincreasing
              (Sem.support finite) tf initial owner first next
              Hreachable Hstep Hfirst_contains Hnext_contains)
            as Hsource_first.
          pose proof
            (@active_prefix_source_credit_nonincreasing
              (Sem.support finite) tf initial owner next final
              Hnext_reachable Htail Hfinal_contains)
            as Hsource_rest.
          assert (Hsource_step :
            Credits.source_side_credit
                (Sem.support finite) (R.cfg_state next) owner =
            Credits.source_side_credit
                (Sem.support finite) (R.cfg_state first) owner)
            by lia.
          destruct
            (@evaluation_frontier_step
              (Sem.support finite) tf initial finite owner eq_refl
              base first next Hreachable Hfront Hbelow Hnotcommit
              Hstep Hmaterialized_step Hsource_step)
            as [Hfront_next Hbelow_next].
          eapply IH; eauto; lia.
    Qed.

    Fixpoint continuation_has_root_drain
      (owner : V.t) (base : R.continuation)
      (k : R.continuation) : Prop :=
      match k with
      | R.KLoop | R.KSeedLoop _ => False
      | R.KAfterGet _ _ _ rest
      | R.KAfterSide _ _ rest
      | R.KAfterSpawn _ _ rest
      | R.KDead _ _ _ rest =>
          continuation_has_root_drain owner base rest
      | R.KDrain fr rest =>
          (R.frame_owner fr = owner /\ rest = base) \/
          continuation_has_root_drain owner base rest
      end.

    Definition drain_phase_control
      (owner : V.t) (base : R.continuation)
      (control : R.control) : Prop :=
      match control with
      | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
      | R.StartEpisode _ k
      | R.RunRhs _ _ k
      | R.RunDead _ _ _ k
      | R.RunCommit _ _ k
      | R.Return k =>
          continuation_has_root_drain owner base k
      | R.RunDrain fr k =>
          (R.frame_owner fr = owner /\ k = base) \/
          continuation_has_root_drain owner base k
      end.

    Lemma root_drain_contains :
      forall owner base k,
        continuation_has_root_drain owner base k ->
        continuation_contains owner k.
    Proof.
      intros owner base k. induction k; cbn; intros Hroot;
        try contradiction.
      all: try (right; now apply IHk).
      destruct Hroot as [[Howner Hbase] | Hroot].
      - left. symmetry. exact Howner.
      - right. now apply IHk.
    Qed.

    Lemma drain_phase_contains :
      forall owner base control,
        drain_phase_control owner base control ->
        control_contains owner control.
    Proof.
      intros owner base control Hdrain.
      destruct control; cbn in Hdrain |- *; try contradiction.
      - right. exact (@root_drain_contains owner base _ Hdrain).
      - right. exact (@root_drain_contains owner base _ Hdrain).
      - right. exact (@root_drain_contains owner base _ Hdrain).
      - right. exact (@root_drain_contains owner base _ Hdrain).
      - destruct Hdrain as [[Howner Hbase] | Hroot].
        + left. symmetry. exact Howner.
        + right. exact (@root_drain_contains owner base _ Hroot).
      - exact (@root_drain_contains owner base _ Hdrain).
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

    Lemma root_drain_below :
      forall st owner base upper k,
        continuation_has_root_drain owner base k ->
        continuation_below st upper k ->
        R.rank_lt st owner upper = true.
    Proof.
      intros st owner base upper k. revert upper.
      induction k; intros upper Hroot Hbelow;
        cbn in *; try contradiction.
      all: destruct Hbelow as [Htop Hbelow].
      all: try solve [
        eapply rank_lt_trans_true;
        [eapply IHk; eauto |exact Htop]].
      destruct Hroot as [[Howner Hbase] | Hroot].
      - now rewrite Howner in Htop.
      - eapply rank_lt_trans_true;
          [eapply IHk; eauto |exact Htop].
    Qed.

    Lemma root_drain_materialized :
      forall st owner base k,
        continuation_has_root_drain owner base k ->
        continuation_owners_materialized st k ->
        R.is_materialized st owner = true.
    Proof.
      intros st owner base k. induction k; cbn;
        intros Hroot Hmaterialized; try contradiction.
      all: destruct Hmaterialized as [Hhead Hmaterialized].
      all: try solve [eapply IHk; eauto].
      destruct Hroot as [[Howner Hbase] | Hroot].
      - now rewrite Howner in Hhead.
      - eapply IHk; eauto.
    Qed.

    Lemma drain_phase_solved :
      forall tf roots owner base c,
        Sem.steps tf (R.initial_config roots) c ->
        drain_phase_control owner base (R.cfg_control c) ->
        Sem.solved (R.cfg_state c) owner.
    Proof.
      intros tf roots owner base [st control] Hreachable Hdrain.
      pose proof (reachable_owners_materialized Hreachable) as Hmaterialized.
      apply materialized_solved.
      destruct control; cbn in Hdrain, Hmaterialized |- *;
        try contradiction.
      - eapply root_drain_materialized; eauto.
      - eapply root_drain_materialized; [exact Hdrain |exact (proj2 Hmaterialized)].
      - eapply root_drain_materialized; [exact Hdrain |exact (proj2 Hmaterialized)].
      - eapply root_drain_materialized; [exact Hdrain |exact (proj2 Hmaterialized)].
      - destruct Hdrain as [[Howner Hbase] | Hroot].
        + now rewrite Howner in Hmaterialized.
        + eapply root_drain_materialized; [exact Hroot |exact (proj2 Hmaterialized)].
      - eapply root_drain_materialized; eauto.
    Qed.

    Lemma drain_phase_step :
      forall tf roots owner base before after,
        Sem.steps tf (R.initial_config roots) before ->
        drain_phase_control owner base (R.cfg_control before) ->
        ~ List.In owner (R.queue (R.cfg_state before)) ->
        control_contains owner (R.cfg_control after) ->
        Sem.step tf before after ->
        drain_phase_control owner base (R.cfg_control after).
    Proof.
      intros tf roots owner base [st control] after
        Hreachable Hdrain Hnotqueued Hcontains Hstep.
      unfold Sem.step in Hstep. destruct control as
        [|seed_roots |remaining |current k |fr body k
         |fr direct pending k |fr direct k |fr k |k];
        try contradiction.
      - cbn -[R.materialize] in Hstep.
        inversion Hstep; subst. exact Hdrain.
      - destruct body as [value |target next |target raw next |target next].
        + cbn in Hstep. inversion Hstep; subst. exact Hdrain.
        + cbn -[R.observe R.complete_get] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (negb (R.is_materialized observed target) &&
            R.rank_lt observed (R.frame_owner fr) target)%bool.
          * inversion Hstep; subst. exact Hdrain.
          * destruct (R.complete_get
              (if R.is_materialized observed target
               then observed else R.enqueue observed target)
              fr target) as [[st1 fr1] value].
            inversion Hstep; subst. exact Hdrain.
        + cbn -[R.observe R.record_side_input
            R.write_side_contribution R.continue_side] in Hstep.
          destruct (R.record_side_input fr target raw) as [fr1 input].
          destruct (R.write_side_contribution
            (R.observe st target) fr1 target input) as [st1 changed].
          unfold R.continue_side in Hstep. destruct changed;
            [destruct (R.rank_lt st1 (R.frame_owner fr1) target &&
              negb (R.is_materialized st1 target))%bool |];
            inversion Hstep; subst; exact Hdrain.
        + cbn -[R.observe R.materialize R.enqueue] in Hstep.
          set (observed := R.observe st target) in *.
          destruct (R.is_materialized observed target).
          * inversion Hstep; subst. exact Hdrain.
          * destruct (R.rank_lt observed (R.frame_owner fr) target);
              inversion Hstep; subst; exact Hdrain.
      - destruct pending as [|target remaining].
        + cbn -[R.publish_targets] in Hstep.
          inversion Hstep; subst. exact Hdrain.
        + cbn -[R.write_side_contribution R.continue_dead] in Hstep.
          destruct (S.mem target (R.frame_current_targets fr)).
          * inversion Hstep; subst. exact Hdrain.
          * destruct (R.write_side_contribution st fr target D.bottom)
              as [st1 changed].
            unfold R.continue_dead in Hstep. destruct changed;
              [destruct (R.rank_lt st1 (R.frame_owner fr) target &&
                negb (R.is_materialized st1 target))%bool |];
              inversion Hstep; subst; exact Hdrain.
      - cbn -[R.set_value] in Hstep.
        destruct (R.set_value st fr direct) as [st1 fr1].
        inversion Hstep; subst. cbn in Hdrain |- *. right. exact Hdrain.
      - cbn -[R.reset_registered_cells] in Hstep.
        destruct (R.queue_peek (R.queue st)) as [next |] eqn:Hpeek.
        + destruct (V.eq_dec next (R.frame_owner fr)) as [Heq |Hneq].
          * destruct (R.queue_pop (R.queue st))
              as [[head tail] |] eqn:Hpop; try discriminate.
            inversion Hstep; subst. cbn in Hdrain |- *.
            destruct Hdrain as [[Howner Hbase] | Hroot].
            -- exfalso. apply Hnotqueued.
               rewrite <- Howner. now apply queue_peek_member in Hpeek.
            -- exact Hroot.
          * destruct (R.rank_lt st (R.frame_owner fr) next) eqn:Hhigher.
            -- destruct (R.queue_pop (R.queue st))
                 as [[head tail] |] eqn:Hpop; try discriminate.
               inversion Hstep; subst. exact Hdrain.
            -- inversion Hstep; subst. cbn in Hdrain |- *.
               destruct Hdrain as [[Howner Hbase] | Hroot].
               ++ exfalso. pose proof (reachable_control_ordered Hreachable)
                    as Hordered. cbn in Hordered, Hcontains.
                  rewrite Howner in Hordered. subst k.
                  pose proof (@continuation_contains_below
                    st owner base owner Hordered Hcontains) as Hfalse.
                  pose proof (proj1 (@rank_lt_true_ranked
                    st owner owner Hfalse)) as Hranked.
                  rewrite (@rank_lt_irrefl st owner Hranked) in Hfalse.
                  discriminate.
               ++ exact Hroot.
        + inversion Hstep; subst. cbn in Hdrain |- *.
          destruct Hdrain as [[Howner Hbase] | Hroot].
          * exfalso. pose proof (reachable_control_ordered Hreachable)
              as Hordered. cbn in Hordered, Hcontains.
            rewrite Howner in Hordered. subst k.
            pose proof (@continuation_contains_below
              st owner base owner Hordered Hcontains) as Hfalse.
            pose proof (proj1 (@rank_lt_true_ranked
              st owner owner Hfalse)) as Hranked.
            rewrite (@rank_lt_irrefl st owner Hranked) in Hfalse.
            discriminate.
          * exact Hroot.
      - destruct k as
          [|remaining |fr target next rest |fr next rest |fr next rest
           |fr direct pending rest |fr rest];
          cbn -[R.complete_get] in Hstep, Hdrain |- *;
          try contradiction.
        all: inversion Hstep; subst; exact Hdrain.
    Qed.

    Definition executed_rerun
      (tf : R.ConstraintSystem.system) (owner : V.t)
      (k : R.continuation) (before : R.state)
      (fr : R.frame) (tail : R.work_queue) : R.config :=
      {| R.cfg_state := R.with_queue before tail;
         R.cfg_control :=
           R.RunRhs
             (R.fresh_frame (R.with_queue before tail)
               owner (R.frame_phase fr))
             (tf owner) k |}.

    Lemma executed_rerun_step :
      forall tf owner k before fr tail,
        R.frame_owner fr = owner ->
        R.queue_pop (R.queue before) = Some (owner, tail) ->
        Sem.step tf
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain fr k |}
          (executed_rerun tf owner k before fr tail).
    Proof.
      intros tf owner k before fr tail Howner Hpop.
      unfold Sem.step, executed_rerun. cbn.
      destruct (R.queue before) as [|head rest] eqn:Hqueue;
        cbn in Hpop; try discriminate.
      inversion Hpop; subst head rest. cbn.
      rewrite Howner. destruct (V.eq_dec owner owner);
        [reflexivity |congruence].
    Qed.

    Lemma set_value_equivalent_queue :
      forall st fr direct next next_fr,
        R.set_value st fr direct = (next, next_fr) ->
        R.equivalent
          (R.sigma_value next (R.frame_owner fr))
          (R.sigma_value st (R.frame_owner fr)) = true ->
        R.queue next = R.queue st.
    Proof.
      intros st fr direct next next_fr Hset Hequivalent.
      unfold R.set_value in Hset.
      destruct (R.equivalent
        (D.join direct (R.aggregate st (R.frame_owner fr)))
        (R.sigma_value st (R.frame_owner fr))) eqn:Hcandidate.
      - inversion Hset; reflexivity.
      - destruct (if S.mem (R.frame_owner fr) (R.controlled st)
          then U.update false (R.frame_owner fr) (R.frame_phase fr)
            (R.sigma_value st (R.frame_owner fr))
            (D.join direct (R.aggregate st (R.frame_owner fr)))
          else (R.frame_phase fr,
            D.join direct (R.aggregate st (R.frame_owner fr))))
          as [phase value] eqn:Hupdate.
        cbn in Hset. destruct (R.equivalent value
          (R.sigma_value st (R.frame_owner fr))) eqn:Hvalue.
        + inversion Hset; reflexivity.
        + inversion Hset; subst.
          rewrite Credits.sigma_value_after_commit in Hequivalent.
          rewrite Hvalue in Hequivalent. discriminate.
    Qed.

    Lemma uncontrolled_set_value_queue_below :
      forall tf roots owner st fr direct next next_fr k,
        R.frame_owner fr = owner ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunCommit fr direct k |} ->
        S.mem owner (R.controlled st) = false ->
        queue_strictly_below owner st ->
        R.set_value st fr direct = (next, next_fr) ->
        queue_strictly_below owner next.
    Proof.
      intros tf roots owner st fr direct next next_fr k
        Howner Hreachable Huncontrolled Hbelow Hset queued Hin.
      destruct (in_dec V.eq_dec queued (R.queue st)) as [Hold |Hnew].
      - pose proof (Hbelow queued Hold) as Hrank.
        pose proof (@rank_lt_true_ranked st queued owner Hrank)
          as [Hqueued Howner_ranked].
        rewrite <- (@rank_lt_stable st next queued owner
          (@rank_extends_set_value st fr direct next next_fr Hset)
          Hqueued Howner_ranked).
        exact Hrank.
      - destruct (@set_value_new_queue_cause
          st fr direct next next_fr queued Hset Hnew Hin)
          as [_ Hreader].
        pose proof (ReaderOrder.reachable_reader_edges_ordered Hreachable)
          as Hordered.
        destruct (Hordered (R.frame_owner fr) queued Hreader)
          as [Hrank |Hcontrolled].
        + rewrite Howner in Hrank.
          pose proof (@rank_lt_true_ranked st queued owner Hrank)
            as [Hqueued Howner_ranked].
          rewrite <- (@rank_lt_stable st next queued owner
            (@rank_extends_set_value st fr direct next next_fr Hset)
            Hqueued Howner_ranked).
          exact Hrank.
        + cbn in Hcontrolled. rewrite Howner, Huncontrolled in Hcontrolled.
          discriminate.
    Qed.

    Lemma drain_below_cannot_rerun_owner :
      forall tf roots owner st fr k before drain_fr tail,
        R.frame_owner fr = owner ->
        queue_strictly_below owner st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
        active_prefix owner tf
          {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |} ->
        R.frame_owner drain_fr = owner ->
        R.queue_pop (R.queue before) = Some (owner, tail) ->
        False.
    Proof.
      intros tf roots owner st fr k before drain_fr tail
        Howner Hbelow Hreachable Hprefix Hdrain_owner Hpop.
      inversion Hprefix as [|first next final Hcontains Hstep Htail].
      - subst before drain_fr.
        assert (Hqueued : List.In owner (R.queue st)).
        { destruct (R.queue st) as [|head rest] eqn:Hqueue;
            cbn in Hpop; try discriminate.
          inversion Hpop; subst. now left. }
        pose proof (Hbelow owner Hqueued) as Hfalse.
        pose proof (proj1 (@rank_lt_true_ranked
          st owner owner Hfalse)) as Howner_ranked.
        rewrite (@rank_lt_irrefl st owner Howner_ranked) in Hfalse.
        discriminate.
      - subst first final.
        assert (Hnext_return : R.cfg_control next = R.Return k).
        {
          unfold Sem.step in Hstep.
          cbn -[R.reset_registered_cells] in Hstep.
          destruct (R.queue_peek (R.queue st)) as [queued |] eqn:Hpeek.
          - pose proof (@queue_peek_member (R.queue st) queued Hpeek)
              as Hqueued.
            pose proof (Hbelow queued Hqueued) as Hqueued_below.
            destruct (V.eq_dec queued (R.frame_owner fr)) as [Heq |Hneq].
            + subst queued. rewrite Howner in Hqueued_below.
              pose proof (proj1 (@rank_lt_true_ranked
                st owner owner Hqueued_below)) as Hranked.
              rewrite (@rank_lt_irrefl st owner Hranked) in Hqueued_below.
              discriminate.
            + destruct (R.rank_lt st (R.frame_owner fr) queued)
                eqn:Hhigher.
              * rewrite Howner in Hhigher.
                pose proof (@rank_lt_asymmetric st owner queued
                  (proj1 (@rank_lt_true_ranked st owner queued Hhigher))
                  (proj2 (@rank_lt_true_ranked st owner queued Hhigher))
                  Hhigher) as Hasym.
                rewrite Hqueued_below in Hasym. discriminate.
              * inversion Hstep. reflexivity.
          - inversion Hstep. reflexivity.
        }
        assert (Hfinal_contains :
          control_contains owner (R.RunDrain drain_fr k))
          by (cbn; left; symmetry; exact Hdrain_owner).
        pose proof (@active_prefix_initial_contains owner tf next
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |}
          Htail Hfinal_contains) as Hnext_contains.
        rewrite Hnext_return in Hnext_contains. cbn in Hnext_contains.
        pose proof (reachable_control_ordered Hreachable) as Hordered.
        cbn in Hordered.
        pose proof (@continuation_contains_below st
          (R.frame_owner fr) k owner Hordered Hnext_contains) as Hfalse.
        rewrite Howner in Hfalse.
        pose proof (proj1 (@rank_lt_true_ranked
          st owner owner Hfalse)) as Hranked.
        rewrite (@rank_lt_irrefl st owner Hranked) in Hfalse.
        discriminate.
    Qed.

    Lemma executed_rerun_requires_owner_change :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        forall st fr k commit_st commit_fr direct drain_st owner_drain_fr
          before drain_fr tail,
        R.frame_owner fr = owner ->
        queue_strictly_below owner st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} ->
        active_prefix owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        until_owner_commit owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        R.frame_owner commit_fr = owner ->
        R.set_value commit_st commit_fr direct =
          (drain_st, owner_drain_fr) ->
        R.frame_owner owner_drain_fr = owner ->
        active_prefix owner tf
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |} ->
        R.frame_owner drain_fr = owner ->
        R.queue_pop (R.queue before) = Some (owner, tail) ->
        unmaterialized_count support (R.with_queue before tail) =
          unmaterialized_count support st ->
        promotion_reserve (R.with_queue before tail) owner =
          promotion_reserve st owner ->
        Credits.source_side_credit support
            (R.with_queue before tail) owner =
          Credits.source_side_credit support st owner ->
        target_side_credit support (R.with_queue before tail) owner =
          target_side_credit support st owner ->
        S.mem owner (R.controlled st) = true /\
        R.equivalent
          (R.sigma_value drain_st owner)
          (R.sigma_value commit_st owner) = false.
    Proof.
      intros support tf roots finite owner Hsupport Howner
        st fr k commit_st commit_fr direct drain_st owner_drain_fr
        before drain_fr tail Hframe Hbelow Hreachable
        Heval Hfirst_commit Hcommit_owner Hset Howner_drain
        Hdrain Hdrain_owner Hpop
        Hmaterialized Hpromotion Hsource Htarget.
      pose proof (@steps_transitive tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        Hreachable (active_prefix_steps Heval)) as Hcommit_reachable.
      assert (Hcommit_contains :
        control_contains owner (R.RunCommit commit_fr direct k))
        by (cbn; left; symmetry; exact Hcommit_owner).
      assert (Hset_step :
        Sem.step tf
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |}
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}).
      { unfold Sem.step. cbn -[R.set_value]. now rewrite Hset. }
      pose proof (@steps_append_one tf (R.initial_config roots)
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain owner_drain_fr k |}
        Hcommit_reachable Hset_step) as Hdrain_reachable.
      assert (Hbefore_contains :
        control_contains owner (R.RunDrain drain_fr k))
        by (cbn; left; symmetry; exact Hdrain_owner).
      pose proof (@executed_rerun_step
        tf owner k before drain_fr tail Hdrain_owner Hpop) as Hpop_step.
      pose proof (@active_prefix_snoc owner tf
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain owner_drain_fr k |}
        {| R.cfg_state := before;
           R.cfg_control := R.RunDrain drain_fr k |}
        (executed_rerun tf owner k before drain_fr tail)
        Hdrain Hbefore_contains Hpop_step) as Hdrain_to_final.
      assert (Hcommit_to_final : active_prefix owner tf
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)).
      { econstructor; [exact Hcommit_contains |exact Hset_step |
          exact Hdrain_to_final]. }
      pose proof (@active_prefix_trans owner tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)
        Heval Hcommit_contains Hcommit_to_final) as Hfull.
      assert (Hfinal_contains : control_contains owner
        (R.cfg_control (executed_rerun tf owner k before drain_fr tail)))
        by (unfold executed_rerun; cbn; left; reflexivity).
      pose proof (@unmaterialized_count_steps_nonincreasing support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        (active_prefix_steps Heval)) as Hmaterialized_eval.
      pose proof (@unmaterialized_count_steps_nonincreasing support tf
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)
        (active_prefix_steps Hcommit_to_final)) as Hmaterialized_rest.
      pose proof (@promotion_reserve_steps_nonincreasing tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        owner (active_prefix_steps Heval)) as Hpromotion_eval.
      pose proof (@promotion_reserve_steps_nonincreasing tf
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)
        owner (active_prefix_steps Hcommit_to_final)) as Hpromotion_rest.
      pose proof (@active_prefix_source_credit_nonincreasing support tf roots
        owner {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        Hreachable Heval Hcommit_contains) as Hsource_eval.
      pose proof (@active_prefix_source_credit_nonincreasing support tf roots
        owner {| R.cfg_state := commit_st;
                 R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)
        Hcommit_reachable Hcommit_to_final Hfinal_contains) as Hsource_rest.
      pose proof (@active_prefix_target_credit_nonincreasing support tf roots
        owner {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        Hreachable Heval Hcommit_contains) as Htarget_eval.
      pose proof (@active_prefix_target_credit_nonincreasing support tf roots
        owner {| R.cfg_state := commit_st;
                 R.cfg_control := R.RunCommit commit_fr direct k |}
        (executed_rerun tf owner k before drain_fr tail)
        Hcommit_reachable Hcommit_to_final Hfinal_contains) as Htarget_rest.
      cbn in Hmaterialized_eval, Hmaterialized_rest,
        Hpromotion_eval, Hpromotion_rest, Hsource_eval, Hsource_rest,
        Htarget_eval, Htarget_rest.
      assert (Hmaterialized_commit :
        unmaterialized_count support commit_st =
        unmaterialized_count support st) by lia.
      assert (Hpromotion_commit :
        promotion_reserve commit_st owner =
        promotion_reserve st owner) by lia.
      assert (Hsource_commit :
        Credits.source_side_credit support commit_st owner =
        Credits.source_side_credit support st owner) by lia.
      assert (Htarget_commit :
        target_side_credit support commit_st owner =
        target_side_credit support st owner) by lia.
      assert (Hfrontier : evaluation_frontier support owner k
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |})
        by (apply EvaluationRhs; exact Hframe).
      pose proof (@evaluation_frontier_until_queue_below
        support tf roots finite owner Hsupport k
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        Hreachable Hfirst_commit Heval Hfrontier Hbelow
        Hmaterialized_commit Hsource_commit) as Hcommit_below.
      cbn in Hcommit_below.
      destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
      - split; [reflexivity |].
        destruct (R.equivalent
          (R.sigma_value drain_st owner)
          (R.sigma_value commit_st owner)) eqn:Hchanged.
        + exfalso.
          assert (Hchanged_frame : R.equivalent
            (R.sigma_value drain_st (R.frame_owner commit_fr))
            (R.sigma_value commit_st (R.frame_owner commit_fr)) = true)
            by (now rewrite Hcommit_owner).
          pose proof (@set_value_equivalent_queue commit_st commit_fr direct
            drain_st owner_drain_fr Hset Hchanged_frame) as Hqueue.
          assert (Hdrain_below : queue_strictly_below owner drain_st).
          { intros queued Hin.
            assert (Hin_commit : List.In queued (R.queue commit_st))
              by (now rewrite <- Hqueue).
            pose proof (Hcommit_below queued Hin_commit) as Hrank.
            pose proof (@rank_lt_true_ranked commit_st queued owner Hrank)
              as [Hqueued Howner_ranked].
            rewrite <- (@rank_lt_stable commit_st drain_st queued owner
              (@rank_extends_set_value commit_st commit_fr direct
                drain_st owner_drain_fr Hset) Hqueued Howner_ranked).
            exact Hrank. }
          exact (@drain_below_cannot_rerun_owner tf roots owner
            drain_st owner_drain_fr k before drain_fr tail Howner_drain
            Hdrain_below Hdrain_reachable Hdrain Hdrain_owner Hpop).
        + reflexivity.
      - exfalso.
        pose proof (@promotion_reserve_equal_membership
          st commit_st owner Hpromotion_commit) as Hcommit_uncontrolled.
        rewrite Hcontrolled in Hcommit_uncontrolled.
        assert (Hskip : S.mem (R.frame_owner commit_fr)
          (R.controlled commit_st) = false) by now rewrite Hcommit_owner.
        assert (Hdrain_uncontrolled :
          S.mem owner (R.controlled drain_st) = false).
        { rewrite (@set_value_controlled commit_st commit_fr direct
            drain_st owner_drain_fr Hset). exact Hcommit_uncontrolled. }
        assert (Hcommit_notqueued : ~ List.In owner (R.queue commit_st)).
        { intro Hin. pose proof (Hcommit_below owner Hin) as Hfalse.
          pose proof (proj1 (@rank_lt_true_ranked
            commit_st owner owner Hfalse)) as Hranked.
          rewrite (@rank_lt_irrefl commit_st owner Hranked) in Hfalse.
          discriminate. }
        pose proof (@uncontrolled_set_value_queue_below tf roots owner
          commit_st commit_fr direct drain_st owner_drain_fr k
          Hcommit_owner Hcommit_reachable Hcommit_uncontrolled
          Hcommit_below Hset) as Hdrain_below.
        assert (Hpromotion_set : promotion_reserve drain_st owner =
          promotion_reserve commit_st owner).
        { unfold promotion_reserve.
          rewrite (@set_value_controlled commit_st commit_fr direct
            drain_st owner_drain_fr Hset). reflexivity. }
        assert (Hpromotion_queue :
          promotion_reserve (R.with_queue before tail) owner =
          promotion_reserve before owner) by reflexivity.
        assert (Hpromotion_before : promotion_reserve before owner =
          promotion_reserve drain_st owner) by lia.
        pose proof (@target_credit_set_value support commit_st commit_fr direct
          drain_st owner_drain_fr owner Hset) as Htarget_set.
        pose proof (@target_credit_with_queue support before tail owner)
          as Htarget_queue.
        assert (Htarget_before : target_side_credit support before owner =
          target_side_credit support drain_st owner) by lia.
        exact (@drain_below_cannot_rerun_owner tf roots owner
          drain_st owner_drain_fr k before drain_fr tail Howner_drain
          Hdrain_below Hdrain_reachable Hdrain Hdrain_owner Hpop).
    Qed.

    Lemma active_rerun_ordinary_payment :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        forall st fr k commit_st commit_fr direct drain_st owner_drain_fr
          before drain_fr tail,
        R.frame_owner fr = owner ->
        queue_strictly_below owner st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} ->
        active_prefix owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        until_owner_commit owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        R.frame_owner commit_fr = owner ->
        R.set_value commit_st commit_fr direct =
          (drain_st, owner_drain_fr) ->
        R.frame_owner owner_drain_fr = owner ->
        active_prefix owner tf
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |} ->
        R.frame_owner drain_fr = owner ->
        R.queue_pop (R.queue before) = Some (owner, tail) ->
        unmaterialized_count support
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail)) =
          unmaterialized_count support st ->
        promotion_reserve
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
            owner = promotion_reserve st owner ->
        Credits.source_side_credit support
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
            owner = Credits.source_side_credit support st owner ->
        target_side_credit support
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
            owner = target_side_credit support st owner ->
        active_ordinary_credit
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
            (R.cfg_control (executed_rerun tf owner k before drain_fr tail))
            owner <
          active_ordinary_credit st (R.RunRhs fr (tf owner) k) owner.
    Proof.
      intros support tf roots finite owner Hsupport Howner
        st fr k commit_st commit_fr direct drain_st owner_drain_fr
        before drain_fr tail Hframe Hbelow Hreachable
        Heval_prefix Hfirst_commit Hcommit_owner Hset Howner_drain
        Hdrain_prefix Hdrain_owner Hpop
        Hmaterialized Hpromotion Hsource Htarget.
      destruct (@executed_rerun_requires_owner_change support tf roots finite
        owner Hsupport Howner st fr k commit_st commit_fr direct drain_st
        owner_drain_fr before drain_fr tail Hframe Hbelow Hreachable
        Heval_prefix Hfirst_commit Hcommit_owner Hset Howner_drain
        Hdrain_prefix Hdrain_owner Hpop Hmaterialized Hpromotion Hsource Htarget)
        as [Hcontrolled Hchanged].
      assert (Hcommit_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}).
      { eapply steps_transitive; [exact Hreachable |].
        exact (active_prefix_steps Heval_prefix). }
      assert (Hcommit_controlled :
        S.mem owner (R.controlled commit_st) = true).
      { exact (@controlled_steps_monotone tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |}
          owner (active_prefix_steps Heval_prefix) Hcontrolled). }
      assert (Hcommit_controlled_owner :
        S.mem (R.frame_owner commit_fr) (R.controlled commit_st) = true)
        by (now rewrite Hcommit_owner).
      assert (Hdrain_controlled :
        S.mem owner (R.controlled drain_st) = true).
      { rewrite (@set_value_controlled commit_st commit_fr direct drain_st
          owner_drain_fr Hset). exact Hcommit_controlled. }
      assert (Hbefore_controlled :
        S.mem owner (R.controlled before) = true).
      { exact (@controlled_steps_monotone tf
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |}
          owner (active_prefix_steps Hdrain_prefix) Hdrain_controlled). }
      assert (Hstart_frame :
        control_frame owner (R.RunRhs fr (tf owner) k) = Some fr).
      { unfold control_frame. destruct (V.eq_dec (R.frame_owner fr) owner);
          congruence. }
      assert (Hcommit_frame :
        control_frame owner (R.RunCommit commit_fr direct k) = Some commit_fr).
      { unfold control_frame.
        destruct (V.eq_dec (R.frame_owner commit_fr) owner); congruence. }
      assert (Howner_drain_frame : control_frame owner
        (R.RunDrain owner_drain_fr k) = Some owner_drain_fr).
      { unfold control_frame.
        destruct (V.eq_dec (R.frame_owner owner_drain_fr) owner); congruence. }
      assert (Hdrain_frame :
        control_frame owner (R.RunDrain drain_fr k) = Some drain_fr).
      { unfold control_frame.
        destruct (V.eq_dec (R.frame_owner drain_fr) owner); congruence. }
      assert (Heval_credit : active_ordinary_credit commit_st
          (R.RunCommit commit_fr direct k) owner <=
        active_ordinary_credit st (R.RunRhs fr (tf owner) k) owner).
      { eapply (@active_prefix_owner_credit_nonincreasing tf roots owner
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |}
          fr Hreachable Heval_prefix).
        - cbn. left. symmetry. exact Hcommit_owner.
        - exact Hstart_frame.
        - exact Hcontrolled. }
      assert (Hset_credit : Credits.ordinary_credit drain_st owner_drain_fr <
        Credits.ordinary_credit commit_st commit_fr).
      { eapply Credits.set_value_changed_credit_decreases;
          [exact Hcommit_controlled_owner |exact Hset |].
        now rewrite Hcommit_owner. }
      assert (Hdrain_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain owner_drain_fr k |}).
      { eapply steps_append_one; [exact Hcommit_reachable |].
        unfold Sem.step. cbn -[R.set_value]. now rewrite Hset. }
      assert (Hdrain_credit : active_ordinary_credit before
          (R.RunDrain drain_fr k) owner <=
        active_ordinary_credit drain_st
          (R.RunDrain owner_drain_fr k) owner).
      { eapply (@active_prefix_owner_credit_nonincreasing tf roots owner
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |}
          owner_drain_fr Hdrain_reachable Hdrain_prefix).
        - cbn. left. symmetry. exact Hdrain_owner.
        - exact Howner_drain_frame.
        - exact Hdrain_controlled. }
      assert (Hstart_credit : active_ordinary_credit st
          (R.RunRhs fr (tf owner) k) owner = Credits.ordinary_credit st fr).
      { unfold active_ordinary_credit. rewrite Hcontrolled, Hstart_frame.
        reflexivity. }
      assert (Hcommit_credit : active_ordinary_credit commit_st
          (R.RunCommit commit_fr direct k) owner =
        Credits.ordinary_credit commit_st commit_fr).
      { unfold active_ordinary_credit.
        rewrite Hcommit_controlled, Hcommit_frame. reflexivity. }
      assert (Howner_drain_credit : active_ordinary_credit drain_st
          (R.RunDrain owner_drain_fr k) owner =
        Credits.ordinary_credit drain_st owner_drain_fr).
      { unfold active_ordinary_credit.
        rewrite Hdrain_controlled, Howner_drain_frame. reflexivity. }
      assert (Hbefore_credit : active_ordinary_credit before
          (R.RunDrain drain_fr k) owner =
        Credits.ordinary_credit before drain_fr).
      { unfold active_ordinary_credit.
        rewrite Hbefore_controlled, Hdrain_frame. reflexivity. }
      assert (Hrerun_credit : active_ordinary_credit
          (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
          (R.cfg_control (executed_rerun tf owner k before drain_fr tail))
          owner = Credits.ordinary_credit before drain_fr).
      { unfold executed_rerun, active_ordinary_credit, control_frame,
          Credits.ordinary_credit, R.fresh_frame, R.with_queue,
          R.sigma_value. cbn. rewrite Hbefore_controlled.
        destruct (V.eq_dec owner owner); [|contradiction].
        now rewrite Hdrain_owner. }
      rewrite Hrerun_credit, Hstart_credit.
      rewrite Hcommit_credit in Heval_credit.
      rewrite Howner_drain_credit, Hbefore_credit in Hdrain_credit.
      lia.
    Qed.

    Lemma active_rerun_pays :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        forall st fr k commit_st commit_fr direct drain_st owner_drain_fr
          before drain_fr tail,
        R.frame_owner fr = owner ->
        queue_strictly_below owner st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} ->
        active_prefix owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        until_owner_commit owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} ->
        R.frame_owner commit_fr = owner ->
        R.set_value commit_st commit_fr direct =
          (drain_st, owner_drain_fr) ->
        R.frame_owner owner_drain_fr = owner ->
        active_prefix owner tf
          {| R.cfg_state := drain_st;
             R.cfg_control := R.RunDrain owner_drain_fr k |}
          {| R.cfg_state := before;
             R.cfg_control := R.RunDrain drain_fr k |} ->
        R.frame_owner drain_fr = owner ->
        R.queue_pop (R.queue before) = Some (owner, tail) ->
        round_payment support owner
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          (executed_rerun tf owner k before drain_fr tail).
    Proof.
      intros support tf roots finite owner Hsupport Howner
        st fr k commit_st commit_fr direct drain_st owner_drain_fr
        before drain_fr tail Hframe Hbelow Hreachable
        Heval_prefix Hfirst_commit Hcommit_owner Hset Howner_drain
        Hdrain_prefix Hdrain_owner Hpop.
      assert (Hcommit_contains :
        control_contains owner (R.RunCommit commit_fr direct k))
        by (cbn; left; symmetry; exact Hcommit_owner).
      assert (Hset_step : Sem.step tf
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain owner_drain_fr k |}).
      { unfold Sem.step. cbn -[R.set_value]. now rewrite Hset. }
      assert (Howner_drain_contains :
        control_contains owner (R.RunDrain owner_drain_fr k))
        by (cbn; left; symmetry; exact Howner_drain).
      assert (Hprefix : active_prefix owner tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := before;
           R.cfg_control := R.RunDrain drain_fr k |}).
      { eapply active_prefix_trans.
        - exact Heval_prefix.
        - exact Hcommit_contains.
        - econstructor; [exact Hcommit_contains |exact Hset_step |].
          eapply active_prefix_trans;
            [constructor |exact Howner_drain_contains |exact Hdrain_prefix]. }
      assert (Hpop_step : Sem.step tf
        {| R.cfg_state := before;
           R.cfg_control := R.RunDrain drain_fr k |}
        (executed_rerun tf owner k before drain_fr tail)).
      { exact (@executed_rerun_step tf owner k before drain_fr tail
          Hdrain_owner Hpop). }
      assert (Hdrain_contains :
        control_contains owner (R.RunDrain drain_fr k))
        by (cbn; left; symmetry; exact Hdrain_owner).
      assert (Hfull : active_prefix owner tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        (executed_rerun tf owner k before drain_fr tail)).
      { eapply active_prefix_trans; [exact Hprefix |exact Hdrain_contains |].
        econstructor; [exact Hdrain_contains |exact Hpop_step |constructor]. }
      pose proof (active_prefix_steps Hfull) as Hsteps.
      assert (Hfinal_contains : control_contains owner
        (R.cfg_control (executed_rerun tf owner k before drain_fr tail)))
        by (unfold executed_rerun; cbn; left; reflexivity).
      pose proof (@unmaterialized_count_steps_nonincreasing support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        (executed_rerun tf owner k before drain_fr tail) Hsteps)
        as Hmaterialized.
      pose proof (@promotion_reserve_steps_nonincreasing tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        (executed_rerun tf owner k before drain_fr tail) owner Hsteps)
        as Hpromotion.
      pose proof (@active_prefix_source_credit_nonincreasing support tf roots
        owner {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |}
        (executed_rerun tf owner k before drain_fr tail)
        Hreachable Hfull Hfinal_contains) as Hsource.
      pose proof (@active_prefix_target_credit_nonincreasing support tf roots
        owner {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |}
        (executed_rerun tf owner k before drain_fr tail)
        Hreachable Hfull Hfinal_contains) as Htarget.
      cbn in Hmaterialized, Hpromotion, Hsource, Htarget.
      unfold round_payment.
      destruct (Nat.eq_dec
        (unmaterialized_count support
          (R.cfg_state (executed_rerun tf owner k before drain_fr tail)))
        (unmaterialized_count support st))
        as [Hmaterialized_eq |Hmaterialized_neq].
      - right. split; [exact Hmaterialized_eq |].
        destruct (Nat.eq_dec
          (promotion_reserve
            (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
            owner) (promotion_reserve st owner))
          as [Hpromotion_eq |Hpromotion_neq].
        + right. split; [exact Hpromotion_eq |].
          destruct (Nat.eq_dec
            (Credits.source_side_credit support
              (R.cfg_state (executed_rerun tf owner k before drain_fr tail))
              owner) (Credits.source_side_credit support st owner))
            as [Hsource_eq |Hsource_neq].
          * right. split; [exact Hsource_eq |].
            destruct (Nat.eq_dec
              (target_side_credit support
                (R.cfg_state
                  (executed_rerun tf owner k before drain_fr tail)) owner)
              (target_side_credit support st owner))
              as [Htarget_eq |Htarget_neq].
            -- right. split; [exact Htarget_eq |].
               eapply (@active_rerun_ordinary_payment support tf roots finite
                 owner Hsupport Howner st fr k commit_st commit_fr direct
                 drain_st owner_drain_fr before drain_fr tail Hframe Hbelow
                 Hreachable Heval_prefix Hfirst_commit Hcommit_owner Hset
                 Howner_drain Hdrain_prefix Hdrain_owner Hpop
                 Hmaterialized_eq Hpromotion_eq Hsource_eq Htarget_eq).
            -- left. unfold executed_rerun in Htarget_neq |- *.
               cbn in Htarget_neq |- *. lia.
          * left. unfold executed_rerun in Hsource_neq |- *.
            cbn in Hsource_neq |- *. lia.
        + left. unfold executed_rerun in Hpromotion_neq |- *.
          cbn in Hpromotion_neq |- *. lia.
      - left. unfold executed_rerun in Hmaterialized_neq |- *.
        cbn in Hmaterialized_neq |- *. lia.
    Qed.

    Lemma run_rhs_reaches_paid_boundary :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        higher_episodes_complete support tf roots owner ->
        forall st fr k,
        R.frame_owner fr = owner ->
        queue_strictly_below owner st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} ->
        exists boundary,
          Sem.steps tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr (tf owner) k |}
            boundary /\
          drain_boundary tf owner k boundary /\
          forall st' fr',
            boundary =
              {| R.cfg_state := st';
                 R.cfg_control := R.RunRhs fr' (tf owner) k |} ->
            round_payment support owner
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |}
              boundary.
    Proof.
      intros support tf roots finite owner Hsupport Howner Hchildren
        st fr k Hframe Hbelow Hreachable.
      assert (Hbody : Sem.rhs_supported (supported support) (tf owner)).
      { unfold supported. rewrite Hsupport. apply Sem.system_supported.
        now rewrite <- Hsupport. }
      destruct (@run_rhs_reaches_executed_round_boundary
        support tf roots finite owner Hsupport Hchildren st fr (tf owner) k
        Hframe Hbody Hreachable)
        as [boundary
          [commit_st [commit_fr [direct
            [drain_st [owner_drain_fr
              [Heval [Hcommit_owner
                [Hset [Howner_drain Hexecuted]]]]]]]]]].
      assert (Hcommit_contains :
        control_contains owner (R.RunCommit commit_fr direct k))
        by (cbn; left; symmetry; exact Hcommit_owner).
      assert (Hset_step : Sem.step tf
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        {| R.cfg_state := drain_st;
           R.cfg_control := R.RunDrain owner_drain_fr k |}).
      { unfold Sem.step. cbn -[R.set_value]. now rewrite Hset. }
      assert (Howner_drain_contains :
        control_contains owner (R.RunDrain owner_drain_fr k))
        by (cbn; left; symmetry; exact Howner_drain).
      assert (Hstart_active : episode_active_control owner k
        (R.RunRhs fr (tf owner) k)) by (cbn; left; auto).
      destruct (@steps_to_episode_boundary owner k tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs fr (tf owner) k |}
        {| R.cfg_state := commit_st;
           R.cfg_control := R.RunCommit commit_fr direct k |}
        Heval Hstart_active)
        as [[exit [Heval_prefix Hexit]] |[Heval_prefix Heval_active]].
      - destruct (@active_exit_is_boundary tf roots owner st fr (tf owner) k
          exit Hframe Hreachable Heval_prefix Hexit)
          as [exit_st [Hexit_shape Hexit_below]].
        subst exit. exists {| R.cfg_state := exit_st;
          R.cfg_control := R.Return k |}. split.
        + exact (active_prefix_steps Heval_prefix).
        + split; [now apply DrainBoundaryReturn |intros st' fr' Hshape;
            discriminate].
      - assert (Hbase_excludes : ~ continuation_contains owner k).
        { intro Hcontains.
          pose proof (reachable_control_ordered Hreachable) as Hordered.
          cbn in Hordered. rewrite Hframe in Hordered.
          pose proof (@continuation_contains_below st owner k owner
            Hordered Hcontains) as Hfalse.
          pose proof (proj1 (@rank_lt_true_ranked
            st owner owner Hfalse)) as Hranked.
          rewrite (@rank_lt_irrefl st owner Hranked) in Hfalse.
          discriminate. }
        assert (Horiginal_commit : owner_commitb owner
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |} = true).
        { unfold owner_commitb. cbn.
          destruct (V.eq_dec (R.frame_owner commit_fr) owner);
            [reflexivity |contradiction]. }
        destruct (@active_prefix_to_first_owner_commit owner tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}
          {| R.cfg_state := commit_st;
             R.cfg_control := R.RunCommit commit_fr direct k |}
          Heval_prefix Horiginal_commit)
          as [first_commit [Hfirst_until Hfirst_prefix]].
        assert (Hfirst_contains :
          control_contains owner (R.cfg_control first_commit)).
        { apply owner_commitb_contains.
          now apply until_owner_commit_final in Hfirst_until. }
        assert (Hfirst_active : episode_active_control owner k
          (R.cfg_control first_commit)).
        { eapply active_prefix_episode_active;
            [exact Hfirst_prefix |exact Hstart_active |exact Hbase_excludes |
             exact Hfirst_contains]. }
        assert (Hfirst_reachable :
          Sem.steps tf (R.initial_config roots) first_commit).
        { eapply steps_transitive; [exact Hreachable |].
          exact (active_prefix_steps Hfirst_prefix). }
        destruct (@active_owner_commit_shape tf roots owner k first_commit
          Hfirst_reachable Hfirst_active (until_owner_commit_final Hfirst_until))
          as [first_st [first_fr [first_direct
            [Hfirst_shape Hfirst_owner]]]].
        subst first_commit.
        destruct (R.set_value first_st first_fr first_direct)
          as [first_drain_st first_drain_fr] eqn:Hfirst_set.
        pose proof (@set_value_owner first_st first_fr first_direct
          first_drain_st first_drain_fr Hfirst_set) as Hfirst_drain_owner0.
        assert (Hfirst_drain_owner :
          R.frame_owner first_drain_fr = owner)
          by (now rewrite Hfirst_drain_owner0, Hfirst_owner).
        assert (Hfirst_set_step : Sem.step tf
          {| R.cfg_state := first_st;
             R.cfg_control := R.RunCommit first_fr first_direct k |}
          {| R.cfg_state := first_drain_st;
             R.cfg_control := R.RunDrain first_drain_fr k |}).
        { unfold Sem.step. cbn -[R.set_value]. now rewrite Hfirst_set. }
        assert (Hfirst_drain_reachable : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := first_drain_st;
             R.cfg_control := R.RunDrain first_drain_fr k |}).
        { eapply steps_append_one; eauto. }
        destruct (@run_drain_reaches_executed_boundary support tf roots finite
          owner Hsupport Hchildren (RankFinite.bound (Sem.support finite))
          (first_drain_st) first_drain_fr k Hfirst_drain_owner
          Hfirst_drain_reachable) as [first_boundary Hfirst_executed].
        { intros next rank Hpeek Hhigher Hlookup.
          eapply reachable_rank_bound; eauto. }
        assert (Hfirst_commit_contains : control_contains owner
          (R.RunCommit first_fr first_direct k))
          by (cbn; left; symmetry; exact Hfirst_owner).
        assert (Hfirst_drain_contains : control_contains owner
          (R.RunDrain first_drain_fr k))
          by (cbn; left; symmetry; exact Hfirst_drain_owner).
        assert (Hfirst_drain_active : episode_active_control owner k
          (R.RunDrain first_drain_fr k)) by (cbn; left; auto).
        destruct Hfirst_executed as
          [final Hreturn Hreturn_below |
           before drain_fr tail Hdrain Hdrain_owner Hpop].
        + exists {| R.cfg_state := final; R.cfg_control := R.Return k |}.
          split.
          * eapply steps_transitive with (middle :=
              {| R.cfg_state := first_st;
                 R.cfg_control := R.RunCommit first_fr first_direct k |}).
            -- exact (active_prefix_steps Hfirst_prefix).
            -- econstructor; [exact Hfirst_set_step |exact Hreturn].
          * split; [now apply DrainBoundaryReturn |intros st' fr' Hshape;
              discriminate].
        + destruct (@steps_to_episode_boundary owner k tf
            {| R.cfg_state := first_drain_st;
               R.cfg_control := R.RunDrain first_drain_fr k |}
            {| R.cfg_state := before;
               R.cfg_control := R.RunDrain drain_fr k |}
            Hdrain Hfirst_drain_active)
            as [[exit [Hdrain_prefix Hexit]] |
                [Hdrain_prefix Hdrain_active]].
          * assert (Hcombined : active_prefix owner tf
              {| R.cfg_state := st;
                 R.cfg_control := R.RunRhs fr (tf owner) k |} exit).
            { eapply active_prefix_trans.
              - exact Hfirst_prefix.
              - exact Hfirst_commit_contains.
              - econstructor;
                  [exact Hfirst_commit_contains |exact Hfirst_set_step |].
                eapply active_prefix_trans;
                  [constructor |exact Hfirst_drain_contains |
                   exact Hdrain_prefix]. }
            destruct (@active_exit_is_boundary tf roots owner st fr
              (tf owner) k exit Hframe Hreachable Hcombined Hexit)
              as [exit_st [Hexit_shape Hexit_below]].
            subst exit. exists {| R.cfg_state := exit_st;
              R.cfg_control := R.Return k |}. split.
            -- exact (active_prefix_steps Hcombined).
            -- split; [now apply DrainBoundaryReturn |intros st' fr' Hshape;
                 discriminate].
          * exists (executed_rerun tf owner k before drain_fr tail). split.
            -- eapply steps_transitive with (middle :=
                 {| R.cfg_state := first_st;
                    R.cfg_control := R.RunCommit first_fr first_direct k |}).
               ++ exact (active_prefix_steps Hfirst_prefix).
               ++ econstructor; [exact Hfirst_set_step |].
                  eapply steps_append_one;
                    [exact (active_prefix_steps Hdrain_prefix) |
                     exact (@executed_rerun_step tf owner k before drain_fr
                       tail Hdrain_owner Hpop)].
            -- split.
               ++ apply DrainBoundaryRerun.
                  ** unfold executed_rerun. cbn. reflexivity.
                  ** unfold executed_rerun. cbn.
                     apply with_queue_strictly_below.
                     --- pose proof (@steps_transitive tf
                           (R.initial_config roots)
                           {| R.cfg_state := first_drain_st;
                              R.cfg_control := R.RunDrain first_drain_fr k |}
                           {| R.cfg_state := before;
                              R.cfg_control := R.RunDrain drain_fr k |}
                           Hfirst_drain_reachable
                           (active_prefix_steps Hdrain_prefix)) as Hbefore.
                         exact (configuration_queue_ordered
                           (reachable_configuration_ranked Hbefore)).
                     --- exact Hpop.
               ++ intros st' fr' Hshape.
                  eapply (@active_rerun_pays support tf roots finite owner
                    Hsupport Howner st fr k first_st first_fr first_direct
                    first_drain_st first_drain_fr before drain_fr tail
                    Hframe Hbelow Hreachable Hfirst_prefix Hfirst_until
                    Hfirst_owner Hfirst_set Hfirst_drain_owner Hdrain_prefix
                    Hdrain_owner Hpop).
    Qed.

    Definition owner_round_complete
      (support : list V.t) (tf : R.ConstraintSystem.system)
      (roots : list V.t) (owner : V.t) (entry : nat * R.config) : Prop :=
      forall first st fr k,
        entry = (first,
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}) ->
        R.frame_owner fr = owner ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} ->
        (first = 0 -> queue_strictly_below owner st) ->
        episode_complete tf owner k
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |}.

    Lemma owner_rounds_complete :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        higher_episodes_complete support tf roots owner ->
        forall entry, owner_round_complete support tf roots owner entry.
    Proof.
      intros support tf roots finite owner Hsupport Howner Hchildren.
      apply (well_founded_induction_type
        (owner_round_measure_lt_well_founded support owner)).
      intros [budget c] IH. unfold owner_round_complete.
      intros first st fr k Hentry Hframe Hreachable Hbelow.
      inversion Hentry; subst budget c; clear Hentry.
      assert (Hbody : Sem.rhs_supported (supported support) (tf owner)).
      { unfold supported. rewrite Hsupport. apply Sem.system_supported.
        now rewrite <- Hsupport. }
      assert (Hresult : exists boundary,
        Sem.steps tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs fr (tf owner) k |} boundary /\
        drain_boundary tf owner k boundary /\
        forall st' fr', boundary =
          {| R.cfg_state := st';
             R.cfg_control := R.RunRhs fr' (tf owner) k |} ->
          first = 0 -> round_payment support owner
            {| R.cfg_state := st;
               R.cfg_control := R.RunRhs fr (tf owner) k |} boundary).
      { destruct first as [|first].
        - destruct (@run_rhs_reaches_paid_boundary support tf roots finite
            owner Hsupport Howner Hchildren st fr k Hframe (Hbelow eq_refl)
            Hreachable) as [boundary [Hsteps [Hboundary Hpayment]]].
          exists boundary. repeat split; try assumption.
          intros st' fr' Hshape _. exact (Hpayment st' fr' Hshape).
        - destruct (@run_rhs_reaches_boundary support tf roots finite owner
            Hsupport Hchildren st fr (tf owner) k Hframe Hbody Hreachable)
            as [boundary [Hsteps Hboundary]].
          exists boundary. repeat split; try assumption.
          intros st' fr' Hshape Hzero. discriminate. }
      destruct Hresult as [boundary [Hsteps [Hboundary Hpayment]]].
      destruct Hboundary as
        [final Hfinal_below |final next_fr Hnext_frame Hfinal_below].
      - exists final. split; assumption.
      - set (next := {| R.cfg_state := final;
          R.cfg_control := R.RunRhs next_fr (tf owner) k |}).
        assert (Hnext_reachable :
          Sem.steps tf (R.initial_config roots) next).
        { unfold next. eapply steps_transitive; eauto. }
        assert (Hdecrease : owner_round_measure_lt support owner (0, next)
          (first, {| R.cfg_state := st;
            R.cfg_control := R.RunRhs fr (tf owner) k |})).
        { destruct first as [|first].
          - apply round_payment_decreases. eapply Hpayment; reflexivity.
          - apply positive_round_decreases. lia. }
        specialize (IH (0, next) Hdecrease).
        unfold owner_round_complete in IH.
        destruct (IH 0 final next_fr k eq_refl Hnext_frame Hnext_reachable
          (fun _ => Hfinal_below)) as [done [Hdone Hdone_below]].
        exists done. split.
        + unfold next in Hdone. eapply steps_transitive; eauto.
        + exact Hdone_below.
    Qed.

    Lemma start_episode_complete :
      forall support tf roots
        (finite : Sem.finite_system tf roots) owner,
        support = Sem.support finite ->
        List.In owner support ->
        higher_episodes_complete support tf roots owner ->
        forall st k,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.StartEpisode owner k |} ->
        episode_complete tf owner k
          {| R.cfg_state := st;
             R.cfg_control := R.StartEpisode owner k |}.
    Proof.
      intros support tf roots finite owner Hsupport Howner Hchildren
        st k Hreachable.
      set (st1 := R.materialize st owner).
      set (fr := R.fresh_frame st1 owner (U.initial_phase false owner)).
      set (started := {| R.cfg_state := st1;
        R.cfg_control := R.RunRhs fr (tf owner) k |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.StartEpisode owner k |} started).
      { unfold Sem.step, started, st1, fr. cbn. reflexivity. }
      assert (Hstarted_reachable :
        Sem.steps tf (R.initial_config roots) started).
      { eapply steps_append_one; eauto. }
      assert (Hfr : R.frame_owner fr = owner).
      { unfold fr, R.fresh_frame. reflexivity. }
      pose proof (@owner_rounds_complete support tf roots finite owner
        Hsupport Howner Hchildren (1, started)) as Hcomplete.
      unfold owner_round_complete in Hcomplete.
      destruct (Hcomplete 1 st1 fr k eq_refl Hfr Hstarted_reachable
        (fun Hzero => ltac:(discriminate))) as [final [Hround Hbelow]].
      exists final. split.
      - econstructor; [exact Hstep |exact Hround].
      - exact Hbelow.
    Qed.

    Lemma reachable_steps_comparable :
      forall tf origin left right,
        Sem.steps tf origin left ->
        Sem.steps tf origin right ->
        Sem.steps tf left right \/ Sem.steps tf right left.
    Proof.
      intros tf origin left right Hleft. revert right.
      induction Hleft as [origin |origin next left Hstep Htail IH];
        intros right Hright.
      - now left.
      - inversion Hright as [|origin0 next0 right0 Hstep0 Htail0]; subst.
        + right. econstructor; eauto.
        + assert (Heq : next = next0).
          { unfold Sem.step in Hstep, Hstep0. congruence. }
          subst next0. now apply IH.
    Qed.

    Lemma reachable_rank_lookup_agree :
      forall tf roots left right x left_rank right_rank,
        Sem.steps tf (R.initial_config roots) left ->
        Sem.steps tf (R.initial_config roots) right ->
        R.Ranking.lookup (R.ranking (R.cfg_state left)) x = Some left_rank ->
        R.Ranking.lookup (R.ranking (R.cfg_state right)) x = Some right_rank ->
        left_rank = right_rank.
    Proof.
      intros tf roots left right x left_rank right_rank Hleft Hright
        Hleft_lookup Hright_lookup.
      destruct (@reachable_steps_comparable tf (R.initial_config roots)
        left right Hleft Hright) as [Hlr |Hrl].
      - pose proof ((steps_rank_extends Hlr) x left_rank Hleft_lookup)
          as Hlookup. rewrite Hright_lookup in Hlookup. now inversion Hlookup.
      - pose proof ((steps_rank_extends Hrl) x right_rank Hright_lookup)
          as Hlookup. rewrite Hleft_lookup in Hlookup. now inversion Hlookup.
    Qed.

    Definition ranked_episode_property
      (tf : R.ConstraintSystem.system) (roots : list V.t)
      (finite : Sem.finite_system tf roots) (rank : nat) : Prop :=
      forall owner k start,
        List.In owner (Sem.support finite) ->
        Sem.steps tf (R.initial_config roots) start ->
        R.cfg_control start = R.StartEpisode owner k ->
        R.Ranking.lookup (R.ranking (R.cfg_state start)) owner = Some rank ->
        episode_complete tf owner k start.

    Theorem all_episodes_complete :
      forall tf roots (finite : Sem.finite_system tf roots) owner k start,
        List.In owner (Sem.support finite) ->
        Sem.steps tf (R.initial_config roots) start ->
        R.cfg_control start = R.StartEpisode owner k ->
        episode_complete tf owner k start.
    Proof.
      intros tf roots finite.
      assert (Hall : forall rank,
        @ranked_episode_property tf roots finite rank).
      { apply (well_founded_induction_type
          (well_founded_ltof nat
            (fun rank => RankFinite.bound (Sem.support finite) - rank))).
        intros rank IH. unfold ranked_episode_property.
        intros owner k start Howner Hreachable Hcontrol Howner_lookup.
        destruct start as [st control]. cbn in Hcontrol, Howner_lookup.
        subst control.
        eapply start_episode_complete with
          (support := Sem.support finite) (finite := finite); eauto.
        intros target child_k child Htarget Hhigher Hchild Hchild_control.
        assert (Htarget_ranked : ranked (R.cfg_state child) target).
        { exact (proj2 (@rank_lt_true_ranked (R.cfg_state child)
            owner target Hhigher)). }
        destruct Htarget_ranked as [target_rank Htarget_lookup].
        assert (Howner_child_ranked : ranked (R.cfg_state child) owner).
        { exact (proj1 (@rank_lt_true_ranked (R.cfg_state child)
            owner target Hhigher)). }
        destruct Howner_child_ranked as [child_owner_rank Hchild_owner_lookup].
        assert (Howner_rank : child_owner_rank = rank).
        { symmetry. exact (@reachable_rank_lookup_agree tf roots
            {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |}
            child owner rank child_owner_rank Hreachable Hchild
            Howner_lookup Hchild_owner_lookup). }
        subst child_owner_rank.
        assert (Hstrict : rank < target_rank).
        { unfold R.rank_lt, R.ranking_lt in Hhigher.
          rewrite Hchild_owner_lookup, Htarget_lookup in Hhigher.
          now apply Nat.ltb_lt. }
        assert (Hbound : target_rank < RankFinite.bound (Sem.support finite)).
        { eapply reachable_rank_bound; eauto. }
        eapply (IH target_rank); eauto. unfold ltof. lia. }
      intros owner k start Howner Hreachable Hcontrol.
      pose proof (reachable_configuration_ranked Hreachable) as Hranked.
      pose proof (configuration_control_ranked Hranked) as Hcontrol_ranked.
      unfold control_ranked in Hcontrol_ranked.
      rewrite Hcontrol in Hcontrol_ranked. cbn in Hcontrol_ranked.
      destruct Hcontrol_ranked as [[rank Hlookup] _].
      eapply Hall; eauto.
    Qed.

    Definition base_continuation (mode : option (list V.t)) : R.continuation :=
      match mode with None => R.KLoop | Some rest => R.KSeedLoop rest end.

    Definition base_control (mode : option (list V.t)) : R.control :=
      match mode with None => R.RunLoop | Some rest => R.RunSeedLoop rest end.

    Lemma queue_pop_member :
      forall queue owner tail,
        R.queue_pop queue = Some (owner, tail) -> List.In owner queue.
    Proof.
      intros queue owner tail Hpop. destruct queue as [|head rest];
        cbn in Hpop; try discriminate. inversion Hpop. now left.
    Qed.

    Lemma rank_lt_lookup_nat :
      forall st x y xrank yrank,
        R.Ranking.lookup (R.ranking st) x = Some xrank ->
        R.Ranking.lookup (R.ranking st) y = Some yrank ->
        R.rank_lt st x y = true -> xrank < yrank.
    Proof.
      intros st x y xrank yrank Hx Hy Hlt.
      unfold R.rank_lt, R.ranking_lt in Hlt.
      rewrite Hx, Hy in Hlt. now apply Nat.ltb_lt.
    Qed.

    Lemma popped_episode_complete :
      forall tf roots (finite : Sem.finite_system tf roots) mode st owner tail,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := base_control mode |} ->
        R.queue_pop (R.queue st) = Some (owner, tail) ->
        exists done,
          Sem.steps tf
            {| R.cfg_state := st; R.cfg_control := base_control mode |}
            {| R.cfg_state := done; R.cfg_control := base_control mode |} /\
          queue_strictly_below owner done.
    Proof.
      intros tf roots finite mode st owner tail Hreachable Hpop.
      assert (Howner : List.In owner (Sem.support finite)).
      { pose proof (reachable_config_supported finite Hreachable) as [Hstate _].
        apply (state_queue_supported Hstate). cbn.
        exact (@queue_pop_member (R.queue st) owner tail Hpop). }
      set (child := {| R.cfg_state := R.with_queue st tail;
        R.cfg_control := R.StartEpisode owner (base_continuation mode) |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st; R.cfg_control := base_control mode |} child).
      { unfold Sem.step, child, base_control, base_continuation.
        destruct mode; cbn; rewrite Hpop; reflexivity. }
      assert (Hchild : Sem.steps tf (R.initial_config roots) child).
      { eapply steps_append_one; eauto. }
      destruct (@all_episodes_complete tf roots finite owner
        (base_continuation mode) child Howner Hchild eq_refl)
        as [done [Hepisode Hbelow]].
      assert (Hreturn : Sem.step tf
        {| R.cfg_state := done;
           R.cfg_control := R.Return (base_continuation mode) |}
        {| R.cfg_state := done; R.cfg_control := base_control mode |}).
      { unfold Sem.step, base_continuation, base_control.
        destruct mode; reflexivity. }
      exists done. split; [|exact Hbelow].
      econstructor; [exact Hstep |].
      eapply steps_transitive; [exact Hepisode |]. apply one_step. exact Hreturn.
    Qed.

    Definition drain_below_rank_property
      (tf : R.ConstraintSystem.system) (roots : list V.t)
      (finite : Sem.finite_system tf roots) (rank : nat) : Prop :=
      forall upper mode st,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := base_control mode |} ->
        R.Ranking.lookup (R.ranking st) upper = Some rank ->
        queue_strictly_below upper st ->
        exists final,
          Sem.steps tf
            {| R.cfg_state := st; R.cfg_control := base_control mode |}
            {| R.cfg_state := final; R.cfg_control := base_control mode |} /\
          R.queue_pop (R.queue final) = None.

    Theorem drain_below_rank_complete :
      forall tf roots (finite : Sem.finite_system tf roots) rank,
        @drain_below_rank_property tf roots finite rank.
    Proof.
      intros tf roots finite rank. induction rank using lt_wf_ind.
      unfold drain_below_rank_property.
      intros upper mode st Hreachable Hupper_lookup Hbelow.
      destruct (R.queue_pop (R.queue st)) as [[owner tail] |] eqn:Hpop.
      - assert (Hmember : List.In owner (R.queue st))
          by exact (@queue_pop_member (R.queue st) owner tail Hpop).
        pose proof (Hbelow owner Hmember) as Hlower.
        pose proof (reachable_configuration_ranked Hreachable) as Hranked.
        destruct ((data_queue_ranked (configuration_state_data Hranked))
          owner Hmember) as [owner_rank Howner_lookup].
        assert (Hrank_lt : owner_rank < rank).
        { eapply rank_lt_lookup_nat; eauto. }
        destruct (@popped_episode_complete tf roots finite mode st owner tail
          Hreachable Hpop) as [done [Hepisode Hdone_below]].
        assert (Hdone_reachable : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := done; R.cfg_control := base_control mode |}).
        { eapply steps_transitive; eauto. }
        assert (Hdone_lookup :
          R.Ranking.lookup (R.ranking done) owner = Some owner_rank).
        { exact ((steps_rank_extends Hepisode) owner owner_rank Howner_lookup). }
        destruct (H owner_rank Hrank_lt owner mode done Hdone_reachable
          Hdone_lookup Hdone_below) as [final [Hrest Hempty]].
        exists final. split; [eapply steps_transitive; eauto |exact Hempty].
      - exists st. split; [constructor |exact Hpop].
    Qed.

    Theorem drain_queue_complete :
      forall tf roots (finite : Sem.finite_system tf roots) mode st,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := base_control mode |} ->
        exists final,
          Sem.steps tf
            {| R.cfg_state := st; R.cfg_control := base_control mode |}
            {| R.cfg_state := final; R.cfg_control := base_control mode |} /\
          R.queue_pop (R.queue final) = None.
    Proof.
      intros tf roots finite mode st Hreachable.
      destruct (R.queue_pop (R.queue st)) as [[owner tail] |] eqn:Hpop.
      - assert (Hmember : List.In owner (R.queue st))
          by exact (@queue_pop_member (R.queue st) owner tail Hpop).
        pose proof (reachable_configuration_ranked Hreachable) as Hranked.
        destruct ((data_queue_ranked (configuration_state_data Hranked))
          owner Hmember) as [owner_rank Howner_lookup].
        destruct (@popped_episode_complete tf roots finite mode st owner tail
          Hreachable Hpop) as [done [Hepisode Hdone_below]].
        assert (Hdone_reachable : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := done; R.cfg_control := base_control mode |}).
        { eapply steps_transitive; eauto. }
        assert (Hdone_lookup :
          R.Ranking.lookup (R.ranking done) owner = Some owner_rank).
        { exact ((steps_rank_extends Hepisode) owner owner_rank Howner_lookup). }
        destruct (@drain_below_rank_complete tf roots finite owner_rank owner
          mode done Hdone_reachable Hdone_lookup Hdone_below)
          as [final [Hrest Hempty]].
        exists final. split; [eapply steps_transitive; eauto |exact Hempty].
      - exists st. split; [constructor |exact Hpop].
    Qed.

    Theorem seeds_reach_terminal :
      forall tf roots (finite : Sem.finite_system tf roots) remaining st,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |} ->
        exists final,
          Sem.steps tf
            {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |}
            (Sem.terminal_config final) /\ Sem.quiescent final.
    Proof.
      intros tf roots finite remaining. induction remaining as [|root rest IH];
        intros st Hreachable.
      - assert (Hstep : Sem.step tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds [] |}
          {| R.cfg_state := st; R.cfg_control := base_control None |})
          by reflexivity.
        assert (Hloop : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := base_control None |}).
        { eapply steps_append_one; eauto. }
        destruct (@drain_queue_complete tf roots finite None st Hloop)
          as [final [Hdrain Hempty]].
        exists final. split.
        + econstructor; [exact Hstep |exact Hdrain].
        + unfold Sem.quiescent, R.queue_peek, R.queue_pop in *.
          destruct (R.queue final); [reflexivity |discriminate].
      - set (observed := R.observe st root).
        destruct (R.is_materialized observed root) eqn:Hmaterialized.
        + assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunSeeds (root :: rest) |}
            {| R.cfg_state := observed;
               R.cfg_control := R.RunSeeds rest |}).
          { unfold Sem.step, observed. cbn.
            unfold observed in Hmaterialized. now rewrite Hmaterialized. }
          assert (Hnext : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := observed; R.cfg_control := R.RunSeeds rest |}).
          { eapply steps_append_one; eauto. }
          destruct (IH observed Hnext) as [final [Hrest Hquiet]].
          exists final. split; [econstructor; eauto |exact Hquiet].
        + assert (Hroot : List.In root (Sem.support finite)).
          { pose proof (reachable_config_supported finite Hreachable)
              as [_ Hcontrol]. cbn in Hcontrol. inversion Hcontrol; assumption. }
          set (child := {| R.cfg_state := observed;
            R.cfg_control := R.StartEpisode root (R.KSeedLoop rest) |}).
          assert (Hstep : Sem.step tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunSeeds (root :: rest) |} child).
          { unfold Sem.step, child, observed. cbn.
            unfold observed in Hmaterialized. now rewrite Hmaterialized. }
          assert (Hchild : Sem.steps tf (R.initial_config roots) child).
          { eapply steps_append_one; eauto. }
          destruct (@all_episodes_complete tf roots finite root
            (R.KSeedLoop rest) child Hroot Hchild eq_refl)
            as [done [Hepisode Hbelow]].
          assert (Hreturn : Sem.step tf
            {| R.cfg_state := done;
               R.cfg_control := R.Return (R.KSeedLoop rest) |}
            {| R.cfg_state := done;
               R.cfg_control := base_control (Some rest) |}) by reflexivity.
          assert (Hbase : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := done;
               R.cfg_control := base_control (Some rest) |}).
          { eapply steps_transitive; [exact Hchild |].
            eapply steps_transitive; [exact Hepisode |].
            apply one_step. exact Hreturn. }
          destruct (@drain_queue_complete tf roots finite (Some rest)
            done Hbase) as [drained [Hdrain Hempty]].
          assert (Hadmin : Sem.step tf
            {| R.cfg_state := drained;
               R.cfg_control := base_control (Some rest) |}
            {| R.cfg_state := drained;
               R.cfg_control := R.RunSeeds rest |}).
          { unfold Sem.step, base_control. cbn. rewrite Hempty. reflexivity. }
          assert (Hnext : Sem.steps tf (R.initial_config roots)
            {| R.cfg_state := drained; R.cfg_control := R.RunSeeds rest |}).
          { eapply steps_append_one.
            - eapply steps_transitive; [exact Hbase |exact Hdrain].
            - exact Hadmin. }
          destruct (IH drained Hnext) as [final [Hrest Hquiet]].
          exists final. split; [|exact Hquiet].
          econstructor; [exact Hstep |].
          eapply steps_transitive; [exact Hepisode |].
          econstructor; [exact Hreturn |].
          eapply steps_transitive; [exact Hdrain |]. econstructor; eauto.
    Qed.

    Theorem solver_reaches_terminal :
      forall tf roots (finite : Sem.finite_system tf roots),
        exists final,
          Sem.steps tf (R.initial_config roots) (Sem.terminal_config final) /\
          Sem.quiescent final.
    Proof.
      intros tf roots finite. apply (@seeds_reach_terminal tf roots finite roots
        (R.cfg_state (R.initial_config roots))).
      change (Sem.steps tf (R.initial_config roots) (R.initial_config roots)).
      constructor.
    Qed.

    Theorem solver_terminates :
      forall tf roots,
        Sem.finite_system tf roots ->
        exists final, Sem.terminates_to tf roots final.
    Proof.
      intros tf roots finite. exact (@solver_reaches_terminal tf roots finite).
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
    inversion Hterminal; subst. split; [reflexivity |exact Hqueue].
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

  Theorem solver_terminates :
    forall tf roots,
      Sem.finite_system tf roots ->
      exists final, Sem.terminates_to tf roots final.
  Proof. exact Termination.solver_terminates. Qed.

  Lemma terminal_config_stuck :
    forall tf final,
      Sem.quiescent final ->
      R.next_config tf (Sem.terminal_config final) = None.
  Proof.
    intros tf final Hquiet. unfold Sem.quiescent in Hquiet.
    cbn. unfold R.queue_peek in Hquiet.
    destruct (R.queue final); [reflexivity |discriminate].
  Qed.

  Lemma steps_have_fuel :
    forall tf first final,
      Sem.steps tf first final ->
      R.next_config tf final = None ->
      exists fuel, R.run_fuel fuel tf first = final.
  Proof.
    intros tf first final Hsteps. induction Hsteps; intros Hstuck.
    - exists 0. reflexivity.
    - destruct (IHHsteps Hstuck) as [fuel Hfuel].
      exists (S fuel). cbn. rewrite H. exact Hfuel.
  Qed.

  Lemma terminates_to_has_fuel :
    forall tf roots final,
      Sem.terminates_to tf roots final ->
      exists fuel, R.solve_fuel fuel tf roots = Some final.
  Proof.
    intros tf roots final [Hsteps Hquiet].
    destruct (@steps_have_fuel tf _ _ Hsteps
      (@terminal_config_stuck tf final Hquiet)) as [fuel Hfuel].
    exists fuel. unfold R.solve_fuel. rewrite Hfuel. cbn.
    unfold Sem.quiescent in Hquiet. now rewrite Hquiet.
  Qed.

  Theorem sufficient_fuel :
    forall tf roots,
      Sem.finite_system tf roots ->
      exists fuel final, R.solve_fuel fuel tf roots = Some final.
  Proof.
    intros tf roots Hfinite.
    destruct (@solver_terminates tf roots Hfinite) as [final Hterminates].
    destruct (@terminates_to_has_fuel tf roots final Hterminates)
      as [fuel Hfuel]. now exists fuel, final.
  Qed.

  Section Correctness.

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
        rhs_trace next direct reads effects ->
        rhs_trace (R.ConstraintSystem.Spawn target next)
          direct reads effects.

    Definition reads_agree
      (st : R.state) (reads : list (V.t * D.t)) : Prop :=
      forall target value, List.In (target, value) reads ->
        M.lookup (R.sigma st) target = Some value.

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
        | Hleft : M.lookup _ _ = Some _,
          Hright : M.lookup _ _ = Some _ |- _ =>
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
      List.In x (R.queue st).

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
      intros st x Hquiet Hin. unfold Sem.quiescent, R.queue_peek in Hquiet.
      destruct (R.queue st) as [|head tail] eqn:Hqueue.
      - unfold queued in Hin. rewrite Hqueue in Hin. contradiction.
      - discriminate Hquiet.
    Qed.

    Lemma guarded_reads_agree :
      forall st owner reads,
        Sem.quiescent st -> guarded_reads st owner reads ->
        reads_agree st reads.
    Proof.
      intros st owner reads Hquiet Hguard target value Hin.
      destruct (Hguard target value Hin)
        as [[current Hlookup] [_ [Hequal |Hqueued]]].
      - unfold R.sigma_value in Hequal.
        rewrite Hlookup in Hequal. cbn in Hequal. subst. exact Hlookup.
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
      rewrite (proj1 (observe_solver_view st x)). exact Hlookup.
    Qed.

    Lemma queued_observe :
      forall st x owner, queued st owner -> queued (R.observe st x) owner.
    Proof.
      intros st x owner Hqueued. unfold queued in *.
      rewrite (proj1 (proj2 (observe_solver_view st x))). exact Hqueued.
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
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [next_phase contribution] eqn:Hupdate.
      inversion Hwrite; subst next changed. rewrite aggregate_register_reset.
      eapply DL.leq_trans.
      - pose proof (UL.update_sound true target
          (R.side_phase
            (R.stored_side_cell base (R.frame_owner fr) target))
          (R.stored_contribution base (R.frame_owner fr) target) input)
          as Hsound. rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
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
            -- pose proof (UL.update_sound false owner
                 (R.frame_phase fr) old candidate) as Hsound.
               rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
            -- unfold R.equivalent in Hvalue.
               apply Bool.andb_true_iff in Hvalue. exact (proj1 Hvalue).
          * inversion Hset; subst.
            rewrite sigma_value_with_readers, sigma_value_enqueue_all,
              sigma_value_update_same.
            pose proof (UL.update_sound false owner
              (R.frame_phase fr) old candidate) as Hsound.
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
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
        as [next_phase contribution] eqn:Hupdate.
      inversion Hwrite; subst next changed. exists contribution. split.
      - rewrite contributions_register_reset. apply lookup_update_map_same.
      - pose proof (UL.update_sound true target
          (R.side_phase
            (R.stored_side_cell base (R.frame_owner fr) target))
          (R.stored_contribution base (R.frame_owner fr) target) input)
          as Hsound. rewrite Hupdate in Hsound. cbn in Hsound. exact Hsound.
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
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input).
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
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input).
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
      R.queue after = R.queue before.

    Definition same_solver_view (before after : R.state) : Prop :=
      same_read_view before after /\
      R.contributions after = R.contributions before.

    Lemma same_read_view_trans :
      forall first middle last,
        same_read_view first middle -> same_read_view middle last ->
        same_read_view first last.
    Proof.
      intros first middle last [Hs1 [Hr1 Hq1]] [Hs2 [Hr2 Hq2]].
      repeat split; congruence.
    Qed.

    Lemma same_read_view_observe :
      forall st x, same_read_view st (R.observe st x).
    Proof.
      intros st x. destruct (observe_solver_view st x)
        as [Hsigma [Hqueue [Hreaders _]]].
      unfold same_read_view. repeat split; assumption.
    Qed.

    Lemma guarded_reads_same_view :
      forall before after owner reads,
        same_read_view before after ->
        guarded_reads before owner reads ->
        guarded_reads after owner reads.
    Proof.
      intros before after owner reads [Hsigma [Hreaders Hqueue]]
        Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split.
      - destruct Hsolved as [current Hlookup]. exists current. now rewrite Hsigma.
      - split.
        + destruct Hreader as [Hreader |Hqueued].
          * left. unfold R.lookup_set. now rewrite Hreaders.
          * right. unfold queued in *. now rewrite Hqueue.
        + destruct Hvalue as [Hvalue |Hqueued].
          * left. unfold R.sigma_value in *. now rewrite Hsigma.
          * right. unfold queued in *. now rewrite Hqueue.
    Qed.

    Lemma write_side_contribution_same_read_view :
      forall st fr target input next changed,
        R.write_side_contribution st fr target input = (next, changed) ->
        same_read_view st next.
    Proof.
      intros st fr target input next changed Hwrite.
      unfold R.write_side_contribution in Hwrite.
      set (base := R.promote_side_target st fr target) in *.
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
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
      intros before after x [[Hsigma _] _] [value Hlookup].
      exists value. now rewrite Hsigma.
    Qed.

    Lemma solved_same_solver_view_back :
      forall before after x,
        same_solver_view before after ->
        Sem.solved after x -> Sem.solved before x.
    Proof.
      intros before after x [[Hsigma _] _] [value Hlookup].
      exists value. now rewrite Hsigma in Hlookup.
    Qed.

    Lemma queued_same_solver_view :
      forall before after x,
        same_solver_view before after -> queued before x -> queued after x.
    Proof.
      intros before after x [[_ [_ Hqueue]] _] Hqueued.
      unfold queued in *. now rewrite Hqueue.
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

    Definition add_reader
      (st : R.state) (target owner : V.t) : R.state :=
      R.with_readers st (M.update (R.readers st) target
        (S.add owner (R.lookup_set (R.readers st) target))).

    Lemma guarded_reads_enqueue :
      forall st inserted owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.enqueue st inserted) owner reads.
    Proof.
      intros st inserted owner reads Hguard target value Hin.
      destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
      split; [exact Hsolved |]. split.
      - destruct Hreader as [Hreader |Hqueued]; [now left |right].
        unfold queued in *. cbn. apply queue_insert_members. now right.
      - destruct Hvalue as [Hvalue |Hqueued]; [now left |right].
        unfold queued in *. cbn. apply queue_insert_members. now right.
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
      - destruct Hreader as [Hreader |Hqueued]; [now left |right].
        unfold queued in *. cbn. eapply Htail; eauto.
      - destruct Hvalue as [Hvalue |Hqueued]; [now left |right].
        unfold queued in *. cbn. eapply Htail; eauto.
    Qed.

    Lemma guarded_reads_materialize :
      forall st inserted owner reads,
        guarded_reads st owner reads ->
        guarded_reads (R.materialize st inserted) owner reads.
    Proof.
      intros st inserted owner reads Hguard. unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted) as [current |] eqn:Hinserted.
      - exact Hguard.
      - intros target value Hin.
        destruct (Hguard target value Hin) as [Hsolved [Hreader Hvalue]].
        assert (Hneq : target <> inserted).
        { intro Heq. subst. destruct Hsolved as [found Hfound].
          rewrite Hinserted in Hfound. discriminate. }
        split.
        + destruct Hsolved as [found Hfound]. exists found. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hfound.
        + split; [exact Hreader |].
          destruct Hvalue as [Hequal |Hqueued]; [left |now right].
          unfold R.sigma_value in *. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Hequal.
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
        + exists value. cbn. apply ML.lookup_update_same.
        + exists current. cbn. rewrite ML.lookup_update_other by exact Hneq.
          exact Hlookup.
      - cbn. split.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * right. unfold queued. cbn. apply queue_insert_all_members.
            destruct Hreader as [Hmember |Hqueued].
            -- left. apply SL.mem_spec. exact Hmember.
            -- now right.
          * destruct Hreader as [Hmember |Hqueued].
            -- left. unfold R.lookup_set in *.
               rewrite ML.lookup_update_other by exact Hneq. exact Hmember.
            -- right. unfold queued in *. cbn. apply queue_insert_all_members.
               now right.
        + destruct (V.eq_dec target owner) as [-> |Hneq].
          * right. unfold queued. cbn. apply queue_insert_all_members.
            destruct Hreader as [Hmember |Hqueued].
            -- left. apply SL.mem_spec. exact Hmember.
            -- now right.
          * destruct Hvalue as [Hequal |Hqueued].
            -- left. unfold R.sigma_value in *. cbn.
               rewrite ML.lookup_update_other by exact Hneq. exact Hequal.
            -- right. unfold queued in *. cbn. apply queue_insert_all_members.
               now right.
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
      all: try (eexists; cbn; apply ML.lookup_update_same).
      all: exists current; cbn;
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
        [now right |left; exists current; cbn in Hlookup;
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

    Definition rhs_context
      (root current : R.ConstraintSystem.rhs)
      (prefix_reads prefix_effects : list (V.t * D.t)) : Prop :=
      forall direct reads effects,
        rhs_trace current direct reads effects ->
        rhs_trace root direct
          (prefix_reads ++ reads) (prefix_effects ++ effects).

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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hread). exact Hlookup.
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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hread). exact Hlookup.
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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hread). exact Hlookup.
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
      intros st x. destruct (observe_solver_view st x)
        as [Hsigma [Hqueue [Hreaders Hcontributions]]].
      split; [repeat split; assumption |exact Hcontributions].
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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hview). exact Hlookup.
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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hview). exact Hlookup.
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
      - destruct Hsolved as [value Hlookup]. exists value.
        rewrite (proj1 Hview). exact Hlookup.
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
      intros st x. unfold Sem.solved, R.materialize.
      destruct (M.lookup (R.sigma st) x) as [value|] eqn:Hlookup.
      - now exists value.
      - exists D.bottom. cbn. apply ML.lookup_update_same.
    Qed.

    Lemma materialize_preserves_solved :
      forall st inserted x,
        Sem.solved st x -> Sem.solved (R.materialize st inserted) x.
    Proof.
      intros st inserted x [value Hlookup]. unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted) eqn:Hinserted.
      - now exists value.
      - destruct (V.eq_dec x inserted) as [-> | Hneq].
        + rewrite Hinserted in Hlookup. discriminate.
        + exists value. cbn.
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
      assert (Hneq : x <> inserted).
      { intro Heq. subst. rewrite Hinserted in Hlookup. discriminate. }
      unfold R.sigma_value. cbn.
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

    Lemma initial_rhs_context :
      forall body, rhs_context body body [] [].
    Proof. intros body direct reads effects Htrace. exact Htrace. Qed.

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

    Lemma rhs_context_get :
      forall root target next prefix_reads prefix_effects value,
        rhs_context root (R.ConstraintSystem.Get target next)
          prefix_reads prefix_effects ->
        rhs_context root (next value)
          (prefix_reads ++ [(target, value)]) prefix_effects.
    Proof.
      unfold rhs_context.
      intros root target next prefix_reads prefix_effects value
        Hcontext direct reads effects Htrace.
      rewrite <- List.app_assoc. cbn. apply Hcontext. constructor. exact Htrace.
    Qed.

    Lemma rhs_context_side :
      forall root target value next prefix_reads prefix_effects,
        rhs_context root (R.ConstraintSystem.Side target value next)
          prefix_reads prefix_effects ->
        rhs_context root next prefix_reads
          (prefix_effects ++ [(target, value)]).
    Proof.
      unfold rhs_context.
      intros root target value next prefix_reads prefix_effects
        Hcontext direct reads effects Htrace.
      rewrite <- List.app_assoc. cbn. apply Hcontext. constructor. exact Htrace.
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
      - destruct Hsolved as [value Hvalue]. exists value.
        rewrite Howner, (proj1 Hview). exact Hvalue.
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
        rhs_context root (R.ConstraintSystem.Spawn target next)
          prefix_reads prefix_effects ->
        rhs_context root next prefix_reads prefix_effects.
    Proof. unfold rhs_context. intros. apply H. constructor. exact H0. Qed.

    Lemma evaluation_witness_spawn :
      forall tf st fr target next,
        evaluation_witness tf st fr (R.ConstraintSystem.Spawn target next) ->
        evaluation_witness tf st fr next.
    Proof.
      intros tf st fr target next
        [Hsolved [reads [effects
          [Hcontext [Hreads [Heffects Hframe]]]]]]. split; [exact Hsolved |].
      exists reads, effects. split.
      - eapply rhs_context_spawn. exact Hcontext.
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
      - specialize (Hcontext direct [] [] (TraceRet direct)).
        now rewrite !List.app_nil_r in Hcontext.
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
      - destruct Hsolved as [value Hlookup]. exists value.
        now rewrite (proj1 Hview).
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

    Lemma next_config_control_history :
      forall tf before after,
        configuration_ranked before ->
        Termination.control_ordered (R.cfg_state before)
          (R.cfg_control before) ->
        control_history tf (R.cfg_state before) (R.cfg_control before) ->
        R.next_config tf before = Some after ->
        control_history tf (R.cfg_state after) (R.cfg_control after).
    Proof.
      intros tf [st control] after Hranked Hordered Hhistory Hstep.
      pose proof (configuration_control_ranked Hranked) as Hcontrol_ranked.
      destruct control; cbn in Hordered, Hhistory, Hcontrol_ranked, Hstep.
      - destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
          try discriminate. inversion Hstep; subst. exact I.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. exact I.
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; exact I.
      - destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
          inversion Hstep; subst; exact I.
      - inversion Hstep; subst. cbn. split.
        + apply initial_evaluation_witness.
          apply materialize_solved_correctness.
        + now apply continuation_history_materialize.
      - destruct Hcontrol_ranked as [Hframe_ranked Hcontinuation_ranked].
        destruct Hhistory as [Hcurrent Hcontinuation].
        destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. cbn. split.
          * now apply evaluation_ret_completed.
          * exact Hcontinuation.
        + set (observed := R.observe st t) in *.
          assert (Hcurrent0 : evaluation_witness tf observed f
            (R.ConstraintSystem.Get t r)).
          { subst observed. now apply evaluation_witness_observe. }
          assert (Hcontinuation0 : continuation_history tf observed c).
          { subst observed. now apply continuation_history_observe. }
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. cbn. split; assumption.
          * set (st0 := if R.is_materialized observed t
              then observed else R.enqueue observed t) in *.
            change (Some
              (let '(st1, fr1, value) := R.complete_get st0 f t in
               {| R.cfg_state := st1;
                  R.cfg_control := R.RunRhs fr1 (r value) c |}) =
              Some after) in Hstep.
            destruct (R.complete_get st0 f t)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. cbn. split.
            -- eapply evaluation_witness_complete_get; [exact Hget |].
               unfold st0. destruct (R.is_materialized observed t);
                 [exact Hcurrent0 |now apply evaluation_witness_enqueue].
            -- eapply continuation_history_complete_get; [exact Hget |].
               unfold st0. destruct (R.is_materialized observed t);
                 [exact Hcontinuation0 |now apply continuation_history_enqueue].
        + set (observed := R.observe st t) in *.
          assert (Hcurrent0 : evaluation_witness tf observed f
            (R.ConstraintSystem.Side t t0 r)).
          { subst observed. now apply evaluation_witness_observe. }
          assert (Hcontinuation0 : continuation_history tf observed c).
          { subst observed. now apply continuation_history_observe. }
          assert (Hordered0 : Termination.continuation_below observed
            (R.frame_owner f) c).
          { subst observed. eapply observed_continuation_below; eauto. }
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0)
            as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          assert (Hcurrent1 : evaluation_witness tf st1 fr1 r).
          { eapply evaluation_witness_side; eauto. }
          assert (Howner1 : R.frame_owner fr1 = R.frame_owner f).
          { pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord)
              as Howner. cbn in Howner. symmetry. exact Howner. }
          assert (Hcontinuation1 : continuation_history tf st1 c).
          { eapply continuation_history_write_side;
              [exact Hwrite | |exact Hcontinuation0].
            now rewrite Howner1. }
          unfold R.continue_side. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool; cbn.
            -- split; assumption.
            -- split; [now apply evaluation_witness_enqueue
                       |now apply continuation_history_enqueue].
          * cbn. split; assumption.
        + set (observed := R.observe st t) in *.
          assert (Hcurrent0 : evaluation_witness tf observed f
            (R.ConstraintSystem.Spawn t r)).
          { subst observed. now apply evaluation_witness_observe. }
          assert (Hcontinuation0 : continuation_history tf observed c).
          { subst observed. now apply continuation_history_observe. }
          pose proof (evaluation_witness_spawn Hcurrent0) as Hnext.
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. cbn. split; assumption.
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. cbn. split; assumption.
            -- inversion Hstep; subst. cbn. split.
               ++ apply evaluation_witness_materialize.
                  now apply evaluation_witness_enqueue.
               ++ apply continuation_history_materialize.
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
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Hcurrent1 : completed_witness tf st1 f t).
            { eapply completed_witness_dead_side; eauto. }
            assert (Hcontinuation1 : continuation_history tf st1 c).
            { eapply continuation_history_write_side; eauto. }
            unfold R.continue_dead. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner f) target &&
                 negb (R.is_materialized st1 target))%bool; cbn.
               ++ split; assumption.
               ++ split; [now apply completed_witness_enqueue
                           |now apply continuation_history_enqueue].
            -- cbn. split; assumption.
      - destruct Hcontrol_ranked as [Hframe_ranked Hcontinuation_ranked].
        destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. cbn.
        assert (Howner : R.frame_owner fr1 = R.frame_owner f)
          by (eapply set_value_frame_owner; eauto). split.
        + rewrite Howner.
          eapply completed_witness_set_value_summary; eauto.
        +
          eapply continuation_history_set_value; eauto.
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
            -- eapply continuation_history_pop_above.
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

    Lemma queued_enqueue :
      forall st inserted x, queued st x -> queued (R.enqueue st inserted) x.
    Proof.
      intros st inserted x Hqueued. unfold queued in *. cbn.
      apply queue_insert_members. now right.
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
        as [_ [_ Hqueue]]. unfold queued in *. now rewrite Hqueue.
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
      all: unfold commit_value, queued in *; cbn;
        apply queue_insert_all_members; now right.
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
        R.set_value st fr direct = (st', fr') /\
        after =
          {| R.cfg_state := st'; R.cfg_control := R.RunDrain fr' k |} /\
        x = R.frame_owner fr.

    Lemma queued_step_scheduled :
      forall tf before after x,
        queued (R.cfg_state before) x ->
        R.next_config tf before = Some after ->
        queued (R.cfg_state after) x \/
        control_active x (R.cfg_control after).
    Proof.
      intros tf [st control] after x Hqueued Hstep.
      destruct control; cbn in Hstep.
      - destruct (R.queue st) as [|owner rest] eqn:Hqueue;
          try discriminate. inversion Hstep; subst.
        unfold queued in Hqueued. cbn in Hqueued.
        rewrite Hqueue in Hqueued. cbn in Hqueued.
        destruct Hqueued as [-> | Hqueued]; [right; now left |now left].
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; left; now apply queued_observe_preserved.
      - destruct (R.queue st) as [|owner rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + inversion Hstep; subst. unfold queued in Hqueued. cbn in Hqueued.
          rewrite Hqueue in Hqueued. cbn in Hqueued.
          destruct Hqueued as [-> | Hqueued]; [right; now left |now left].
      - inversion Hstep; subst. left. now apply queued_materialize.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. now left.
        + set (observed := R.observe st t) in *.
          assert (Hqueued0 : queued observed x)
            by (subst observed; now apply queued_observe_preserved).
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. now left.
          * set (st0 := if R.is_materialized observed t
              then observed else R.enqueue observed t) in *.
            change (Some
              (let '(st1, fr1, value) := R.complete_get st0 f t in
               {| R.cfg_state := st1;
                  R.cfg_control := R.RunRhs fr1 (r value) c |}) =
              Some after) in Hstep.
            destruct (R.complete_get st0 f t)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. left. eapply queued_complete_get;
              [exact Hget |]. unfold st0.
            destruct (R.is_materialized observed t);
              [exact Hqueued0 |now apply queued_enqueue].
        + set (observed := R.observe st t) in *.
          assert (Hqueued0 : queued observed x)
            by (subst observed; now apply queued_observe_preserved).
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          assert (Hqueued1 : queued st1 x)
            by (eapply queued_write_side; eauto).
          unfold R.continue_side. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool;
              [now left |left; now apply queued_enqueue].
          * now left.
        + set (observed := R.observe st t) in *.
          assert (Hqueued0 : queued observed x)
            by (subst observed; now apply queued_observe_preserved).
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. now left.
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. now left.
            -- inversion Hstep; subst. left. apply queued_materialize.
               now apply queued_enqueue.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. now left.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Hqueued1 : queued st1 x)
              by (eapply queued_write_side; eauto).
            unfold R.continue_dead. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner f) target &&
                 negb (R.is_materialized st1 target))%bool;
                 [now left |left; now apply queued_enqueue].
            -- now left.
      - destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. left.  eapply queued_set_value; eauto.
      - destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. left.
          eapply queued_same_solver_view;
            [apply reset_registered_cells_same_solver_view |exact Hqueued].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst. unfold queued in Hqueued. cbn in Hqueued.
            rewrite Hqueue in Hqueued. cbn in Hqueued.
            destruct Hqueued as [Hqueued | Hqueued].
            -- subst x. right. now left.
            -- now left.
          * destruct (R.rank_lt st (R.frame_owner f) next).
            -- inversion Hstep; subst. unfold queued in Hqueued.
               cbn in Hqueued. rewrite Hqueue in Hqueued. cbn in Hqueued.
               destruct Hqueued as [Hqueued | Hqueued].
               ++ subst x. right. now left.
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
        + set (observed := R.observe st t) in *.
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. right. left. cbn. right. exact Hactive.
          * set (st0 := if R.is_materialized observed t
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
            -- left. rewrite (@complete_get_frame_owner
                 st0 f t st1 fr1 value Hget). exact Howner.
            -- right. exact Hactive.
        + set (observed := R.observe st t) in *.
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          assert (Howner : R.frame_owner fr1 = R.frame_owner f).
          { pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord)
              as H. cbn in H. symmetry. exact H. }
          unfold R.continue_side. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool.
            -- right. left. cbn. right. rewrite Howner. exact Hactive.
            -- right. left. cbn. rewrite Howner. exact Hactive.
          * right. left. cbn. rewrite Howner. exact Hactive.
        + set (observed := R.observe st t) in *.
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. right. left. exact Hactive.
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. right. left. cbn. right. exact Hactive.
            -- inversion Hstep; subst. right. left. exact Hactive.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hactive.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. right. left. exact Hactive.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            unfold R.continue_dead. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner f) target &&
                 negb (R.is_materialized st1 target))%bool.
               ++ right. left. cbn. right. exact Hactive.
               ++ right. left. cbn. exact Hactive.
            -- right. left. cbn. exact Hactive.
      - destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
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
      destruct (U.update true target
        (R.side_phase (R.stored_side_cell base (R.frame_owner fr) target))
        (R.stored_contribution base (R.frame_owner fr) target) input)
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
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; right; right;
            subst observed; now apply aggregate_bounded_observe.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; right; right; exact Hbounded.
      - inversion Hstep; subst. right. right.
        now apply aggregate_bounded_materialize.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + set (observed := R.observe st t) in *.
          assert (Hbounded0 : aggregate_bounded observed target)
            by (subst observed; now apply aggregate_bounded_observe).
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. right. right. exact Hbounded0.
          * set (st0 := if R.is_materialized observed t
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
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          destruct (V.eq_dec target t) as [-> | Hneq].
          * unfold R.continue_side. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool.
               ++ right. left. now left.
               ++ left. unfold queued. apply queue_insert_members. now left.
            -- right. right.
               eapply aggregate_bounded_write_unchanged; eauto.
          * assert (Hbounded1 : aggregate_bounded st1 target)
              by (eapply aggregate_bounded_write_other; eauto).
            unfold R.continue_side. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool;
                 [right; right; exact Hbounded1 |
                  right; right; now apply aggregate_bounded_enqueue].
            -- right. right. exact Hbounded1.
        + set (observed := R.observe st t) in *.
          assert (Hbounded0 : aggregate_bounded observed target)
            by (subst observed; now apply aggregate_bounded_observe).
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. right. right. exact Hbounded0.
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. right. right. exact Hbounded0.
            -- inversion Hstep; subst. right. right.
               apply aggregate_bounded_materialize.
               now apply aggregate_bounded_enqueue.
      - destruct l as [|dead remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. right. exact Hbounded.
        + destruct (S.mem dead (R.frame_current_targets f)).
          * inversion Hstep; subst. right. right. exact Hbounded.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f dead D.bottom in
               R.continue_dead st1 f t dead remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f dead D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            destruct (V.eq_dec target dead) as [-> | Hneq].
            -- unfold R.continue_dead. destruct changed.
               ++ destruct (R.rank_lt st1 (R.frame_owner f) dead &&
                    negb (R.is_materialized st1 dead))%bool.
                  ** right. left. now left.
                  ** left. unfold queued.
                     apply queue_insert_members. now left.
               ++ right. right.
                  eapply aggregate_bounded_write_unchanged; eauto.
            -- assert (Hbounded1 : aggregate_bounded st1 target)
                 by (eapply aggregate_bounded_write_other; eauto).
               unfold R.continue_dead. destruct changed.
               ++ destruct (R.rank_lt st1 (R.frame_owner f) dead &&
                    negb (R.is_materialized st1 dead))%bool;
                    [right; right; exact Hbounded1 |
                     right; right; now apply aggregate_bounded_enqueue].
               ++ right. right. exact Hbounded1.
      - destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. right. right.
        eapply aggregate_bounded_set_value; eauto.
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
      - destruct (@queued_step_scheduled tf before after target Hqueued Hstep);
          [now left |now right; left].
      - destruct (@active_step_scheduled_or_commit
          tf before after target Hactive Hstep)
          as [Hqueued | [Hactive' | Hcommit]];
          try (now left); try (now right; left).
        right. right. destruct Hcommit as
          [st [fr [direct [k [st' [fr'
            [-> [Hset [-> ->]]]]]]]]].
        unfold aggregate_bounded. cbn. unfold R.aggregate.

        rewrite (@set_value_contributions st fr direct st' fr' Hset).
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
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; right; right;
            subst observed; now apply summary_valid_observe.
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
          * set (observed := R.observe st t) in *.
            destruct (negb (R.is_materialized observed t) &&
              R.rank_lt observed (R.frame_owner f) t)%bool.
            -- inversion Hstep; subst. right. left. cbn. now right; left.
            -- set (st0 := if R.is_materialized observed t
                 then observed else R.enqueue observed t) in *.
               change (Some
                 (let '(st1, fr1, value) := R.complete_get st0 f t in
                  {| R.cfg_state := st1;
                     R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                 Some after) in Hstep.
               destruct (R.complete_get st0 f t)
                 as [[st1 fr1] value] eqn:Hget.
               inversion Hstep; subst. right. left. left.
               symmetry. eapply complete_get_frame_owner; eauto.
          * set (observed := R.observe st t) in *.
            change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, changed) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
            destruct (R.record_side_input f t t0)
              as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Howner : R.frame_owner fr1 = R.frame_owner f).
            { pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord)
                as H. cbn in H. symmetry. exact H. }
            unfold R.continue_side. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool.
               ++ right. left. cbn. right. left. symmetry. exact Howner.
               ++ right. left. cbn. left. symmetry. exact Howner.
            -- right. left. cbn. left. symmetry. exact Howner.
          * set (observed := R.observe st t) in *.
            destruct (R.is_materialized observed t).
            -- inversion Hstep; subst. right. left. now left.
            -- destruct (R.rank_lt observed (R.frame_owner f) t).
               ++ inversion Hstep; subst. right. left. cbn. now right; left.
               ++ inversion Hstep; subst. right. left. now left.
        + destruct r; cbn -[R.observe R.complete_get R.enqueue
            R.record_side_input R.write_side_contribution R.continue_side
            R.materialize] in Hstep.
          * inversion Hstep; subst. right. right. exact Hsummary.
          * set (observed := R.observe st t) in *.
            assert (Hsummary0 : summary_valid tf observed owner)
              by (subst observed; now apply summary_valid_observe).
            destruct (negb (R.is_materialized observed t) &&
              R.rank_lt observed (R.frame_owner f) t)%bool.
            -- inversion Hstep; subst. right. right. exact Hsummary0.
            -- set (st0 := if R.is_materialized observed t
                 then observed else R.enqueue observed t) in *.
               change (Some
                 (let '(st1, fr1, value) := R.complete_get st0 f t in
                  {| R.cfg_state := st1;
                     R.cfg_control := R.RunRhs fr1 (r value) c |}) =
                 Some after) in Hstep.
               destruct (R.complete_get st0 f t)
                 as [[st1 fr1] value] eqn:Hget.
               inversion Hstep; subst. right. right.
               eapply summary_valid_complete_get; [exact Hget |].
               unfold st0. destruct (R.is_materialized observed t);
                 [exact Hsummary0 |now apply summary_valid_enqueue].
          * set (observed := R.observe st t) in *.
            assert (Hsummary0 : summary_valid tf observed owner)
              by (subst observed; now apply summary_valid_observe).
            change (Some
              (let '(fr1, input) := R.record_side_input f t t0 in
               let '(st1, changed) :=
                 R.write_side_contribution observed fr1 t input in
               R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
            destruct (R.record_side_input f t t0)
              as [fr1 input] eqn:Hrecord.
            destruct (R.write_side_contribution observed fr1 t input)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            assert (Hsummary1 : summary_valid tf st1 owner).
            { eapply summary_valid_write_other_source;
                [exact Hwrite | |exact Hsummary0].
              pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord)
                as H. cbn in H. rewrite <- H. exact Hother. }
            unfold R.continue_side. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
                 negb (R.is_materialized st1 t))%bool;
                 [right; right; exact Hsummary1 |
                  right; right; now apply summary_valid_enqueue].
            -- right. right. exact Hsummary1.
          * set (observed := R.observe st t) in *.
            assert (Hsummary0 : summary_valid tf observed owner)
              by (subst observed; now apply summary_valid_observe).
            destruct (R.is_materialized observed t).
            -- inversion Hstep; subst. right. right. exact Hsummary0.
            -- destruct (R.rank_lt observed (R.frame_owner f) t).
               ++ inversion Hstep; subst. right. right. exact Hsummary0.
               ++ inversion Hstep; subst. right. right.
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
                 R.continue_dead st1 f t dead remaining c changed) =
                Some after) in Hstep.
               destruct (R.write_side_contribution st f dead D.bottom)
                 as [st1 changed] eqn:Hwrite.
               inversion Hstep; subst. unfold R.continue_dead.
               destruct changed.
               ++ destruct (R.rank_lt st1 (R.frame_owner f) dead &&
                    negb (R.is_materialized st1 dead))%bool.
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
                 R.continue_dead st1 f t dead remaining c changed) =
                Some after) in Hstep.
               destruct (R.write_side_contribution st f dead D.bottom)
                 as [st1 changed] eqn:Hwrite.
               inversion Hstep; subst.
               assert (Hsummary1 : summary_valid tf st1 owner)
                 by (eapply summary_valid_write_other_source; eauto).
               unfold R.continue_dead. destruct changed.
               ++ destruct (R.rank_lt st1 (R.frame_owner f) dead &&
                    negb (R.is_materialized st1 dead))%bool;
                    [right; right; exact Hsummary1 |
                     right; right; now apply summary_valid_enqueue].
               ++ right. right. exact Hsummary1.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst.
        destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hother].
        + right. right.
          eapply completed_witness_set_value_summary; eauto.
        + right. right.
          eapply summary_valid_set_value_other; eauto.
      - destruct Hhistory as [Hframe Hcontinuation].
        destruct (R.queue st) as [|next rest] eqn:Hqueue; cbn in Hstep.
        + inversion Hstep; subst. right. right.
          eapply summary_valid_same_solver_view;
            [apply reset_registered_cells_same_solver_view |exact Hsummary].
        + destruct (V.eq_dec next (R.frame_owner f)).
          * inversion Hstep; subst.
            destruct (V.eq_dec owner (R.frame_owner f)) as [-> | Hneq].
            -- right. left. now left.
            -- right. right. eapply summary_valid_pop_other.
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
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; cbn; repeat split; exact I.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; cbn; repeat split; exact I.
      - inversion Hstep; subst. exact Hconsistent.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. split; assumption.
        + set (observed := R.observe st t) in *.
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. cbn. split; [reflexivity |].
            split; assumption.
          * set (st0 := if R.is_materialized observed t
              then observed else R.enqueue observed t) in *.
            change (Some
              (let '(st1, fr1, value) := R.complete_get st0 f t in
               {| R.cfg_state := st1;
                  R.cfg_control := R.RunRhs fr1 (r value) c |}) =
              Some after) in Hstep.
            destruct (R.complete_get st0 f t)
              as [[st1 fr1] value] eqn:Hget.
            inversion Hstep; subst. split.
            -- rewrite (@complete_get_frame_owner
                 st0 f t st1 fr1 value Hget). exact Hexpect.
            -- exact Hcontinuation.
        + set (observed := R.observe st t) in *.
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          assert (Howner : R.frame_owner fr1 = R.frame_owner f).
          { pose proof (f_equal (fun p => R.frame_owner (fst p)) Hrecord)
              as H. cbn in H. symmetry. exact H. }
          unfold R.continue_side. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool.
            -- cbn. split; [exact I |]. split.
               ++ now rewrite Howner.
               ++ exact Hcontinuation.
            -- cbn. split; [now rewrite Howner |exact Hcontinuation].
          * cbn. split; [now rewrite Howner |exact Hcontinuation].
        + set (observed := R.observe st t) in *.
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. split; assumption.
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. cbn. split; [exact I |].
               split; assumption.
            -- inversion Hstep; subst. split; assumption.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. split; assumption.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. split; assumption.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst. unfold R.continue_dead. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner f) target &&
                 negb (R.is_materialized st1 target))%bool.
               ++ cbn. split; [exact I |]. split; assumption.
               ++ cbn. split; assumption.
            -- cbn. split; assumption.
      - destruct Hconsistent as [Hexpect Hcontinuation].
        destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst. split.
        + rewrite (@set_value_frame_owner st f t st1 fr1 Hset).
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
      destruct Hsolved as [value Hvalue]. exists value. cbn in Hvalue.
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

    Lemma solved_observe_back :
      forall st observed x,
        Sem.solved (R.observe st observed) x -> Sem.solved st x.
    Proof.
      intros st observed x [value Hlookup]. exists value.
      rewrite (proj1 (observe_solver_view st observed)) in Hlookup.
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
        control_active x (R.cfg_control after).
    Proof.
      intros tf [st control] after x Hconsistent Hhistory Hsolved Hstep.
      destruct control; cbn in Hconsistent, Hhistory, Hstep.
      - destruct (R.queue st); try discriminate.
        inversion Hstep; subst. now left.
      - destruct l as [|root remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + set (observed := R.observe st root) in *.
          destruct (R.is_materialized observed root);
            inversion Hstep; subst; left; subst observed;
            exact (@solved_observe_back st root x Hsolved).
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; now left.
      - inversion Hstep; subst.
        destruct (@materialize_solved_origin_correctness st t x Hsolved)
          as [Hbefore | ->]; [now left |right; right; now left].
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. now left.
        + set (observed := R.observe st t) in *.
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. left. subst observed.
            exact (@solved_observe_back st t x Hsolved).
          * set (st0 := if R.is_materialized observed t
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
              st0 f t st1 fr1 value x Hget Hsolved) as [Hst0 | ->].
            -- left. unfold st0 in Hst0.
               destruct (R.is_materialized observed t); subst observed;
                 exact (@solved_observe_back st t x Hst0).
            -- unfold st0. destruct (R.is_materialized observed t) eqn:Hmat.
               ++ left. subst observed. apply (@solved_observe_back st t t).
                  unfold R.is_materialized in Hmat.
                  destruct (M.lookup (R.sigma (R.observe st t)) t)
                    as [current|] eqn:Hlookup; try discriminate.
                  now exists current.
               ++ right. left. eapply queued_complete_get; [exact Hget |].
                  destruct (R.is_materialized observed t); try discriminate.
                  unfold queued. apply queue_insert_members. now left.
        + set (observed := R.observe st t) in *.
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input] eqn:Hrecord.
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed] eqn:Hwrite.
          inversion Hstep; subst.
          destruct (write_side_contribution_same_read_view Hwrite)
            as [Hsigma _].
          left. apply solved_observe_back with (observed := t).
          destruct Hsolved as [value Hlookup]. exists value.
          unfold R.continue_side in Hlookup. destruct changed.
          * destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool;
              cbn in Hlookup; now rewrite Hsigma in Hlookup.
          * cbn in Hlookup. now rewrite Hsigma in Hlookup.
        + set (observed := R.observe st t) in *.
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. left. subst observed.
            exact (@solved_observe_back st t x Hsolved).
          * destruct (R.rank_lt observed (R.frame_owner f) t).
            -- inversion Hstep; subst. left. subst observed.
               exact (@solved_observe_back st t x Hsolved).
            -- inversion Hstep; subst.
               destruct (@materialize_solved_origin_correctness
                 (R.enqueue observed t) t x Hsolved) as [Horigin | ->].
               ++ left. subst observed.
                  exact (@solved_observe_back st t x Horigin).
               ++ right. left. apply queued_materialize.
                  unfold queued. apply queue_insert_members. now left.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. now left.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. now left.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed] eqn:Hwrite.
            inversion Hstep; subst.
            destruct (write_side_contribution_same_read_view Hwrite)
              as [Hsigma _].
            left. destruct Hsolved as [value Hlookup]. exists value.
            unfold R.continue_dead in Hlookup. destruct changed.
            -- destruct (R.rank_lt st1 (R.frame_owner f) target &&
                 negb (R.is_materialized st1 target))%bool;
                 cbn in Hlookup; now rewrite Hsigma in Hlookup.
            -- cbn in Hlookup. now rewrite Hsigma in Hlookup.
      - destruct Hhistory as [Hcurrent Hcontinuation].
        destruct (R.set_value st f t) as [st1 fr1] eqn:Hset.
        inversion Hstep; subst.
        destruct (@set_value_solved_origin
          st f t st1 fr1 x Hset Hsolved) as [Hbefore | ->].
        + now left.
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

    Lemma next_config_preserves_solved :
      forall tf before after x,
        Sem.solved (R.cfg_state before) x ->
        R.next_config tf before = Some after ->
        Sem.solved (R.cfg_state after) x.
    Proof.
      intros tf before after x [value Hlookup] Hstep.
      destruct (@Termination.next_config_sigma_extends
        tf before after Hstep x value Hlookup) as [next Hnext].
      now exists next.
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
        as [Hbefore | [Hqueued | Hactive]].
      - destruct (Hguard owner Hbefore)
          as [Hqueued | [Hactive | Hsummary]].
        + destruct (@queued_step_scheduled
            tf before after owner Hqueued Hstep);
            [now left |now right; left].
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
            exact (proj1 Hhistory).
        + eapply summary_valid_step_guarded; eauto.
      - now left.
      - now right; left.
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
        try discriminate. now exists value.
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
        set (observed := R.observe st root) in *.
        destruct Hpending as [Heq | Hpending].
        + subst x. destruct (R.is_materialized observed root) eqn:Hmat.
          * inversion Hstep; subst. left. now apply materialized_solved.
          * inversion Hstep; subst. right. right. now left.
        + destruct (R.is_materialized observed root);
            inversion Hstep; subst; right; left; exact Hpending.
      - destruct (R.queue st); cbn in Hstep;
          inversion Hstep; subst; right; left; exact Hpending.
      - inversion Hstep; subst. right. left. exact Hpending.
      - destruct r; cbn -[R.observe R.complete_get R.enqueue
          R.record_side_input R.write_side_contribution R.continue_side
          R.materialize] in Hstep.
        + inversion Hstep; subst. right. left. exact Hpending.
        + set (observed := R.observe st t) in *.
          destruct (negb (R.is_materialized observed t) &&
            R.rank_lt observed (R.frame_owner f) t)%bool.
          * inversion Hstep; subst. right. left. exact Hpending.
          * set (st0 := if R.is_materialized observed t
              then observed else R.enqueue observed t) in *.
            change (Some
              (let '(st1, fr1, value) := R.complete_get st0 f t in
               {| R.cfg_state := st1;
                  R.cfg_control := R.RunRhs fr1 (r value) c |}) =
              Some after) in Hstep.
            destruct (R.complete_get st0 f t). destruct p.
            inversion Hstep; subst. right. left. exact Hpending.
        + set (observed := R.observe st t) in *.
          change (Some
            (let '(fr1, input) := R.record_side_input f t t0 in
             let '(st1, changed) :=
               R.write_side_contribution observed fr1 t input in
             R.continue_side st1 fr1 t r c changed) = Some after) in Hstep.
          destruct (R.record_side_input f t t0) as [fr1 input].
          destruct (R.write_side_contribution observed fr1 t input)
            as [st1 changed].
          inversion Hstep; subst. unfold R.continue_side.
          destruct changed;
            destruct (R.rank_lt st1 (R.frame_owner fr1) t &&
              negb (R.is_materialized st1 t))%bool;
            cbn; right; left; exact Hpending.
        + set (observed := R.observe st t) in *.
          destruct (R.is_materialized observed t).
          * inversion Hstep; subst. right. left. exact Hpending.
          * destruct (R.rank_lt observed (R.frame_owner f) t);
              inversion Hstep; subst; right; left; exact Hpending.
      - destruct l as [|target remaining]; cbn in Hstep.
        + inversion Hstep; subst. right. left. exact Hpending.
        + destruct (S.mem target (R.frame_current_targets f)).
          * inversion Hstep; subst. right. left. exact Hpending.
          * change (Some
              (let '(st1, changed) :=
                 R.write_side_contribution st f target D.bottom in
               R.continue_dead st1 f t target remaining c changed) =
              Some after) in Hstep.
            destruct (R.write_side_contribution st f target D.bottom)
              as [st1 changed].
            inversion Hstep; subst. unfold R.continue_dead.
            destruct changed;
              destruct (R.rank_lt st1 (R.frame_owner f) target &&
                negb (R.is_materialized st1 target))%bool;
              cbn; right; left; exact Hpending.
      - destruct (R.set_value st f t).
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
          as [Hqueued' | Hactive'];
          [right; left; exact Hqueued' |right; right; right; exact Hactive'].
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
          change (Sem.solved st' (R.frame_owner fr)).
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
      - intros owner [value Hlookup]. cbn in Hlookup.
        rewrite ML.lookup_empty in Hlookup. discriminate.
      - apply initial_roots_guarded.
    Qed.

    Lemma invariant_step :
      forall tf roots before after,
        invariant tf roots before ->
        R.next_config tf before = Some after -> invariant tf roots after.
    Proof.
      intros tf roots before after Hinv Hstep.
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
        Sem.steps tf first final -> invariant tf roots final.
    Proof.
      intros tf roots first final Hinv Hsteps. induction Hsteps.
      - exact Hinv.
      - apply IHHsteps. eapply invariant_step; eauto.
    Qed.

    Lemma terminal_invariant :
      forall tf roots final,
        Sem.terminates_to tf roots final ->
        invariant tf roots (Sem.terminal_config final).
    Proof.
      intros tf roots final [Hsteps _]. eapply invariant_steps.
      - apply initial_invariant.
      - exact Hsteps.
    Qed.

    Theorem terminal_state_correct :
      forall tf roots final,
        Sem.terminates_to tf roots final ->
        Sem.correct_final_state tf roots final.
    Proof.
      intros tf roots final Hterminates.
      pose proof (@terminal_invariant tf roots final Hterminates) as Hinv.
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

    Theorem solve_fuel_correct :
      forall fuel tf roots final,
        R.solve_fuel fuel tf roots = Some final ->
        Sem.correct_final_state tf roots final.
    Proof.
      intros fuel tf roots final Hsolve.
      apply terminal_state_correct.
      exact (@successful_run_terminates_to fuel tf roots final Hsolve).
    Qed.

    Theorem total_correct :
      forall tf roots,
        Sem.finite_system tf roots -> Sem.totally_correct_on tf roots.
    Proof.
      intros tf roots Hfinite.
      destruct (@sufficient_fuel tf roots Hfinite)
        as [fuel [final Hsolve]].
      exists fuel, final. split; [exact Hsolve |].
      exact (@solve_fuel_correct fuel tf roots final Hsolve).
    Qed.

  End Correctness.

End Make.

Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V Rk Laws :=
    ListFiniteDiscoveryOrderLaws V.
  Include Make V D U S M Rk Features Laws Finite DL UL SL ML.
End FirstDiscovery.
