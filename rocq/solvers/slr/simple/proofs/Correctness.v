From Stdlib Require Import
  List Lia Arith.PeanoNat Sorting.Sorted Sorting.Permutation
  Wellfounded Wf_nat Relations.Relation_Operators
  Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product.
From TcSolvers Require Import
  common.Assumptions
  common.ConstraintSemantics
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.simple.Simple.

Import ListNotations.
Set Implicit Arguments.

(** Proof-only interpretation of the Simple machine. *)
Module Semantics.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V).

  Module R := Simple.Make V D U S M Rk.
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

  Definition solved (st : R.state) (x : V.t) : Prop :=
    exists value, M.lookup (R.sigma st) x = Some value.

  Definition rhs_eval (st : R.state) :=
    rhs_eval_with (fun target => M.lookup (R.sigma st) target).

  Definition side_effects_below
    (st : R.state) (effects : list (V.t * D.t)) : Prop :=
    forall target value,
      List.In (target, value) effects ->
      D.leq value (R.sigma_value st target) = true.

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

(** Internal correctness proof.  The reviewer-facing results are re-stated in
    [solvers.slr.simple.Theorems].

    The common rank layer.  In particular, none of these proofs knows how a
    fresh rank is selected. *)
Module Make
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).

  Module Sem := Semantics.Make V D U S M Rk.
  Module R := Sem.R.

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

  Lemma rank_extends_enqueue_handle :
    forall st entry,
      rank_extends st (R.enqueue_handle st entry).
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

  Lemma rank_valid_enqueue_handle :
    forall st entry,
      rank_valid st -> rank_valid (R.enqueue_handle st entry).
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
      eauto using rank_valid_observe, rank_valid_enqueue_handle,
        rank_valid_get_ready, rank_valid_side_ready,
        rank_valid_start_evaluation, rank_valid_materialize,
        rank_valid_set_value.
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
      eauto using rank_extends_refl, rank_extends_observe,
        rank_extends_after_observe, rank_extends_with_queue,
        rank_extends_with_started, rank_extends_enqueue_handle,
        rank_extends_start_evaluation, rank_extends_materialize,
        rank_extends_get_ready, rank_extends_side_ready,
        rank_extends_set_value.
    - eapply rank_extends_trans.
      + apply rank_extends_start_evaluation.
      + apply rank_extends_with_started.
    - eapply rank_extends_after_observe; [eassumption |].
      eapply rank_extends_trans.
      + apply rank_extends_enqueue_handle.
      + apply rank_extends_get_ready.
    - eapply rank_extends_after_observe; [eassumption |].
      eapply rank_extends_trans.
      + apply rank_extends_side_ready.
      + apply rank_extends_enqueue_handle.
    - eapply rank_extends_after_observe; [eassumption |].
      eapply rank_extends_trans.
      + apply rank_extends_enqueue_handle.
      + apply rank_extends_materialize.
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
      unobserved_budget support after <=
        unobserved_budget support before.
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
      unobserved_budget support after <
        unobserved_budget support before.
  Proof.
    induction support as [|y rest IH];
      intros before after x Hnodup Hin Hextends Hbefore [rank Hafter].
    - contradiction.
    - inversion Hnodup as [|? ? Hnotin Hrest]; subst.
      destruct Hin as [<- | Hin].
      + pose proof
          (@unobserved_budget_nonincreasing rest before after Hextends)
          as Htail.
        cbn. rewrite Hbefore, Hafter. cbn.
        lia.
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
    forall support st x next entry,
      NoDup support ->
      List.In x support ->
      R.Ranking.lookup (R.ranking st) x = None ->
      R.observe st x = (next, entry) ->
      unobserved_budget support next < unobserved_budget support st.
  Proof.
    intros support st x next entry Hnodup Hin Hfresh Hobserve.
    eapply (@unobserved_budget_strict support st next x); eauto.
    - exact (@rank_extends_observe st x next entry Hobserve).
    - exists (R.handle_rank entry).
      pose proof (@observed_handle_variable st x next entry Hobserve)
        as Hvariable.
      rewrite <- Hvariable.
      exact (@observed_handle_valid st x next entry Hobserve).
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
      destruct (U.update true (R.handle_variable target)
        (R.stored_side_phase st (R.handle_variable source)
          (R.handle_variable target))
        (R.stored_contribution st (R.handle_variable source)
          (R.handle_variable target))
        (R.accumulated_side_input st (R.handle_variable source)
          (R.handle_variable target) raw));
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

  Lemma next_config_handles_valid :
    forall tf before after,
      handles_valid before ->
      R.next_config tf before = Some after ->
      handles_valid after.
  Proof.
    intros tf [st control] after [Hrank Hqueue Hcontrol] Hstep.
    pose proof (@next_config_rank_valid tf
      {| R.cfg_state := st; R.cfg_control := control |} after Hrank Hstep)
      as Hrank_after.
    pose proof (@next_config_rank_extends tf
      {| R.cfg_state := st; R.cfg_control := control |} after Hstep)
      as Hextends.
    cbn in Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hrank, Hqueue, Hcontrol, Hrank_after, Hextends.
    all: constructor; [exact Hrank_after | |].
    all: try exact Hqueue; try exact I.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?entry, ?rest),
        Hvalid : queue_valid ?before
        |- queue_valid (R.with_queue ?before ?rest) =>
          apply queue_valid_with_queue;
          destruct (@queue_pop_valid before entry rest Hvalid Hpop);
          assumption
      | Hpop : R.queue_pop (R.queue ?before) = Some (?entry, ?rest),
        Hvalid : queue_valid ?before
        |- control_valid (R.with_queue ?before ?rest)
             (R.RunSolveOne ?entry ?k) =>
          destruct (@queue_pop_valid before entry rest Hvalid Hpop)
            as [Hentry Hrest];
          cbn; split; [exact Hentry | exact I]
      end.
    all: try (apply queue_valid_start_evaluation; exact Hqueue).
    all: try (apply queue_valid_set_value; exact Hqueue).
    all: try (apply queue_valid_get_ready;
      match goal with
      | Hobs : R.observe ?before ?x = (?next, ?entry) |-
          queue_valid ?next =>
          exact (@queue_valid_observe before x next entry Hqueue Hobs)
      end).
    all: try (apply queue_valid_side_ready;
      match goal with
      | Hobs : R.observe ?before ?x = (?next, ?entry) |-
          queue_valid ?next =>
          exact (@queue_valid_observe before x next entry Hqueue Hobs)
      end).
    all: try (apply queue_valid_materialize;
      eapply queue_valid_enqueue_handle;
      [eauto using observed_handle_valid, handle_valid_extended
      | match goal with
        | Hobs : R.observe ?before ?x = (?next, ?entry) |-
            queue_valid ?next =>
            exact (@queue_valid_observe before x next entry Hqueue Hobs)
        end]).
    all: try (eapply queue_valid_enqueue_handle;
      [eauto 3 using observed_handle_valid, handle_valid_extended
      | apply queue_valid_side_ready;
        match goal with
        | Hobs : R.observe ?before ?x = (?next, ?entry) |-
            queue_valid ?next =>
            exact (@queue_valid_observe before x next entry Hqueue Hobs)
        end]).
    all: try match goal with
      | Hobs : R.observe ?before ?x = (?next, ?entry)
        |- queue_valid ?next =>
          exact (@queue_valid_observe before x next entry Hqueue Hobs)
      | Hobs : R.observe ?before ?x = (?next, ?entry)
        |- control_valid ?next (R.RunSolveOne ?entry _) =>
          cbn; split;
          [exact (@observed_handle_valid before x next entry Hobs)
          | exact I]
      end.
    all: cbn; try exact Hqueue; try exact I.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?entry, ?rest),
        Hvalid : queue_valid ?before
        |- Forall _ ?rest =>
          destruct (@queue_pop_valid before entry rest Hvalid Hpop);
          assumption
      | Hpop : R.queue_pop (R.queue ?before) = Some (?entry, ?rest),
        Hvalid : queue_valid ?before
        |- handle_valid _ ?entry /\ _ =>
          destruct (@queue_pop_valid before entry rest Hvalid Hpop)
            as [Hentry Hrest]
      end.
    all: try match goal with
      | Hobs : R.observe ?before ?x = (?next, ?entry)
        |- handle_valid ?next ?entry /\ True =>
          split;
          [exact (@observed_handle_valid before x next entry Hobs)
          | exact I]
      end.
    all: try match type of Hcontrol with
      | True =>
          clear Hcontrol; cbn; repeat split;
          eauto 4 using handle_valid_extended,
            continuation_valid_extended, continuation_valid_continue
      | False => contradiction
      end.
    all: try match type of Hcontrol with
      | _ /\ _ =>
          destruct Hcontrol as [Howner Hcontinuation];
          cbn; repeat split;
          eauto 4 using handle_valid_extended,
            continuation_valid_extended, continuation_valid_continue
      end.
    all: try match type of Hcontrol with
      | _ /\ (_ /\ _) =>
          destruct Hcontrol as [Howner [Htarget Hcontinuation]];
          cbn; repeat split;
          eauto 4 using handle_valid_extended,
            continuation_valid_extended, continuation_valid_continue
      end.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?entry, ?rest),
        Hvalid : queue_valid ?before
        |- queue_valid (R.with_queue ?before ?rest) =>
          apply queue_valid_with_queue;
          destruct (@queue_pop_valid before entry rest Hvalid Hpop);
          assumption
      end.
    all: try match goal with
      | Hobs : R.observe ?before ?x = (?next, ?entry)
        |- handle_valid ?next ?entry =>
          exact (@observed_handle_valid before x next entry Hobs)
      end.
    all: try (eapply handle_valid_extended;
      [first [apply rank_extends_side_ready
             |apply rank_extends_get_ready
             |apply rank_extends_enqueue_handle
             |apply rank_extends_materialize]
      |match goal with
       | Hobs : R.observe ?before ?x = (?next, ?entry)
         |- handle_valid ?next ?entry =>
           exact (@observed_handle_valid before x next entry Hobs)
       end]).
    all: try (apply queue_valid_get_ready;
      eapply queue_valid_enqueue_handle;
      [match goal with
       | Hobs : R.observe ?before ?x = (?next, ?entry)
         |- handle_valid ?next ?entry =>
           exact (@observed_handle_valid before x next entry Hobs)
       end
      |match goal with
       | Hobs : R.observe ?before ?x = (?next, ?entry),
         Hvalid : queue_valid ?before
         |- queue_valid ?next =>
           exact (@queue_valid_observe before x next entry Hvalid Hobs)
       end]).
    - apply queue_valid_get_ready. exact Hqueue.
    - apply continuation_valid_extended with st.
      + exact Hextends.
      + exact (proj2 Hcontinuation).
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
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hordered.
  Qed.

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
      eauto 5 using queue_pop_ordered, observe_ordered,
        start_evaluation_ordered, get_ready_ordered, side_ready_ordered,
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
  Definition supported (support : list V.t) (x : V.t) : Prop :=
    List.In x support.

  Definition ranking_generated
    (support : list V.t) (st : R.state) : Prop :=
    RankFinite.generated support (R.ranking st).

  Definition map_keys_supported {A : Type}
    (support : list V.t) (table : M.t A) : Prop :=
    forall x value,
      M.lookup table x = Some value -> supported support x.

  Definition set_supported (support : list V.t) (values : S.t) : Prop :=
    forall x, S.mem x values = true -> supported support x.

  Definition queue_supported (support : list V.t) (queue : R.work_queue) : Prop :=
    forall entry,
      List.In entry queue -> supported support (R.handle_variable entry).

  Definition readers_supported
    (support : list V.t) (readers : R.readers_table) : Prop :=
    map_keys_supported support readers /\
    forall target owner,
      S.mem owner (R.lookup_set readers target) = true ->
      supported support owner.

  Definition nested_supported {A : Type}
    (support : list V.t) (table : M.t (M.t A)) : Prop :=
    map_keys_supported support table /\
    forall outer inner value,
      M.lookup (R.lookup_map table outer) inner = Some value ->
      supported support outer /\ supported support inner.

  Record state_supported (support : list V.t) (st : R.state) : Prop := {
    state_ranking_generated : ranking_generated support st;
    sigma_supported : map_keys_supported support (R.sigma st);
    queue_is_supported : queue_supported support (R.queue st);
    started_supported : set_supported support (R.started st);
    readers_are_supported : readers_supported support (R.readers st);
    contributions_supported : nested_supported support (R.contributions st);
    phases_supported : map_keys_supported support (R.phases st);
    side_phases_supported : nested_supported support (R.side_phases st);
    local_sides_supported : nested_supported support (R.local_sides st);
    controlled_supported : set_supported support (R.controlled st);
  }.

  Fixpoint continuation_supported
    (support : list V.t) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop => True
    | R.KSeedLoop roots => Forall (supported support) roots
    | R.KSolveOneLoop owner rest =>
        supported support (R.handle_variable owner) /\
        continuation_supported support rest
    | R.KAfterGet owner target next rest =>
        supported support (R.handle_variable owner) /\
        supported support (R.handle_variable target) /\
        (forall value, Sem.rhs_supported (supported support) (next value)) /\
        continuation_supported support rest
    | R.KAfterSide owner next rest
    | R.KAfterSpawn owner next rest =>
        supported support (R.handle_variable owner) /\
        Sem.rhs_supported (supported support) next /\
        continuation_supported support rest
    end.

  Definition control_supported
    (support : list V.t) (control : R.control) : Prop :=
    match control with
    | R.RunLoop => True
    | R.RunSeeds roots | R.RunSeedLoop roots =>
        Forall (supported support) roots
    | R.RunSolveOne owner rest | R.RunSolveOneLoop owner rest =>
        supported support (R.handle_variable owner) /\
        continuation_supported support rest
    | R.RunRhs owner body rest =>
        supported support (R.handle_variable owner) /\
        Sem.rhs_supported (supported support) body /\
        continuation_supported support rest
    | R.AfterGet owner target next rest =>
        supported support (R.handle_variable owner) /\
        supported support (R.handle_variable target) /\
        (forall value, Sem.rhs_supported (supported support) (next value)) /\
        continuation_supported support rest
    | R.AfterSide owner next rest | R.AfterSpawn owner next rest =>
        supported support (R.handle_variable owner) /\
        Sem.rhs_supported (supported support) next /\
        continuation_supported support rest
    end.

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
    destruct (V.eq_dec observed x) as [-> | Hneq]; auto.
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
    apply SL.add_spec in Hmem. destruct Hmem as [-> | Hmem]; auto.
  Qed.

  Lemma set_elements_supported :
    forall support values,
      set_supported support values ->
      forall x, List.In x (S.elements values) -> supported support x.
  Proof.
    intros support values Hvalues x Hin.
    apply Hvalues, SL.mem_spec. exact Hin.
  Qed.

  Lemma queue_insert_members :
    forall entry queue observed,
      List.In observed (R.queue_insert entry queue) ->
      observed = entry \/ List.In observed queue.
  Proof.
    intros entry queue observed Hin. unfold R.queue_insert in Hin.
    destruct (R.queue_contains_rank (R.handle_rank entry) queue).
    - now right.
    - now apply queue_insert_fresh_members in Hin.
  Qed.

  Lemma queue_supported_insert :
    forall support queue entry,
      supported support (R.handle_variable entry) ->
      queue_supported support queue ->
      queue_supported support (R.queue_insert entry queue).
  Proof.
    intros support queue entry Hentry Hqueue observed Hin.
    apply queue_insert_members in Hin. destruct Hin as [-> | Hin]; auto.
  Qed.

  Lemma queue_supported_pop :
    forall support queue entry rest,
      queue_supported support queue ->
      R.queue_pop queue = Some (entry, rest) ->
      supported support (R.handle_variable entry) /\
      queue_supported support rest.
  Proof.
    intros support queue entry rest Hqueue Hpop.
    destruct queue as [|head tail]; cbn in Hpop; try discriminate.
    inversion Hpop; subst. split.
    - apply Hqueue. now left.
    - intros observed Hin. apply Hqueue. now right.
  Qed.

  Lemma nested_supported_empty :
    forall A support, nested_supported support (M.empty (M.t A)).
  Proof.
    intros A support. split.
    - apply map_keys_supported_empty.
    - intros outer inner value Hlookup. unfold R.lookup_map in Hlookup.
      rewrite ML.lookup_empty, ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma nested_supported_update :
    forall A support (table : M.t (M.t A)) outer inner value,
      supported support outer -> supported support inner ->
      nested_supported support table ->
      nested_supported support (R.update_map table outer inner value).
  Proof.
    intros A support table outer inner value Houter Hinner
      [Hkeys Hnested]. split.
    - unfold R.update_map. now apply map_keys_supported_update.
    - intros observed_outer observed_inner old Hlookup.
      destruct (V.eq_dec observed_outer outer) as [-> | Houter_neq].
      + split; [exact Houter |].
        unfold R.update_map, R.lookup_map in Hlookup.
        rewrite ML.lookup_update_same in Hlookup.
        destruct (V.eq_dec observed_inner inner) as [-> | Hinner_neq]; auto.
        rewrite ML.lookup_update_other in Hlookup by exact Hinner_neq.
        exact (proj2 (Hnested outer observed_inner old Hlookup)).
      + unfold R.update_map, R.lookup_map in Hlookup.
        rewrite ML.lookup_update_other in Hlookup by exact Houter_neq.
        exact (Hnested observed_outer observed_inner old Hlookup).
  Qed.

  Lemma nested_supported_replace_row :
    forall A support (table : M.t (M.t A)) outer row,
      supported support outer -> map_keys_supported support row ->
      nested_supported support table ->
      nested_supported support (M.update table outer row).
  Proof.
    intros A support table outer row Houter Hrow [Hkeys Hnested]. split.
    - now apply map_keys_supported_update.
    - intros observed_outer observed_inner value Hlookup.
      destruct (V.eq_dec observed_outer outer) as [-> | Hneq].
      + split; [exact Houter |]. unfold R.lookup_map in Hlookup.
        rewrite ML.lookup_update_same in Hlookup.
        now apply (Hrow observed_inner value).
      + unfold R.lookup_map in Hlookup.
        rewrite ML.lookup_update_other in Hlookup by exact Hneq.
        exact (Hnested observed_outer observed_inner value Hlookup).
  Qed.

  Lemma readers_supported_empty :
    forall support, readers_supported support (M.empty S.t).
  Proof.
    intros support. split; [apply map_keys_supported_empty |].
    intros target owner Hmem. unfold R.lookup_set in Hmem.
    rewrite ML.lookup_empty, SL.empty_spec in Hmem. discriminate.
  Qed.

  Lemma readers_supported_update :
    forall support readers target owners,
      supported support target -> set_supported support owners ->
      readers_supported support readers ->
      readers_supported support (M.update readers target owners).
  Proof.
    intros support readers target owners Htarget Howners
      [Hkeys Hreaders]. split.
    - now apply map_keys_supported_update.
    - intros observed owner Hmem.
      destruct (V.eq_dec observed target) as [-> | Hneq].
      + unfold R.lookup_set in Hmem. rewrite ML.lookup_update_same in Hmem.
        now apply Howners.
      + unfold R.lookup_set in Hmem.
        rewrite ML.lookup_update_other in Hmem by exact Hneq.
        now apply (Hreaders observed owner).
  Qed.

  Lemma empty_state_supported :
    forall support, state_supported support R.empty_state.
  Proof.
    intros support. constructor; cbn.
    - apply RankFinite.generated_empty.
    - apply map_keys_supported_empty.
    - intros entry [].
    - apply set_supported_empty.
    - apply readers_supported_empty.
    - apply nested_supported_empty.
    - apply map_keys_supported_empty.
    - apply nested_supported_empty.
    - apply nested_supported_empty.
    - apply set_supported_empty.
  Qed.

  Lemma with_ranking_supported :
    forall support st ranking,
      state_supported support st ->
      RankFinite.generated support ranking ->
      state_supported support (R.with_ranking st ranking).
  Proof.
    intros support st ranking Hstate Hranking.
    destruct Hstate. constructor; cbn; assumption.
  Qed.

  Lemma with_queue_supported :
    forall support st queue,
      state_supported support st -> queue_supported support queue ->
      state_supported support (R.with_queue st queue).
  Proof.
    intros support st queue Hstate Hqueue.
    destruct Hstate. constructor; cbn; assumption.
  Qed.

  Lemma with_started_supported :
    forall support st started,
      state_supported support st -> set_supported support started ->
      state_supported support (R.with_started st started).
  Proof.
    intros support st started Hstate Hstarted.
    destruct Hstate. constructor; cbn; assumption.
  Qed.

  Lemma materialize_supported :
    forall support st target,
      supported support target -> state_supported support st ->
      state_supported support (R.materialize st target).
  Proof.
    intros support st target Htarget Hstate.
    unfold R.materialize, R.is_materialized.
    destruct (M.lookup (R.sigma st) target); [exact Hstate |].
    destruct Hstate. constructor; cbn; try assumption.
    now apply map_keys_supported_update.
  Qed.

  Lemma observe_supported :
    forall support st x next entry,
      supported support x -> state_supported support st ->
      R.observe st x = (next, entry) ->
      state_supported support next /\
      supported support (R.handle_variable entry).
  Proof.
    intros support st x next entry Hx Hstate Hobserve.
    split.
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) x) as [ranking rank]
        eqn:Hrank.
      assert (Hgenerated : RankFinite.generated support ranking).
      {
        eapply RankFinite.generated_observe.
        - exact (state_ranking_generated Hstate).
        - exact Hx.
        - exact Hrank.
      }
      inversion Hobserve; subst.
      now apply with_ranking_supported.
    - rewrite (@observed_handle_variable st x next entry Hobserve).
      exact Hx.
  Qed.

  Lemma enqueue_handle_supported :
    forall support st entry,
      supported support (R.handle_variable entry) ->
      state_supported support st ->
      state_supported support (R.enqueue_handle st entry).
  Proof.
    intros support st entry Hentry Hstate. apply with_queue_supported.
    - exact Hstate.
    - apply queue_supported_insert; [exact Hentry |].
      exact (queue_is_supported Hstate).
  Qed.

  Lemma enqueue_supported :
    forall support st target,
      supported support target -> state_supported support st ->
      state_supported support (R.enqueue st target).
  Proof.
    intros support st target Htarget Hstate. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    destruct (@observe_supported support st target next entry
      Htarget Hstate Hobserve) as [Hnext Hentry].
    now apply enqueue_handle_supported.
  Qed.

  Lemma enqueue_all_supported :
    forall support targets st,
      (forall x, List.In x targets -> supported support x) ->
      state_supported support st ->
      state_supported support (R.enqueue_all st targets).
  Proof.
    intros support targets. induction targets as [|x xs IH];
      intros st Htargets Hstate; cbn; auto.
    apply IH.
    - intros y Hy. apply Htargets. now right.
    - apply enqueue_supported; [apply Htargets; now left | exact Hstate].
  Qed.

  Lemma promote_controlled_supported :
    forall support st target,
      supported support target -> state_supported support st ->
      state_supported support (R.promote_controlled st target).
  Proof.
    intros support st target Htarget Hstate. destruct Hstate.
    constructor; cbn; try assumption. now apply set_supported_add.
  Qed.

  Lemma add_reader_supported :
    forall support st target owner,
      supported support target -> supported support owner ->
      state_supported support st ->
      state_supported support (R.add_reader st target owner).
  Proof.
    intros support st target owner Htarget Howner Hstate.
    destruct Hstate. constructor; cbn; try assumption.
    apply readers_supported_update; [exact Htarget | |assumption].
    apply set_supported_add; [exact Howner |].
    intros x Hmem. exact ((proj2 readers_are_supported0) target x Hmem).
  Qed.

  Lemma get_ready_supported :
    forall support st owner target,
      supported support (R.handle_variable owner) ->
      supported support (R.handle_variable target) ->
      state_supported support st ->
      state_supported support (R.get_ready_state st owner target).
  Proof.
    intros support st owner target Howner Htarget Hstate.
    unfold R.get_ready_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target)).
    - apply materialize_supported; [exact Htarget |].
      now apply add_reader_supported.
    - apply materialize_supported; [exact Htarget |].
      apply add_reader_supported; [exact Htarget | exact Howner |].
      now apply promote_controlled_supported.
  Qed.

  Lemma reset_local_sides_supported :
    forall support st owner,
      supported support owner -> state_supported support st ->
      state_supported support (R.reset_local_sides st owner).
  Proof.
    intros support st owner Howner Hstate. destruct Hstate.
    constructor; cbn; try assumption.
    apply nested_supported_replace_row; [exact Howner | |assumption].
    apply map_keys_supported_empty.
  Qed.

  Lemma start_evaluation_supported :
    forall support st owner,
      supported support owner -> state_supported support st ->
      state_supported support (R.start_evaluation st owner).
  Proof.
    intros support st owner Howner Hstate. unfold R.start_evaluation.
    apply reset_local_sides_supported; [exact Howner |].
    now apply materialize_supported.
  Qed.

  Lemma start_owner_supported :
    forall support st owner,
      supported support (R.handle_variable owner) ->
      state_supported support st ->
      state_supported support
        (R.with_started
          (R.start_evaluation st (R.handle_variable owner))
          (S.add (R.handle_variable owner)
            (R.started (R.start_evaluation st (R.handle_variable owner))))).
  Proof.
    intros support st owner Howner Hstate. apply with_started_supported.
    - now apply start_evaluation_supported.
    - apply set_supported_add; [exact Howner |].
      replace
        (R.started (R.start_evaluation st (R.handle_variable owner)))
        with (R.started st).
      + exact (started_supported Hstate).
      + unfold R.start_evaluation, R.reset_local_sides, R.materialize.
        destruct (R.is_materialized st (R.handle_variable owner));
          reflexivity.
  Qed.

  Lemma record_side_payload_supported :
    forall support st source target raw,
      supported support source -> supported support target ->
      state_supported support st ->
      state_supported support (R.record_side_payload st source target raw).
  Proof.
    intros support st source target raw Hsource Htarget Hstate.
    unfold R.record_side_payload.
    destruct (U.update true target (R.stored_side_phase st source target)
      (R.stored_contribution st source target)
      (R.accumulated_side_input st source target raw)) as [phase value].
    destruct Hstate. constructor; cbn; try assumption;
      now apply nested_supported_update.
  Qed.

  Lemma side_ready_supported :
    forall support st source target raw,
      supported support (R.handle_variable source) ->
      supported support (R.handle_variable target) ->
      state_supported support st ->
      state_supported support (R.side_ready_state st source target raw).
  Proof.
    intros support st source target raw Hsource Htarget Hstate.
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source)).
    - now apply record_side_payload_supported.
    - apply promote_controlled_supported; [exact Hsource |].
      now apply record_side_payload_supported.
  Qed.

  Lemma write_changed_value_supported :
    forall support st owner value,
      supported support owner -> state_supported support st ->
      state_supported support (R.write_changed_value st owner value).
  Proof.
    intros support st owner value Howner Hstate.
    unfold R.write_changed_value.
    set (st1 := R.with_sigma st (M.update (R.sigma st) owner value)).
    assert (Hst1 : state_supported support st1).
    { unfold st1. destruct Hstate. constructor; cbn; try assumption.
      now apply map_keys_supported_update. }
    set (targets := S.elements (R.lookup_set (R.readers st) owner)).
    set (st2 := R.enqueue_all st1 targets).
    assert (Hst2 : state_supported support st2).
    { unfold st2. apply enqueue_all_supported; [|exact Hst1].
      intros x Hin. apply set_elements_supported with
        (values := R.lookup_set (R.readers st) owner); [|exact Hin].
      intros y Hmem. exact ((proj2 (readers_are_supported Hstate)) owner y Hmem). }
    unfold st2, st1, targets in *.
    destruct Hst2. constructor; cbn; try assumption.
    apply readers_supported_update; [exact Howner | |assumption].
    apply set_supported_empty.
  Qed.

  Lemma update_phase_supported :
    forall support st owner phase,
      supported support owner -> state_supported support st ->
      state_supported support
        (R.with_phases st (M.update (R.phases st) owner phase)).
  Proof.
    intros support st owner phase Howner Hstate. destruct Hstate.
    constructor; cbn; try assumption. now apply map_keys_supported_update.
  Qed.

  Lemma set_value_supported :
    forall support st owner direct,
      supported support owner -> state_supported support st ->
      state_supported support (R.set_value st owner direct).
  Proof.
    intros support st owner direct Howner Hstate. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner)); auto.
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
        as [phase value]; cbn.
      destruct (R.equivalent value (R.sigma_value st owner)).
      + now apply update_phase_supported.
      + apply write_changed_value_supported; [exact Howner |].
        now apply update_phase_supported.
    - now apply write_changed_value_supported.
  Qed.

  Lemma continue_supported :
    forall support k,
      continuation_supported support k ->
      control_supported support (R.continue k).
  Proof. intros support k Hsupported. destruct k; exact Hsupported. Qed.

  Lemma initial_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots),
      config_supported (Sem.support finite) (R.initial_config roots).
  Proof.
    intros tf roots finite. split; cbn.
    - apply empty_state_supported.
    - rewrite Forall_forall. exact (Sem.initial_supported finite).
  Qed.

  Lemma next_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      config_supported (Sem.support finite) before ->
      R.next_config tf before = Some after ->
      config_supported (Sem.support finite) after.
  Proof.
    intros tf roots finite [st control] after [Hstate Hcontrol] Hstep.
    cbn in Hstep. destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; clear Hstep;
      cbn in Hcontrol |- *.
    all: cbn in Hstate.
    - destruct (@queue_supported_pop (Sem.support finite) (R.queue st) h w
        (queue_is_supported Hstate) Hcase) as [Howner Hrest].
      split; [now apply with_queue_supported |]. cbn. now split.
    - split; [exact Hstate | exact I].
    - inversion Hcontrol as [|? ? Hroot Hroots]; subst.
      destruct (@observe_supported (Sem.support finite) st t s h
        Hroot Hstate Hcase0) as [Hs _]. split; assumption.
    - inversion Hcontrol as [|? ? Hroot Hroots]; subst.
      destruct (@observe_supported (Sem.support finite) st t s h
        Hroot Hstate Hcase0) as [Hs Hh]. split; [exact Hs |].
      cbn. split; assumption.
    - destruct (@queue_supported_pop (Sem.support finite) (R.queue st) h w
        (queue_is_supported Hstate) Hcase) as [Howner Hrest].
      split; [now apply with_queue_supported |]. cbn. split; assumption.
    - split; assumption.
    - destruct Hcontrol as [Howner Hk]. split.
      + apply start_owner_supported; assumption.
      + cbn. repeat split; auto. apply Sem.system_supported, Howner.
    - destruct Hcontrol as [Howner Hk].
      destruct (@queue_supported_pop (Sem.support finite) (R.queue st) h0 w
        (queue_is_supported Hstate) Hcase0) as [_ Hrest].
      split; [now apply with_queue_supported |]. cbn. split; assumption.
    - destruct Hcontrol as [Howner Hk].
      destruct (@queue_supported_pop (Sem.support finite) (R.queue st) h0 w
        (queue_is_supported Hstate) Hcase0) as [Hnext Hrest].
      split; [now apply with_queue_supported |].
      cbn. repeat split; assumption.
    - split; [exact Hstate |].
      apply continue_supported. exact (proj2 Hcontrol).
    - split.
      + apply set_value_supported; [exact (proj1 Hcontrol) | exact Hstate].
      + cbn. split; [exact (proj1 Hcontrol) | exact (proj2 (proj2 Hcontrol))].
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_get_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split; [apply get_ready_supported; assumption |].
      cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_get_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split; [exact Hs |]. cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_get_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      assert (Henqueued : state_supported (Sem.support finite)
        (R.enqueue_handle s h0)) by
        (apply enqueue_handle_supported; assumption).
      split; [apply get_ready_supported; assumption |].
      cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_side_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      assert (Hready : state_supported (Sem.support finite)
        (R.side_ready_state s h h0 t0)) by
        (apply side_ready_supported; assumption).
      split; [exact Hready |]. cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_side_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      assert (Hready : state_supported (Sem.support finite)
        (R.side_ready_state s h h0 t0)) by
        (apply side_ready_supported; assumption).
      split; [now apply enqueue_handle_supported |].
      cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_side_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split; [apply side_ready_supported; assumption |].
      cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split; [exact Hs |]. cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split; [exact Hs |]. cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Hbody Hk]].
      destruct (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
      destruct (@observe_supported (Sem.support finite) st t s h0
        Htarget Hstate Hcase0) as [Hs Htarget_handle].
      split.
      + apply materialize_supported; [exact Htarget |].
        now apply enqueue_handle_supported.
      + cbn. repeat split; auto.
    - destruct Hcontrol as [Howner [Htarget [Hnext Hk]]]. split.
      + apply get_ready_supported; assumption.
      + cbn. repeat split; auto.
    - split; [exact Hstate | exact Hcontrol].
    - split; [exact Hstate | exact Hcontrol].
  Qed.

  Lemma steps_supported :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      config_supported (Sem.support finite) before ->
      Sem.steps tf before after ->
      config_supported (Sem.support finite) after.
  Proof.
    intros tf roots finite before after Hsupported Hsteps.
    induction Hsteps; auto.
    apply IHHsteps. eapply next_config_supported; eauto.
  Qed.

  Theorem reachable_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots) after,
      Sem.steps tf (R.initial_config roots) after ->
      config_supported (Sem.support finite) after.
  Proof.
    intros tf roots finite after Hsteps. eapply steps_supported; eauto.
    apply initial_config_supported.
  Qed.

  Theorem reachable_rank_bound :
    forall tf roots (finite : Sem.finite_system tf roots) after x rank,
      Sem.steps tf (R.initial_config roots) after ->
      R.Ranking.lookup (R.ranking (R.cfg_state after)) x = Some rank ->
      rank < RankFinite.bound (Sem.support finite).
  Proof.
    intros tf roots finite after x rank Hsteps Hlookup.
    eapply RankFinite.generated_lookup_bound.
    - exact (handles_rank_valid (reachable_handles_valid Hsteps)).
    - exact (state_ranking_generated
        (proj1 (reachable_config_supported finite Hsteps))).
    - exact Hlookup.
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
      rewrite Hafter in Hold_after. inversion Hold_after. reflexivity.
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
  Module Seed.
  Fixpoint continuation_seed_measure (k : R.continuation) : nat :=
    match k with
    | R.KLoop => 0
    | R.KSeedLoop roots => 2 * length roots + 2
    | R.KSolveOneLoop _ rest
    | R.KAfterGet _ _ _ rest
    | R.KAfterSide _ _ rest
    | R.KAfterSpawn _ _ rest => continuation_seed_measure rest
    end.

  Definition seed_measure (control : R.control) : nat :=
    match control with
    | R.RunLoop => 0
    | R.RunSeeds roots => 2 * length roots + 1
    | R.RunSeedLoop roots => 2 * length roots + 2
    | R.RunSolveOne _ rest
    | R.RunSolveOneLoop _ rest
    | R.RunRhs _ _ rest
    | R.AfterGet _ _ _ rest
    | R.AfterSide _ _ rest
    | R.AfterSpawn _ _ rest => continuation_seed_measure rest
    end.

  Lemma continue_seed_measure :
    forall k,
      seed_measure (R.continue k) <= continuation_seed_measure k.
  Proof. intros k. destruct k; cbn; lia. Qed.

  Theorem next_config_seed_measure_nonincreasing :
    forall tf before after,
      R.next_config tf before = Some after ->
      seed_measure (R.cfg_control after) <=
      seed_measure (R.cfg_control before).
  Proof.
    intros tf [st control] after Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn; try lia;
      apply continue_seed_measure.
  Qed.

  Theorem run_seeds_step_strict :
    forall tf st roots after,
      R.next_config tf
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds roots |} =
        Some after ->
      seed_measure (R.cfg_control after) < seed_measure (R.RunSeeds roots).
  Proof.
    intros tf st roots after Hstep. cbn in Hstep.
    destruct roots as [|root rest].
    - inversion Hstep; subst. cbn. lia.
    - destruct (R.observe st root) as [next entry] eqn:Hobserve.
      destruct (S.mem root (R.started next)); inversion Hstep; subst; cbn; lia.
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
    rewrite Hempty in Hstep. inversion Hstep; subst. cbn. lia.
  Qed.
  End Seed.

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
    intros tf [st control] after Hordered Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in *;
      try exact Hordered; try exact I;
      try (apply continuation_ordered_continue; exact Hordered).
    - split.
      + eapply owner_may_pop_higher; eauto.
      + exact Hordered.
    - exact (continuation_ordered_continue h c Hordered).
    - split; [exact Hcase2 | exact Hordered].
    - apply Bool.andb_true_iff in Hcase2 as [Hlt _].
      split; [exact Hlt | exact Hordered].
    - split; [exact Hcase2 | exact Hordered].
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
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact H.
  Qed.

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
        solved_materialize, solved_enqueue_handle, solved_set_value.
    eapply solved_same_sigma; [reflexivity |].
    now apply solved_start_evaluation.
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
    - destruct Hsolved as [Howner _].
      eapply continuation_ready_continue; eassumption.
    - split; [reflexivity | exact Hready].
    - exact (proj2 Hready).
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

  Module Sim.
  Inductive scoped_continuation
    (owner : R.handle) (base : R.continuation) :
    R.continuation -> Prop :=
  | ScopedContinuationSolve :
      scoped_continuation owner base
        (R.KSolveOneLoop owner base)
  | ScopedContinuationGet :
      forall target next,
        scoped_continuation owner base
          (R.KAfterGet owner target next base)
  | ScopedContinuationSide :
      forall next,
        scoped_continuation owner base
          (R.KAfterSide owner next base)
  | ScopedContinuationSpawn :
      forall next,
        scoped_continuation owner base
          (R.KAfterSpawn owner next base)
  | ScopedContinuationUnderSolve :
      forall current rest,
        scoped_continuation owner base rest ->
        scoped_continuation owner base
          (R.KSolveOneLoop current rest)
  | ScopedContinuationUnderGet :
      forall current target next rest,
        scoped_continuation owner base rest ->
        scoped_continuation owner base
          (R.KAfterGet current target next rest)
  | ScopedContinuationUnderSide :
      forall current next rest,
        scoped_continuation owner base rest ->
        scoped_continuation owner base
          (R.KAfterSide current next rest)
  | ScopedContinuationUnderSpawn :
      forall current next rest,
        scoped_continuation owner base rest ->
        scoped_continuation owner base
          (R.KAfterSpawn current next rest).

  Definition continuation_in_scope
    (owner : R.handle) (base : R.continuation)
    (active : R.handle) (rest : R.continuation) : Prop :=
    (active = owner /\ rest = base) \/
    scoped_continuation owner base rest.

  Definition control_in_scope
    (owner : R.handle) (base : R.continuation)
    (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
    | R.RunSolveOne active rest
    | R.RunSolveOneLoop active rest
    | R.RunRhs active _ rest
    | R.AfterGet active _ _ rest
    | R.AfterSide active _ rest
    | R.AfterSpawn active _ rest =>
        continuation_in_scope owner base active rest
    end.

  Inductive scoped_until_steps
    (owner : R.handle) (base : R.continuation)
    (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | ScopedUntilRefl :
      forall c, scoped_until_steps owner base tf c c
  | ScopedUntilStep :
      forall first next final,
        control_in_scope owner base (R.cfg_control first) ->
        Sem.step tf first next ->
        scoped_until_steps owner base tf next final ->
        scoped_until_steps owner base tf first final.

  Lemma scoped_until_semantic :
    forall owner base tf first final,
      scoped_until_steps owner base tf first final ->
      Sem.steps tf first final.
  Proof.
    intros owner base tf first final Hsteps. induction Hsteps.
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma scoped_until_transitive :
    forall owner base tf first middle final,
      scoped_until_steps owner base tf first middle ->
      scoped_until_steps owner base tf middle final ->
      scoped_until_steps owner base tf first final.
  Proof.
    intros owner base tf first middle final Hfirst Hfinal.
    induction Hfirst; [exact Hfinal |]. econstructor; eauto.
  Qed.

  Lemma scoped_continuation_embed :
    forall outer outer_base inner inner_base rest,
      scoped_continuation outer outer_base inner_base ->
      scoped_continuation inner inner_base rest ->
      scoped_continuation outer outer_base rest.
  Proof.
    intros outer outer_base inner inner_base rest Hbase Hrest.
    induction Hrest; constructor; assumption.
  Qed.

  Lemma control_in_scope_lift :
    forall outer outer_base inner inner_base control,
      scoped_continuation outer outer_base inner_base ->
      control_in_scope inner inner_base control ->
      control_in_scope outer outer_base control.
  Proof.
    intros outer outer_base inner inner_base control Hbase Hscope.
    assert (Hlift : forall active rest,
      continuation_in_scope inner inner_base active rest ->
      continuation_in_scope outer outer_base active rest).
    {
      intros active rest [[-> ->] | Hrest].
      - right. exact Hbase.
      - right. eapply scoped_continuation_embed; eassumption.
    }
    destruct control; cbn in *; try contradiction; eauto.
  Qed.

  Lemma scoped_until_lift :
    forall outer outer_base inner inner_base tf first final,
      scoped_continuation outer outer_base inner_base ->
      scoped_until_steps inner inner_base tf first final ->
      scoped_until_steps outer outer_base tf first final.
  Proof.
    intros outer outer_base inner inner_base tf first final Hbase Hsteps.
    induction Hsteps; [constructor |]. econstructor; eauto using
      control_in_scope_lift.
  Qed.

  Lemma steps_transitive :
    forall tf first middle last,
      Sem.steps tf first middle ->
      Sem.steps tf middle last ->
      Sem.steps tf first last.
  Proof.
    intros tf first middle last Hfirst Hlast.
    induction Hfirst; [exact Hlast |]. econstructor; eauto.
  Qed.

  Lemma steps_append_one :
    forall tf first middle last,
      Sem.steps tf first middle ->
      Sem.step tf middle last ->
      Sem.steps tf first last.
  Proof.
    intros. eapply steps_transitive; [eassumption |].
    econstructor; [eassumption | constructor].
  Qed.

  Lemma one_step :
    forall tf before after,
      Sem.step tf before after -> Sem.steps tf before after.
  Proof. intros. econstructor; [eassumption | constructor]. Qed.

  Definition episode_complete
    (tf : R.ConstraintSystem.system)
    (owner : R.handle) (k : R.continuation)
    (start : R.config) : Prop :=
    exists st,
      scoped_until_steps owner k tf start
        {| R.cfg_state := st; R.cfg_control := R.continue k |} /\
      queue_strictly_below owner st.

  Definition higher_episodes_complete
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (roots : list V.t) (owner : R.handle) : Prop :=
    forall target k start,
      List.In (R.handle_variable target) support ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true ->
      Sem.steps tf (R.initial_config roots) start ->
      R.cfg_control start = R.RunSolveOne target k ->
      episode_complete tf target k start.

  Definition rhs_finishes
    (tf : R.ConstraintSystem.system)
    (owner : R.handle) (body : R.ConstraintSystem.rhs)
    (k : R.continuation) (start : R.config) : Prop :=
    exists st,
      scoped_until_steps owner k tf start
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner k |}.

  Lemma reachable_after_steps :
    forall tf roots first last,
      Sem.steps tf (R.initial_config roots) first ->
      Sem.steps tf first last ->
      Sem.steps tf (R.initial_config roots) last.
  Proof. intros. eapply steps_transitive; eauto. Qed.

  Lemma rhs_finishes_one_step :
    forall tf owner body k start after,
      control_in_scope owner k (R.cfg_control start) ->
      Sem.step tf start after ->
      rhs_finishes tf owner body k after ->
      rhs_finishes tf owner body k start.
  Proof.
    intros tf owner body k start after Hscope Hstep [done Hdone].
    exists done. econstructor; eauto.
  Qed.

  Lemma rhs_finishes_after_child :
    forall tf owner body k start child child_owner child_k returned after,
      control_in_scope owner k (R.cfg_control start) ->
      Sem.step tf start child ->
      scoped_continuation owner k child_k ->
      scoped_until_steps child_owner child_k tf child returned ->
      control_in_scope owner k (R.cfg_control returned) ->
      Sem.step tf returned after ->
      rhs_finishes tf owner body k after ->
      rhs_finishes tf owner body k start.
  Proof.
    intros tf owner body k start child child_owner child_k returned after
      Hstart Hstep Hnested Hchild Hreturned Hreturn [done Hdone].
    exists done. econstructor; [exact Hstart | exact Hstep |].
    eapply scoped_until_transitive.
    - eapply scoped_until_lift; eassumption.
    - econstructor; eauto.
  Qed.

  Lemma run_ret_finishes :
    forall tf st owner direct k,
      rhs_finishes tf owner (R.ConstraintSystem.Ret direct) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}.
  Proof.
    intros. exists (R.set_value st (R.handle_variable owner) direct).
    econstructor.
    - cbn. left. split; reflexivity.
    - reflexivity.
    - constructor.
  Qed.

  End Sim.

  Module Episodes.
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

  Lemma rhs_child_well_founded : well_founded rhs_child.
  Proof.
    unfold well_founded. intro body.
    induction body using R.ConstraintSystem.rhs_ind.
    - constructor. intros child Hchild. inversion Hchild.
    - constructor. intros child Hchild. inversion Hchild; subst. apply H.
    - constructor. intros child Hchild. inversion Hchild; subst. exact IHbody.
    - constructor. intros child Hchild. inversion Hchild; subst. exact IHbody.
  Qed.

  Lemma rhs_supported_get_inv :
    forall supported target next,
      Sem.rhs_supported supported (R.ConstraintSystem.Get target next) ->
      supported target /\
      forall value, Sem.rhs_supported supported (next value).
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma rhs_supported_side_inv :
    forall supported target value next,
      Sem.rhs_supported supported
        (R.ConstraintSystem.Side target value next) ->
      supported target /\ Sem.rhs_supported supported next.
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma rhs_supported_spawn_inv :
    forall supported target next,
      Sem.rhs_supported supported (R.ConstraintSystem.Spawn target next) ->
      supported target /\ Sem.rhs_supported supported next.
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma run_get_finishes :
    forall support tf roots owner st target next k,
      List.In target support ->
      Sim.higher_episodes_complete support tf roots owner ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |} ->
      (forall value next_state,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner (next value) k |} ->
        Sim.rhs_finishes tf owner (next value) k
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner (next value) k |}) ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Get target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
    destruct (R.observe st target) as [observed target_handle]
      eqn:Hobserve.
    destruct (R.is_materialized observed target) eqn:Hmaterialized.
    - set (ready := R.get_ready_state observed owner target_handle).
      set (after :=
        {| R.cfg_state := ready;
           R.cfg_control :=
             R.RunRhs owner (next (R.sigma_value ready target)) k |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}
        after).
      {
        unfold Sem.step, after, ready. cbn.
        now rewrite Hobserve, Hmaterialized.
      }
      assert (Hafter : Sem.steps tf (R.initial_config roots) after).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.
    - destruct (Nat.ltb (R.handle_rank owner)
        (R.handle_rank target_handle)) eqn:Hhigher.
      + set (child_k := R.KAfterGet owner target_handle next k).
        set (child :=
          {| R.cfg_state := observed;
             R.cfg_control := R.RunSolveOne target_handle child_k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs owner (R.ConstraintSystem.Get target next) k |}
          child).
        {
          unfold Sem.step, child, child_k. cbn.
          rewrite Hobserve, Hmaterialized.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate; try rewrite Hhigher; reflexivity.
        }
        assert (Hchild : Sem.steps tf (R.initial_config roots) child).
        { eapply Sim.steps_append_one; eauto. }
        assert (Htarget_handle :
          List.In (R.handle_variable target_handle) support).
        {
          rewrite (observed_handle_variable
            st target Hobserve).
          exact Htarget.
        }
        destruct (Hchildren target_handle child_k child
          Htarget_handle Hhigher Hchild eq_refl)
          as [child_st [Hepisode Hbelow]].
        set (returned :=
          {| R.cfg_state := child_st;
             R.cfg_control := R.continue child_k |}).
        assert (Hreturned :
          Sem.steps tf (R.initial_config roots) returned).
        {
          unfold returned. eapply Sim.steps_transitive; [exact Hchild |].
          now apply Sim.scoped_until_semantic in Hepisode.
        }
        assert (Htarget_solved :
          R.is_materialized child_st (R.handle_variable target_handle) = true).
        {
          unfold returned, child_k in Hreturned. cbn in Hreturned.
          eapply Progress.reachable_after_get_materialized; eauto.
        }
        set (ready := R.get_ready_state child_st owner target_handle).
        set (after :=
          {| R.cfg_state := ready;
             R.cfg_control := R.RunRhs owner
               (next (R.sigma_value ready (R.handle_variable target_handle)))
               k |}).
        assert (Hreturn : Sem.step tf returned after).
        {
          unfold Sem.step, returned, after, child_k, ready. cbn.
          now rewrite Htarget_solved.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        {
          eapply Sim.steps_append_one; [exact Hreturned | exact Hreturn].
        }
        assert (Hdone : Sim.rhs_finishes tf owner
          (next (R.sigma_value ready (R.handle_variable target_handle))) k
          after).
        { apply Hfinish. exact Hafter. }
        eapply Sim.rhs_finishes_after_child with
          (child := child) (child_owner := target_handle)
          (child_k := child_k) (returned := returned) (after := after);
          eauto.
        * cbn. left. split; reflexivity.
        * apply Sim.ScopedContinuationGet.
        * cbn. left. split; reflexivity.
      + set (ready := R.get_ready_state
          (R.enqueue_handle observed target_handle) owner target_handle).
        set (after :=
          {| R.cfg_state := ready;
             R.cfg_control := R.RunRhs owner
               (next (R.sigma_value ready target)) k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs owner (R.ConstraintSystem.Get target next) k |}
          after).
        {
          unfold Sem.step, after, ready. cbn.
          rewrite Hobserve, Hmaterialized.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate; try rewrite Hhigher; reflexivity.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        { eapply Sim.steps_append_one; eauto. }
        eapply Sim.rhs_finishes_one_step; eauto.
        cbn. left. split; reflexivity.
  Qed.

  Lemma run_spawn_finishes :
    forall support tf roots owner st target next k,
      List.In target support ->
      Sim.higher_episodes_complete support tf roots owner ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |} ->
      (forall next_state,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner next k |} ->
        Sim.rhs_finishes tf owner next k
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner next k |}) ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Spawn target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
    destruct (R.observe st target) as [observed target_handle]
      eqn:Hobserve.
    destruct (R.is_materialized observed target) eqn:Hmaterialized.
    - set (after :=
        {| R.cfg_state := observed;
           R.cfg_control := R.RunRhs owner next k |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}
        after).
      {
        unfold Sem.step, after. cbn.
        now rewrite Hobserve, Hmaterialized.
      }
      assert (Hafter : Sem.steps tf (R.initial_config roots) after).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.
    - destruct (Nat.ltb (R.handle_rank owner)
        (R.handle_rank target_handle)) eqn:Hhigher.
      + set (child_k := R.KAfterSpawn owner next k).
        set (child :=
          {| R.cfg_state := observed;
             R.cfg_control := R.RunSolveOne target_handle child_k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}
          child).
        {
          unfold Sem.step, child, child_k. cbn.
          rewrite Hobserve, Hmaterialized.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate; try rewrite Hhigher; reflexivity.
        }
        assert (Hchild : Sem.steps tf (R.initial_config roots) child).
        { eapply Sim.steps_append_one; eauto. }
        assert (Htarget_handle :
          List.In (R.handle_variable target_handle) support).
        {
          rewrite (observed_handle_variable st target Hobserve).
          exact Htarget.
        }
        destruct (Hchildren target_handle child_k child
          Htarget_handle Hhigher Hchild eq_refl)
          as [child_st [Hepisode Hbelow]].
        set (returned :=
          {| R.cfg_state := child_st;
             R.cfg_control := R.continue child_k |}).
        set (after :=
          {| R.cfg_state := child_st;
             R.cfg_control := R.RunRhs owner next k |}).
        assert (Hreturn : Sem.step tf returned after).
        { unfold Sem.step, returned, after, child_k. reflexivity. }
        assert (Hreturned :
          Sem.steps tf (R.initial_config roots) returned).
        {
          unfold returned. eapply Sim.steps_transitive; [exact Hchild |].
          now apply Sim.scoped_until_semantic in Hepisode.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        { eapply Sim.steps_append_one; eauto. }
        eapply Sim.rhs_finishes_after_child with
          (child := child) (child_owner := target_handle)
          (child_k := child_k) (returned := returned) (after := after);
          eauto.
        * cbn. left. split; reflexivity.
        * apply Sim.ScopedContinuationSpawn.
        * cbn. left. split; reflexivity.
      + set (ready := R.materialize
          (R.enqueue_handle observed target_handle) target).
        set (after :=
          {| R.cfg_state := ready;
             R.cfg_control := R.RunRhs owner next k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control :=
               R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}
          after).
        {
          unfold Sem.step, after, ready. cbn.
          rewrite Hobserve, Hmaterialized.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate; try rewrite Hhigher; reflexivity.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        { eapply Sim.steps_append_one; eauto. }
        eapply Sim.rhs_finishes_one_step; eauto.
        cbn. left. split; reflexivity.
  Qed.

  Lemma run_side_finishes :
    forall support tf roots owner st target raw next k,
      List.In target support ->
      Sim.higher_episodes_complete support tf roots owner ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |} ->
      (forall next_state,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner next k |} ->
        Sim.rhs_finishes tf owner next k
          {| R.cfg_state := next_state;
             R.cfg_control := R.RunRhs owner next k |}) ->
      Sim.rhs_finishes tf owner
        (R.ConstraintSystem.Side target raw next) k
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}.
  Proof.
    intros support tf roots owner st target raw next k Htarget Hchildren
      Hreachable Hfinish.
    destruct (R.observe st target) as [observed target_handle]
      eqn:Hobserve.
    set (ready := R.side_ready_state observed owner target_handle raw).
    destruct (negb (D.leq (R.aggregate ready target)
      (R.aggregate observed target))) eqn:Hchanged.
    - destruct (andb
        (Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle))
        (negb (R.is_materialized observed target))) eqn:Hchild_case.
      + apply Bool.andb_true_iff in Hchild_case as [Hhigher Hunmaterialized].
        set (child_k := R.KAfterSide owner next k).
        set (child :=
          {| R.cfg_state := ready;
             R.cfg_control := R.RunSolveOne target_handle child_k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs owner
               (R.ConstraintSystem.Side target raw next) k |}
          child).
        {
          unfold Sem.step, child, child_k, ready in *. cbn.
          rewrite Hobserve, Hchanged.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate;
            rewrite Hhigher, Hunmaterialized; reflexivity.
        }
        assert (Hchild : Sem.steps tf (R.initial_config roots) child).
        { eapply Sim.steps_append_one; eauto. }
        assert (Htarget_handle :
          List.In (R.handle_variable target_handle) support).
        {
          rewrite (observed_handle_variable st target Hobserve).
          exact Htarget.
        }
        destruct (Hchildren target_handle child_k child
          Htarget_handle Hhigher Hchild eq_refl)
          as [child_st [Hepisode Hbelow]].
        set (returned :=
          {| R.cfg_state := child_st;
             R.cfg_control := R.continue child_k |}).
        set (after :=
          {| R.cfg_state := child_st;
             R.cfg_control := R.RunRhs owner next k |}).
        assert (Hreturn : Sem.step tf returned after).
        { unfold Sem.step, returned, after, child_k. reflexivity. }
        assert (Hreturned :
          Sem.steps tf (R.initial_config roots) returned).
        {
          unfold returned. eapply Sim.steps_transitive; [exact Hchild |].
          now apply Sim.scoped_until_semantic in Hepisode.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        { eapply Sim.steps_append_one; eauto. }
        eapply Sim.rhs_finishes_after_child with
          (child := child) (child_owner := target_handle)
          (child_k := child_k) (returned := returned) (after := after);
          eauto.
        * cbn. left. split; reflexivity.
        * apply Sim.ScopedContinuationSide.
        * cbn. left. split; reflexivity.
      + set (after :=
          {| R.cfg_state := R.enqueue_handle ready target_handle;
             R.cfg_control := R.RunRhs owner next k |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs owner
               (R.ConstraintSystem.Side target raw next) k |}
          after).
        {
          unfold Sem.step, after, ready in *. cbn.
          rewrite Hobserve, Hchanged.
          destruct (R.handle_rank target_handle); cbn in Hchild_case |- *;
            try rewrite Hchild_case; reflexivity.
        }
        assert (Hafter : Sem.steps tf (R.initial_config roots) after).
        { eapply Sim.steps_append_one; eauto. }
        eapply Sim.rhs_finishes_one_step; eauto.
        cbn. left. split; reflexivity.
    - set (after :=
        {| R.cfg_state := ready;
           R.cfg_control := R.RunRhs owner next k |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}
        after).
      {
        unfold Sem.step, after, ready in *. cbn.
        now rewrite Hobserve, Hchanged.
      }
      assert (Hafter : Sem.steps tf (R.initial_config roots) after).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.
  Qed.

  Theorem run_rhs_finishes :
    forall support tf roots owner,
      Sim.higher_episodes_complete support tf roots owner ->
      forall st body k,
        Sem.rhs_supported (fun x => List.In x support) body ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs owner body k |} ->
        Sim.rhs_finishes tf owner body k
          {| R.cfg_state := st;
             R.cfg_control := R.RunRhs owner body k |}.
  Proof.
    intros support tf roots owner Hchildren st body k Hbody Hreachable.
    revert st k Hbody Hreachable. pattern body.
    apply (well_founded_induction_type rhs_child_well_founded).
    intros current IH st k Hbody Hreachable.
    destruct current as [direct | target next | target raw next | target next].
    - apply Sim.run_ret_finishes.
    - destruct (rhs_supported_get_inv Hbody) as [Htarget Hnext].
      eapply run_get_finishes; eauto.
      intros value next_state Hafter.
      eapply IH with (y := next value); eauto using RhsGetChild.
    - destruct (rhs_supported_side_inv Hbody) as [Htarget Hnext].
      eapply run_side_finishes; eauto.
      intros next_state Hafter.
      eapply IH with (y := next); eauto using RhsSideChild.
    - destruct (rhs_supported_spawn_inv Hbody) as [Htarget Hnext].
      eapply run_spawn_finishes; eauto.
      intros next_state Hafter.
      eapply IH with (y := next); eauto using RhsSpawnChild.
  Qed.

  End Episodes.
  Module Measure.
  Fixpoint sum_over
    (support : list V.t) (credit : V.t -> nat) : nat :=
    match support with
    | [] => 0
    | x :: rest => credit x + sum_over rest credit
    end.

  Definition ordinary_credit (st : R.state) (owner : V.t) : nat :=
    UL.remaining_changes
      (R.stored_phase st owner) (R.sigma_value st owner).

  Definition side_credit
    (st : R.state) (source target : V.t) : nat :=
    UL.remaining_changes
      (R.stored_side_phase st source target)
      (R.stored_contribution st source target).

  Definition side_credit_sum (support : list V.t) (st : R.state) : nat :=
    sum_over support (fun source =>
      sum_over support (side_credit st source)).

  Definition charged_ordinary_credit
    (st : R.state) (owner : V.t) : nat :=
    if S.mem owner (R.controlled st) then ordinary_credit st owner else 0.

  Definition charged_ordinary_credit_sum
    (support : list V.t) (st : R.state) : nat :=
    sum_over support (charged_ordinary_credit st).

  Definition charged_update_credit
    (support : list V.t) (st : R.state) : nat :=
    charged_ordinary_credit_sum support st + side_credit_sum support st.

  Fixpoint unmaterialized_count
    (support : list V.t) (st : R.state) : nat :=
    match support with
    | [] => 0
    | x :: rest =>
        (if R.is_materialized st x then 0 else 1) +
        unmaterialized_count rest st
    end.

  Fixpoint uncontrolled_count
    (support : list V.t) (st : R.state) : nat :=
    match support with
    | [] => 0
    | x :: rest =>
        (if S.mem x (R.controlled st) then 0 else 1) +
        uncontrolled_count rest st
    end.

  Lemma materialized_step_mono :
    forall tf before after x,
      Sem.step tf before after ->
      R.is_materialized (R.cfg_state before) x = true ->
      R.is_materialized (R.cfg_state after) x = true.
  Proof.
    intros tf before after x Hstep Hmaterialized.
    apply Progress.solved_is_materialized.
    eapply Progress.next_config_solved_preserved; [exact Hstep |].
    now apply Progress.solved_is_materialized.
  Qed.

  Lemma materialized_steps_mono :
    forall tf before after x,
      Sem.steps tf before after ->
      R.is_materialized (R.cfg_state before) x = true ->
      R.is_materialized (R.cfg_state after) x = true.
  Proof.
    intros tf before after x Hsteps Hmaterialized. induction Hsteps; auto.
    apply IHHsteps. eapply materialized_step_mono; eauto.
  Qed.

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
    - rewrite (@materialized_step_mono tf before after x Hstep Hbefore). lia.
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

  Lemma unmaterialized_count_strict :
    forall support tf before after x,
      NoDup support ->
      List.In x support ->
      Sem.steps tf before after ->
      R.is_materialized (R.cfg_state before) x = false ->
      R.is_materialized (R.cfg_state after) x = true ->
      unmaterialized_count support (R.cfg_state after) <
      unmaterialized_count support (R.cfg_state before).
  Proof.
    intros support. induction support as [|head rest IH];
      intros tf before after x Hnodup Hin Hsteps Hbefore Hafter;
      [contradiction |].
    inversion Hnodup as [|? ? Hnotin Hrest]; subst. cbn in Hin |- *.
    destruct Hin as [-> | Hin].
    - rewrite Hbefore, Hafter. cbn.
      pose proof (unmaterialized_count_steps_nonincreasing rest Hsteps). lia.
    - destruct (R.is_materialized (R.cfg_state before) head)
        eqn:Hhead.
      + rewrite (@materialized_steps_mono tf before after head Hsteps Hhead).
        cbn.
        specialize (IH tf before after x Hrest Hin Hsteps Hbefore Hafter).
        lia.
      + destruct (R.is_materialized (R.cfg_state after) head);
          specialize (IH tf before after x Hrest Hin Hsteps Hbefore Hafter);
          lia.
  Qed.

  Lemma controlled_get_ready_mono :
    forall st owner target x,
      S.mem x (R.controlled st) = true ->
      S.mem x (R.controlled (R.get_ready_state st owner target)) = true.
  Proof.
    intros st owner target x Hcontrolled.
    unfold R.get_ready_state, R.materialize, R.add_reader,
      R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target)).
    - destruct (R.is_materialized _ _); exact Hcontrolled.
    - destruct (R.is_materialized _ _); cbn;
        apply SL.add_spec; now right.
  Qed.

  Lemma controlled_side_ready_mono :
    forall st source target raw x,
      S.mem x (R.controlled st) = true ->
      S.mem x (R.controlled (R.side_ready_state st source target raw)) = true.
  Proof.
    intros st source target raw x Hcontrolled.
    unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      cbn; auto.
    apply SL.add_spec. now right.
  Qed.

  Lemma controlled_observe :
    forall st target next entry,
      R.observe st target = (next, entry) ->
      R.controlled next = R.controlled st.
  Proof.
    intros st target next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma controlled_materialize :
    forall st target,
      R.controlled (R.materialize st target) = R.controlled st.
  Proof.
    intros. unfold R.materialize.
    destruct (R.is_materialized st target); reflexivity.
  Qed.

  Lemma controlled_enqueue :
    forall st target,
      R.controlled (R.enqueue st target) = R.controlled st.
  Proof.
    intros st target. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    cbn. now apply controlled_observe in Hobserve.
  Qed.

  Lemma controlled_enqueue_all :
    forall xs st,
      R.controlled (R.enqueue_all st xs) = R.controlled st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH, controlled_enqueue. reflexivity.
  Qed.

  Lemma controlled_write_changed_value :
    forall st owner value,
      R.controlled (R.write_changed_value st owner value) = R.controlled st.
  Proof.
    intros. unfold R.write_changed_value. cbn.
    rewrite controlled_enqueue_all. reflexivity.
  Qed.

  Lemma controlled_set_value :
    forall st owner direct,
      R.controlled (R.set_value st owner direct) = R.controlled st.
  Proof.
    intros. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value].
      cbn. destruct (R.equivalent value (R.sigma_value st owner));
        [reflexivity | rewrite controlled_write_changed_value; reflexivity].
    - rewrite controlled_write_changed_value. reflexivity.
  Qed.

  Theorem controlled_step_mono :
    forall tf before after x,
      Sem.step tf before after ->
      S.mem x (R.controlled (R.cfg_state before)) = true ->
      S.mem x (R.controlled (R.cfg_state after)) = true.
  Proof.
    intros tf [st control] after x Hstep Hcontrolled.
    unfold Sem.step in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in Hcontrolled |- *;
      eauto using controlled_get_ready_mono, controlled_side_ready_mono.
    all: try match goal with
      | Hobs : R.observe ?before ?target = (?next, ?entry) |- _ =>
          assert (Hobserved : S.mem x (R.controlled next) = true)
            by (rewrite (@controlled_observe before target next entry Hobs);
                exact Hcontrolled)
      end.
    all: try (rewrite controlled_materialize; exact Hcontrolled).
    all: try (apply controlled_get_ready_mono; exact Hobserved).
    all: try (apply controlled_side_ready_mono; exact Hobserved).
    all: try (rewrite controlled_materialize; exact Hobserved).
    all: try (rewrite controlled_set_value; exact Hcontrolled).
    all: first [exact Hobserved | exact Hcontrolled].
  Qed.

  Lemma controlled_steps_mono :
    forall tf before after x,
      Sem.steps tf before after ->
      S.mem x (R.controlled (R.cfg_state before)) = true ->
      S.mem x (R.controlled (R.cfg_state after)) = true.
  Proof.
    intros tf before after x Hsteps Hcontrolled. induction Hsteps; auto.
    apply IHHsteps. eapply controlled_step_mono; eauto.
  Qed.

  Lemma uncontrolled_count_step_nonincreasing :
    forall support tf before after,
      Sem.step tf before after ->
      uncontrolled_count support (R.cfg_state after) <=
      uncontrolled_count support (R.cfg_state before).
  Proof.
    intros support. induction support as [|x rest IH];
      intros tf before after Hstep; cbn; [lia |].
    specialize (IH tf before after Hstep).
    destruct (S.mem x (R.controlled (R.cfg_state before))) eqn:Hbefore.
    - rewrite (controlled_step_mono Hstep Hbefore). lia.
    - destruct (S.mem x (R.controlled (R.cfg_state after))); lia.
  Qed.

  Lemma uncontrolled_count_steps_nonincreasing :
    forall support tf before after,
      Sem.steps tf before after ->
      uncontrolled_count support (R.cfg_state after) <=
      uncontrolled_count support (R.cfg_state before).
  Proof.
    intros support tf before after Hsteps. induction Hsteps; [lia |].
    pose proof (uncontrolled_count_step_nonincreasing support H) as Hfirst.
    lia.
  Qed.

  Lemma uncontrolled_count_strict :
    forall support tf before after x,
      NoDup support ->
      List.In x support ->
      Sem.steps tf before after ->
      S.mem x (R.controlled (R.cfg_state before)) = false ->
      S.mem x (R.controlled (R.cfg_state after)) = true ->
      uncontrolled_count support (R.cfg_state after) <
      uncontrolled_count support (R.cfg_state before).
  Proof.
    intros support. induction support as [|head rest IH];
      intros tf before after x Hnodup Hin Hsteps Hbefore Hafter;
      [contradiction |].
    inversion Hnodup as [|? ? Hnotin Hrest]; subst. cbn in Hin |- *.
    destruct Hin as [-> | Hin].
    - rewrite Hbefore, Hafter. cbn.
      pose proof (uncontrolled_count_steps_nonincreasing rest Hsteps). lia.
    - destruct (S.mem head (R.controlled (R.cfg_state before))) eqn:Hhead.
      + rewrite (controlled_steps_mono Hsteps Hhead). cbn.
        specialize (IH tf before after x Hrest Hin Hsteps Hbefore Hafter).
        lia.
      + destruct (S.mem head (R.controlled (R.cfg_state after)));
          specialize (IH tf before after x Hrest Hin Hsteps Hbefore Hafter);
          lia.
  Qed.

  Lemma uncontrolled_count_mono_from_mono :
    forall support before after,
      (forall x,
        S.mem x (R.controlled before) = true ->
        S.mem x (R.controlled after) = true) ->
      uncontrolled_count support after <= uncontrolled_count support before.
  Proof.
    intros support. induction support as [|head rest IH];
      intros before after Hmono; cbn; [lia |].
    pose proof (IH before after Hmono) as Htail.
    destruct (S.mem head (R.controlled before)) eqn:Hbefore.
    - rewrite (Hmono head Hbefore). lia.
    - destruct (S.mem head (R.controlled after)); lia.
  Qed.

  Lemma uncontrolled_count_strict_from_mono :
    forall support before after variable,
      NoDup support ->
      List.In variable support ->
      (forall x,
        S.mem x (R.controlled before) = true ->
        S.mem x (R.controlled after) = true) ->
      S.mem variable (R.controlled before) = false ->
      S.mem variable (R.controlled after) = true ->
      uncontrolled_count support after < uncontrolled_count support before.
  Proof.
    intros support. induction support as [|head rest IH];
      intros before after variable Hnodup Hin Hmono Hbefore Hafter;
      [contradiction |].
    inversion Hnodup as [|? ? Hnotin Hrest]; subst. cbn in Hin |- *.
    destruct Hin as [-> | Hin].
    - rewrite Hbefore, Hafter.
      pose proof (uncontrolled_count_mono_from_mono
        rest before after Hmono). lia.
    - destruct (S.mem head (R.controlled before)) eqn:Hhead.
      + rewrite (Hmono head Hhead).
        specialize (IH before after variable Hrest Hin Hmono
          Hbefore Hafter). lia.
      + destruct (S.mem head (R.controlled after));
          specialize (IH before after variable Hrest Hin Hmono
            Hbefore Hafter); lia.
  Qed.

  Definition round_key (support : list V.t) (c : R.config) :
    nat * (nat * nat) :=
    (unmaterialized_count support (R.cfg_state c),
      (uncontrolled_count support (R.cfg_state c),
       charged_update_credit support (R.cfg_state c))).

  Definition nat_pair_lt : nat * nat -> nat * nat -> Prop :=
    slexprod nat nat lt lt.

  Definition round_key_lt :
    nat * (nat * nat) -> nat * (nat * nat) -> Prop :=
    slexprod nat (nat * nat) lt nat_pair_lt.

  Definition round_measure_lt (support : list V.t) :
    R.config -> R.config -> Prop :=
    fun left right => round_key_lt
      (round_key support left) (round_key support right).

  Lemma nat_pair_lt_well_founded : well_founded nat_pair_lt.
  Proof.
    unfold nat_pair_lt. apply wf_slexprod;
      apply PeanoNat.Nat.lt_wf_0.
  Qed.

  Lemma round_key_lt_well_founded : well_founded round_key_lt.
  Proof.
    unfold round_key_lt. apply wf_slexprod.
    - apply PeanoNat.Nat.lt_wf_0.
    - apply nat_pair_lt_well_founded.
  Qed.

  Theorem round_measure_lt_well_founded :
    forall support, well_founded (round_measure_lt support).
  Proof.
    intros. unfold round_measure_lt. apply wf_inverse_image.
    apply round_key_lt_well_founded.
  Qed.

  Lemma round_measure_materialized :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      Sem.steps tf before after ->
      R.is_materialized (R.cfg_state before) variable = false ->
      R.is_materialized (R.cfg_state after) variable = true ->
      round_measure_lt support after before.
  Proof.
    intros support tf before after variable
      Hnodup Hin Hsteps Hbefore Hafter.
    unfold round_measure_lt, round_key_lt, round_key.
    apply left_slex.
    eapply unmaterialized_count_strict; eauto.
  Qed.

  Lemma round_measure_controlled :
    forall support before after,
      unmaterialized_count support (R.cfg_state after) =
        unmaterialized_count support (R.cfg_state before) ->
      uncontrolled_count support (R.cfg_state after) <
        uncontrolled_count support (R.cfg_state before) ->
      round_measure_lt support after before.
  Proof.
    intros support before after Hmaterialized Hcontrolled.
    unfold round_measure_lt, round_key_lt, round_key.
    rewrite Hmaterialized. apply right_slex.
    unfold nat_pair_lt. now apply left_slex.
  Qed.

  Lemma round_measure_update :
    forall support before after,
      unmaterialized_count support (R.cfg_state after) =
        unmaterialized_count support (R.cfg_state before) ->
      uncontrolled_count support (R.cfg_state after) =
        uncontrolled_count support (R.cfg_state before) ->
      charged_update_credit support (R.cfg_state after) <
        charged_update_credit support (R.cfg_state before) ->
      round_measure_lt support after before.
  Proof.
    intros support before after Hmaterialized Hcontrolled Hupdate.
    unfold round_measure_lt, round_key_lt, round_key.
    rewrite Hmaterialized. apply right_slex.
    unfold nat_pair_lt. rewrite Hcontrolled.
    now apply right_slex.
  Qed.

  End Measure.

  Module Accounting.
  Definition side_grows
    (st : R.state) (source target : R.handle) (raw : D.t) : Prop :=
    D.leq
      (R.aggregate (R.side_ready_state st source target raw)
        (R.handle_variable target))
      (R.aggregate st (R.handle_variable target)) = false.

  Lemma equivalent_refl : forall value, UL.equivalent value value.
  Proof. intros. split; apply DL.leq_refl. Qed.

  Lemma equivalent_sym :
    forall left right, UL.equivalent left right -> UL.equivalent right left.
  Proof. intros left right [Hlr Hrl]. now split. Qed.

  Lemma equivalent_trans :
    forall first second third,
      UL.equivalent first second -> UL.equivalent second third ->
      UL.equivalent first third.
  Proof.
    intros first second third [H12 H21] [H23 H32]. split;
      eapply DL.leq_trans; eauto.
  Qed.

  Lemma join_congruent :
    forall left left' right right',
      UL.equivalent left left' -> UL.equivalent right right' ->
      UL.equivalent (D.join left right) (D.join left' right').
  Proof.
    intros left left' right right' [Hleft Hleft'] [Hright Hright'].
    split; apply DL.join_least.
    - eapply DL.leq_trans; [exact Hleft | apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hright | apply DL.join_upper_right].
    - eapply DL.leq_trans; [exact Hleft' | apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hright' | apply DL.join_upper_right].
  Qed.

  Lemma join_bottom_left :
    forall value, UL.equivalent (D.join D.bottom value) value.
  Proof.
    intros. split; [apply DL.join_least | apply DL.join_upper_right];
      auto using DL.bottom_least, DL.leq_refl.
  Qed.

  Lemma join_swap :
    forall left right rest,
      UL.equivalent (D.join left (D.join right rest))
        (D.join right (D.join left rest)).
  Proof.
    intros. split; apply DL.join_least.
    - eapply DL.leq_trans; [apply DL.join_upper_left |
        apply DL.join_upper_right].
    - apply DL.join_least; [apply DL.join_upper_left |].
      eapply DL.leq_trans; [apply DL.join_upper_right |
        apply DL.join_upper_right].
    - eapply DL.leq_trans; [apply DL.join_upper_left |
        apply DL.join_upper_right].
    - apply DL.join_least; [apply DL.join_upper_left |].
      eapply DL.leq_trans; [apply DL.join_upper_right |
        apply DL.join_upper_right].
  Qed.

  Lemma join_values_permutation :
    forall values values',
      Permutation values values' ->
      UL.equivalent (R.join_values values) (R.join_values values').
  Proof.
    intros values values' Hperm. induction Hperm; cbn.
    - apply equivalent_refl.
    - apply join_congruent; auto using equivalent_refl.
    - apply join_swap.
    - eapply equivalent_trans; eauto.
  Qed.

  Lemma lookup_map_update_same_row :
    forall A (table : M.t (M.t A)) outer inner value,
      R.lookup_map (R.update_map table outer inner value) outer =
      M.update (R.lookup_map table outer) inner value.
  Proof.
    intros. unfold R.update_map, R.lookup_map.
    now rewrite ML.lookup_update_same.
  Qed.

  Lemma lookup_update_map_other_outer :
    forall A (table : M.t (M.t A)) outer inner value observed,
      observed <> outer ->
      R.lookup_map (R.update_map table outer inner value) observed =
      R.lookup_map table observed.
  Proof.
    intros. unfold R.update_map, R.lookup_map.
    now rewrite ML.lookup_update_other by assumption.
  Qed.

  Lemma lookup_update_map_other_inner :
    forall A (table : M.t (M.t A)) outer inner value observed,
      observed <> inner ->
      M.lookup (R.lookup_map
        (R.update_map table outer inner value) outer) observed =
      M.lookup (R.lookup_map table outer) observed.
  Proof.
    intros. unfold R.update_map, R.lookup_map.
    rewrite ML.lookup_update_same.
    now rewrite ML.lookup_update_other by assumption.
  Qed.

  Lemma aggregate_row_update_equivalent :
    forall st source target value,
      UL.equivalent value (R.stored_contribution st source target) ->
      UL.equivalent
        (R.aggregate (R.with_contributions st
          (R.update_map (R.contributions st) target source value)) target)
        (R.aggregate st target).
  Proof.
    intros st source target value Hequivalent.
    unfold R.aggregate. cbn. rewrite lookup_map_update_same_row.
    set (row := R.lookup_map (R.contributions st) target) in *.
    destruct (ML.values_update row source value)
      as [rest [Hupdated Hprevious]].
    pose proof (join_values_permutation Hupdated) as Hnew.
    destruct (M.lookup row source) as [previous |] eqn:Hlookup.
    - pose proof (join_values_permutation Hprevious) as Hold.
      unfold R.stored_contribution in Hequivalent.
      fold row in Hequivalent. rewrite Hlookup in Hequivalent.
      eapply equivalent_trans; [exact Hnew |].
      eapply equivalent_trans; [|apply equivalent_sym; exact Hold].
      cbn. apply join_congruent; auto using equivalent_refl.
    - pose proof (join_values_permutation Hprevious) as Hold.
      unfold R.stored_contribution in Hequivalent.
      fold row in Hequivalent. rewrite Hlookup in Hequivalent.
      eapply equivalent_trans; [exact Hnew |].
      eapply equivalent_trans with
        (second := D.join D.bottom (R.join_values rest)).
      + cbn. apply join_congruent;
          [exact Hequivalent | apply equivalent_refl].
      + eapply equivalent_trans; [apply join_bottom_left |].
        apply equivalent_sym. exact Hold.
  Qed.

  Lemma aggregate_record_side_equivalent :
    forall st source target raw,
      UL.equivalent
        (snd (U.update true target
          (R.stored_side_phase st source target)
          (R.stored_contribution st source target)
          (R.accumulated_side_input st source target raw)))
        (R.stored_contribution st source target) ->
      UL.equivalent
        (R.aggregate (R.record_side_payload st source target raw) target)
        (R.aggregate st target).
  Proof.
    intros st source target raw Hequivalent.
    unfold R.record_side_payload. cbn.
    eapply aggregate_row_update_equivalent with
      (st := R.with_local_sides st
        (R.update_map (R.local_sides st) source target
          (R.accumulated_side_input st source target raw))).
    exact Hequivalent.
  Qed.

  Lemma side_grows_update_changes :
    forall st source target raw,
      side_grows st source target raw ->
      ~ UL.equivalent
          (snd (U.update true (R.handle_variable target)
            (R.stored_side_phase st (R.handle_variable source)
              (R.handle_variable target))
            (R.stored_contribution st (R.handle_variable source)
              (R.handle_variable target))
            (R.accumulated_side_input st (R.handle_variable source)
              (R.handle_variable target) raw)))
          (R.stored_contribution st (R.handle_variable source)
            (R.handle_variable target)).
  Proof.
    intros st source target raw Hgrows Hequivalent.
    pose proof
      (@aggregate_record_side_equivalent
        st (R.handle_variable source) (R.handle_variable target)
        raw Hequivalent) as [Hcovered _].
    unfold side_grows in Hgrows.
    assert (Haggregate :
      R.aggregate (R.side_ready_state st source target raw)
        (R.handle_variable target) =
      R.aggregate (R.record_side_payload st
        (R.handle_variable source) (R.handle_variable target) raw)
        (R.handle_variable target)).
    {
      unfold R.side_ready_state, R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
        reflexivity.
    }
    rewrite Haggregate, Hcovered in Hgrows. discriminate.
  Qed.

  Lemma sum_over_pointwise_le :
    forall support left right,
      (forall x, List.In x support -> left x <= right x) ->
      Measure.sum_over support left <= Measure.sum_over support right.
  Proof.
    intros support. induction support as [|x rest IH];
      intros left right Hle; cbn; [lia |].
    pose proof (Hle x (or_introl eq_refl)).
    pose proof (IH left right (fun y Hy => Hle y (or_intror Hy))). lia.
  Qed.

  Lemma sum_over_one_strict :
    forall support left right chosen,
      List.In chosen support ->
      (forall x, List.In x support -> left x <= right x) ->
      left chosen < right chosen ->
      Measure.sum_over support left < Measure.sum_over support right.
  Proof.
    intros support. induction support as [|x rest IH];
      intros left right chosen Hin Hle Hstrict; [contradiction |].
    cbn in Hin |- *. destruct Hin as [-> | Hin].
    - pose proof (sum_over_pointwise_le rest left right
        (fun y Hy => Hle y (or_intror Hy))). lia.
    - pose proof (Hle x (or_introl eq_refl)).
      pose proof (IH left right chosen Hin
        (fun y Hy => Hle y (or_intror Hy)) Hstrict). lia.
  Qed.

  Lemma sum_over_pointwise_eq :
    forall support left right,
      (forall x, List.In x support -> left x = right x) ->
      Measure.sum_over support left = Measure.sum_over support right.
  Proof.
    intros support. induction support as [|x rest IH];
      intros left right Heq; cbn; [reflexivity |].
    rewrite (Heq x (or_introl eq_refl)). f_equal.
    apply IH. intros. apply Heq. now right.
  Qed.

  Lemma sigma_enqueue_all :
    forall xs st, R.sigma (R.enqueue_all st xs) = R.sigma st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma phases_enqueue_all :
    forall xs st, R.phases (R.enqueue_all st xs) = R.phases st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma side_phases_enqueue_all :
    forall xs st,
      R.side_phases (R.enqueue_all st xs) = R.side_phases st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma contributions_enqueue_all :
    forall xs st,
      R.contributions (R.enqueue_all st xs) = R.contributions st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH. unfold R.enqueue, R.observe.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma stored_phase_write_changed :
    forall st owner value observed,
      R.stored_phase (R.write_changed_value st owner value) observed =
      R.stored_phase st observed.
  Proof.
    intros. unfold R.write_changed_value, R.stored_phase. cbn.
    now rewrite phases_enqueue_all.
  Qed.

  Lemma sigma_value_write_changed_same :
    forall st owner value,
      R.sigma_value (R.write_changed_value st owner value) owner = value.
  Proof.
    intros. unfold R.write_changed_value, R.sigma_value. cbn.
    rewrite sigma_enqueue_all. cbn. now rewrite ML.lookup_update_same.
  Qed.

  Lemma sigma_value_write_changed_other :
    forall st owner value observed,
      observed <> owner ->
      R.sigma_value (R.write_changed_value st owner value) observed =
      R.sigma_value st observed.
  Proof.
    intros. unfold R.write_changed_value, R.sigma_value. cbn.
    rewrite sigma_enqueue_all. cbn.
    now rewrite ML.lookup_update_other by assumption.
  Qed.

  Lemma side_credit_write_changed :
    forall st owner value source target,
      Measure.side_credit (R.write_changed_value st owner value)
        source target = Measure.side_credit st source target.
  Proof.
    intros. unfold Measure.side_credit, R.write_changed_value,
      R.stored_side_phase, R.stored_contribution. cbn.
    rewrite side_phases_enqueue_all, contributions_enqueue_all.
    reflexivity.
  Qed.

  Lemma stored_side_phase_record_same :
    forall st source target raw,
      R.stored_side_phase (R.record_side_payload st source target raw)
        source target =
      fst (U.update true target
        (R.stored_side_phase st source target)
        (R.stored_contribution st source target)
        (R.accumulated_side_input st source target raw)).
  Proof.
    intros. unfold R.record_side_payload, R.stored_side_phase. cbn.
    rewrite lookup_map_update_same_row, ML.lookup_update_same. reflexivity.
  Qed.

  Lemma stored_contribution_record_same :
    forall st source target raw,
      R.stored_contribution (R.record_side_payload st source target raw)
        source target =
      snd (U.update true target
        (R.stored_side_phase st source target)
        (R.stored_contribution st source target)
        (R.accumulated_side_input st source target raw)).
  Proof.
    intros. unfold R.record_side_payload, R.stored_contribution. cbn.
    rewrite lookup_map_update_same_row, ML.lookup_update_same. reflexivity.
  Qed.

  Lemma side_credit_record_same_nonincreasing :
    forall st source target raw,
      Measure.side_credit (R.record_side_payload st source target raw)
        source target <= Measure.side_credit st source target.
  Proof.
    intros. unfold Measure.side_credit.
    rewrite stored_side_phase_record_same,
      stored_contribution_record_same.
    apply UL.remaining_changes_nonincreasing.
  Qed.

  Lemma side_credit_record_same_decreases :
    forall st source target raw,
      ~ UL.equivalent
          (snd (U.update true target
            (R.stored_side_phase st source target)
            (R.stored_contribution st source target)
            (R.accumulated_side_input st source target raw)))
          (R.stored_contribution st source target) ->
      Measure.side_credit (R.record_side_payload st source target raw)
        source target < Measure.side_credit st source target.
  Proof.
    intros. unfold Measure.side_credit.
    rewrite stored_side_phase_record_same,
      stored_contribution_record_same.
    now apply UL.update_change_consumes.
  Qed.

  Lemma side_credit_record_other_target :
    forall st source target raw observed_source observed_target,
      observed_target <> target ->
      Measure.side_credit (R.record_side_payload st source target raw)
        observed_source observed_target =
      Measure.side_credit st observed_source observed_target.
  Proof.
    intros st source target raw observed_source observed_target Hneq.
    unfold Measure.side_credit, R.stored_side_phase,
      R.stored_contribution, R.record_side_payload. cbn.
    rewrite (@lookup_update_map_other_outer U.phase
      (R.side_phases st) target source _ observed_target Hneq).
    rewrite (@lookup_update_map_other_outer D.t
      (R.contributions st) target source _ observed_target Hneq).
    reflexivity.
  Qed.

  Lemma side_credit_record_other_source :
    forall st source target raw observed_source,
      observed_source <> source ->
      Measure.side_credit (R.record_side_payload st source target raw)
        observed_source target =
      Measure.side_credit st observed_source target.
  Proof.
    intros st source target raw observed_source Hneq.
    unfold Measure.side_credit, R.stored_side_phase,
      R.stored_contribution, R.record_side_payload. cbn.
    rewrite (@lookup_update_map_other_inner U.phase
      (R.side_phases st) target source _ observed_source Hneq).
    rewrite (@lookup_update_map_other_inner D.t
      (R.contributions st) target source _ observed_source Hneq).
    reflexivity.
  Qed.

  Lemma side_credit_record_nonincreasing :
    forall st source target raw observed_source observed_target,
      Measure.side_credit (R.record_side_payload st source target raw)
        observed_source observed_target <=
      Measure.side_credit st observed_source observed_target.
  Proof.
    intros. destruct (V.eq_dec observed_target target) as [-> | Htarget].
    - destruct (V.eq_dec observed_source source) as [-> | Hsource].
      + apply side_credit_record_same_nonincreasing.
      + rewrite side_credit_record_other_source by exact Hsource. lia.
    - rewrite side_credit_record_other_target by exact Htarget. lia.
  Qed.

  Lemma side_credit_side_ready_nonincreasing :
    forall st source target raw observed_source observed_target,
      Measure.side_credit (R.side_ready_state st source target raw)
        observed_source observed_target <=
      Measure.side_credit st observed_source observed_target.
  Proof.
    intros. unfold R.side_ready_state, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      apply side_credit_record_nonincreasing.
  Qed.

  Lemma side_credit_side_ready_same_decreases :
    forall st source target raw,
      side_grows st source target raw ->
      Measure.side_credit (R.side_ready_state st source target raw)
        (R.handle_variable source) (R.handle_variable target) <
      Measure.side_credit st
        (R.handle_variable source) (R.handle_variable target).
  Proof.
    intros st source target raw Hgrows.
    pose proof (side_grows_update_changes Hgrows) as Hchanges.
    unfold R.side_ready_state, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      now apply side_credit_record_same_decreases.
  Qed.

  Lemma side_credit_sum_side_ready_nonincreasing :
    forall support st source target raw,
      Measure.side_credit_sum support
        (R.side_ready_state st source target raw) <=
      Measure.side_credit_sum support st.
  Proof.
    intros. unfold Measure.side_credit_sum.
    apply sum_over_pointwise_le. intros observed_source Hsource.
    apply sum_over_pointwise_le. intros observed_target Htarget.
    apply side_credit_side_ready_nonincreasing.
  Qed.

  Lemma side_credit_sum_side_ready_decreases :
    forall support st source target raw,
      List.In (R.handle_variable source) support ->
      List.In (R.handle_variable target) support ->
      side_grows st source target raw ->
      Measure.side_credit_sum support
        (R.side_ready_state st source target raw) <
      Measure.side_credit_sum support st.
  Proof.
    intros support st source target raw Hsource Htarget Hgrows.
    unfold Measure.side_credit_sum.
    apply sum_over_one_strict with
      (chosen := R.handle_variable source); [exact Hsource | |].
    - intros. apply sum_over_pointwise_le. intros.
      apply side_credit_side_ready_nonincreasing.
    - apply sum_over_one_strict with
        (chosen := R.handle_variable target); [exact Htarget | |].
      + intros. apply side_credit_side_ready_nonincreasing.
      + now apply side_credit_side_ready_same_decreases.
  Qed.

  Lemma equivalent_true :
    forall left right,
      R.equivalent left right = true -> UL.equivalent left right.
  Proof.
    intros left right Hequivalent. unfold R.equivalent in Hequivalent.
    now apply Bool.andb_true_iff.
  Qed.

  Lemma equivalent_false :
    forall left right,
      R.equivalent left right = false -> ~ UL.equivalent left right.
  Proof.
    intros left right Hfalse [Hleft Hright].
    unfold R.equivalent in Hfalse.
    rewrite Hleft, Hright in Hfalse. discriminate.
  Qed.

  Lemma ordinary_credit_set_value_controlled_nonincreasing :
    forall st owner direct,
      S.mem owner (R.controlled st) = true ->
      Measure.ordinary_credit (R.set_value st owner direct) owner <=
      Measure.ordinary_credit st owner.
  Proof.
    intros st owner direct Hcontrolled. unfold R.set_value.
    set (candidate := D.join direct (R.aggregate st owner)).
    set (old := R.sigma_value st owner).
    destruct (R.equivalent candidate old) eqn:Hcandidate; [lia |].
    rewrite Hcontrolled.
    destruct (U.update false owner (R.stored_phase st owner) old candidate)
      as [phase value] eqn:Hupdate. cbn.
    destruct (R.equivalent value old) eqn:Hstutter.
    - unfold Measure.ordinary_credit, R.stored_phase. cbn.
      rewrite ML.lookup_update_same.
      pose proof (UL.remaining_changes_nonincreasing false owner
        (R.stored_phase st owner) old candidate) as Hle.
      rewrite Hupdate in Hle. cbn in Hle.
      pose proof (@UL.remaining_changes_extensional phase value old
        (@equivalent_true value old Hstutter)) as Heq.
      change (UL.remaining_changes phase old <=
        UL.remaining_changes (R.stored_phase st owner) old).
      lia.
    - unfold Measure.ordinary_credit.
      rewrite stored_phase_write_changed,
        sigma_value_write_changed_same.
      unfold R.stored_phase. cbn. rewrite ML.lookup_update_same.
      pose proof (UL.remaining_changes_nonincreasing false owner
        (R.stored_phase st owner) old candidate) as Hle.
      rewrite Hupdate in Hle. cbn in Hle. exact Hle.
  Qed.

  Lemma ordinary_credit_set_value_other :
    forall st owner direct observed,
      observed <> owner ->
      Measure.ordinary_credit (R.set_value st owner direct) observed =
      Measure.ordinary_credit st observed.
  Proof.
    intros st owner direct observed Hneq. unfold R.set_value.
    set (candidate := D.join direct (R.aggregate st owner)).
    set (old := R.sigma_value st owner).
    destruct (R.equivalent candidate old); [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner) old candidate)
        as [phase value]. cbn.
      destruct (R.equivalent value old).
      + unfold Measure.ordinary_credit, R.stored_phase. cbn.
        now rewrite ML.lookup_update_other by exact Hneq.
      + unfold Measure.ordinary_credit.
        rewrite stored_phase_write_changed,
          sigma_value_write_changed_other by exact Hneq.
        unfold R.stored_phase. cbn.
        now rewrite ML.lookup_update_other by exact Hneq.
    - unfold Measure.ordinary_credit.
      rewrite stored_phase_write_changed,
        sigma_value_write_changed_other by exact Hneq.
      reflexivity.
  Qed.

  Lemma ordinary_credit_set_value_controlled_decreases :
    forall st owner direct,
      S.mem owner (R.controlled st) = true ->
      ~ UL.equivalent
          (R.sigma_value (R.set_value st owner direct) owner)
          (R.sigma_value st owner) ->
      Measure.ordinary_credit (R.set_value st owner direct) owner <
      Measure.ordinary_credit st owner.
  Proof.
    intros st owner direct Hcontrolled Hchanges.
    unfold R.set_value in Hchanges |- *.
    set (candidate := D.join direct (R.aggregate st owner)) in *.
    set (old := R.sigma_value st owner) in *.
    destruct (R.equivalent candidate old) eqn:Hcandidate.
    - exfalso. apply Hchanges. apply equivalent_refl.
    - rewrite Hcontrolled in Hchanges |- *.
      destruct (U.update false owner (R.stored_phase st owner) old candidate)
        as [phase value] eqn:Hupdate. cbn in *.
      destruct (R.equivalent value old) eqn:Hstutter.
      + exfalso. apply Hchanges. apply equivalent_refl.
      + unfold Measure.ordinary_credit.
        rewrite stored_phase_write_changed,
          sigma_value_write_changed_same.
        unfold R.stored_phase. cbn. rewrite ML.lookup_update_same.
        assert (Hupdate_changes :
          ~ UL.equivalent
            (snd (U.update false owner (R.stored_phase st owner)
              old candidate)) old).
        { rewrite Hupdate. cbn. now apply equivalent_false. }
        pose proof (@UL.update_change_consumes false owner
          (R.stored_phase st owner) old candidate Hupdate_changes)
          as Hdecrease.
        rewrite Hupdate in Hdecrease. cbn in Hdecrease. exact Hdecrease.
  Qed.

  Lemma side_credit_set_value :
    forall st owner direct source target,
      Measure.side_credit (R.set_value st owner direct) source target =
      Measure.side_credit st source target.
  Proof.
    intros. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner));
        [reflexivity | rewrite side_credit_write_changed; reflexivity].
    - apply side_credit_write_changed.
  Qed.

  Lemma side_credit_sum_set_value :
    forall support st owner direct,
      Measure.side_credit_sum support (R.set_value st owner direct) =
      Measure.side_credit_sum support st.
  Proof.
    intros. unfold Measure.side_credit_sum.
    apply sum_over_pointwise_eq. intros source Hsource.
    apply sum_over_pointwise_eq. intros target Htarget.
    apply side_credit_set_value.
  Qed.

  Lemma charged_ordinary_credit_set_value_controlled_nonincreasing :
    forall st owner direct observed,
      S.mem owner (R.controlled st) = true ->
      Measure.charged_ordinary_credit (R.set_value st owner direct) observed <=
      Measure.charged_ordinary_credit st observed.
  Proof.
    intros st owner direct observed Hcontrolled.
    unfold Measure.charged_ordinary_credit.
    rewrite Measure.controlled_set_value.
    destruct (S.mem observed (R.controlled st)) eqn:Hobserved; [|lia].
    destruct (V.eq_dec observed owner) as [-> | Hneq].
    - now apply ordinary_credit_set_value_controlled_nonincreasing.
    - rewrite ordinary_credit_set_value_other by exact Hneq. lia.
  Qed.

  Lemma charged_update_credit_set_value_controlled_nonincreasing :
    forall support st owner direct,
      S.mem owner (R.controlled st) = true ->
      Measure.charged_update_credit support (R.set_value st owner direct) <=
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner direct Hcontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum.
    rewrite side_credit_sum_set_value.
    pose proof (sum_over_pointwise_le support
      (Measure.charged_ordinary_credit (R.set_value st owner direct))
      (Measure.charged_ordinary_credit st)
      (fun observed _ =>
        @charged_ordinary_credit_set_value_controlled_nonincreasing
          st owner direct observed Hcontrolled)). lia.
  Qed.

  Lemma charged_update_credit_set_value_controlled_decreases :
    forall support st owner direct,
      List.In owner support ->
      S.mem owner (R.controlled st) = true ->
      ~ UL.equivalent
          (R.sigma_value (R.set_value st owner direct) owner)
          (R.sigma_value st owner) ->
      Measure.charged_update_credit support (R.set_value st owner direct) <
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner direct Howner Hcontrolled Hchanges.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum.
    rewrite side_credit_sum_set_value.
    assert (Hstrict :
      Measure.sum_over support
        (Measure.charged_ordinary_credit (R.set_value st owner direct)) <
      Measure.sum_over support (Measure.charged_ordinary_credit st)).
    {
      apply sum_over_one_strict with (chosen := owner); [exact Howner | |].
      - intros. now apply
          charged_ordinary_credit_set_value_controlled_nonincreasing.
      - unfold Measure.charged_ordinary_credit.
        rewrite Measure.controlled_set_value, Hcontrolled.
        now apply ordinary_credit_set_value_controlled_decreases.
    }
    lia.
  Qed.

  Lemma charged_ordinary_credit_set_value_uncontrolled :
    forall st owner direct observed,
      S.mem owner (R.controlled st) = false ->
      Measure.charged_ordinary_credit (R.set_value st owner direct) observed =
      Measure.charged_ordinary_credit st observed.
  Proof.
    intros st owner direct observed Huncontrolled.
    unfold Measure.charged_ordinary_credit.
    rewrite Measure.controlled_set_value.
    destruct (V.eq_dec observed owner) as [-> | Hneq].
    - now rewrite Huncontrolled.
    - destruct (S.mem observed (R.controlled st));
        [rewrite ordinary_credit_set_value_other by exact Hneq |];
        reflexivity.
  Qed.

  Lemma charged_update_credit_set_value_uncontrolled :
    forall support st owner direct,
      S.mem owner (R.controlled st) = false ->
      Measure.charged_update_credit support (R.set_value st owner direct) =
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner direct Huncontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum.
    rewrite side_credit_sum_set_value. f_equal.
    apply sum_over_pointwise_eq. intros.
    now apply charged_ordinary_credit_set_value_uncontrolled.
  Qed.

  Lemma mem_add_existing :
    forall values inserted observed,
      S.mem inserted values = true ->
      S.mem observed (S.add inserted values) = S.mem observed values.
  Proof.
    intros values inserted observed Hinserted.
    destruct (S.mem observed (S.add inserted values)) eqn:Hafter;
      destruct (S.mem observed values) eqn:Hbefore; try reflexivity.
    - apply SL.add_spec in Hafter. destruct Hafter as [-> | Hafter].
      + rewrite Hinserted in Hbefore. discriminate.
      + rewrite Hafter in Hbefore. discriminate.
    - exfalso. pose proof (proj2 (SL.add_spec observed inserted values)
        (or_intror Hbefore)) as Htrue.
      rewrite Hafter in Htrue. discriminate.
  Qed.

  Lemma ordinary_credit_side_ready :
    forall st source target raw observed,
      Measure.ordinary_credit (R.side_ready_state st source target raw)
        observed = Measure.ordinary_credit st observed.
  Proof.
    intros. unfold Measure.ordinary_credit, R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      unfold R.record_side_payload, R.promote_controlled,
        R.stored_phase, R.sigma_value;
      destruct (U.update true (R.handle_variable target)
        (R.stored_side_phase st (R.handle_variable source)
          (R.handle_variable target))
        (R.stored_contribution st (R.handle_variable source)
          (R.handle_variable target))
        (R.accumulated_side_input st (R.handle_variable source)
          (R.handle_variable target) raw));
      reflexivity.
  Qed.

  Lemma charged_ordinary_credit_side_ready_stable_control :
    forall st source target raw observed,
      (Nat.ltb (R.handle_rank target) (R.handle_rank source) = true \/
       S.mem (R.handle_variable source) (R.controlled st) = true) ->
      Measure.charged_ordinary_credit
        (R.side_ready_state st source target raw) observed =
      Measure.charged_ordinary_credit st observed.
  Proof.
    intros st source target raw observed Hstable.
    unfold Measure.charged_ordinary_credit.
    rewrite ordinary_credit_side_ready.
    unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source))
      eqn:Horder; [reflexivity |].
    destruct Hstable as [Hcontra | Hcontrolled]; [congruence |].
    unfold R.promote_controlled. cbn. now rewrite mem_add_existing.
  Qed.

  Lemma charged_update_credit_side_ready_nonincreasing :
    forall support st source target raw,
      (Nat.ltb (R.handle_rank target) (R.handle_rank source) = true \/
       S.mem (R.handle_variable source) (R.controlled st) = true) ->
      Measure.charged_update_credit support
        (R.side_ready_state st source target raw) <=
      Measure.charged_update_credit support st.
  Proof.
    intros support st source target raw Hstable.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum.
    assert (Hordinary :
      Measure.sum_over support
        (Measure.charged_ordinary_credit
          (R.side_ready_state st source target raw)) =
      Measure.sum_over support (Measure.charged_ordinary_credit st)).
    {
      apply sum_over_pointwise_eq. intros.
      now apply charged_ordinary_credit_side_ready_stable_control.
    }
    rewrite Hordinary.
    pose proof (side_credit_sum_side_ready_nonincreasing
      support st source target raw). lia.
  Qed.

  Lemma charged_update_credit_side_ready_decreases :
    forall support st source target raw,
      List.In (R.handle_variable source) support ->
      List.In (R.handle_variable target) support ->
      (Nat.ltb (R.handle_rank target) (R.handle_rank source) = true \/
       S.mem (R.handle_variable source) (R.controlled st) = true) ->
      side_grows st source target raw ->
      Measure.charged_update_credit support
        (R.side_ready_state st source target raw) <
      Measure.charged_update_credit support st.
  Proof.
    intros support st source target raw Hsource Htarget Hstable Hgrows.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum.
    assert (Hordinary :
      Measure.sum_over support
        (Measure.charged_ordinary_credit
          (R.side_ready_state st source target raw)) =
      Measure.sum_over support (Measure.charged_ordinary_credit st)).
    {
      apply sum_over_pointwise_eq. intros.
      now apply charged_ordinary_credit_side_ready_stable_control.
    }
    rewrite Hordinary.
    pose proof (@side_credit_sum_side_ready_decreases
      support st source target raw Hsource Htarget Hgrows). lia.
  Qed.

  End Accounting.

  Module Payment.
  Lemma rhs_supported_get_inv :
    forall support target next,
      Sem.rhs_supported support (R.ConstraintSystem.Get target next) ->
      support target /\ forall value, Sem.rhs_supported support (next value).
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma rhs_supported_side_inv :
    forall support target value next,
      Sem.rhs_supported support (R.ConstraintSystem.Side target value next) ->
      support target /\ Sem.rhs_supported support next.
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma rhs_supported_spawn_inv :
    forall support target next,
      Sem.rhs_supported support (R.ConstraintSystem.Spawn target next) ->
      support target /\ Sem.rhs_supported support next.
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma charged_update_credit_with_queue :
    forall support st queue,
      Measure.charged_update_credit support (R.with_queue st queue) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

  Lemma charged_update_credit_with_started :
    forall support st started,
      Measure.charged_update_credit support (R.with_started st started) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

  Lemma unmaterialized_count_with_ranking :
    forall support st ranking,
      Measure.unmaterialized_count support (R.with_ranking st ranking) =
      Measure.unmaterialized_count support st.
  Proof.
    induction support as [|x rest IH]; intros; cbn; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma uncontrolled_count_with_ranking :
    forall support st ranking,
      Measure.uncontrolled_count support (R.with_ranking st ranking) =
      Measure.uncontrolled_count support st.
  Proof.
    induction support as [|x rest IH]; intros; cbn; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma uncontrolled_count_with_queue :
    forall support st queue,
      Measure.uncontrolled_count support (R.with_queue st queue) =
      Measure.uncontrolled_count support st.
  Proof.
    induction support as [|x rest IH]; intros; cbn; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma unmaterialized_count_observe :
    forall support st target next entry,
      R.observe st target = (next, entry) ->
      Measure.unmaterialized_count support next =
      Measure.unmaterialized_count support st.
  Proof.
    intros support st target next entry Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; subst. apply unmaterialized_count_with_ranking.
  Qed.

  Lemma uncontrolled_count_observe :
    forall support st target next entry,
      R.observe st target = (next, entry) ->
      Measure.uncontrolled_count support next =
      Measure.uncontrolled_count support st.
  Proof.
    intros support st target next entry Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; subst. apply uncontrolled_count_with_ranking.
  Qed.

  Lemma uncontrolled_count_enqueue_handle :
    forall support st entry,
      Measure.uncontrolled_count support (R.enqueue_handle st entry) =
      Measure.uncontrolled_count support st.
  Proof.
    intros. unfold R.enqueue_handle.
    apply uncontrolled_count_with_queue.
  Qed.

  Lemma observed_handle_variable :
    forall st target next entry,
      R.observe st target = (next, entry) ->
      R.handle_variable entry = target.
  Proof.
    intros st target next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma charged_update_credit_observe :
    forall support st target next entry,
      R.observe st target = (next, entry) ->
      Measure.charged_update_credit support next =
      Measure.charged_update_credit support st.
  Proof.
    intros support st target next entry Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma charged_update_credit_enqueue_handle :
    forall support st entry,
      Measure.charged_update_credit support (R.enqueue_handle st entry) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

  Lemma charged_update_credit_enqueue :
    forall support st target,
      Measure.charged_update_credit support (R.enqueue st target) =
      Measure.charged_update_credit support st.
  Proof.
    intros. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    rewrite charged_update_credit_enqueue_handle.
    exact (@charged_update_credit_observe
      support st target next entry Hobserve).
  Qed.

  Lemma sigma_value_materialize :
    forall st target observed,
      R.sigma_value (R.materialize st target) observed =
      R.sigma_value st observed.
  Proof.
    intros. unfold R.materialize, R.is_materialized, R.sigma_value.
    destruct (M.lookup (R.sigma st) target) eqn:Htarget; [reflexivity |].
    destruct (V.eq_dec observed target) as [-> | Hneq].
    - cbn. rewrite ML.lookup_update_same, Htarget. reflexivity.
    - cbn. now rewrite ML.lookup_update_other by exact Hneq.
  Qed.

  Lemma charged_ordinary_credit_materialize :
    forall st target observed,
      Measure.charged_ordinary_credit (R.materialize st target) observed =
      Measure.charged_ordinary_credit st observed.
  Proof.
    intros. unfold Measure.charged_ordinary_credit,
      Measure.ordinary_credit.
    rewrite sigma_value_materialize.
    unfold R.materialize.
    destruct (R.is_materialized st target); reflexivity.
  Qed.

  Lemma side_credit_materialize :
    forall st target source observed,
      Measure.side_credit (R.materialize st target) source observed =
      Measure.side_credit st source observed.
  Proof.
    intros. unfold R.materialize.
    destruct (R.is_materialized st target); reflexivity.
  Qed.

  Lemma charged_update_credit_materialize :
    forall support st target,
      Measure.charged_update_credit support (R.materialize st target) =
      Measure.charged_update_credit support st.
  Proof.
    intros. unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    - apply Accounting.sum_over_pointwise_eq. intros.
      apply charged_ordinary_credit_materialize.
    - apply Accounting.sum_over_pointwise_eq. intros source Hsource.
      apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      apply side_credit_materialize.
  Qed.

  Lemma charged_update_credit_start_evaluation :
    forall support st owner,
      Measure.charged_update_credit support (R.start_evaluation st owner) =
      Measure.charged_update_credit support st.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides.
    change (Measure.charged_update_credit support
      (R.materialize st owner) = Measure.charged_update_credit support st).
    apply charged_update_credit_materialize.
  Qed.

  Lemma controlled_get_ready_stable :
    forall st owner target,
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true \/
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      forall observed,
        S.mem observed (R.controlled (R.get_ready_state st owner target)) =
        S.mem observed (R.controlled st).
  Proof.
    intros st owner target Hstable observed.
    unfold R.get_ready_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target))
      eqn:Hhigher.
    - unfold R.materialize, R.add_reader.
      destruct (R.is_materialized _ _); reflexivity.
    - destruct Hstable as [Hcontra | Hcontrolled]; [congruence |].
      unfold R.promote_controlled, R.materialize, R.add_reader.
      destruct (R.is_materialized _ _); cbn;
        now rewrite Accounting.mem_add_existing.
  Qed.

  Lemma sigma_value_get_ready :
    forall st owner target observed,
      R.sigma_value (R.get_ready_state st owner target) observed =
      R.sigma_value st observed.
  Proof.
    intros. unfold R.get_ready_state, R.add_reader, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      rewrite sigma_value_materialize; reflexivity.
  Qed.

  Lemma stored_phase_get_ready :
    forall st owner target observed,
      R.stored_phase (R.get_ready_state st owner target) observed =
      R.stored_phase st observed.
  Proof.
    intros. unfold R.get_ready_state, R.add_reader, R.promote_controlled,
      R.materialize, R.stored_phase.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      destruct (R.is_materialized _ _); reflexivity.
  Qed.

  Lemma charged_ordinary_credit_get_ready_stable :
    forall st owner target,
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true \/
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      forall observed,
        Measure.charged_ordinary_credit
          (R.get_ready_state st owner target) observed =
        Measure.charged_ordinary_credit st observed.
  Proof.
    intros st owner target Hstable observed.
    unfold Measure.charged_ordinary_credit, Measure.ordinary_credit.
    rewrite (@controlled_get_ready_stable st owner target Hstable observed),
      sigma_value_get_ready, stored_phase_get_ready. reflexivity.
  Qed.

  Lemma side_credit_get_ready :
    forall st owner target source observed,
      Measure.side_credit (R.get_ready_state st owner target)
        source observed = Measure.side_credit st source observed.
  Proof.
    intros. unfold Measure.side_credit, R.get_ready_state,
      R.add_reader, R.promote_controlled, R.materialize,
      R.stored_side_phase, R.stored_contribution.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      destruct (R.is_materialized _ _); reflexivity.
  Qed.

  Lemma charged_update_credit_get_ready_stable :
    forall support st owner target,
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true \/
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      Measure.charged_update_credit support
        (R.get_ready_state st owner target) =
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner target Hstable.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    - apply Accounting.sum_over_pointwise_eq. intros.
      now apply charged_ordinary_credit_get_ready_stable.
    - apply Accounting.sum_over_pointwise_eq. intros source Hsource.
      apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      apply side_credit_get_ready.
  Qed.

  Lemma controlled_get_ready_target_not_higher :
    forall st owner target,
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = false ->
      S.mem (R.handle_variable target)
        (R.controlled (R.get_ready_state st owner target)) = true.
  Proof.
    intros st owner target Hnothigher.
    unfold R.get_ready_state. rewrite Hnothigher.
    unfold R.promote_controlled, R.add_reader, R.materialize.
    destruct (R.is_materialized _ _); cbn;
      apply SL.add_spec; now left.
  Qed.

  Lemma get_ready_stable_from_count :
    forall support st owner target,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.get_ready_state st owner target) =
      Measure.uncontrolled_count support st ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true \/
      S.mem (R.handle_variable target) (R.controlled st) = true.
  Proof.
    intros support st owner target Hnodup Htarget Hcount.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target))
      eqn:Hhigher; [now left |].
    destruct (S.mem (R.handle_variable target) (R.controlled st))
      eqn:Hcontrolled; [now right |].
    exfalso. pose proof (@Measure.uncontrolled_count_strict_from_mono
      support st (R.get_ready_state st owner target)
      (R.handle_variable target) Hnodup Htarget
      (fun observed Hobserved =>
        @Measure.controlled_get_ready_mono st owner target observed Hobserved)
      Hcontrolled
      (@controlled_get_ready_target_not_higher st owner target Hhigher))
      as Hstrict. lia.
  Qed.

  Lemma side_ready_source_controlled_not_down :
    forall st source target raw,
      Nat.ltb (R.handle_rank target) (R.handle_rank source) = false ->
      S.mem (R.handle_variable source)
        (R.controlled (R.side_ready_state st source target raw)) = true.
  Proof.
    intros st source target raw Horder.
    unfold R.side_ready_state. rewrite Horder.
    unfold R.promote_controlled. cbn.
    apply SL.add_spec. now left.
  Qed.

  Lemma side_ready_stable_from_count :
    forall support st source target raw,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      Measure.uncontrolled_count support
        (R.side_ready_state st source target raw) =
      Measure.uncontrolled_count support st ->
      Nat.ltb (R.handle_rank target) (R.handle_rank source) = true \/
      S.mem (R.handle_variable source) (R.controlled st) = true.
  Proof.
    intros support st source target raw Hnodup Hsource Hcount.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source))
      eqn:Horder; [now left |].
    destruct (S.mem (R.handle_variable source) (R.controlled st))
      eqn:Hcontrolled; [now right |].
    exfalso. pose proof (@Measure.uncontrolled_count_strict_from_mono
      support st (R.side_ready_state st source target raw)
      (R.handle_variable source) Hnodup Hsource
      (fun observed Hobserved =>
        @Measure.controlled_side_ready_mono
          st source target raw observed Hobserved)
      Hcontrolled
      (@side_ready_source_controlled_not_down st source target raw Horder))
      as Hstrict. lia.
  Qed.

  Lemma charged_update_credit_get_ready_from_count :
    forall support st owner target,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.get_ready_state st owner target) =
      Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.get_ready_state st owner target) =
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner target Hnodup Htarget Hcount.
    apply charged_update_credit_get_ready_stable.
    eapply get_ready_stable_from_count; eauto.
  Qed.

  Lemma charged_update_credit_side_ready_from_count :
    forall support st source target raw,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      Measure.uncontrolled_count support
        (R.side_ready_state st source target raw) =
      Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.side_ready_state st source target raw) <=
      Measure.charged_update_credit support st.
  Proof.
    intros support st source target raw Hnodup Hsource Hcount.
    apply Accounting.charged_update_credit_side_ready_nonincreasing.
    eapply side_ready_stable_from_count; eauto.
  Qed.

  Lemma charged_update_credit_set_value_nonincreasing :
    forall support st owner direct,
      Measure.charged_update_credit support (R.set_value st owner direct) <=
      Measure.charged_update_credit support st.
  Proof.
    intros. destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
    - now apply
        Accounting.charged_update_credit_set_value_controlled_nonincreasing.
    - rewrite Accounting.charged_update_credit_set_value_uncontrolled
        by exact Hcontrolled. lia.
  Qed.

  Lemma observed_get_ready_credit_nonincreasing :
    forall support before target observed target_handle owner,
      R.observe before target = (observed, target_handle) ->
      NoDup support ->
      List.In target support ->
      Measure.uncontrolled_count support
        (R.get_ready_state observed owner target_handle) =
      Measure.uncontrolled_count support before ->
      Measure.charged_update_credit support
        (R.get_ready_state observed owner target_handle) <=
      Measure.charged_update_credit support before.
  Proof.
    intros support before target observed target_handle owner
      Hobserve Hnodup Htarget Hcount.
    assert (Hhandle : List.In (R.handle_variable target_handle) support).
    { rewrite (@observed_handle_variable before target observed
        target_handle Hobserve). exact Htarget. }
    assert (Hobserved : Measure.uncontrolled_count support observed =
      Measure.uncontrolled_count support before).
    { exact (@uncontrolled_count_observe support before target observed
        target_handle Hobserve). }
    rewrite (@charged_update_credit_get_ready_from_count
      support observed owner target_handle Hnodup Hhandle) by lia.
    rewrite (@charged_update_credit_observe support before target
      observed target_handle Hobserve). lia.
  Qed.

  Lemma observed_enqueued_get_ready_credit_nonincreasing :
    forall support before target observed target_handle owner,
      R.observe before target = (observed, target_handle) ->
      NoDup support ->
      List.In target support ->
      Measure.uncontrolled_count support
        (R.get_ready_state (R.enqueue_handle observed target_handle)
          owner target_handle) =
      Measure.uncontrolled_count support before ->
      Measure.charged_update_credit support
        (R.get_ready_state (R.enqueue_handle observed target_handle)
          owner target_handle) <=
      Measure.charged_update_credit support before.
  Proof.
    intros support before target observed target_handle owner
      Hobserve Hnodup Htarget Hcount.
    assert (Hhandle : List.In (R.handle_variable target_handle) support).
    { rewrite (@observed_handle_variable before target observed
        target_handle Hobserve). exact Htarget. }
    assert (Hobserved : Measure.uncontrolled_count support observed =
      Measure.uncontrolled_count support before).
    { exact (@uncontrolled_count_observe support before target observed
        target_handle Hobserve). }
    rewrite (@charged_update_credit_get_ready_from_count support
      (R.enqueue_handle observed target_handle) owner target_handle
      Hnodup Hhandle)
      by (rewrite uncontrolled_count_enqueue_handle; lia).
    rewrite charged_update_credit_enqueue_handle.
    rewrite (@charged_update_credit_observe support before target
      observed target_handle Hobserve). lia.
  Qed.

  Lemma observed_side_ready_credit_nonincreasing :
    forall support before target observed target_handle source raw,
      R.observe before target = (observed, target_handle) ->
      NoDup support ->
      List.In (R.handle_variable source) support ->
      Measure.uncontrolled_count support
        (R.side_ready_state observed source target_handle raw) =
      Measure.uncontrolled_count support before ->
      Measure.charged_update_credit support
        (R.side_ready_state observed source target_handle raw) <=
      Measure.charged_update_credit support before.
  Proof.
    intros support before target observed target_handle source raw
      Hobserve Hnodup Hsource Hcount.
    assert (Hobserved : Measure.uncontrolled_count support observed =
      Measure.uncontrolled_count support before).
    { exact (@uncontrolled_count_observe support before target observed
        target_handle Hobserve). }
    pose proof (@charged_update_credit_side_ready_from_count
      support observed source target_handle raw Hnodup Hsource)
      as Hle.
    assert (Hready : Measure.uncontrolled_count support
      (R.side_ready_state observed source target_handle raw) =
      Measure.uncontrolled_count support observed) by lia.
    specialize (Hle Hready).
    rewrite (@charged_update_credit_observe support before target
      observed target_handle Hobserve) in Hle.
    exact Hle.
  Qed.

  Lemma observed_enqueued_side_ready_credit_nonincreasing :
    forall support before target observed target_handle source raw,
      R.observe before target = (observed, target_handle) ->
      NoDup support ->
      List.In (R.handle_variable source) support ->
      Measure.uncontrolled_count support
        (R.enqueue_handle
          (R.side_ready_state observed source target_handle raw)
          target_handle) =
      Measure.uncontrolled_count support before ->
      Measure.charged_update_credit support
        (R.enqueue_handle
          (R.side_ready_state observed source target_handle raw)
          target_handle) <=
      Measure.charged_update_credit support before.
  Proof.
    intros support before target observed target_handle source raw
      Hobserve Hnodup Hsource Hcount.
    rewrite charged_update_credit_enqueue_handle.
    apply observed_side_ready_credit_nonincreasing with (target := target);
      eauto.
    rewrite uncontrolled_count_enqueue_handle in Hcount. exact Hcount.
  Qed.

  Lemma observed_enqueued_materialize_credit :
    forall support before target observed target_handle,
      R.observe before target = (observed, target_handle) ->
      Measure.charged_update_credit support
        (R.materialize (R.enqueue_handle observed target_handle) target) =
      Measure.charged_update_credit support before.
  Proof.
    intros. rewrite charged_update_credit_materialize,
      charged_update_credit_enqueue_handle.
    exact (@charged_update_credit_observe
      support before target observed target_handle H).
  Qed.

  Lemma charged_update_credit_step_nonincreasing :
    forall support tf before after,
      NoDup support ->
      control_supported support (R.cfg_control before) ->
      Sem.step tf before after ->
      Measure.unmaterialized_count support (R.cfg_state after) =
        Measure.unmaterialized_count support (R.cfg_state before) ->
      Measure.uncontrolled_count support (R.cfg_state after) =
        Measure.uncontrolled_count support (R.cfg_state before) ->
      Measure.charged_update_credit support (R.cfg_state after) <=
        Measure.charged_update_credit support (R.cfg_state before).
  Proof.
    intros support tf [st control] after Hnodup Hsupported Hstep
      Hmaterialized Hcontrolled.
    unfold Sem.step in Hstep. cbn in Hstep, Hsupported.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst;
      cbn in Hsupported, Hmaterialized, Hcontrolled |- *.
    all: try (rewrite charged_update_credit_with_queue; lia).
    all: try (rewrite charged_update_credit_with_started,
      charged_update_credit_start_evaluation; lia).
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite (@charged_update_credit_observe
            support before target next entry Hobserve); lia
      end.
    all: try apply charged_update_credit_set_value_nonincreasing.
    all: try lia.
    all: try match goal with
      | Hsup : supported ?sup _ /\
          Sem.rhs_supported (supported ?sup)
            (R.ConstraintSystem.Get ?target ?next) /\ _ |- _ =>
          destruct Hsup as [Howner [Hrhs Hcontinuation]];
          destruct (rhs_supported_get_inv Hrhs) as [Htarget Hnext]
      | Hsup : supported ?sup _ /\
          Sem.rhs_supported (supported ?sup)
            (R.ConstraintSystem.Side ?target ?raw ?next) /\ _ |- _ =>
          destruct Hsup as [Howner [Hrhs Hcontinuation]];
          destruct (rhs_supported_side_inv Hrhs) as [Htarget Hnext]
      | Hsup : supported ?sup _ /\
          Sem.rhs_supported (supported ?sup)
            (R.ConstraintSystem.Spawn ?target ?next) /\ _ |- _ =>
          destruct Hsup as [Howner [Hrhs Hcontinuation]];
          destruct (rhs_supported_spawn_inv Hrhs) as [Htarget Hnext]
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?observed, ?entry),
        Htarget : supported ?sup ?target |-
          Measure.charged_update_credit ?sup
            (R.get_ready_state
              (R.enqueue_handle ?observed ?entry) ?owner ?entry) <= _ =>
          eapply (@observed_enqueued_get_ready_credit_nonincreasing
            sup before target observed entry owner); eauto
      | Hobserve : R.observe ?before ?target = (?observed, ?entry),
        Htarget : supported ?sup ?target |-
          Measure.charged_update_credit ?sup
            (R.get_ready_state ?observed ?owner ?entry) <= _ =>
          eapply (@observed_get_ready_credit_nonincreasing
            sup before target observed entry owner); eauto
      | Hobserve : R.observe ?before ?target = (?observed, ?entry),
        Howner : supported ?sup (R.handle_variable ?source) |-
          Measure.charged_update_credit ?sup
            (R.enqueue_handle
              (R.side_ready_state ?observed ?source ?entry ?raw)
              ?entry) <= _ =>
          eapply (@observed_enqueued_side_ready_credit_nonincreasing
            sup before target observed entry source raw); eauto
      | Hobserve : R.observe ?before ?target = (?observed, ?entry),
        Howner : supported ?sup (R.handle_variable ?source) |-
          Measure.charged_update_credit ?sup
            (R.side_ready_state ?observed ?source ?entry ?raw) <= _ =>
          eapply (@observed_side_ready_credit_nonincreasing
            sup before target observed entry source raw); eauto
      | Hobserve : R.observe ?before ?target = (?observed, ?entry) |-
          Measure.charged_update_credit ?sup
            (R.materialize
              (R.enqueue_handle ?observed ?entry) ?target) <= _ =>
          rewrite (@observed_enqueued_materialize_credit
            sup before target observed entry Hobserve); lia
      end.
    destruct Hsupported as [Howner [Htarget [Hnext Hcontinuation]]].
    rewrite (@charged_update_credit_get_ready_from_count
      support st h h0 Hnodup Htarget Hcontrolled). lia.
  Qed.

  Definition round_nonincreasing
    (support : list V.t) (before after : R.config) : Prop :=
    Measure.unmaterialized_count support (R.cfg_state after) <
      Measure.unmaterialized_count support (R.cfg_state before) \/
    Measure.unmaterialized_count support (R.cfg_state after) =
      Measure.unmaterialized_count support (R.cfg_state before) /\
    (Measure.uncontrolled_count support (R.cfg_state after) <
       Measure.uncontrolled_count support (R.cfg_state before) \/
     Measure.uncontrolled_count support (R.cfg_state after) =
       Measure.uncontrolled_count support (R.cfg_state before) /\
     Measure.charged_update_credit support (R.cfg_state after) <=
       Measure.charged_update_credit support (R.cfg_state before)).

  Definition round_decreases
    (support : list V.t) (before after : R.config) : Prop :=
    Measure.unmaterialized_count support (R.cfg_state after) <
      Measure.unmaterialized_count support (R.cfg_state before) \/
    Measure.unmaterialized_count support (R.cfg_state after) =
      Measure.unmaterialized_count support (R.cfg_state before) /\
    (Measure.uncontrolled_count support (R.cfg_state after) <
       Measure.uncontrolled_count support (R.cfg_state before) \/
     Measure.uncontrolled_count support (R.cfg_state after) =
       Measure.uncontrolled_count support (R.cfg_state before) /\
     Measure.charged_update_credit support (R.cfg_state after) <
       Measure.charged_update_credit support (R.cfg_state before)).

  Lemma round_nonincreasing_step :
    forall support tf before after,
      NoDup support ->
      control_supported support (R.cfg_control before) ->
      Sem.step tf before after ->
      round_nonincreasing support before after.
  Proof.
    intros support tf before after Hnodup Hsupported Hstep.
    pose proof (Measure.unmaterialized_count_step_nonincreasing
      support Hstep) as Hmaterialized.
    destruct (PeanoNat.Nat.eq_dec
      (Measure.unmaterialized_count support (R.cfg_state after))
      (Measure.unmaterialized_count support (R.cfg_state before)))
      as [Hmaterialized_eq | Hmaterialized_neq].
    2: { left. lia. }
    right. split; [exact Hmaterialized_eq |].
    pose proof (Measure.uncontrolled_count_step_nonincreasing
      support Hstep) as Hcontrolled.
    destruct (PeanoNat.Nat.eq_dec
      (Measure.uncontrolled_count support (R.cfg_state after))
      (Measure.uncontrolled_count support (R.cfg_state before)))
      as [Hcontrolled_eq | Hcontrolled_neq].
    2: { left. lia. }
    right. split; [exact Hcontrolled_eq |].
    eapply charged_update_credit_step_nonincreasing; eauto.
  Qed.

  Lemma round_nonincreasing_refl :
    forall support c, round_nonincreasing support c c.
  Proof. intros. right. repeat split; lia. Qed.

  Lemma round_nonincreasing_trans :
    forall support first middle last,
      round_nonincreasing support first middle ->
      round_nonincreasing support middle last ->
      round_nonincreasing support first last.
  Proof.
    intros support first middle last
      [Hfirst | [Hmaterialized1
        [Hcontrolled1 | [Hcontrolled_eq1 Hcredit1]]]]
      [Hsecond | [Hmaterialized2
        [Hcontrolled2 | [Hcontrolled_eq2 Hcredit2]]]].
    all: unfold round_nonincreasing in *.
    all: try (left; lia).
    all: right; split; [lia |].
    all: try (left; lia).
    all: right; split; lia.
  Qed.

  Lemma round_decreases_left :
    forall support first middle last,
      round_decreases support first middle ->
      round_nonincreasing support middle last ->
      round_decreases support first last.
  Proof.
    intros support first middle last
      [Hfirst | [Hmaterialized1
        [Hcontrolled1 | [Hcontrolled_eq1 Hcredit1]]]]
      [Hsecond | [Hmaterialized2
        [Hcontrolled2 | [Hcontrolled_eq2 Hcredit2]]]].
    all: unfold round_decreases, round_nonincreasing in *.
    all: try (left; lia).
    all: right; split; [lia |].
    all: try (left; lia).
    all: right; split; lia.
  Qed.

  Lemma round_decreases_right :
    forall support first middle last,
      round_nonincreasing support first middle ->
      round_decreases support middle last ->
      round_decreases support first last.
  Proof.
    intros support first middle last
      [Hfirst | [Hmaterialized1
        [Hcontrolled1 | [Hcontrolled_eq1 Hcredit1]]]]
      [Hsecond | [Hmaterialized2
        [Hcontrolled2 | [Hcontrolled_eq2 Hcredit2]]]].
    all: unfold round_nonincreasing, round_decreases in *.
    all: try (left; lia).
    all: right; split; [lia |].
    all: try (left; lia).
    all: right; split; lia.
  Qed.

  Lemma round_decreases_measure :
    forall support before after,
      round_decreases support before after ->
      Measure.round_measure_lt support after before.
  Proof.
    intros support before after
      [Hmaterialized | [Hmaterialized
        [Hcontrolled | [Hcontrolled Hcredit]]]].
    - unfold Measure.round_measure_lt, Measure.round_key_lt,
        Measure.round_key. now apply left_slex.
    - unfold Measure.round_measure_lt, Measure.round_key_lt,
        Measure.round_key. rewrite Hmaterialized. apply right_slex.
      unfold Measure.nat_pair_lt. now apply left_slex.
    - unfold Measure.round_measure_lt, Measure.round_key_lt,
        Measure.round_key. rewrite Hmaterialized. apply right_slex.
      unfold Measure.nat_pair_lt. rewrite Hcontrolled.
      now apply right_slex.
  Qed.

  (** A step is unpaid when none of the three finite round resources is
      consumed.  Keeping this predicate independent of the executable shape
      gives the later owner-round proof a small interface to the accounting
      argument above. *)
  Definition unpaid_step
    (support : list V.t) (tf : R.ConstraintSystem.system)
    (before after : R.config) : Prop :=
    Sem.step tf before after /\
    Measure.unmaterialized_count support (R.cfg_state after) =
      Measure.unmaterialized_count support (R.cfg_state before) /\
    Measure.uncontrolled_count support (R.cfg_state after) =
      Measure.uncontrolled_count support (R.cfg_state before) /\
    Measure.charged_update_credit support (R.cfg_state after) =
      Measure.charged_update_credit support (R.cfg_state before).

  Lemma unpaid_step_nonincreasing :
    forall support tf before after,
      unpaid_step support tf before after ->
      round_nonincreasing support before after.
  Proof.
    intros support tf before after
      [_ [Hmaterialized [Hcontrolled Hcredit]]].
    right. split; [exact Hmaterialized |].
    right. split; [exact Hcontrolled |lia].
  Qed.

  Lemma step_decreases_or_unpaid :
    forall support tf before after,
      NoDup support ->
      control_supported support (R.cfg_control before) ->
      Sem.step tf before after ->
      round_decreases support before after \/
      unpaid_step support tf before after.
  Proof.
    intros support tf before after Hnodup Hsupported Hstep.
    pose proof (@round_nonincreasing_step
      support tf before after Hnodup Hsupported Hstep) as Hmono.
    destruct Hmono as
      [Hmaterialized |
       [Hmaterialized
        [Hcontrolled | [Hcontrolled Hcredit]]]].
    - left. now left.
    - left. right. split; [exact Hmaterialized |now left].
    - destruct (PeanoNat.Nat.eq_dec
        (Measure.charged_update_credit support (R.cfg_state after))
        (Measure.charged_update_credit support (R.cfg_state before)))
        as [Hcredit_eq | Hcredit_neq].
      + right. repeat split; assumption.
      + left. right. split; [exact Hmaterialized |].
        right. split; [exact Hcontrolled |lia].
  Qed.

  Lemma unpaid_step_reflects_materialization :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_step support tf before after ->
      R.is_materialized (R.cfg_state after) variable = true ->
      R.is_materialized (R.cfg_state before) variable = true.
  Proof.
    intros support tf before after variable Hnodup Hin
      [Hstep [Hmaterialized [_ _]]] Hafter.
    destruct (R.is_materialized (R.cfg_state before) variable)
      eqn:Hbefore; [reflexivity |].
    pose proof (@Measure.unmaterialized_count_strict
      support tf before after variable Hnodup Hin
      (@Sem.StepsStep tf before after after
        Hstep (@Sem.StepsRefl tf after)) Hbefore Hafter) as Hstrict.
    lia.
  Qed.

  Lemma unpaid_step_reflects_control :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_step support tf before after ->
      S.mem variable (R.controlled (R.cfg_state after)) = true ->
      S.mem variable (R.controlled (R.cfg_state before)) = true.
  Proof.
    intros support tf before after variable Hnodup Hin
      [Hstep [_ [Hcontrolled _]]] Hafter.
    destruct (S.mem variable (R.controlled (R.cfg_state before)))
      eqn:Hbefore; [reflexivity |].
    pose proof (@Measure.uncontrolled_count_strict
      support tf before after variable Hnodup Hin
      (@Sem.StepsStep tf before after after
        Hstep (@Sem.StepsRefl tf after)) Hbefore Hafter) as Hstrict.
    lia.
  Qed.

  Inductive unpaid_steps
    (support : list V.t) (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | UnpaidStepsRefl :
      forall c, unpaid_steps support tf c c
  | UnpaidStepsStep :
      forall first next last,
        unpaid_step support tf first next ->
        unpaid_steps support tf next last ->
        unpaid_steps support tf first last.

  (** [supported_steps] records precisely the support fact required by the
      local payment theorem at each source configuration. *)
  Inductive supported_steps
    (support : list V.t) (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | SupportedStepsRefl :
      forall c, supported_steps support tf c c
  | SupportedStepsStep :
      forall first next last,
        control_supported support (R.cfg_control first) ->
        Sem.step tf first next ->
        supported_steps support tf next last ->
        supported_steps support tf first last.

  Inductive supported_unpaid_steps
    (support : list V.t) (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | SupportedUnpaidRefl :
      forall c, supported_unpaid_steps support tf c c
  | SupportedUnpaidStep :
      forall first next last,
        control_supported support (R.cfg_control first) ->
        unpaid_step support tf first next ->
        supported_unpaid_steps support tf next last ->
        supported_unpaid_steps support tf first last.

  Lemma unpaid_steps_semantic :
    forall support tf before after,
      unpaid_steps support tf before after ->
      Sem.steps tf before after.
  Proof.
    intros support tf before after Hsteps. induction Hsteps.
    - constructor.
    - econstructor; [exact (proj1 H) |exact IHHsteps].
  Qed.

  Lemma supported_steps_semantic :
    forall support tf before after,
      supported_steps support tf before after ->
      Sem.steps tf before after.
  Proof.
    intros support tf before after Hsteps. induction Hsteps.
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma supported_unpaid_steps_unpaid :
    forall support tf before after,
      supported_unpaid_steps support tf before after ->
      unpaid_steps support tf before after.
  Proof.
    intros support tf before after Hsteps. induction Hsteps.
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma supported_steps_nonincreasing :
    forall support tf before after,
      NoDup support ->
      supported_steps support tf before after ->
      round_nonincreasing support before after.
  Proof.
    intros support tf before after Hnodup Hsteps. induction Hsteps.
    - apply round_nonincreasing_refl.
    - eapply round_nonincreasing_trans.
      + eapply round_nonincreasing_step; eauto.
      + exact IHHsteps.
  Qed.

  Lemma supported_steps_decrease_or_unpaid :
    forall support tf before after,
      NoDup support ->
      supported_steps support tf before after ->
      round_decreases support before after \/
      supported_unpaid_steps support tf before after.
  Proof.
    intros support tf before after Hnodup Hsteps.
    induction Hsteps.
    - right. constructor.
    - destruct (@step_decreases_or_unpaid
        support tf first next Hnodup H H0) as [Hfirst | Hfirst].
      + left. eapply round_decreases_left.
        * exact Hfirst.
        * eapply supported_steps_nonincreasing; eauto.
      + destruct IHHsteps as [Htail | Htail].
        * left. eapply round_decreases_right.
          -- exact (@unpaid_step_nonincreasing
               support tf first next Hfirst).
          -- exact Htail.
        * right. econstructor; eauto.
  Qed.

  Lemma reachable_steps_supported :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      Sem.steps tf (R.initial_config roots) before ->
      Sem.steps tf before after ->
      supported_steps (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite before after Hprefix Hsteps.
    revert Hprefix. induction Hsteps; intros Hprefix.
    - constructor.
    - econstructor.
      + exact (proj2
          (reachable_config_supported
            finite Hprefix)).
      + exact H.
      + apply IHHsteps.
        eapply Sim.steps_append_one; eauto.
  Qed.

  Theorem reachable_steps_decrease_or_unpaid :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      Sem.steps tf (R.initial_config roots) before ->
      Sem.steps tf before after ->
      round_decreases (Sem.support finite) before after \/
      supported_unpaid_steps (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite before after Hprefix Hsteps.
    apply supported_steps_decrease_or_unpaid.
    - exact (Sem.support_nodup finite).
    - eapply reachable_steps_supported; eauto.
  Qed.

  Inductive scoped_supported_unpaid_steps
    (owner : R.handle) (base : R.continuation)
    (support : list V.t) (tf : R.ConstraintSystem.system) :
    R.config -> R.config -> Prop :=
  | ScopedSupportedUnpaidRefl :
      forall c,
        scoped_supported_unpaid_steps owner base support tf c c
  | ScopedSupportedUnpaidStep :
      forall first next last,
        Sim.control_in_scope owner base (R.cfg_control first) ->
        control_supported support (R.cfg_control first) ->
        unpaid_step support tf first next ->
        scoped_supported_unpaid_steps owner base support tf next last ->
        scoped_supported_unpaid_steps owner base support tf first last.

  Theorem reachable_scoped_steps_decrease_or_unpaid :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base before after,
      Sem.steps tf (R.initial_config roots) before ->
      Sim.scoped_until_steps owner base tf before after ->
      round_decreases (Sem.support finite) before after \/
      scoped_supported_unpaid_steps
        owner base (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite owner base before after Hprefix Hsteps.
    revert Hprefix. induction Hsteps; intros Hprefix.
    - right. constructor.
    - assert (Hnext_prefix :
        Sem.steps tf (R.initial_config roots) next).
      { eapply Sim.steps_append_one; eauto. }
      pose proof (proj2
        (reachable_config_supported
          finite Hprefix)) as Hsupported.
      destruct (@step_decreases_or_unpaid
        (Sem.support finite) tf first next
        (Sem.support_nodup finite) Hsupported H0)
        as [Hfirst | Hfirst].
      + left. eapply round_decreases_left.
        * exact Hfirst.
        * eapply supported_steps_nonincreasing.
          -- exact (Sem.support_nodup finite).
          -- eapply reachable_steps_supported.
             ++ exact Hnext_prefix.
             ++ exact (Sim.scoped_until_semantic Hsteps).
      + destruct (IHHsteps Hnext_prefix) as [Htail | Htail].
        * left. eapply round_decreases_right.
          -- exact (@unpaid_step_nonincreasing
               (Sem.support finite) tf first next Hfirst).
          -- exact Htail.
        * right. econstructor; eauto.
  Qed.

  Lemma unpaid_steps_reflect_materialization :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_steps support tf before after ->
      R.is_materialized (R.cfg_state after) variable = true ->
      R.is_materialized (R.cfg_state before) variable = true.
  Proof.
    intros support tf before after variable Hnodup Hin Hsteps.
    induction Hsteps; intros Hafter.
    - exact Hafter.
    - eapply unpaid_step_reflects_materialization; eauto.
  Qed.

  Lemma unpaid_steps_reflect_control :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_steps support tf before after ->
      S.mem variable (R.controlled (R.cfg_state after)) = true ->
      S.mem variable (R.controlled (R.cfg_state before)) = true.
  Proof.
    intros support tf before after variable Hnodup Hin Hsteps.
    induction Hsteps; intros Hafter.
    - exact Hafter.
    - eapply unpaid_step_reflects_control; eauto.
  Qed.

  Lemma unpaid_steps_materialized_equal :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_steps support tf before after ->
      R.is_materialized (R.cfg_state after) variable =
      R.is_materialized (R.cfg_state before) variable.
  Proof.
    intros support tf before after variable Hnodup Hin Hsteps.
    destruct (R.is_materialized (R.cfg_state before) variable)
      eqn:Hbefore.
    - eapply Measure.materialized_steps_mono.
      + exact (@unpaid_steps_semantic support tf before after Hsteps).
      + exact Hbefore.
    - destruct (R.is_materialized (R.cfg_state after) variable)
        eqn:Hafter; [|reflexivity].
      pose proof (@unpaid_steps_reflect_materialization
        support tf before after variable Hnodup Hin Hsteps Hafter).
      congruence.
  Qed.

  Lemma unpaid_steps_control_equal :
    forall support tf before after variable,
      NoDup support ->
      List.In variable support ->
      unpaid_steps support tf before after ->
      S.mem variable (R.controlled (R.cfg_state after)) =
      S.mem variable (R.controlled (R.cfg_state before)).
  Proof.
    intros support tf before after variable Hnodup Hin Hsteps.
    destruct (S.mem variable (R.controlled (R.cfg_state before)))
      eqn:Hbefore.
    - eapply Measure.controlled_steps_mono.
      + exact (@unpaid_steps_semantic support tf before after Hsteps).
      + exact Hbefore.
    - destruct (S.mem variable (R.controlled (R.cfg_state after)))
        eqn:Hafter; [|reflexivity].
      pose proof (@unpaid_steps_reflect_control
        support tf before after variable Hnodup Hin Hsteps Hafter).
      congruence.
  Qed.

  Lemma equivalent_set_value_sigma_same :
    forall st owner direct,
      UL.equivalent
        (R.sigma_value (R.set_value st owner direct) owner)
        (R.sigma_value st owner) ->
      R.sigma_value (R.set_value st owner direct) owner =
      R.sigma_value st owner.
  Proof.
    intros st owner direct Hequivalent.
    unfold R.set_value in Hequivalent |- *.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner))
      (R.sigma_value st owner)) eqn:Hcandidate; [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner
        (R.stored_phase st owner) (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner)))
        as [phase value] eqn:Hupdate. cbn in *.
      destruct (R.equivalent value (R.sigma_value st owner))
        eqn:Hvalue; [reflexivity |].
      exfalso. apply (Accounting.equivalent_false Hvalue).
      rewrite Accounting.sigma_value_write_changed_same in Hequivalent.
      exact Hequivalent.
    - exfalso. apply (Accounting.equivalent_false Hcandidate).
      rewrite Accounting.sigma_value_write_changed_same in Hequivalent.
      exact Hequivalent.
  Qed.

  Lemma unpaid_controlled_ret_sigma_same :
    forall support tf st owner direct k,
      List.In (R.handle_variable owner) support ->
      S.mem (R.handle_variable owner) (R.controlled st) = true ->
      unpaid_step support tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        {| R.cfg_state :=
             R.set_value st (R.handle_variable owner) direct;
           R.cfg_control := R.RunSolveOneLoop owner k |} ->
      R.sigma_value
        (R.set_value st (R.handle_variable owner) direct)
        (R.handle_variable owner) =
      R.sigma_value st (R.handle_variable owner).
  Proof.
    intros support tf st owner direct k Howner Hcontrolled
      [_ [_ [_ Hcredit]]].
    apply equivalent_set_value_sigma_same.
    destruct (R.equivalent
      (R.sigma_value
        (R.set_value st (R.handle_variable owner) direct)
        (R.handle_variable owner))
      (R.sigma_value st (R.handle_variable owner)))
      eqn:Hequivalent.
    - now apply Accounting.equivalent_true.
    - exfalso.
      pose proof
        (@Accounting.charged_update_credit_set_value_controlled_decreases
          support st (R.handle_variable owner) direct Howner Hcontrolled
          (@Accounting.equivalent_false _ _ Hequivalent)) as Hstrict.
      cbn in Hcredit. lia.
  Qed.

  Lemma sigma_value_observe :
    forall st target next entry observed,
      R.observe st target = (next, entry) ->
      R.sigma_value next observed = R.sigma_value st observed.
  Proof.
    intros st target next entry observed Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma sigma_value_start_evaluation :
    forall st owner observed,
      R.sigma_value (R.start_evaluation st owner) observed =
      R.sigma_value st observed.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides.
    apply sigma_value_materialize.
  Qed.

  Lemma sigma_value_side_ready :
    forall st source target raw observed,
      R.sigma_value (R.side_ready_state st source target raw) observed =
      R.sigma_value st observed.
  Proof.
    intros. unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      reflexivity.
  Qed.

  Lemma sigma_value_set_value_other :
    forall st owner direct observed,
      observed <> owner ->
      R.sigma_value (R.set_value st owner direct) observed =
      R.sigma_value st observed.
  Proof.
    intros st owner direct observed Hneq. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner)).
      + reflexivity.
      + rewrite Accounting.sigma_value_write_changed_other by exact Hneq.
        reflexivity.
    - now apply Accounting.sigma_value_write_changed_other.
  Qed.

  Lemma unpaid_step_controlled_sigma_same :
    forall support tf before after observed,
      control_supported support (R.cfg_control before) ->
      List.In observed support ->
      S.mem observed (R.controlled (R.cfg_state before)) = true ->
      unpaid_step support tf before after ->
      R.sigma_value (R.cfg_state after) observed =
      R.sigma_value (R.cfg_state before) observed.
  Proof.
    intros support tf [st control] after observed Hsupported Hobserved
      Hcontrolled [Hstep [Hmaterialized [Hcontrolled_count Hcredit]]].
    unfold Sem.step in Hstep. cbn in Hstep, Hsupported, Hcontrolled.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst;
      cbn in Hsupported, Hmaterialized, Hcontrolled_count, Hcredit |- *.
    all: try reflexivity.
    all: try apply sigma_value_start_evaluation.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite (@sigma_value_observe
            before target next entry observed Hobserve); reflexivity
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite sigma_value_get_ready,
            (@sigma_value_observe
              before target next entry observed Hobserve); reflexivity
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite sigma_value_side_ready,
            (@sigma_value_observe
              before target next entry observed Hobserve); reflexivity
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite sigma_value_materialize,
            (@sigma_value_observe
              before target next entry observed Hobserve); reflexivity
      end.
    all: try rewrite sigma_value_get_ready.
    all: try reflexivity.
    all: try change
      (R.sigma_value s observed = R.sigma_value st observed).
    all: try change
      (R.sigma_value (R.side_ready_state s h h0 t0) observed =
       R.sigma_value st observed).
    all: try rewrite sigma_value_side_ready.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite (@sigma_value_observe
            before target next entry observed Hobserve); reflexivity
      end.
    all: try rewrite sigma_value_materialize.
    all: try change
      (R.sigma_value s observed = R.sigma_value st observed).
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite (@sigma_value_observe
            before target next entry observed Hobserve); reflexivity
      end.
    destruct (V.eq_dec observed (R.handle_variable h)) as [-> | Hneq].
    - eapply (@unpaid_controlled_ret_sigma_same support tf st h t c).
      + exact (proj1 Hsupported).
      + exact Hcontrolled.
      + repeat split; assumption.
    - now apply sigma_value_set_value_other.
  Qed.

  Lemma supported_unpaid_steps_controlled_sigma_same :
    forall support tf before after observed,
      List.In observed support ->
      S.mem observed (R.controlled (R.cfg_state before)) = true ->
      supported_unpaid_steps support tf before after ->
      R.sigma_value (R.cfg_state after) observed =
      R.sigma_value (R.cfg_state before) observed.
  Proof.
    intros support tf before after observed Hobserved Hcontrolled Hsteps.
    revert Hcontrolled. induction Hsteps; intros Hcontrolled.
    - reflexivity.
    - assert (Hnext_controlled :
        S.mem observed (R.controlled (R.cfg_state next)) = true).
      {
        eapply Measure.controlled_step_mono.
        - exact (proj1 H0).
        - exact Hcontrolled.
      }
      rewrite (IHHsteps Hnext_controlled).
      eapply unpaid_step_controlled_sigma_same; eauto.
  Qed.

  End Payment.
  Module Restart.
  Definition reader_registered
    (st : R.state) (reader dependency : V.t) : Prop :=
    S.mem reader (R.lookup_set (R.readers st) dependency) = true.

  Definition ranked_before
    (st : R.state) (lower upper : V.t) : Prop :=
    exists lower_rank upper_rank,
      R.Ranking.lookup (R.ranking st) lower = Some lower_rank /\
      R.Ranking.lookup (R.ranking st) upper = Some upper_rank /\
      Nat.ltb lower_rank upper_rank = true.

  Definition readers_ranked (st : R.state) : Prop :=
    forall dependency reader,
      reader_registered st reader dependency ->
      S.mem dependency (R.controlled st) = false ->
      ranked_before st reader dependency.

  Lemma ranked_before_irrefl :
    forall st variable, ~ ranked_before st variable variable.
  Proof.
    intros st variable [left [right [Hleft [Hright Hlt]]]].
    rewrite Hleft in Hright. inversion Hright; subst.
    rewrite Nat.ltb_irrefl in Hlt. discriminate.
  Qed.

  Definition controlled_included (before after : R.state) : Prop :=
    forall variable,
      S.mem variable (R.controlled before) = true ->
      S.mem variable (R.controlled after) = true.

  Lemma noncontrolled_reflect :
    forall before after variable,
      controlled_included before after ->
      S.mem variable (R.controlled after) = false ->
      S.mem variable (R.controlled before) = false.
  Proof.
    intros before after variable Hincluded Hafter.
    destruct (S.mem variable (R.controlled before)) eqn:Hbefore;
      [|reflexivity].
    rewrite (Hincluded variable Hbefore) in Hafter. discriminate.
  Qed.

  Lemma ranked_before_extended :
    forall before after lower upper,
      rank_extends before after ->
      ranked_before before lower upper ->
      ranked_before after lower upper.
  Proof.
    intros before after lower upper Hextends
      [lower_rank [upper_rank [Hlower [Hupper Hlt]]]].
    exists lower_rank, upper_rank. repeat split; auto.
  Qed.

  Lemma readers_ranked_weaken :
    forall before after,
      rank_extends before after ->
      (forall dependency,
        R.lookup_set (R.readers after) dependency =
        R.lookup_set (R.readers before) dependency) ->
      controlled_included before after ->
      readers_ranked before ->
      readers_ranked after.
  Proof.
    intros before after Hextends Hreaders Hincluded Hranked
      dependency reader Hregistered Hnoncontrolled.
    apply ranked_before_extended with (before := before); [exact Hextends |].
    apply Hranked.
    - unfold reader_registered in *. now rewrite Hreaders in Hregistered.
    - eapply noncontrolled_reflect; eauto.
  Qed.

  Lemma readers_ranked_promote :
    forall st variable,
      readers_ranked st -> readers_ranked (R.promote_controlled st variable).
  Proof.
    intros st variable Hranked.
    eapply (@readers_ranked_weaken st (R.promote_controlled st variable)).
    - apply rank_extends_same_ranking. reflexivity.
    - reflexivity.
    - intros observed Hobserved. unfold R.promote_controlled. cbn.
      apply SL.add_spec. now right.
    - exact Hranked.
  Qed.

  Lemma readers_ranked_materialize :
    forall st variable,
      readers_ranked st -> readers_ranked (R.materialize st variable).
  Proof.
    intros st variable Hranked. unfold R.materialize.
    destruct (R.is_materialized st variable); exact Hranked.
  Qed.

  Lemma readers_ranked_add_reader :
    forall st dependency reader,
      handle_valid st dependency ->
      handle_valid st reader ->
      readers_ranked st ->
      (S.mem (R.handle_variable dependency) (R.controlled st) = false ->
       Nat.ltb (R.handle_rank reader) (R.handle_rank dependency) = true) ->
      readers_ranked (R.add_reader st
        (R.handle_variable dependency) (R.handle_variable reader)).
  Proof.
    intros st dependency reader Hdependency Hreader Hranked Hnew
      observed current Hregistered Hnoncontrolled.
    unfold reader_registered, R.add_reader, R.lookup_set in Hregistered.
    cbn in Hregistered, Hnoncontrolled.
    destruct (V.eq_dec observed (R.handle_variable dependency))
      as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hregistered.
      apply SL.add_spec in Hregistered.
      destruct Hregistered as [-> | Hregistered].
      + exists (R.handle_rank reader), (R.handle_rank dependency).
        repeat split; auto.
      + apply Hranked; assumption.
    - rewrite ML.lookup_update_other in Hregistered by exact Hneq.
      apply Hranked; assumption.
  Qed.

  Lemma readers_ranked_get_ready :
    forall st owner target,
      handle_valid st owner ->
      handle_valid st target ->
      readers_ranked st ->
      readers_ranked (R.get_ready_state st owner target).
  Proof.
    intros st owner target Howner Htarget Hranked.
    unfold R.get_ready_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target))
      eqn:Horder.
    - apply readers_ranked_materialize.
      eapply readers_ranked_add_reader; eauto.
    - apply readers_ranked_materialize.
      eapply readers_ranked_add_reader.
      + exact Htarget.
      + exact Howner.
      + apply readers_ranked_promote. exact Hranked.
      + intros Hnoncontrolled. exfalso.
        unfold R.promote_controlled in Hnoncontrolled. cbn in Hnoncontrolled.
        pose proof (proj2
          (SL.add_spec (R.handle_variable target)
            (R.handle_variable target) (R.controlled st))
          (or_introl eq_refl)) as Hmember.
        rewrite Hmember in Hnoncontrolled. discriminate.
  Qed.

  Lemma readers_ranked_record_side :
    forall st source target raw,
      readers_ranked st ->
      readers_ranked (R.record_side_payload st source target raw).
  Proof.
    intros st source target raw Hranked. unfold R.record_side_payload.
    destruct (U.update true target
      (R.stored_side_phase st source target)
      (R.stored_contribution st source target)
      (R.accumulated_side_input st source target raw)).
    exact Hranked.
  Qed.

  Lemma readers_ranked_side_ready :
    forall st source target raw,
      readers_ranked st -> readers_ranked (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw Hranked. unfold R.side_ready_state.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source)).
    - now apply readers_ranked_record_side.
    - apply readers_ranked_promote. now apply readers_ranked_record_side.
  Qed.

  Lemma readers_observe :
    forall st target next entry,
      R.observe st target = (next, entry) ->
      R.readers next = R.readers st.
  Proof.
    intros st target next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma readers_enqueue :
    forall st target,
      R.readers (R.enqueue st target) = R.readers st.
  Proof.
    intros st target. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    cbn. now apply readers_observe in Hobserve.
  Qed.

  Lemma readers_enqueue_all :
    forall xs st,
      R.readers (R.enqueue_all st xs) = R.readers st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn; [reflexivity |].
    rewrite IH, readers_enqueue. reflexivity.
  Qed.

  Lemma readers_ranked_observe :
    forall st target next entry,
      readers_ranked st ->
      R.observe st target = (next, entry) ->
      readers_ranked next.
  Proof.
    intros st target next entry Hranked Hobserve.
    eapply (@readers_ranked_weaken st next).
    - now apply rank_extends_observe in Hobserve.
    - intros dependency. unfold R.lookup_set.
      now rewrite (@readers_observe st target next entry Hobserve).
    - intros variable Hcontrolled.
      rewrite (@Measure.controlled_observe st target next entry Hobserve).
      exact Hcontrolled.
    - exact Hranked.
  Qed.

  Lemma readers_ranked_enqueue_handle :
    forall st entry,
      readers_ranked st -> readers_ranked (R.enqueue_handle st entry).
  Proof. intros. exact H. Qed.

  Lemma readers_ranked_enqueue :
    forall st target,
      readers_ranked st -> readers_ranked (R.enqueue st target).
  Proof.
    intros st target Hranked. unfold R.enqueue.
    destruct (R.observe st target) as [next entry] eqn:Hobserve.
    apply readers_ranked_enqueue_handle.
    eapply readers_ranked_observe; eauto.
  Qed.

  Lemma readers_ranked_enqueue_all :
    forall xs st,
      readers_ranked st -> readers_ranked (R.enqueue_all st xs).
  Proof. induction xs; intros; cbn; auto using readers_ranked_enqueue. Qed.

  Lemma readers_ranked_with_queue :
    forall st queue,
      readers_ranked st -> readers_ranked (R.with_queue st queue).
  Proof. intros. exact H. Qed.

  Lemma readers_ranked_with_started :
    forall st started,
      readers_ranked st -> readers_ranked (R.with_started st started).
  Proof. intros. exact H. Qed.

  Lemma readers_ranked_with_phases :
    forall st phases,
      readers_ranked st -> readers_ranked (R.with_phases st phases).
  Proof. intros. exact H. Qed.

  Lemma readers_ranked_start_evaluation :
    forall st owner,
      readers_ranked st -> readers_ranked (R.start_evaluation st owner).
  Proof.
    intros st owner Hranked. unfold R.start_evaluation, R.reset_local_sides.
    now apply readers_ranked_materialize.
  Qed.

  Lemma readers_ranked_write_changed :
    forall st owner value,
      readers_ranked st -> readers_ranked (R.write_changed_value st owner value).
  Proof.
    intros st owner value Hranked dependency reader
      Hregistered Hnoncontrolled.
    apply ranked_before_extended with (before := st).
    - apply rank_extends_write_changed.
    - apply Hranked.
      + unfold reader_registered, R.write_changed_value,
          R.lookup_set in Hregistered. cbn in Hregistered.
        rewrite readers_enqueue_all in Hregistered.
        destruct (V.eq_dec dependency owner) as [-> | Hneq].
        * rewrite ML.lookup_update_same, SL.empty_spec in Hregistered.
          discriminate.
        * now rewrite ML.lookup_update_other in Hregistered by exact Hneq.
      + unfold R.write_changed_value in Hnoncontrolled. cbn in Hnoncontrolled.
        rewrite Measure.controlled_enqueue_all in Hnoncontrolled.
        exact Hnoncontrolled.
  Qed.

  Lemma readers_ranked_set_value :
    forall st owner direct,
      readers_ranked st -> readers_ranked (R.set_value st owner direct).
  Proof.
    intros st owner direct Hranked. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hranked |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner))) as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner)).
      + now apply readers_ranked_with_phases.
      + apply readers_ranked_write_changed.
        now apply readers_ranked_with_phases.
    - now apply readers_ranked_write_changed.
  Qed.

  Lemma readers_ranked_observed_get_ready :
    forall st target next target_handle owner,
      handle_valid st owner ->
      readers_ranked st ->
      R.observe st target = (next, target_handle) ->
      readers_ranked (R.get_ready_state next owner target_handle).
  Proof.
    intros st target next target_handle owner Howner Hranked Hobserve.
    apply readers_ranked_get_ready.
    - eapply handle_valid_extended.
      + exact (@rank_extends_observe
          st target next target_handle Hobserve).
      + exact Howner.
    - exact (@observed_handle_valid
        st target next target_handle Hobserve).
    - eapply readers_ranked_observe; eauto.
  Qed.

  Lemma readers_ranked_observed_enqueued_get_ready :
    forall st target next target_handle owner,
      handle_valid st owner ->
      readers_ranked st ->
      R.observe st target = (next, target_handle) ->
      readers_ranked
        (R.get_ready_state (R.enqueue_handle next target_handle)
          owner target_handle).
  Proof.
    intros st target next target_handle owner Howner Hranked Hobserve.
    apply readers_ranked_get_ready.
    - eapply handle_valid_extended.
      + apply rank_extends_enqueue_handle.
      + eapply handle_valid_extended.
        * exact (@rank_extends_observe
            st target next target_handle Hobserve).
        * exact Howner.
    - eapply handle_valid_extended.
      + apply rank_extends_enqueue_handle.
      + exact (@observed_handle_valid
          st target next target_handle Hobserve).
    - apply readers_ranked_enqueue_handle.
      eapply readers_ranked_observe; eauto.
  Qed.

  Lemma initial_readers_ranked :
    forall roots,
      readers_ranked (R.cfg_state (R.initial_config roots)).
  Proof.
    intros roots dependency reader Hregistered Hnoncontrolled.
    unfold reader_registered, R.initial_config, R.lookup_set,
      R.empty_state in Hregistered. cbn in Hregistered.
    rewrite ML.lookup_empty, SL.empty_spec in Hregistered. discriminate.
  Qed.

  Lemma readers_ranked_step :
    forall tf before after,
      handles_valid before ->
      readers_ranked (R.cfg_state before) ->
      Sem.step tf before after ->
      readers_ranked (R.cfg_state after).
  Proof.
    intros tf [st control] after Hhandles Hranked Hstep.
    destruct Hhandles as [Hrank_valid Hqueue_valid Hcontrol_valid].
    unfold Sem.step in Hstep. cbn in Hstep, Hcontrol_valid.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst;
      cbn in Hcontrol_valid |- *.
    all: try exact Hranked.
    all: try now apply readers_ranked_with_queue.
    all: try (apply readers_ranked_with_started;
      now apply readers_ranked_start_evaluation).
    all: try now apply readers_ranked_set_value.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry),
        Hvalid : handle_valid ?before ?owner /\ _ |-
          readers_ranked (R.get_ready_state ?next ?owner ?entry) =>
          exact (@readers_ranked_observed_get_ready
            before target next entry owner (proj1 Hvalid) Hranked Hobserve)
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry),
        Hvalid : handle_valid ?before ?owner /\ _ |-
          readers_ranked
            (R.get_ready_state (R.enqueue_handle ?next ?entry) ?owner ?entry) =>
          exact (@readers_ranked_observed_enqueued_get_ready
            before target next entry owner (proj1 Hvalid) Hranked Hobserve)
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          exact (readers_ranked_side_ready _ _ _
            (@readers_ranked_observe
              before target next entry Hranked Hobserve))
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          apply readers_ranked_enqueue_handle;
          exact (readers_ranked_side_ready _ _ _
            (@readers_ranked_observe
              before target next entry Hranked Hobserve))
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          apply readers_ranked_materialize;
          apply readers_ranked_enqueue_handle;
          exact (@readers_ranked_observe
            before target next entry Hranked Hobserve)
      end.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          exact (@readers_ranked_observe
            before target next entry Hranked Hobserve)
      end.
    eapply readers_ranked_get_ready; eauto.
    - exact (proj1 Hcontrol_valid).
    - exact (proj1 (proj2 Hcontrol_valid)).
  Qed.

  Lemma readers_ranked_steps :
    forall tf before after,
      handles_valid before ->
      readers_ranked (R.cfg_state before) ->
      Sem.steps tf before after ->
      readers_ranked (R.cfg_state after).
  Proof.
    intros tf before after Hhandles Hranked Hsteps.
    induction Hsteps; [exact Hranked |].
    apply IHHsteps.
    - eapply next_config_handles_valid; eauto.
    - eapply readers_ranked_step; eauto.
  Qed.

  Theorem reachable_readers_ranked :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      readers_ranked (R.cfg_state after).
  Proof.
    intros tf roots after Hsteps.
    eapply readers_ranked_steps.
    - apply initial_handles_valid.
    - apply initial_readers_ranked.
    - exact Hsteps.
  Qed.

  Definition queued_variable (st : R.state) (variable : V.t) : Prop :=
    exists entry,
      List.In entry (R.queue st) /\
      R.handle_variable entry = variable.

  Lemma queued_variable_dec :
    forall st variable,
      {queued_variable st variable} + {~ queued_variable st variable}.
  Proof.
    intros st variable. unfold queued_variable.
    induction (R.queue st) as [|entry rest IH].
    - right. intros [observed [[] _]].
    - destruct (V.eq_dec (R.handle_variable entry) variable)
        as [Heq | Hneq].
      + left. exists entry. split; [now left |exact Heq].
      + destruct IH as [Hin | Hnotin].
        * left. destruct Hin as [observed [Hin Hvariable]].
          exists observed. split; [now right |exact Hvariable].
        * right. intros [observed [[-> | Hin] Hvariable]].
          -- contradiction.
          -- apply Hnotin. exists observed. now split.
  Qed.

  Lemma queue_observe :
    forall st target next entry,
      R.observe st target = (next, entry) -> R.queue next = R.queue st.
  Proof.
    intros st target next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma queued_variable_enqueue_origin :
    forall st inserted queued,
      queued_variable (R.enqueue st inserted) queued ->
      queued = inserted \/ queued_variable st queued.
  Proof.
    intros st inserted queued Hqueued. unfold queued_variable in *.
    unfold R.enqueue, R.enqueue_handle in Hqueued.
    destruct (R.observe st inserted) as [next entry] eqn:Hobserve.
    cbn in Hqueued. destruct Hqueued as [observed [Hin Hvariable]].
    apply queue_insert_members in Hin.
    destruct Hin as [-> | Hin].
    - left. rewrite <- Hvariable.
      exact (@observed_handle_variable
        st inserted next entry Hobserve).
    - right. exists observed. split; [|exact Hvariable].
      now rewrite (@queue_observe st inserted next entry Hobserve) in Hin.
  Qed.

  Lemma queued_variable_enqueue_all_origin :
    forall xs st queued,
      queued_variable (R.enqueue_all st xs) queued ->
      List.In queued xs \/ queued_variable st queued.
  Proof.
    induction xs as [|inserted rest IH]; intros st queued Hqueued.
    - now right.
    - cbn in Hqueued. apply IH in Hqueued.
      destruct Hqueued as [Hin | Hqueued].
      + left. now right.
      + apply queued_variable_enqueue_origin in Hqueued.
        destruct Hqueued as [-> | Hqueued].
        * left. now left.
        * now right.
  Qed.

  Lemma queued_variable_write_changed_origin :
    forall st owner value queued,
      queued_variable (R.write_changed_value st owner value) queued ->
      queued_variable st queued \/ reader_registered st queued owner.
  Proof.
    intros st owner value queued Hqueued.
    unfold R.write_changed_value in Hqueued. cbn in Hqueued.
    apply queued_variable_enqueue_all_origin in Hqueued.
    destruct Hqueued as [Hinvalidated | Hqueued].
    - right. unfold reader_registered. now apply SL.mem_spec.
    - now left.
  Qed.

  Lemma queued_variable_set_value_origin :
    forall st owner direct queued,
      queued_variable (R.set_value st owner direct) queued ->
      queued_variable st queued \/
      (reader_registered st queued owner /\
       ~ UL.equivalent
          (R.sigma_value (R.set_value st owner direct) owner)
          (R.sigma_value st owner)).
  Proof.
    intros st owner direct queued Hqueued.
    unfold R.set_value in Hqueued |- *.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner))
      eqn:Hcandidate; [now left |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner)
        (D.join direct (R.aggregate st owner)))
        as [phase value] eqn:Hupdate. cbn in *.
      destruct (R.equivalent value (R.sigma_value st owner))
        eqn:Hvalue; [now left |].
      destruct (@queued_variable_write_changed_origin
        (R.with_phases st (M.update (R.phases st) owner phase))
        owner value queued Hqueued) as [Hold | Hreader].
      + now left.
      + right. split; [exact Hreader |]. intros Hequivalent.
        apply (Accounting.equivalent_false Hvalue).
        rewrite Accounting.sigma_value_write_changed_same in Hequivalent.
        exact Hequivalent.
    - destruct (@queued_variable_write_changed_origin st owner
        (D.join direct (R.aggregate st owner)) queued Hqueued)
        as [Hold | Hreader].
      + now left.
      + right. split; [exact Hreader |]. intros Hequivalent.
        apply (Accounting.equivalent_false Hcandidate).
        rewrite Accounting.sigma_value_write_changed_same in Hequivalent.
        exact Hequivalent.
  Qed.

  Lemma unpaid_controlled_ret_queue_subset :
    forall support tf st owner direct k,
      List.In (R.handle_variable owner) support ->
      S.mem (R.handle_variable owner) (R.controlled st) = true ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        {| R.cfg_state :=
             R.set_value st (R.handle_variable owner) direct;
           R.cfg_control := R.RunSolveOneLoop owner k |} ->
      forall queued,
        queued_variable
          (R.set_value st (R.handle_variable owner) direct) queued ->
        queued_variable st queued.
  Proof.
    intros support tf st owner direct k Howner Hcontrolled Hunpaid
      queued Hqueued.
    destruct (@queued_variable_set_value_origin st
      (R.handle_variable owner) direct queued Hqueued)
      as [Hold | [Hreader Hchanges]]; [exact Hold |].
    exfalso. apply Hchanges.
    rewrite (@Payment.unpaid_controlled_ret_sigma_same
      support tf st owner direct k Howner Hcontrolled Hunpaid).
    apply Accounting.equivalent_refl.
  Qed.

  Lemma unpaid_ret_new_queue_ranked_source :
    forall tf roots (finite : Sem.finite_system tf roots)
      st owner direct k queued,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |} ->
      Payment.unpaid_step (Sem.support finite) tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        {| R.cfg_state :=
             R.set_value st (R.handle_variable owner) direct;
           R.cfg_control := R.RunSolveOneLoop owner k |} ->
      queued_variable
        (R.set_value st (R.handle_variable owner) direct) queued ->
      ~ queued_variable st queued ->
      ranked_before st queued (R.handle_variable owner).
  Proof.
    intros tf roots finite st owner direct k queued Hreachable Hunpaid
      Hqueued Hnotqueued.
    destruct (@queued_variable_set_value_origin st
      (R.handle_variable owner) direct queued Hqueued)
      as [Hold | [Hreader Hchanges]]; [contradiction |].
    destruct (S.mem (R.handle_variable owner) (R.controlled st))
      eqn:Hcontrolled.
    - exfalso. apply Hchanges.
      rewrite (@Payment.unpaid_controlled_ret_sigma_same
        (Sem.support finite) tf st owner direct k
        (proj1 (proj2
          (reachable_config_supported finite Hreachable)))
        Hcontrolled Hunpaid).
      apply Accounting.equivalent_refl.
    - pose proof (@reachable_readers_ranked tf roots
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        Hreachable) as Hranked.
      exact (Hranked (R.handle_variable owner) queued
        Hreader Hcontrolled).
  Qed.

  Lemma queued_variable_with_queue :
    forall st queue variable,
      queued_variable (R.with_queue st queue) variable <->
      exists entry,
        List.In entry queue /\ R.handle_variable entry = variable.
  Proof. reflexivity. Qed.

  Lemma queued_variable_materialize_inv :
    forall st target variable,
      queued_variable (R.materialize st target) variable ->
      queued_variable st variable.
  Proof.
    intros st target variable Hqueued. unfold R.materialize in Hqueued.
    destruct (R.is_materialized st target); exact Hqueued.
  Qed.

  Lemma queued_variable_start_evaluation_inv :
    forall st owner variable,
      queued_variable (R.start_evaluation st owner) variable ->
      queued_variable st variable.
  Proof.
    intros st owner variable Hqueued.
    unfold R.start_evaluation, R.reset_local_sides in Hqueued.
    now apply queued_variable_materialize_inv in Hqueued.
  Qed.

  Lemma queued_variable_get_ready_inv :
    forall st owner target variable,
      queued_variable (R.get_ready_state st owner target) variable ->
      queued_variable st variable.
  Proof.
    intros st owner target variable Hqueued.
    unfold R.get_ready_state, R.add_reader, R.promote_controlled in Hqueued.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      now apply queued_variable_materialize_inv in Hqueued.
  Qed.

  Lemma queued_variable_side_ready_inv :
    forall st source target raw variable,
      queued_variable (R.side_ready_state st source target raw) variable ->
      queued_variable st variable.
  Proof.
    intros st source target raw variable Hqueued.
    unfold queued_variable, R.side_ready_state, R.record_side_payload,
      R.promote_controlled in Hqueued |- *.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hqueued.
  Qed.

  Lemma queued_variable_enqueue_handle_origin :
    forall st inserted queued,
      queued_variable (R.enqueue_handle st inserted) queued ->
      queued = R.handle_variable inserted \/ queued_variable st queued.
  Proof.
    intros st inserted queued [observed [Hin Hvariable]].
    unfold R.enqueue_handle in Hin. cbn in Hin.
    apply queue_insert_members in Hin.
    destruct Hin as [-> | Hin].
    - now left.
    - right. exists observed. now split.
  Qed.

  Lemma queued_variable_observe_inv :
    forall st target next entry queued,
      R.observe st target = (next, entry) ->
      queued_variable next queued ->
      queued_variable st queued.
  Proof.
    intros st target next entry queued Hobserve
      [observed [Hqueued Hvariable]].
    exists observed. split; [|exact Hvariable].
    now rewrite (@queue_observe st target next entry Hobserve) in Hqueued.
  Qed.

  Lemma queued_variable_pop_inv :
    forall st head tail queued,
      R.queue_pop (R.queue st) = Some (head, tail) ->
      queued_variable (R.with_queue st tail) queued ->
      queued_variable st queued.
  Proof.
    intros st head tail queued Hpop [entry [Hentry Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.queue_pop in Hpop.
    destruct (R.queue st); cbn in Hpop; try discriminate.
    inversion Hpop; subst. now right.
  Qed.

  Lemma unpaid_side_cannot_grow :
    forall support tf st source target raw before_control after_control,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      List.In (R.handle_variable target) support ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := before_control |}
        {| R.cfg_state := R.side_ready_state st source target raw;
           R.cfg_control := after_control |} ->
      ~ Accounting.side_grows st source target raw.
  Proof.
    intros support tf st source target raw before_control after_control
      Hnodup Hsource Htarget
      [_ [_ [Hcontrolled Hcredit]]] Hgrows.
    pose proof (@Payment.side_ready_stable_from_count
      support st source target raw Hnodup Hsource Hcontrolled) as Hstable.
    pose proof (@Accounting.charged_update_credit_side_ready_decreases
      support st source target raw Hsource Htarget Hstable Hgrows) as Hstrict.
    cbn in Hcredit. lia.
  Qed.

  Lemma unpaid_side_enqueue_cannot_grow :
    forall support tf st source target raw before_control after_control,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      List.In (R.handle_variable target) support ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := before_control |}
        {| R.cfg_state :=
             R.enqueue_handle (R.side_ready_state st source target raw) target;
           R.cfg_control := after_control |} ->
      ~ Accounting.side_grows st source target raw.
  Proof.
    intros support tf st source target raw before_control after_control
      Hnodup Hsource Htarget
      [_ [_ [Hcontrolled Hcredit]]] Hgrows.
    cbn in Hcontrolled, Hcredit.
    rewrite Payment.uncontrolled_count_enqueue_handle in Hcontrolled.
    pose proof (@Payment.side_ready_stable_from_count
      support st source target raw Hnodup Hsource Hcontrolled) as Hstable.
    pose proof (@Accounting.charged_update_credit_side_ready_decreases
      support st source target raw Hsource Htarget Hstable Hgrows) as Hstrict.
    rewrite Payment.charged_update_credit_enqueue_handle in Hcredit.
    cbn in Hcredit. lia.
  Qed.

  Lemma unpaid_observed_side_enqueue_cannot_grow :
    forall support tf st observed source target target_variable raw
      before_control after_control,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      List.In target_variable support ->
      R.observe st target_variable = (observed, target) ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := before_control |}
        {| R.cfg_state :=
             R.enqueue_handle
               (R.side_ready_state observed source target raw) target;
           R.cfg_control := after_control |} ->
      ~ Accounting.side_grows observed source target raw.
  Proof.
    intros support tf st observed source target target_variable raw
      before_control after_control Hnodup Hsource Htarget Hobserve
      [_ [_ [Hcontrolled Hcredit]]] Hgrows.
    assert (Htarget_handle :
      List.In (R.handle_variable target) support).
    {
      rewrite (@observed_handle_variable
        st target_variable observed target Hobserve).
      exact Htarget.
    }
    cbn in Hcontrolled, Hcredit.
    rewrite Payment.uncontrolled_count_enqueue_handle in Hcontrolled.
    rewrite <- (@Payment.uncontrolled_count_observe
      support st target_variable observed target Hobserve) in Hcontrolled.
    pose proof (@Payment.side_ready_stable_from_count
      support observed source target raw Hnodup Hsource Hcontrolled) as Hstable.
    pose proof (@Accounting.charged_update_credit_side_ready_decreases
      support observed source target raw Hsource Htarget_handle Hstable Hgrows)
      as Hstrict.
    rewrite Payment.charged_update_credit_enqueue_handle in Hcredit.
    rewrite <- (@Payment.charged_update_credit_observe
      support st target_variable observed target Hobserve) in Hcredit.
    cbn in Hcredit. lia.
  Qed.

  Definition queue_at_most (owner : R.handle) (st : R.state) : Prop :=
    forall queued,
      List.In queued (R.queue st) ->
      R.handle_variable queued = R.handle_variable owner \/
      Nat.ltb (R.handle_rank queued) (R.handle_rank owner) = true.

  Lemma queue_strictly_below_at_most :
    forall owner st,
      queue_strictly_below owner st ->
      queue_at_most owner st.
  Proof.
    intros owner st Hbelow queued Hqueued. right.
    apply Nat.ltb_lt. now apply Hbelow.
  Qed.

  Lemma ranked_before_handles :
    forall before after lower owner,
      ranked_before before (R.handle_variable lower)
        (R.handle_variable owner) ->
      handle_valid before owner ->
      rank_extends before after ->
      handle_valid after lower ->
      Nat.ltb (R.handle_rank lower) (R.handle_rank owner) = true.
  Proof.
    intros before after lower owner
      [lower_rank [owner_rank [Hlower [Howner Hlt]]]]
      Howner_handle Hextends Hlower_handle.
    pose proof (Hextends _ _ Hlower) as Hlower_after.
    unfold handle_valid in Howner_handle, Hlower_handle.
    rewrite Hlower_handle in Hlower_after. inversion Hlower_after; subst.
    rewrite Howner_handle in Howner. inversion Howner; subst. exact Hlt.
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

  Lemma queue_entry_valid :
    forall st entry,
      queue_valid st ->
      List.In entry (R.queue st) ->
      handle_valid st entry.
  Proof.
    intros st entry Hvalid Hin. unfold queue_valid in Hvalid.
    now apply Forall_forall with (x := entry) in Hvalid.
  Qed.

  Lemma queue_at_most_pop :
    forall owner st head tail,
      queue_at_most owner st ->
      R.queue_pop (R.queue st) = Some (head, tail) ->
      queue_at_most owner (R.with_queue st tail).
  Proof.
    intros owner st head tail Hqueue Hpop queued Hqueued.
    apply Hqueue. unfold R.queue_pop in Hpop.
    destruct (R.queue st) as [|first rest]; try discriminate.
    inversion Hpop; subst. now right.
  Qed.

  Lemma queue_at_most_enqueue_handle :
    forall owner st inserted,
      (R.handle_variable inserted = R.handle_variable owner \/
       Nat.ltb (R.handle_rank inserted) (R.handle_rank owner) = true) ->
      queue_at_most owner st ->
      queue_at_most owner (R.enqueue_handle st inserted).
  Proof.
    intros owner st inserted Hinserted Hqueue queued Hqueued.
    unfold R.enqueue_handle in Hqueued. cbn in Hqueued.
    apply queue_insert_members in Hqueued.
    destruct Hqueued as [-> | Hqueued]; [exact Hinserted |].
    now apply Hqueue.
  Qed.

  Lemma queue_at_most_start_evaluation :
    forall owner st active,
      queue_at_most owner st ->
      queue_at_most owner (R.start_evaluation st active).
  Proof.
    intros owner st active Hqueue queued Hqueued.
    apply Hqueue. unfold R.start_evaluation, R.reset_local_sides,
      R.materialize in Hqueued.
    destruct (R.is_materialized st active); exact Hqueued.
  Qed.

  Lemma queue_at_most_get_ready :
    forall owner st active target,
      queue_at_most owner st ->
      queue_at_most owner (R.get_ready_state st active target).
  Proof.
    intros owner st active target Hqueue queued Hqueued.
    apply Hqueue. unfold R.get_ready_state, R.add_reader,
      R.promote_controlled, R.materialize in Hqueued.
    destruct (Nat.ltb (R.handle_rank active) (R.handle_rank target));
      destruct (R.is_materialized _ _); exact Hqueued.
  Qed.

  Lemma queue_at_most_side_ready :
    forall owner st active target raw,
      queue_at_most owner st ->
      queue_at_most owner (R.side_ready_state st active target raw).
  Proof.
    intros owner st active target raw Hqueue queued Hqueued.
    apply Hqueue. unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled in Hqueued.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable active)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable active)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable active)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank active));
      exact Hqueued.
  Qed.

  Lemma queue_at_most_materialize :
    forall owner st target,
      queue_at_most owner st ->
      queue_at_most owner (R.materialize st target).
  Proof.
    intros owner st target Hqueue queued Hqueued.
    apply Hqueue. unfold R.materialize in Hqueued.
    destruct (R.is_materialized st target); exact Hqueued.
  Qed.

  Lemma queue_at_most_observe :
    forall owner st target next entry,
      queue_at_most owner st ->
      R.observe st target = (next, entry) ->
      queue_at_most owner next.
  Proof.
    intros owner st target next entry Hqueue Hobserve queued Hqueued.
    apply Hqueue. now rewrite <- (@queue_observe st target next entry Hobserve).
  Qed.

  Lemma observed_not_higher_is_at_most :
    forall st owner target next entry,
      rank_valid st ->
      handle_valid st owner ->
      R.observe st target = (next, entry) ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank entry) = false ->
      R.handle_variable entry = R.handle_variable owner \/
      Nat.ltb (R.handle_rank entry) (R.handle_rank owner) = true.
  Proof.
    intros st owner target next entry Hrank Howner Hobserve Hnot_higher.
    destruct (V.eq_dec (R.handle_variable entry)
      (R.handle_variable owner)) as [Heq | Hneq]; [now left |].
    right. apply Nat.ltb_lt. apply Nat.ltb_ge in Hnot_higher.
    assert (Hranks_neq : R.handle_rank entry <> R.handle_rank owner).
    {
      intro Hranks. apply Hneq.
      eapply handle_rank_equal_variable_equal.
      - eapply rank_valid_observe; eauto.
      - eapply observed_handle_valid; eauto.
      - eapply handle_valid_extended; eauto using rank_extends_observe.
      - exact Hranks.
    }
    lia.
  Qed.

  Lemma unpaid_ret_preserves_queue_at_most :
    forall tf roots (finite : Sem.finite_system tf roots)
      st owner direct k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |} ->
      queue_at_most owner st ->
      Payment.unpaid_step (Sem.support finite) tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        {| R.cfg_state :=
             R.set_value st (R.handle_variable owner) direct;
           R.cfg_control := R.RunSolveOneLoop owner k |} ->
      queue_at_most owner
        (R.set_value st (R.handle_variable owner) direct).
  Proof.
    intros tf roots finite st owner direct k Hreachable Hqueue Hunpaid
      queued Hqueued.
    set (before :=
      {| R.cfg_state := st;
         R.cfg_control :=
           R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}).
    set (after :=
      {| R.cfg_state := R.set_value st (R.handle_variable owner) direct;
         R.cfg_control := R.RunSolveOneLoop owner k |}).
    pose proof (reachable_handles_valid Hreachable) as Hbefore_valid.
    assert (Hafter_valid : handles_valid after).
    {
      eapply next_config_handles_valid.
      - exact Hbefore_valid.
      - exact (proj1 Hunpaid).
    }
    destruct (@queued_variable_dec st (R.handle_variable queued))
      as [[old [Hold Hvariable]] | Hnew].
    - pose proof (Hqueue old Hold) as Hold_bound.
      assert (Hold_valid_before : handle_valid st old).
      {
        eapply queue_entry_valid; [|exact Hold].
        exact (handles_queue_valid Hbefore_valid).
      }
      assert (Hold_valid_after :
        handle_valid (R.cfg_state after) old).
      {
        eapply handle_valid_extended.
        - apply rank_extends_set_value.
        - exact Hold_valid_before.
      }
      assert (Hqueued_valid :
        handle_valid (R.cfg_state after) queued).
      {
        eapply queue_entry_valid; [|exact Hqueued].
        exact (handles_queue_valid Hafter_valid).
      }
      assert (Hranks : R.handle_rank queued = R.handle_rank old).
      {
        eapply same_variable_valid_rank; eauto.
      }
      destruct Hold_bound as [Hsame | Hbelow].
      + left. congruence.
      + right. now rewrite Hranks.
    - right. eapply ranked_before_handles.
      + eapply unpaid_ret_new_queue_ranked_source; eauto.
        exists queued. now split.
      + exact (proj1 (handles_control_valid Hbefore_valid)).
      + apply rank_extends_set_value.
      + eapply queue_entry_valid; [|exact Hqueued].
        exact (handles_queue_valid Hafter_valid).
  Qed.

  Lemma unpaid_ret_preserves_unqueued :
    forall tf roots (finite : Sem.finite_system tf roots)
      st owner direct k,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |} ->
      Payment.unpaid_step (Sem.support finite) tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Ret direct) k |}
        {| R.cfg_state := R.set_value st (R.handle_variable owner) direct;
           R.cfg_control := R.RunSolveOneLoop owner k |} ->
      ~ queued_variable st (R.handle_variable owner) ->
      ~ queued_variable (R.set_value st (R.handle_variable owner) direct)
          (R.handle_variable owner).
  Proof.
    intros tf roots finite st owner direct k Hreachable Hunpaid
      Hunqueued Hqueued.
    destruct (@queued_variable_set_value_origin st
      (R.handle_variable owner) direct (R.handle_variable owner) Hqueued)
      as [Hold | [_ Hchanged]]; [now apply Hunqueued |].
    pose proof (@unpaid_ret_new_queue_ranked_source tf roots finite st owner
      direct k (R.handle_variable owner) Hreachable Hunpaid Hqueued Hunqueued)
      as Hranked.
    exact (@ranked_before_irrefl st (R.handle_variable owner) Hranked).
  Qed.

  Definition control_at_owner_root
    (owner : R.handle) (base : R.continuation)
    (control : R.control) : Prop :=
    match control with
    | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
    | R.RunSolveOne active rest
    | R.RunSolveOneLoop active rest
    | R.RunRhs active _ rest
    | R.AfterGet active _ _ rest
    | R.AfterSide active _ rest
    | R.AfterSpawn active _ rest => active = owner /\ rest = base
    end.

  Inductive root_step_shape
    (owner : R.handle) (base : R.continuation) : R.config -> Prop :=
  | RootStepStays :
      forall after,
        control_at_owner_root owner base (R.cfg_control after) ->
        root_step_shape owner base after
  | RootStepFreshChild :
      forall after target rest,
        R.cfg_control after = R.RunSolveOne target rest ->
        R.is_materialized (R.cfg_state after)
          (R.handle_variable target) = false ->
        root_step_shape owner base after
  | RootStepExits :
      forall after,
        R.cfg_control after = R.continue base ->
        root_step_shape owner base after.

  Lemma is_materialized_side_ready :
    forall st source target raw observed,
      R.is_materialized (R.side_ready_state st source target raw) observed =
      R.is_materialized st observed.
  Proof.
    intros. unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled, R.is_materialized.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      reflexivity.
  Qed.

  Lemma queue_at_most_excludes_higher_pop :
    forall owner st next tail,
      queue_at_most owner st ->
      R.owner_may_still_be_queued st owner = true ->
      R.queue_pop (R.queue st) = Some (next, tail) ->
      R.handle_variable next <> R.handle_variable owner ->
      False.
  Proof.
    intros owner st next tail Hqueue Hmay Hpop Hneq.
    unfold R.owner_may_still_be_queued in Hmay.
    unfold R.queue_pop in Hpop.
    destruct (R.queue st) as [|head rest] eqn:Hentries;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst head rest.
    assert (Hnext : List.In next (R.queue st)) by (rewrite Hentries; now left).
    destruct (Hqueue next Hnext) as [Heq | Hbelow]; [contradiction |].
    cbn in Hmay.
    destruct (V.eq_dec (R.handle_variable next)
      (R.handle_variable owner)); [contradiction |].
    apply Nat.ltb_lt in Hbelow, Hmay. lia.
  Qed.

  Lemma root_step_has_shape :
    forall tf owner base before after,
      control_at_owner_root owner base (R.cfg_control before) ->
      queue_at_most owner (R.cfg_state before) ->
      ~ queued_variable (R.cfg_state before) (R.handle_variable owner) ->
      Sem.step tf before after ->
      root_step_shape owner base after.
  Proof.
    intros tf owner base [st control] after Hroot Hqueue Hunqueued Hstep.
    unfold Sem.step in Hstep. cbn in Hstep, Hroot.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in Hroot |- *.
    all: try contradiction.
    all: try (destruct Hroot as [-> ->]).
    all: try (apply RootStepStays; cbn; split; reflexivity).
    all: try (apply RootStepExits; reflexivity).
    - exfalso. eapply queue_at_most_excludes_higher_pop; eauto.
    - eapply RootStepFreshChild with
        (target := h0) (rest := R.KAfterGet owner h0 r0 base).
      + reflexivity.
      + rewrite (@observed_handle_variable st t s h0 Hcase0).
        exact Hcase1.
    - eapply RootStepFreshChild with
        (target := h0) (rest := R.KAfterSide owner r0 base).
      + reflexivity.
      + apply Bool.andb_true_iff in Hcase2 as [_ Hunmaterialized].
        apply Bool.negb_true_iff in Hunmaterialized. cbn.
        rewrite is_materialized_side_ready.
        rewrite (@observed_handle_variable st t s h0 Hcase0).
        exact Hunmaterialized.
    - eapply RootStepFreshChild with
        (target := h0) (rest := R.KAfterSpawn owner r0 base).
      + reflexivity.
      + cbn. rewrite (@observed_handle_variable st t s h0 Hcase0).
        exact Hcase1.
  Qed.

  Lemma reachable_observed_unmaterialized_not_owner :
    forall tf roots st owner body k target observed target_handle,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs owner body k |} ->
      R.observe st target = (observed, target_handle) ->
      R.is_materialized observed target = false ->
      R.handle_variable target_handle <> R.handle_variable owner.
  Proof.
    intros tf roots st owner body k target observed target_handle
      Hreachable Hobserve Hunmaterialized Hequal.
    assert (Htarget : target = R.handle_variable owner).
    {
      rewrite <- (@observed_handle_variable
        st target observed target_handle Hobserve).
      exact Hequal.
    }
    pose proof (Progress.reachable_control_solved Hreachable) as Hsolved.
    cbn in Hsolved. destruct Hsolved as [Howner _].
    pose proof (@Progress.solved_observe st target observed target_handle
      (R.handle_variable owner) Hobserve Howner) as Hobserved.
    apply Progress.solved_is_materialized in Hobserved.
    rewrite Htarget in Hunmaterialized. congruence.
  Qed.

  Lemma unpaid_root_step_preserves_queue_at_most :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base before after,
      Sem.steps tf (R.initial_config roots) before ->
      control_at_owner_root owner base (R.cfg_control before) ->
      queue_at_most owner (R.cfg_state before) ->
      Payment.unpaid_step (Sem.support finite) tf before after ->
      queue_at_most owner (R.cfg_state after).
  Proof.
    intros tf roots finite owner base [st control] after
      Hreachable Hroot Hqueue Hunpaid.
    pose proof (reachable_handles_valid Hreachable) as Hhandles.
    pose proof
      (reachable_config_supported finite Hreachable)
      as Hsupported.
    pose proof (proj1 Hunpaid) as Hstep.
    unfold Sem.step in Hstep. cbn in Hstep, Hroot.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst;
      cbn in Hroot |- *.
    all: try contradiction.
    all: try (destruct Hroot as [-> ->]).
    all: try exact Hqueue.
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?s) = Some (?head, ?tail) |-
          queue_at_most ?bound (R.with_queue ?s ?tail) =>
          exact (@queue_at_most_pop bound s head tail Hqueue Hpop)
      end.
    all: try (apply queue_at_most_start_evaluation; exact Hqueue).
    all: try (apply queue_at_most_get_ready; exact Hqueue).
    all: try match goal with
      | Hobserve : R.observe ?s ?target = (?next, ?entry) |-
          queue_at_most ?bound
            (R.get_ready_state ?next ?active ?entry) =>
          apply queue_at_most_get_ready;
          exact (@queue_at_most_observe bound s target next entry
            Hqueue Hobserve)
      end.
    all: try match goal with
      | Hobserve : R.observe ?s ?target = (?next, ?entry) |-
          queue_at_most ?bound ?next =>
          exact (@queue_at_most_observe bound s target next entry
            Hqueue Hobserve)
      end.
    all: try match goal with
      | Hobserve : R.observe ?s ?target = (?next, ?entry) |-
          queue_at_most ?bound
            (R.side_ready_state ?next ?active ?entry ?raw) =>
          apply queue_at_most_side_ready;
          exact (@queue_at_most_observe bound s target next entry
            Hqueue Hobserve)
      end.
    all: try (eapply unpaid_ret_preserves_queue_at_most; eauto).
    all: try match goal with
      | Hobserve : R.observe ?s ?target = (?next, ?entry) |-
          queue_at_most ?bound
            (R.get_ready_state (R.enqueue_handle ?next ?entry) ?bound ?entry) =>
          apply queue_at_most_get_ready;
          apply queue_at_most_enqueue_handle;
          [eapply observed_not_higher_is_at_most;
            [exact (handles_rank_valid Hhandles)
            |exact (proj1 (handles_control_valid Hhandles))
            |exact Hobserve |exact Hcase2]
          |exact (@queue_at_most_observe bound s target next entry
            Hqueue Hobserve)]
      end.
    all: try match goal with
      | Hobserve : R.observe ?s ?target = (?next, ?entry) |-
          queue_at_most ?bound
            (R.materialize (R.enqueue_handle ?next ?entry) ?target) =>
          apply queue_at_most_materialize;
          apply queue_at_most_enqueue_handle;
          [eapply observed_not_higher_is_at_most;
            [exact (handles_rank_valid Hhandles)
            |exact (proj1 (handles_control_valid Hhandles))
            |exact Hobserve |exact Hcase2]
          |exact (@queue_at_most_observe bound s target next entry
            Hqueue Hobserve)]
      end.
    exfalso.
    destruct Hsupported as [_ Hcontrol]. cbn in Hcontrol.
    destruct Hcontrol as [Howner [Hrhs _]].
    destruct (Payment.rhs_supported_side_inv Hrhs) as [Htarget _].
    eapply (@unpaid_observed_side_enqueue_cannot_grow
      (Sem.support finite) tf st s owner h0 t t0).
    - exact (Sem.support_nodup finite).
    - exact Howner.
    - exact Htarget.
    - exact Hcase0.
    - exact Hunpaid.
    - unfold Accounting.side_grows.
      rewrite (@observed_handle_variable st t s h0 Hcase0).
      destruct (D.leq (R.aggregate (R.side_ready_state s owner h0 t0) t)
        (R.aggregate s t)); cbn in Hcase1 |- *; congruence.
  Qed.

  Lemma unpaid_root_step_preserves_unqueued :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base before after,
      Sem.steps tf (R.initial_config roots) before ->
      control_at_owner_root owner base (R.cfg_control before) ->
      queue_at_most owner (R.cfg_state before) ->
      Payment.unpaid_step (Sem.support finite) tf before after ->
      ~ queued_variable (R.cfg_state before) (R.handle_variable owner) ->
      ~ queued_variable (R.cfg_state after) (R.handle_variable owner).
  Proof.
    intros tf roots finite owner base [st control] after Hreachable Hroot
      Hqueue Hunpaid Hunqueued Hqueued.
    pose proof
      (reachable_config_supported finite Hreachable)
      as Hsupported.
    pose proof (proj1 Hunpaid) as Hstep.
    unfold Sem.step in Hstep. cbn in Hstep, Hroot.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in Hroot, Hqueued |- *.
    all: try contradiction.
    all: try (destruct Hroot as [-> ->]).
    all: try (apply Hunqueued; exact Hqueued).
    all: try match goal with
      | Hpop : R.queue_pop (R.queue ?before) = Some (?head, ?tail),
        Hq : queued_variable (R.with_queue ?before ?tail) ?variable |- False =>
          apply Hunqueued;
          exact (@queued_variable_pop_inv before head tail variable Hpop Hq)
      end.
    all: try match goal with
      | Hq : queued_variable
          (R.with_started (R.start_evaluation ?before ?active) ?started)
          ?variable |- False =>
          apply Hunqueued;
          change (queued_variable (R.start_evaluation before active) variable)
            in Hq;
          exact (@queued_variable_start_evaluation_inv before active variable Hq)
      end.
    all: try match goal with
      | Hq : queued_variable
          (R.get_ready_state ?observed ?active ?target_handle) ?variable,
        Hobserve : R.observe ?before ?target = (?observed, ?target_handle)
          |- False =>
          apply queued_variable_get_ready_inv in Hq;
          apply Hunqueued;
          exact (@queued_variable_observe_inv before target observed target_handle
            variable Hobserve Hq)
      end.
    all: try match goal with
      | Hq : queued_variable
          (R.side_ready_state ?observed ?active ?target_handle ?raw) ?variable,
        Hobserve : R.observe ?before ?target = (?observed, ?target_handle)
          |- False =>
          apply queued_variable_side_ready_inv in Hq;
          apply Hunqueued;
          exact (@queued_variable_observe_inv before target observed target_handle
            variable Hobserve Hq)
      end.
    all: try match goal with
      | Hq : queued_variable ?observed ?variable,
        Hobserve : R.observe ?before ?target = (?observed, ?target_handle)
          |- False =>
          apply Hunqueued;
          exact (@queued_variable_observe_inv before target observed target_handle
            variable Hobserve Hq)
      end.
    - eapply unpaid_ret_preserves_unqueued; eauto.
    - apply queued_variable_get_ready_inv in Hqueued.
      destruct (@queued_variable_enqueue_handle_origin s h0
        (R.handle_variable owner) Hqueued) as [Hequal | Hold].
      + pose proof (@reachable_observed_unmaterialized_not_owner tf roots st
          owner (R.ConstraintSystem.Get t r0) base t s h0
          Hreachable Hcase0 Hcase1) as Hneq.
        symmetry in Hequal. contradiction.
      + apply Hunqueued.
        exact (@queued_variable_observe_inv st t s h0
          (R.handle_variable owner) Hcase0 Hold).
    - destruct Hsupported as [_ Hcontrol]. cbn in Hcontrol.
      destruct Hcontrol as [Howner [Hrhs _]].
      destruct (Payment.rhs_supported_side_inv Hrhs) as [Htarget _].
      eapply (@unpaid_observed_side_enqueue_cannot_grow
        (Sem.support finite) tf st s owner h0 t t0).
      + exact (Sem.support_nodup finite).
      + exact Howner.
      + exact Htarget.
      + exact Hcase0.
      + exact Hunpaid.
      + unfold Accounting.side_grows.
        rewrite (@observed_handle_variable st t s h0 Hcase0).
        destruct (D.leq (R.aggregate (R.side_ready_state s owner h0 t0) t)
          (R.aggregate s t)); cbn in Hcase1 |- *; congruence.
    - apply queued_variable_materialize_inv in Hqueued.
      destruct (@queued_variable_enqueue_handle_origin s h0
        (R.handle_variable owner) Hqueued) as [Hequal | Hold].
      + pose proof (@reachable_observed_unmaterialized_not_owner tf roots st
          owner (R.ConstraintSystem.Spawn t r0) base t s h0
          Hreachable Hcase0 Hcase1) as Hneq.
        symmetry in Hequal. contradiction.
      + apply Hunqueued.
        exact (@queued_variable_observe_inv st t s h0
          (R.handle_variable owner) Hcase0 Hold).
    - apply Hunqueued.
      now apply queued_variable_get_ready_inv in Hqueued.
  Qed.

  Lemma unpaid_fresh_solve_one_cannot_step :
    forall support tf st target rest after,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      R.is_materialized st (R.handle_variable target) = false ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOne target rest |}
        after ->
      False.
  Proof.
    intros support tf st target rest after Hnodup Htarget Hfresh Hunpaid.
    pose proof Hunpaid as Hunpaid_full.
    destruct Hunpaid as [Hstep _].
    unfold Sem.step in Hstep. cbn in Hstep. inversion Hstep; subst.
    assert (Hafter :
      R.is_materialized
        (R.with_started
          (R.start_evaluation st (R.handle_variable target))
          (S.add (R.handle_variable target)
            (R.started (R.materialize st (R.handle_variable target)))))
        (R.handle_variable target) = true).
    {
      change (R.is_materialized
        (R.start_evaluation st (R.handle_variable target))
        (R.handle_variable target) = true).
      apply Progress.solved_is_materialized.
      apply Progress.solved_start_evaluation_self.
    }
    pose proof (@Payment.unpaid_step_reflects_materialization
      support tf _ _ (R.handle_variable target)
      Hnodup Htarget Hunpaid_full Hafter) as Hbefore.
    cbn in Hbefore. congruence.
  Qed.

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
    destruct (R.queue st) as [|head tail] eqn:Hqueue;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. cbn in Hmay.
    destruct (V.eq_dec (R.handle_variable next)
      (R.handle_variable owner)); contradiction || assumption.
  Qed.

  Lemma next_config_control_ordered :
    forall tf before after,
      control_ordered (R.cfg_control before) ->
      Sem.step tf before after ->
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
      try exact Hordered; try exact I;
      try (apply continuation_ordered_continue; exact Hordered).
    - split; [eapply owner_may_pop_higher; eauto |exact Hordered].
    - exact (continuation_ordered_continue h c Hordered).
    - split; [exact Hcase2 |exact Hordered].
    - apply Bool.andb_true_iff in Hcase2 as [Hlt _].
      split; [exact Hlt |exact Hordered].
    - split; [exact Hcase2 |exact Hordered].
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

  Lemma reachable_control_ordered :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      control_ordered (R.cfg_control after).
  Proof.
    intros tf roots after Hsteps. eapply steps_control_ordered; eauto.
    exact I.
  Qed.

  Lemma control_at_owner_root_ordered :
    forall owner base control,
      control_at_owner_root owner base control ->
      control_ordered control ->
      continuation_ordered owner base.
  Proof.
    intros owner base control Hroot Hordered.
    destruct control; cbn in Hroot, Hordered; try contradiction;
      destruct Hroot as [-> ->]; exact Hordered.
  Qed.

  Lemma scoped_continuation_owner_below :
    forall owner base rest active,
      Sim.scoped_continuation owner base rest ->
      continuation_ordered active rest ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank active) = true.
  Proof.
    intros owner base rest active Hscope. revert active.
    induction Hscope; intros active Hordered; cbn in Hordered.
    all: try exact (proj1 Hordered).
    all: destruct Hordered as [Hcurrent Hrest].
    all: apply Nat.ltb_lt in Hcurrent.
    all: specialize (IHHscope _ Hrest); apply Nat.ltb_lt in IHHscope.
    all: apply Nat.ltb_lt; lia.
  Qed.

  Lemma continue_base_outside_scope :
    forall owner base,
      continuation_ordered owner base ->
      ~ Sim.control_in_scope owner base (R.continue base).
  Proof.
    intros owner base Hordered Hscope.
    destruct base; cbn in Hordered, Hscope; try contradiction.
    all: destruct Hordered as [Houter Hordered].
    all: destruct Hscope as [[Hequal _] | Hnested].
    all: try (subst h; apply Nat.ltb_lt in Houter; lia).
    all: try match goal with
      | Hnested : Sim.scoped_continuation ?root _ _ |- _ =>
          pose proof (@scoped_continuation_owner_below
            root _ _ _ Hnested Hordered) as Hinner;
          apply Nat.ltb_lt in Houter, Hinner; lia
      end.
  Qed.

  Lemma scoped_unpaid_root_preserves_unqueued :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base first last,
      Sem.steps tf (R.initial_config roots) first ->
      control_at_owner_root owner base (R.cfg_control first) ->
      queue_at_most owner (R.cfg_state first) ->
      Payment.scoped_supported_unpaid_steps
        owner base (Sem.support finite) tf first last ->
      ~ queued_variable (R.cfg_state first) (R.handle_variable owner) ->
      ~ queued_variable (R.cfg_state last) (R.handle_variable owner).
  Proof.
    intros tf roots finite owner base first last Hreachable Hroot Hqueue
      Hsteps. revert Hreachable Hroot Hqueue.
    induction Hsteps; intros Hreachable Hroot Hqueue Hunqueued.
    - exact Hunqueued.
    - assert (Hnext_reachable :
        Sem.steps tf (R.initial_config roots) next).
      { eapply Sim.steps_append_one; [exact Hreachable |exact (proj1 H1)]. }
      assert (Hnext_queue : queue_at_most owner (R.cfg_state next)).
      {
        exact (@unpaid_root_step_preserves_queue_at_most tf roots finite
          owner base first next Hreachable Hroot Hqueue H1).
      }
      assert (Hnext_unqueued :
        ~ queued_variable (R.cfg_state next) (R.handle_variable owner)).
      {
        exact (@unpaid_root_step_preserves_unqueued tf roots finite
          owner base first next Hreachable Hroot Hqueue H1 Hunqueued).
      }
      pose proof (@root_step_has_shape tf owner base first next
        Hroot Hqueue Hunqueued (proj1 H1)) as Hshape.
      inversion Hshape; subst.
      + eapply IHHsteps; eauto.
      + destruct Hsteps.
        * exact Hnext_unqueued.
        * exfalso. rewrite H2 in H5. cbn in H5.
          assert (Hfirst0 : first0 =
            {| R.cfg_state := R.cfg_state first0;
               R.cfg_control := R.RunSolveOne target rest |}).
          { destruct first0. cbn in H2 |- *. now subst. }
          rewrite Hfirst0 in H6.
          eapply (@unpaid_fresh_solve_one_cannot_step
            (Sem.support finite) tf (R.cfg_state first0) target rest next).
          -- exact (Sem.support_nodup finite).
          -- exact (proj1 H5).
          -- exact H3.
          -- exact H6.
      + destruct Hsteps.
        * exact Hnext_unqueued.
        * exfalso.
          assert (Hordered : continuation_ordered owner base).
          {
            eapply control_at_owner_root_ordered; [exact Hroot |].
            exact (reachable_control_ordered Hreachable).
          }
          apply (@continue_base_outside_scope owner base Hordered).
          now rewrite <- H2.
  Qed.

  Lemma queue_strictly_below_unqueued :
    forall owner st,
      rank_valid st ->
      handle_valid st owner ->
      queue_valid st ->
      queue_strictly_below owner st ->
      ~ queued_variable st (R.handle_variable owner).
  Proof.
    intros owner st Hrank Howner Hqueue Hbelow
      [entry [Hentry Hvariable]].
    assert (Hentry_valid : handle_valid st entry).
    { eapply queue_entry_valid; eauto. }
    assert (Hranks : R.handle_rank entry = R.handle_rank owner).
    { eapply same_variable_valid_rank; eauto. }
    specialize (Hbelow entry Hentry). lia.
  Qed.

  Lemma scoped_restart_decreases :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base start_state pop_state tail,
      queue_strictly_below owner start_state ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := start_state;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |} ->
      Sim.scoped_until_steps owner base tf
        {| R.cfg_state := start_state;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} ->
      R.queue_pop (R.queue pop_state) = Some (owner, tail) ->
      Payment.round_decreases (Sem.support finite)
        {| R.cfg_state := start_state;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots finite owner base start_state pop_state tail Hbelow
      Hreachable Hsteps Hpop.
    destruct (@Payment.reachable_scoped_steps_decrease_or_unpaid
      tf roots finite owner base _ _ Hreachable Hsteps)
      as [Hdecreases | Hunpaid]; [exact Hdecreases |].
    exfalso.
    pose proof (reachable_handles_valid Hreachable) as Hhandles.
    assert (Hstart_unqueued :
      ~ queued_variable start_state (R.handle_variable owner)).
    {
      eapply queue_strictly_below_unqueued.
      - exact (handles_rank_valid Hhandles).
      - exact (proj1 (handles_control_valid Hhandles)).
      - exact (handles_queue_valid Hhandles).
      - exact Hbelow.
    }
    pose proof (@scoped_unpaid_root_preserves_unqueued
      tf roots finite owner base
      {| R.cfg_state := start_state;
         R.cfg_control := R.RunRhs owner
           (tf (R.handle_variable owner)) base |}
      {| R.cfg_state := pop_state;
         R.cfg_control := R.RunSolveOneLoop owner base |}
      Hreachable (conj eq_refl eq_refl)
      (queue_strictly_below_at_most Hbelow) Hunpaid Hstart_unqueued)
      as Hend_unqueued.
    apply Hend_unqueued. exists owner. split; [|reflexivity].
    unfold R.queue_pop in Hpop.
    destruct (R.queue pop_state) as [|head rest] eqn:Hqueue;
      cbn in Hpop; try discriminate.
    inversion Hpop; subst. cbn. rewrite Hqueue. now left.
  Qed.

  End Restart.

  Module ExitReady.
  Definition aggregate_sound (st : R.state) (target : V.t) : Prop :=
    D.leq (R.aggregate st target) (R.sigma_value st target) = true.

  Definition owner_exit_ready (st : R.state) (owner : R.handle) : Prop :=
    aggregate_sound st (R.handle_variable owner) \/
    Restart.queued_variable st (R.handle_variable owner).

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

  Lemma aggregate_observe :
    forall st target next entry observed,
      R.observe st target = (next, entry) ->
      R.aggregate next observed = R.aggregate st observed.
  Proof.
    intros st target next entry observed Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
  Qed.

  Lemma aggregate_materialize :
    forall st target observed,
      R.aggregate (R.materialize st target) observed = R.aggregate st observed.
  Proof.
    intros. unfold R.materialize.
    destruct (R.is_materialized st target); reflexivity.
  Qed.

  Lemma aggregate_start_evaluation :
    forall st owner observed,
      R.aggregate (R.start_evaluation st owner) observed =
      R.aggregate st observed.
  Proof.
    intros. unfold R.start_evaluation, R.reset_local_sides.
    apply aggregate_materialize.
  Qed.

  Lemma aggregate_get_ready :
    forall st owner target observed,
      R.aggregate (R.get_ready_state st owner target) observed =
      R.aggregate st observed.
  Proof.
    intros. unfold R.get_ready_state, R.add_reader, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      unfold R.materialize; destruct (R.is_materialized _ _); reflexivity.
  Qed.

  Lemma aggregate_enqueue :
    forall st inserted observed,
      R.aggregate (R.enqueue st inserted) observed = R.aggregate st observed.
  Proof.
    intros. unfold R.enqueue.
    destruct (R.observe st inserted) as [next entry] eqn:Hobserve.
    unfold R.enqueue_handle. cbn.
    change (R.aggregate next observed = R.aggregate st observed).
    exact (@aggregate_observe st inserted next entry observed Hobserve).
  Qed.

  Lemma aggregate_enqueue_all :
    forall xs st observed,
      R.aggregate (R.enqueue_all st xs) observed = R.aggregate st observed.
  Proof.
    induction xs as [|x xs IH]; intros st observed; cbn;
      [reflexivity |rewrite IH, aggregate_enqueue; reflexivity].
  Qed.

  Lemma aggregate_write_changed_value :
    forall st owner value observed,
      R.aggregate (R.write_changed_value st owner value) observed =
      R.aggregate st observed.
  Proof.
    intros. unfold R.write_changed_value.
    change (R.aggregate
      (R.enqueue_all (R.with_sigma st (M.update (R.sigma st) owner value))
        (S.elements (R.lookup_set (R.readers st) owner))) observed =
      R.aggregate st observed).
    rewrite aggregate_enqueue_all. reflexivity.
  Qed.

  Lemma aggregate_record_side_other :
    forall st source target raw observed,
      observed <> target ->
      R.aggregate (R.record_side_payload st source target raw) observed =
      R.aggregate st observed.
  Proof.
    intros st source target raw observed Hneq.
    unfold R.aggregate, R.record_side_payload. cbn.
    rewrite Accounting.lookup_update_map_other_outer by exact Hneq.
    reflexivity.
  Qed.

  Lemma aggregate_side_ready_other :
    forall st source target raw observed,
      observed <> R.handle_variable target ->
      R.aggregate (R.side_ready_state st source target raw) observed =
      R.aggregate st observed.
  Proof.
    intros st source target raw observed Hneq.
    unfold R.side_ready_state, R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      now apply aggregate_record_side_other.
  Qed.

  Lemma aggregate_set_value :
    forall st owner direct target,
      R.aggregate (R.set_value st owner direct) target = R.aggregate st target.
  Proof.
    intros. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
        as [phase value]. cbn.
      destruct (R.equivalent value (R.sigma_value st owner));
        [reflexivity |rewrite aggregate_write_changed_value; reflexivity].
    - rewrite aggregate_write_changed_value. reflexivity.
  Qed.

  Lemma set_value_candidate_below :
    forall st owner direct,
      D.leq (D.join direct (R.aggregate st owner))
        (R.sigma_value (R.set_value st owner direct) owner) = true.
  Proof.
    intros. unfold R.set_value.
    set (candidate := D.join direct (R.aggregate st owner)).
    set (old := R.sigma_value st owner).
    destruct (R.equivalent candidate old) eqn:Hequivalent.
    - apply Bool.andb_true_iff in Hequivalent. exact (proj1 Hequivalent).
    - destruct (S.mem owner (R.controlled st)).
      + destruct (U.update false owner (R.stored_phase st owner)
          old candidate) as [phase value] eqn:Hupdate. cbn.
        pose proof (UL.update_sound false owner (R.stored_phase st owner)
          old candidate) as Hsound.
        rewrite Hupdate in Hsound. cbn in Hsound.
        destruct (R.equivalent value old) eqn:Hstutter.
        * apply Bool.andb_true_iff in Hstutter.
          eapply DL.leq_trans; [exact Hsound |exact (proj1 Hstutter)].
        * rewrite Accounting.sigma_value_write_changed_same. exact Hsound.
      + rewrite Accounting.sigma_value_write_changed_same.
        apply DL.leq_refl.
  Qed.

  Lemma set_value_aggregate_below :
    forall st owner direct,
      aggregate_sound (R.set_value st owner direct) owner.
  Proof.
    intros. unfold aggregate_sound. rewrite aggregate_set_value.
    eapply DL.leq_trans; [apply DL.join_upper_right |].
    apply set_value_candidate_below.
  Qed.

  Lemma aggregate_sound_start :
    forall st owner tracked,
      aggregate_sound st tracked ->
      aggregate_sound (R.start_evaluation st owner) tracked.
  Proof.
    intros. unfold aggregate_sound in *. rewrite aggregate_start_evaluation,
      Payment.sigma_value_start_evaluation. exact H.
  Qed.

  Lemma aggregate_sound_get_ready :
    forall st owner target tracked,
      aggregate_sound st tracked ->
      aggregate_sound (R.get_ready_state st owner target) tracked.
  Proof.
    intros. unfold aggregate_sound in *. rewrite aggregate_get_ready,
      Payment.sigma_value_get_ready. exact H.
  Qed.

  Lemma aggregate_sound_set_value :
    forall st owner direct tracked,
      aggregate_sound st tracked ->
      aggregate_sound (R.set_value st owner direct) tracked.
  Proof.
    intros st owner direct tracked Hsound.
    destruct (V.eq_dec tracked owner) as [-> | Hneq].
    - apply set_value_aggregate_below.
    - unfold aggregate_sound in *. rewrite aggregate_set_value,
        Payment.sigma_value_set_value_other by exact Hneq.
      exact Hsound.
  Qed.

  Lemma aggregate_sound_side_other :
    forall st source target raw tracked,
      tracked <> R.handle_variable target ->
      aggregate_sound st tracked ->
      aggregate_sound (R.side_ready_state st source target raw) tracked.
  Proof.
    intros. unfold aggregate_sound in *. rewrite aggregate_side_ready_other,
      Payment.sigma_value_side_ready by exact H. exact H0.
  Qed.

  Lemma aggregate_sound_side_covered :
    forall st source target raw,
      D.leq
        (R.aggregate (R.side_ready_state st source target raw)
          (R.handle_variable target))
        (R.aggregate st (R.handle_variable target)) = true ->
      aggregate_sound st (R.handle_variable target) ->
      aggregate_sound (R.side_ready_state st source target raw)
        (R.handle_variable target).
  Proof.
    intros st source target raw Hcovered Hsound.
    unfold aggregate_sound in *. eapply DL.leq_trans; [exact Hcovered |].
    rewrite Payment.sigma_value_side_ready. exact Hsound.
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
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.enqueue_handle st inserted) tracked.
  Proof.
    intros st inserted tracked [entry [Hin Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.enqueue_handle. cbn. now apply queue_insert_preserves.
  Qed.

  Lemma queued_observe :
    forall st target next entry tracked,
      R.observe st target = (next, entry) ->
      Restart.queued_variable st tracked ->
      Restart.queued_variable next tracked.
  Proof.
    intros st target next entry tracked Hobserve Hqueued.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve; subst; exact Hqueued.
  Qed.

  Lemma queued_enqueue :
    forall st inserted tracked,
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.enqueue st inserted) tracked.
  Proof.
    intros st inserted tracked Hqueued. unfold R.enqueue.
    destruct (R.observe st inserted) as [next entry] eqn:Hobserve.
    apply queued_enqueue_handle. eapply queued_observe; eauto.
  Qed.

  Lemma queued_enqueue_all :
    forall xs st tracked,
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.enqueue_all st xs) tracked.
  Proof.
    induction xs as [|x xs IH]; intros st tracked Hqueued; cbn;
      eauto using queued_enqueue.
  Qed.

  Lemma queued_set_value :
    forall st owner direct tracked,
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.set_value st owner direct) tracked.
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
        aggregate_sound before (R.handle_variable owner) ->
        aggregate_sound after (R.handle_variable owner)) ->
      (forall owner,
        Restart.queued_variable before (R.handle_variable owner) ->
        Restart.queued_variable after (R.handle_variable owner)) ->
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
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.start_evaluation st active) tracked.
  Proof.
    intros st active tracked Hqueued.
    unfold R.start_evaluation, R.reset_local_sides, R.materialize.
    destruct (R.is_materialized st active); exact Hqueued.
  Qed.

  Lemma queued_get_ready :
    forall st owner target tracked,
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.get_ready_state st owner target) tracked.
  Proof.
    intros st owner target tracked Hqueued.
    unfold R.get_ready_state, R.add_reader, R.promote_controlled, R.materialize.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      destruct (R.is_materialized _ _); exact Hqueued.
  Qed.

  Lemma queued_side_ready :
    forall st source target raw tracked,
      Restart.queued_variable st tracked ->
      Restart.queued_variable (R.side_ready_state st source target raw) tracked.
  Proof.
    intros st source target raw tracked Hqueued.
    unfold R.side_ready_state, R.record_side_payload, R.promote_controlled.
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable source)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable source)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable source)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      exact Hqueued.
  Qed.

  Lemma owner_exit_start :
    forall st active owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.start_evaluation st active) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply aggregate_sound_start.
    - intros. now apply queued_start.
  Qed.

  Lemma owner_exit_get_ready :
    forall st active target owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.get_ready_state st active target) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply aggregate_sound_get_ready.
    - intros. now apply queued_get_ready.
  Qed.

  Lemma owner_exit_set_value :
    forall st variable direct owner,
      owner_exit_ready st owner ->
      owner_exit_ready (R.set_value st variable direct) owner.
  Proof.
    intros. eapply owner_exit_map; [| |exact H].
    - intros. now apply aggregate_sound_set_value.
    - intros. now apply queued_set_value.
  Qed.

  Lemma owner_exit_side_other :
    forall st source target raw owner,
      R.handle_variable owner <> R.handle_variable target ->
      owner_exit_ready st owner ->
      owner_exit_ready (R.side_ready_state st source target raw) owner.
  Proof.
    intros st source target raw owner Hneq [Hsound | Hqueued].
    - left. now apply aggregate_sound_side_other.
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
      + rewrite Heq in *. now apply aggregate_sound_side_covered.
      + now apply aggregate_sound_side_other.
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
    { eapply Restart.same_variable_valid_rank; eauto. }
    lia.
  Qed.

  Lemma continuation_exit_pop :
    forall st popped tail upper k,
      queue_valid st -> continuation_valid st k ->
      R.queue_pop (R.queue st) = Some (popped, tail) ->
      Restart.continuation_ordered upper k ->
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
      Restart.continuation_ordered upper k ->
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

  Lemma aggregate_sound_observe :
    forall st target next entry tracked,
      R.observe st target = (next, entry) ->
      aggregate_sound st tracked -> aggregate_sound next tracked.
  Proof.
    intros. unfold aggregate_sound in *. rewrite
      (@aggregate_observe st target next entry tracked H),
      (@Payment.sigma_value_observe st target next entry tracked H).
    exact H0.
  Qed.

  Lemma owner_exit_observe :
    forall st target next entry owner,
      R.observe st target = (next, entry) ->
      owner_exit_ready st owner -> owner_exit_ready next owner.
  Proof.
    intros st target next entry owner Hobserve [Hsound | Hqueued].
    - left. eapply aggregate_sound_observe; eauto.
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
    - left. unfold aggregate_sound in *. rewrite aggregate_materialize,
        Payment.sigma_value_materialize. exact Hsound.
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
      Restart.queued_variable (R.enqueue_handle st inserted)
        (R.handle_variable inserted).
  Proof.
    intros st inserted Hrank Hqueue Hinserted.
    unfold R.enqueue_handle, Restart.queued_variable. cbn.
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

  Lemma control_exit_ready_step :
    forall tf before after,
      handles_valid before ->
      Restart.control_ordered (R.cfg_control before) ->
      control_exit_ready (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      control_exit_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hvalid Hordered Hready Hstep.
    unfold Sem.step in Hstep. cbn in Hvalid, Hordered, Hready, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I.
    - apply continuation_exit_with_started, continuation_exit_start.
      exact Hready.
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      assert (Hequal : h0 = h).
      { eapply same_variable_valid_handle_equal.
        - exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
        - exact (proj1 Hcontrol).
        - exact e. }
      subst h0. eapply continuation_exit_pop; eauto.
      + exact (proj2 Hcontrol).
      + exact (proj2 Hready).
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      assert (Hhigher : R.handle_rank h < R.handle_rank h0).
      { apply Nat.ltb_lt. eapply Restart.owner_may_pop_higher; eauto. }
      split.
      + eapply owner_exit_pop_other; [exact Hcase0 | |exact (proj1 Hready)].
        intro Heq. apply n. symmetry.
        eapply handle_rank_equal_variable_equal.
        * exact (handles_rank_valid Hvalid).
        * exact (proj1 Hcontrol).
        * exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
        * eapply Restart.same_variable_valid_rank; eauto.
          -- exact (proj1 Hcontrol).
          -- exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
      + eapply continuation_exit_pop; eauto.
        * exact (proj2 Hcontrol).
        * exact (proj2 Hready).
    - apply continuation_exit_ready_continue. exact (proj2 Hready).
    - split.
      + left. apply set_value_aggregate_below.
      + now apply continuation_exit_set_value.
    - apply continuation_exit_get_ready.
      eapply continuation_exit_observe; eauto.
    - eapply continuation_exit_observe; eauto.
    - apply continuation_exit_get_ready, continuation_exit_enqueue_handle.
      eapply continuation_exit_observe; eauto.
    - apply Bool.andb_true_iff in Hcase2.
      destruct Hcase2 as [Hhigher Hnotmat].
      assert (Hlt : R.handle_rank h < R.handle_rank h0).
      { destruct (R.handle_rank h0) as [|rank] eqn:Htarget;
          cbn in Hhigher; try discriminate.
        apply Nat.leb_le in Hhigher. lia. }
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      cbn in Hcontrol. eapply continuation_exit_side_above with (upper := h).
      + eapply continuation_valid_extended;
          [eapply rank_extends_observe; eauto |exact (proj2 Hcontrol)].
      + eapply observed_handle_valid; eauto.
      + exact Hlt.
      + exact Hordered.
      + eapply continuation_exit_observe; eauto.
    - eapply continuation_exit_side_enqueue.
      + eapply rank_valid_observe;
          [exact (handles_rank_valid Hvalid) |exact Hcase0].
      + eapply queue_valid_observe;
          [exact (handles_queue_valid Hvalid) |exact Hcase0].
      + eapply observed_handle_valid; eauto.
      + eapply continuation_exit_observe; eauto.
    - apply Bool.negb_false_iff in Hcase1.
      pose proof (@observed_handle_variable st t s h0 Hcase0) as Hvariable.
      eapply continuation_exit_side_covered.
      + rewrite Hvariable. exact Hcase1.
      + eapply continuation_exit_observe; eauto.
    - eapply continuation_exit_observe; eauto.
    - eapply continuation_exit_observe; eauto.
    - apply continuation_exit_materialize, continuation_exit_enqueue_handle.
      eapply continuation_exit_observe; eauto.
    - now apply continuation_exit_get_ready.
    - exact Hready.
    - exact Hready.
  Qed.

  Lemma control_exit_ready_steps :
    forall tf before after,
      handles_valid before ->
      Restart.control_ordered (R.cfg_control before) ->
      control_exit_ready (R.cfg_state before) (R.cfg_control before) ->
      Sem.steps tf before after ->
      control_exit_ready (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf before after Hvalid Hordered Hready Hsteps.
    induction Hsteps; [exact Hready |].
    apply IHHsteps.
    - eapply next_config_handles_valid; eauto.
    - eapply Restart.next_config_control_ordered; eauto.
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

  Theorem reachable_exit_ready :
    forall tf roots st owner base,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} ->
      R.owner_may_still_be_queued st owner = false ->
      D.leq (R.aggregate st (R.handle_variable owner))
        (R.sigma_value st (R.handle_variable owner)) = true.
  Proof.
    intros tf roots st owner base Hreachable Hmay.
    pose proof (reachable_control_exit_ready Hreachable) as Hready.
    cbn in Hready. destruct (proj1 Hready) as [Hsound | Hqueued].
    - exact Hsound.
    - exfalso. pose proof (reachable_handles_valid Hreachable)
        as Hhandles.
      apply (@Restart.queue_strictly_below_unqueued owner st
        (handles_rank_valid Hhandles)
        (proj1 (handles_control_valid Hhandles))
        (handles_queue_valid Hhandles)).
      + exact (@reachable_owner_may_false_queue_below
          tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOneLoop owner base |}
          owner Hreachable
          (proj1 (handles_control_valid Hhandles)) Hmay).
      + exact Hqueued.
  Qed.

  End ExitReady.
  Module Total.
  Definition started_evaluation (st : R.state) (owner : R.handle) : R.state :=
    let variable := R.handle_variable owner in
    let ready := R.start_evaluation st variable in
    R.with_started ready (S.add variable (R.started ready)).

  Definition solve_loop_boundary
    (tf : R.ConstraintSystem.system)
    (owner : R.handle) (base : R.continuation)
    (start : R.config) : Prop :=
    (exists st,
      Sim.scoped_until_steps owner base tf start
        {| R.cfg_state := st; R.cfg_control := R.continue base |} /\
      queue_strictly_below owner st) \/
    (exists pop_state tail,
      Sim.scoped_until_steps owner base tf start
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} /\
      R.owner_may_still_be_queued pop_state owner = true /\
      R.queue_pop (R.queue pop_state) = Some (owner, tail) /\
      queue_strictly_below owner
        (started_evaluation (R.with_queue pop_state tail) owner)).

  Lemma owner_may_true_pop :
    forall st owner,
      R.owner_may_still_be_queued st owner = true ->
      exists next tail,
        R.queue_pop (R.queue st) = Some (next, tail).
  Proof.
    intros st owner Hmay. unfold R.owner_may_still_be_queued in Hmay.
    destruct (R.queue st) as [|next tail] eqn:Hqueue;
      [discriminate |].
    now exists next, tail.
  Qed.

  Lemma popped_started_strictly_below :
    forall tf roots st owner tail base,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} ->
      R.queue_pop (R.queue st) = Some (owner, tail) ->
      queue_strictly_below owner
        (started_evaluation (R.with_queue st tail) owner).
  Proof.
    intros tf roots st owner tail base Hreachable Hpop queued Hqueued.
    unfold started_evaluation in Hqueued.
    unfold R.start_evaluation, R.reset_local_sides, R.materialize in Hqueued.
    destruct (R.is_materialized (R.with_queue st tail)
      (R.handle_variable owner)); cbn in Hqueued.
    all: pose proof (reachable_queue_ordered Hreachable) as Hordered.
    all: exact (proj2 (queue_pop_ordered Hordered Hpop) queued Hqueued).
  Qed.

  Definition reachable_exit_ready
    (tf : R.ConstraintSystem.system) (roots : list V.t) : Prop :=
    forall st owner base,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} ->
      R.owner_may_still_be_queued st owner = false ->
      D.leq (R.aggregate st (R.handle_variable owner))
        (R.sigma_value st (R.handle_variable owner)) = true.

  Theorem reachable_exit_ready_proved :
    forall tf roots, reachable_exit_ready tf roots.
  Proof.
    intros tf roots st owner base Hreachable Hmay.
    eapply ExitReady.reachable_exit_ready; eauto.
  Qed.

  Lemma same_variable_valid_handle_equal :
    forall st left right,
      handle_valid st left ->
      handle_valid st right ->
      R.handle_variable left = R.handle_variable right ->
      left = right.
  Proof.
    intros st [left_variable left_rank] [right_variable right_rank]
      Hleft Hright Hvariable. cbn in Hvariable. subst right_variable.
    unfold handle_valid in Hleft, Hright. cbn in Hleft, Hright.
    rewrite Hleft in Hright.
    inversion Hright. reflexivity.
  Qed.

  Lemma bounded_solve_loop_reaches_boundary :
    forall tf roots (finite : Sem.finite_system tf roots) owner base,
      reachable_exit_ready tf roots ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      forall upper st,
        queue_strictly_below upper st ->
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOneLoop owner base |} ->
        solve_loop_boundary tf owner base
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots finite owner base Hexit Hchildren.
    intros upper st Hbelow Hreachable.
    remember (R.handle_rank upper) as upper_rank eqn:Hrank.
    revert upper st Hrank Hbelow Hreachable.
    pattern upper_rank.
    apply (well_founded_induction_type PeanoNat.Nat.lt_wf_0).
    intros rank H upper st Hrank Hbelow Hreachable.
    destruct (R.owner_may_still_be_queued st owner) eqn:Hmay.
    2: {
      left. exists st. split.
      - econstructor.
        + cbn. left. split; reflexivity.
        + unfold Sem.step. cbn. rewrite Hmay, (Hexit st owner base Hreachable Hmay).
          reflexivity.
        + constructor.
      - pose proof (reachable_handles_valid Hreachable) as Hvalid.
        exact (@reachable_owner_may_false_queue_below tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOneLoop owner base |}
          owner Hreachable
          (proj1 (handles_control_valid Hvalid)) Hmay).
    }
    destruct (owner_may_true_pop st owner Hmay) as [next [tail Hpop]].
    destruct (V.eq_dec (R.handle_variable next)
      (R.handle_variable owner)) as [Hsame | Hneq].
    - assert (Hhandles : handles_valid
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |})
        by exact (reachable_handles_valid Hreachable).
      assert (Hnext_owner : next = owner).
      {
        eapply same_variable_valid_handle_equal; eauto.
        - eapply queue_pop_valid; eauto.
          exact (handles_queue_valid Hhandles).
        - exact (proj1 (handles_control_valid Hhandles)).
      }
      subst next. right. exists st, tail. repeat split; try assumption.
      + constructor.
      + eapply popped_started_strictly_below; eauto.
    - assert (Hhigher : Nat.ltb (R.handle_rank owner)
        (R.handle_rank next) = true).
      { eapply Restart.owner_may_pop_higher; eauto. }
      assert (Hnext_queued : List.In next (R.queue st)).
      {
        unfold R.queue_pop in Hpop.
        destruct (R.queue st) as [|head rest] eqn:Hqueue;
          cbn in Hpop; try discriminate.
        inversion Hpop; subst. now left.
      }
      assert (Hnext_supported :
        List.In (R.handle_variable next) (Sem.support finite)).
      {
        pose proof (reachable_config_supported finite Hreachable)
          as Hsupported.
        exact (queue_is_supported (proj1 Hsupported) next Hnext_queued).
      }
      assert (Hnext_upper : R.handle_rank next < R.handle_rank upper).
      { exact (Hbelow next Hnext_queued). }
      set (child_base := R.KSolveOneLoop owner base).
      set (child :=
        {| R.cfg_state := R.with_queue st tail;
           R.cfg_control := R.RunSolveOne next child_base |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} child).
      {
        unfold Sem.step, child, child_base. cbn. rewrite Hmay, Hpop.
        destruct (V.eq_dec (R.handle_variable next)
          (R.handle_variable owner)); [contradiction |reflexivity].
      }
      assert (Hchild : Sem.steps tf (R.initial_config roots) child).
      { eapply Sim.steps_append_one; eauto. }
      destruct (Hchildren next child_base child Hnext_supported Hhigher
        Hchild eq_refl) as [child_state [Hepisode Hchild_below]].
      unfold child_base in Hepisode.
      assert (Hreturned : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := child_state;
           R.cfg_control := R.RunSolveOneLoop owner base |}).
      {
        eapply Sim.steps_transitive; [exact Hchild |].
        exact (Sim.scoped_until_semantic Hepisode).
      }
      assert (Hnext_rank : R.handle_rank next < rank) by lia.
      destruct (H (R.handle_rank next) Hnext_rank next child_state eq_refl)
        as [[done [Hdone Hdone_below]] |
            [pop_state [again_tail
              [Hagain [Hagain_may [Hagain_pop Hagain_below]]]]]];
        try exact Hchild_below; try exact Hreturned.
      + left. exists done. split; [|exact Hdone_below].
        econstructor.
        * cbn. left. split; reflexivity.
        * exact Hstep.
        * eapply Sim.scoped_until_transitive.
          -- eapply Sim.scoped_until_lift.
             ++ apply Sim.ScopedContinuationSolve.
             ++ exact Hepisode.
          -- exact Hdone.
      + right. exists pop_state, again_tail. repeat split; try assumption.
        econstructor.
        * cbn. left. split; reflexivity.
        * exact Hstep.
        * eapply Sim.scoped_until_transitive.
          -- eapply Sim.scoped_until_lift.
             ++ apply Sim.ScopedContinuationSolve.
             ++ exact Hepisode.
          -- exact Hagain.
  Qed.

  Lemma solve_loop_reaches_boundary :
    forall tf roots (finite : Sem.finite_system tf roots) owner base st,
      reachable_exit_ready tf roots ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} ->
      solve_loop_boundary tf owner base
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots finite owner base st Hexit Hchildren Hreachable.
    destruct (R.owner_may_still_be_queued st owner) eqn:Hmay.
    2: {
      left. exists st. split.
      - econstructor.
        + cbn. left. split; reflexivity.
        + unfold Sem.step. cbn. rewrite Hmay,
            (Hexit st owner base Hreachable Hmay). reflexivity.
        + constructor.
      - pose proof (reachable_handles_valid Hreachable) as Hvalid.
        exact (@reachable_owner_may_false_queue_below tf roots
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOneLoop owner base |}
          owner Hreachable
          (proj1 (handles_control_valid Hvalid)) Hmay).
    }
    destruct (owner_may_true_pop st owner Hmay) as [next [tail Hpop]].
    destruct (V.eq_dec (R.handle_variable next)
      (R.handle_variable owner)) as [Hsame | Hneq].
    - pose proof (reachable_handles_valid Hreachable) as Hhandles.
      assert (Hnext_owner : next = owner).
      {
        eapply same_variable_valid_handle_equal; eauto.
        - eapply queue_pop_valid; eauto.
          exact (handles_queue_valid Hhandles).
        - exact (proj1 (handles_control_valid Hhandles)).
      }
      subst next. right. exists st, tail. repeat split; try assumption.
      + constructor.
      + eapply popped_started_strictly_below; eauto.
    - assert (Hhigher : Nat.ltb (R.handle_rank owner)
        (R.handle_rank next) = true).
      { eapply Restart.owner_may_pop_higher; eauto. }
      assert (Hnext_queued : List.In next (R.queue st)).
      {
        unfold R.queue_pop in Hpop.
        destruct (R.queue st) as [|head rest] eqn:Hqueue;
          cbn in Hpop; try discriminate.
        inversion Hpop; subst. now left.
      }
      assert (Hnext_supported :
        List.In (R.handle_variable next) (Sem.support finite)).
      {
        pose proof (reachable_config_supported finite Hreachable)
          as Hsupported.
        exact (queue_is_supported (proj1 Hsupported) next Hnext_queued).
      }
      set (child_base := R.KSolveOneLoop owner base).
      set (child :=
        {| R.cfg_state := R.with_queue st tail;
           R.cfg_control := R.RunSolveOne next child_base |}).
      assert (Hstep : Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunSolveOneLoop owner base |} child).
      {
        unfold Sem.step, child, child_base. cbn. rewrite Hmay, Hpop.
        destruct (V.eq_dec (R.handle_variable next)
          (R.handle_variable owner)); [contradiction |reflexivity].
      }
      assert (Hchild : Sem.steps tf (R.initial_config roots) child).
      { eapply Sim.steps_append_one; eauto. }
      destruct (Hchildren next child_base child Hnext_supported Hhigher
        Hchild eq_refl) as [child_state [Hepisode Hchild_below]].
      unfold child_base in Hepisode.
      assert (Hreturned : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := child_state;
           R.cfg_control := R.RunSolveOneLoop owner base |}).
      {
        eapply Sim.steps_transitive; [exact Hchild |].
        exact (Sim.scoped_until_semantic Hepisode).
      }
      destruct (@bounded_solve_loop_reaches_boundary tf roots finite
        owner base Hexit Hchildren next child_state Hchild_below Hreturned)
        as [[done [Hdone Hdone_below]] |
            [pop_state [again_tail
              [Hagain [Hagain_may [Hagain_pop Hagain_below]]]]]].
      + left. exists done. split; [|exact Hdone_below].
        econstructor.
        * cbn. left. split; reflexivity.
        * exact Hstep.
        * eapply Sim.scoped_until_transitive.
          -- eapply Sim.scoped_until_lift.
             ++ apply Sim.ScopedContinuationSolve.
             ++ exact Hepisode.
          -- exact Hdone.
      + right. exists pop_state, again_tail. repeat split; try assumption.
        econstructor.
        * cbn. left. split; reflexivity.
        * exact Hstep.
        * eapply Sim.scoped_until_transitive.
          -- eapply Sim.scoped_until_lift.
             ++ apply Sim.ScopedContinuationSolve.
             ++ exact Hepisode.
          -- exact Hagain.
  Qed.

  Lemma run_rhs_reaches_boundary :
    forall tf roots (finite : Sem.finite_system tf roots) owner st base,
      reachable_exit_ready tf roots ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      List.In (R.handle_variable owner) (Sem.support finite) ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |} ->
      solve_loop_boundary tf owner base
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}.
  Proof.
    intros tf roots finite owner st base Hexit Hchildren Howner Hreachable.
    assert (Hbody : Sem.rhs_supported
      (supported (Sem.support finite))
      (tf (R.handle_variable owner))).
    {
      unfold supported. now apply Sem.system_supported.
    }
    destruct (@Episodes.run_rhs_finishes (Sem.support finite) tf roots owner
      Hchildren st (tf (R.handle_variable owner)) base Hbody Hreachable)
      as [after Hrhs].
    assert (Hafter : Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := after;
         R.cfg_control := R.RunSolveOneLoop owner base |}).
    {
      eapply Sim.steps_transitive; [exact Hreachable |].
      exact (Sim.scoped_until_semantic Hrhs).
    }
    destruct (@solve_loop_reaches_boundary tf roots finite owner base after
      Hexit Hchildren Hafter)
      as [[done [Hdone Hdone_below]] |
          [pop_state [tail [Hpop [Hmay [Hqueue Hbelow]]]]]].
    - left. exists done. split; [|exact Hdone_below].
      eapply Sim.scoped_until_transitive; eauto.
    - right. exists pop_state, tail. repeat split; try assumption.
      eapply Sim.scoped_until_transitive; eauto.
  Qed.


  Definition owner_round_complete
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (owner : R.handle) (entry : R.config) : Prop :=
    forall st base,
      entry =
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |} ->
      Sem.steps tf (R.initial_config roots) entry ->
      queue_strictly_below owner st ->
      Sim.episode_complete tf owner base entry.

  Lemma owner_rounds_complete :
    forall tf roots (finite : Sem.finite_system tf roots) owner,
      reachable_exit_ready tf roots ->
      List.In (R.handle_variable owner) (Sem.support finite) ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      forall entry, owner_round_complete tf roots owner entry.
  Proof.
    intros tf roots finite owner Hexit Howner Hchildren.
    apply (well_founded_induction_type
      (Measure.round_measure_lt_well_founded (Sem.support finite))).
    intros entry IH. unfold owner_round_complete.
    intros st base Hentry Hreachable Hbelow. subst entry.
    destruct (@run_rhs_reaches_boundary tf roots finite owner st base
      Hexit Hchildren Howner Hreachable)
      as [[done [Hdone Hdone_below]] |
          [pop_state [tail [Hboundary [Hmay [Hpop Hnext_below]]]]]].
    - exists done. now split.
    - set (popped :=
        {| R.cfg_state := R.with_queue pop_state tail;
           R.cfg_control := R.RunSolveOne owner base |}).
      set (next :=
        {| R.cfg_state := started_evaluation
             (R.with_queue pop_state tail) owner;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}).
      assert (Hpop_step : Sem.step tf
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} popped).
      {
        unfold Sem.step, popped. cbn. rewrite Hmay, Hpop.
        destruct (V.eq_dec (R.handle_variable owner)
          (R.handle_variable owner)); [reflexivity |contradiction].
      }
      assert (Hstart_step : Sem.step tf popped next).
      {
        unfold Sem.step, popped, next, started_evaluation.
        reflexivity.
      }
      assert (Hboundary_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |}).
      {
        eapply Sim.steps_transitive; [exact Hreachable |].
        exact (Sim.scoped_until_semantic Hboundary).
      }
      assert (Hnext_reachable :
        Sem.steps tf (R.initial_config roots) next).
      {
        eapply Sim.steps_append_one.
        - eapply Sim.steps_append_one; eauto.
        - exact Hstart_step.
      }
      assert (Hrestart : Payment.round_decreases (Sem.support finite)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |}).
      {
        eapply Restart.scoped_restart_decreases; eauto.
      }
      assert (Hadmin_steps : Sem.steps tf
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} next).
      {
        econstructor; [exact Hpop_step |].
        econstructor; [exact Hstart_step |constructor].
      }
      assert (Hadmin_nonincreasing : Payment.round_nonincreasing
        (Sem.support finite)
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} next).
      {
        eapply Payment.supported_steps_nonincreasing.
        - exact (Sem.support_nodup finite).
        - eapply Payment.reachable_steps_supported; eauto.
      }
      assert (Hdecrease : Measure.round_measure_lt (Sem.support finite) next
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}).
      {
        apply Payment.round_decreases_measure.
        eapply Payment.round_decreases_left; eauto.
      }
      specialize (IH next Hdecrease).
      unfold owner_round_complete in IH.
      destruct (IH (started_evaluation
        (R.with_queue pop_state tail) owner) base eq_refl
        Hnext_reachable Hnext_below) as [final [Hrest Hfinal_below]].
      exists final. split; [|exact Hfinal_below].
      eapply Sim.scoped_until_transitive; [exact Hboundary |].
      econstructor.
      + cbn. left. split; reflexivity.
      + exact Hpop_step.
      + econstructor.
        * cbn. left. split; reflexivity.
        * exact Hstart_step.
        * exact Hrest.
  Qed.

  Theorem reachable_owner_rounds_complete :
    forall tf roots (finite : Sem.finite_system tf roots) owner,
      List.In (R.handle_variable owner) (Sem.support finite) ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      forall entry, owner_round_complete tf roots owner entry.
  Proof.
    intros tf roots finite owner Howner Hchildren.
    eapply owner_rounds_complete; eauto.
    apply reachable_exit_ready_proved.
  Qed.

  Lemma start_episode_complete :
    forall tf roots (finite : Sem.finite_system tf roots) owner,
      List.In (R.handle_variable owner) (Sem.support finite) ->
      Sim.higher_episodes_complete
        (Sem.support finite) tf roots owner ->
      forall st base,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOne owner base |} ->
        Sim.episode_complete tf owner base
          {| R.cfg_state := st;
             R.cfg_control := R.RunSolveOne owner base |}.
  Proof.
    intros tf roots finite owner Howner Hchildren st base Hreachable.
    set (started_state := started_evaluation st owner).
    set (started :=
      {| R.cfg_state := started_state;
         R.cfg_control := R.RunRhs owner
           (tf (R.handle_variable owner)) base |}).
    assert (Hstart : Sem.step tf
      {| R.cfg_state := st;
         R.cfg_control := R.RunSolveOne owner base |} started).
    { unfold Sem.step, started, started_state, started_evaluation.
      reflexivity. }
    assert (Hstarted : Sem.steps tf (R.initial_config roots) started).
    { eapply Sim.steps_append_one; eauto. }
    destruct (@run_rhs_reaches_boundary tf roots finite owner
      started_state base (@reachable_exit_ready_proved tf roots)
      Hchildren Howner Hstarted)
      as [[done [Hdone Hdone_below]] |
          [pop_state [tail [Hboundary [Hmay [Hpop Hnext_below]]]]]].
    - exists done. split; [|exact Hdone_below].
      econstructor.
      + cbn. left. split; reflexivity.
      + exact Hstart.
      + exact Hdone.
    - set (popped :=
        {| R.cfg_state := R.with_queue pop_state tail;
           R.cfg_control := R.RunSolveOne owner base |}).
      set (next_state := started_evaluation
        (R.with_queue pop_state tail) owner).
      set (next :=
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner
             (tf (R.handle_variable owner)) base |}).
      assert (Hpop_step : Sem.step tf
        {| R.cfg_state := pop_state;
           R.cfg_control := R.RunSolveOneLoop owner base |} popped).
      { unfold Sem.step, popped. cbn. rewrite Hmay, Hpop.
        destruct (V.eq_dec (R.handle_variable owner)
          (R.handle_variable owner)); [reflexivity |contradiction]. }
      assert (Hrestart_step : Sem.step tf popped next).
      { unfold Sem.step, popped, next, next_state,
          started_evaluation. reflexivity. }
      assert (Hnext : Sem.steps tf (R.initial_config roots) next).
      { eapply Sim.steps_append_one.
        - eapply Sim.steps_append_one.
          + eapply Sim.steps_transitive; [exact Hstarted |].
            exact (Sim.scoped_until_semantic Hboundary).
          + exact Hpop_step.
        - exact Hrestart_step. }
      pose proof (@reachable_owner_rounds_complete
        tf roots finite owner Howner Hchildren next) as Hcomplete.
      unfold owner_round_complete in Hcomplete.
      destruct (Hcomplete next_state base eq_refl Hnext Hnext_below)
        as [final [Hrest Hfinal_below]].
      exists final. split; [|exact Hfinal_below].
      econstructor.
      + cbn. left. split; reflexivity.
      + exact Hstart.
      + eapply Sim.scoped_until_transitive; [exact Hboundary |].
        econstructor.
        * cbn. left. split; reflexivity.
        * exact Hpop_step.
        * econstructor.
          -- cbn. left. split; reflexivity.
          -- exact Hrestart_step.
          -- exact Hrest.
  Qed.

  Definition episode_property
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (finite : Sem.finite_system tf roots) (owner : R.handle) : Prop :=
    forall base start,
      List.In (R.handle_variable owner) (Sem.support finite) ->
      Sem.steps tf (R.initial_config roots) start ->
      R.cfg_control start = R.RunSolveOne owner base ->
      Sim.episode_complete tf owner base start.

  Theorem all_episodes_complete :
    forall tf roots (finite : Sem.finite_system tf roots) owner,
      @episode_property tf roots finite owner.
  Proof.
    intros tf roots finite.
    apply (well_founded_induction_type
      (well_founded_ltof R.handle
        (fun owner =>
          RankFinite.bound (Sem.support finite) - R.handle_rank owner))).
    intros owner IH. unfold episode_property.
    intros base [st control] Howner Hreachable Hcontrol.
    cbn in Hcontrol. subst control.
    eapply start_episode_complete; eauto.
    intros target child_base child Htarget Hhigher Hchild Hchild_control.
    eapply IH.
    - unfold ltof. apply Nat.ltb_lt in Hhigher.
      pose proof (reachable_handles_valid Hchild) as Hvalid.
      pose proof (handles_control_valid Hvalid) as Hcontrol_valid.
      rewrite Hchild_control in Hcontrol_valid. cbn in Hcontrol_valid.
      pose proof (@reachable_rank_bound tf roots finite child
        (R.handle_variable target) (R.handle_rank target) Hchild
        (proj1 Hcontrol_valid)) as Hbound.
      lia.
    - exact Htarget.
    - exact Hchild.
    - exact Hchild_control.
  Qed.

  Definition base_continuation (mode : option (list V.t)) : R.continuation :=
    match mode with
    | None => R.KLoop
    | Some remaining => R.KSeedLoop remaining
    end.

  Definition base_control (mode : option (list V.t)) : R.control :=
    R.continue (base_continuation mode).

  Lemma queue_pop_member :
    forall queue owner tail,
      R.queue_pop queue = Some (owner, tail) -> List.In owner queue.
  Proof.
    intros queue owner tail Hpop. destruct queue as [|head rest];
      cbn in Hpop; try discriminate. inversion Hpop. now left.
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
    assert (Howner : List.In (R.handle_variable owner) (Sem.support finite)).
    { pose proof (reachable_config_supported finite Hreachable)
        as [Hstate _].
      exact (proj1 (@queue_supported_pop (Sem.support finite)
        (R.queue st) owner tail (queue_is_supported Hstate) Hpop)). }
    set (child :=
      {| R.cfg_state := R.with_queue st tail;
         R.cfg_control := R.RunSolveOne owner (base_continuation mode) |}).
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st; R.cfg_control := base_control mode |} child).
    { unfold Sem.step, child, base_control, base_continuation.
      destruct mode; cbn; rewrite Hpop; reflexivity. }
    assert (Hchild : Sem.steps tf (R.initial_config roots) child).
    { eapply Sim.steps_append_one; eauto. }
    destruct (@all_episodes_complete tf roots finite owner
      (base_continuation mode) child Howner Hchild eq_refl)
      as [done [Hepisode Hbelow]].
    exists done. split; [|exact Hbelow].
    econstructor; [exact Hstep |].
    exact (Sim.scoped_until_semantic Hepisode).
  Qed.

  Definition drain_below_property
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (finite : Sem.finite_system tf roots) (upper : R.handle) : Prop :=
    forall mode st,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := base_control mode |} ->
      queue_strictly_below upper st ->
      exists final,
        Sem.steps tf
          {| R.cfg_state := st; R.cfg_control := base_control mode |}
          {| R.cfg_state := final; R.cfg_control := base_control mode |} /\
        R.queue_pop (R.queue final) = None.

  Theorem drain_below_complete :
    forall tf roots (finite : Sem.finite_system tf roots) upper,
      @drain_below_property tf roots finite upper.
  Proof.
    intros tf roots finite.
    apply (well_founded_induction_type
      (well_founded_ltof R.handle R.handle_rank)).
    intros upper IH. unfold drain_below_property.
    intros mode st Hreachable Hbelow.
    destruct (R.queue_pop (R.queue st)) as [[owner tail]|] eqn:Hpop.
    - assert (Hmember : List.In owner (R.queue st))
        by (eapply queue_pop_member; eauto).
      assert (Hlower : R.handle_rank owner < R.handle_rank upper)
        by exact (Hbelow owner Hmember).
      destruct (@popped_episode_complete tf roots finite mode st owner tail
        Hreachable Hpop) as [done [Hepisode Hdone_below]].
      assert (Hdone_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := done; R.cfg_control := base_control mode |}).
      { eapply Sim.steps_transitive; eauto. }
      destruct (IH owner Hlower mode done Hdone_reachable Hdone_below)
        as [final [Hrest Hempty]].
      exists final. split; [|exact Hempty].
      eapply Sim.steps_transitive; eauto.
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
    destruct (R.queue_pop (R.queue st)) as [[owner tail]|] eqn:Hpop.
    - destruct (@popped_episode_complete tf roots finite mode st owner tail
        Hreachable Hpop) as [done [Hepisode Hbelow]].
      assert (Hdone_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := done; R.cfg_control := base_control mode |}).
      { eapply Sim.steps_transitive; eauto. }
      destruct (@drain_below_complete tf roots finite owner mode done
        Hdone_reachable Hbelow) as [final [Hrest Hempty]].
      exists final. split; [|exact Hempty].
      eapply Sim.steps_transitive; eauto.
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
    intros tf roots finite remaining. induction remaining as [|root remaining IH];
      intros st Hreachable.
    - assert (Hstep : Sem.step tf
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds [] |}
        {| R.cfg_state := st; R.cfg_control := base_control None |})
        by (unfold Sem.step, base_control, base_continuation; reflexivity).
      assert (Hloop : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := base_control None |}).
      { eapply Sim.steps_append_one; eauto. }
      destruct (@drain_queue_complete tf roots finite None st Hloop)
        as [final [Hdrain Hempty]].
      exists final. split.
      + econstructor; [exact Hstep |exact Hdrain].
      + unfold Sem.quiescent, R.queue_peek, R.queue_pop in *.
        destruct (R.queue final); [reflexivity |discriminate].
    - destruct (R.observe st root) as [observed owner] eqn:Hobserve.
      destruct (S.mem root (R.started observed)) eqn:Hstarted.
      + assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunSeeds (root :: remaining) |}
          {| R.cfg_state := observed;
             R.cfg_control := R.RunSeeds remaining |}).
        { unfold Sem.step. cbn. rewrite Hobserve, Hstarted. reflexivity. }
        assert (Hnext : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := observed; R.cfg_control := R.RunSeeds remaining |}).
        { eapply Sim.steps_append_one; eauto. }
        destruct (IH observed Hnext) as [final [Hrest Hquiet]].
        exists final. split; [|exact Hquiet].
        econstructor; eauto.
      + assert (Hroot : List.In (R.handle_variable owner)
          (Sem.support finite)).
        { pose proof (reachable_config_supported finite Hreachable)
            as [_ Hcontrol]. cbn in Hcontrol. inversion Hcontrol; subst.
          rewrite (@observed_handle_variable st root observed owner Hobserve).
          assumption. }
        set (child :=
          {| R.cfg_state := observed;
             R.cfg_control := R.RunSolveOne owner (R.KSeedLoop remaining) |}).
        assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunSeeds (root :: remaining) |} child).
        { unfold Sem.step, child. cbn. rewrite Hobserve, Hstarted. reflexivity. }
        assert (Hchild : Sem.steps tf (R.initial_config roots) child).
        { eapply Sim.steps_append_one; eauto. }
        destruct (@all_episodes_complete tf roots finite owner
          (R.KSeedLoop remaining) child Hroot Hchild eq_refl)
          as [done [Hepisode Hbelow]].
        assert (Hdone : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := done; R.cfg_control := base_control (Some remaining) |}).
        { eapply Sim.steps_transitive; [exact Hchild |].
          exact (Sim.scoped_until_semantic Hepisode). }
        destruct (@drain_below_complete tf roots finite owner (Some remaining)
          done Hdone Hbelow) as [drained [Hdrain Hempty]].
        assert (Hadmin : Sem.step tf
          {| R.cfg_state := drained;
             R.cfg_control := base_control (Some remaining) |}
          {| R.cfg_state := drained; R.cfg_control := R.RunSeeds remaining |}).
        { unfold Sem.step, base_control, base_continuation. cbn.
          rewrite Hempty. reflexivity. }
        assert (Hnext : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := drained; R.cfg_control := R.RunSeeds remaining |}).
        { eapply Sim.steps_append_one.
          - eapply Sim.steps_transitive; [exact Hdone |exact Hdrain].
          - exact Hadmin. }
        destruct (IH drained Hnext) as [final [Hrest Hquiet]].
        exists final. split; [|exact Hquiet].
        econstructor; [exact Hstep |].
        eapply Sim.steps_transitive.
        * exact (Sim.scoped_until_semantic Hepisode).
        * eapply Sim.steps_transitive; [exact Hdrain |].
          econstructor; eauto.
  Qed.

  Theorem solver_reaches_terminal :
    forall tf roots (finite : Sem.finite_system tf roots),
      exists final,
        Sem.steps tf (R.initial_config roots) (Sem.terminal_config final) /\
        Sem.quiescent final.
  Proof.
    intros tf roots finite.
    apply (@seeds_reach_terminal tf roots finite roots
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



  Definition queued (st : R.state) (x : V.t) : Prop :=
    Restart.queued_variable st x.

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

  Definition aggregate_sound := ExitReady.aggregate_sound.

  Definition aggregate_guarded (c : R.config) : Prop :=
    forall target,
      queued (R.cfg_state c) target \/
      control_active target (R.cfg_control c) \/
      aggregate_sound (R.cfg_state c) target.

  Lemma aggregate_sound_empty :
    forall target, aggregate_sound R.empty_state target.
  Proof.
    intros. unfold aggregate_sound, ExitReady.aggregate_sound,
      R.aggregate, R.lookup_map, R.sigma_value. cbn.
    rewrite ML.lookup_empty, ML.values_empty, ML.lookup_empty.
    cbn. apply DL.leq_refl.
  Qed.

  Lemma aggregate_sound_with_queue :
    forall st queue target,
      aggregate_sound st target ->
      aggregate_sound (R.with_queue st queue) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_sound_with_started :
    forall st started target,
      aggregate_sound st target ->
      aggregate_sound (R.with_started st started) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_sound_enqueue_handle :
    forall st inserted target,
      aggregate_sound st target ->
      aggregate_sound (R.enqueue_handle st inserted) target.
  Proof. intros. exact H. Qed.

  Lemma aggregate_sound_materialize :
    forall st inserted target,
      aggregate_sound st target ->
      aggregate_sound (R.materialize st inserted) target.
  Proof.
    intros st inserted target Hsound.
    unfold aggregate_sound, ExitReady.aggregate_sound in *.
    rewrite ExitReady.aggregate_materialize,
      Payment.sigma_value_materialize. exact Hsound.
  Qed.

  Lemma initial_aggregate_guarded :
    forall roots, aggregate_guarded (R.initial_config roots).
  Proof.
    intros roots target. right. right. apply aggregate_sound_empty.
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

  Lemma aggregate_guarded_step :
    forall tf before after,
      handles_valid before ->
      aggregate_guarded before ->
      Sem.step tf before after ->
      aggregate_guarded after.
  Proof.
    intros tf [st control] after Hvalid Hguard Hstep target.
    pose proof (Hguard target) as Htarget.
    unfold Sem.step in Hstep. cbn in Hvalid, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    - destruct (V.eq_dec target (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. eapply queued_pop_other; eauto.
        * contradiction.
        * right. right. now apply aggregate_sound_with_queue.
    - exact Htarget.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. eapply ExitReady.queued_observe; eauto.
      + contradiction.
      + right. right. eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. eapply ExitReady.queued_observe; eauto.
      + contradiction.
      + right. right. eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct (V.eq_dec target (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. eapply queued_pop_other; eauto.
        * contradiction.
        * right. right. now apply aggregate_sound_with_queue.
    - exact Htarget.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. unfold queued in *. cbn.
        eapply ExitReady.queued_start; eauto.
      + now right; left.
      + right. right. apply aggregate_sound_with_started,
          ExitReady.aggregate_sound_start. exact Hsound.
    - destruct (V.eq_dec target (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. eapply queued_pop_other; eauto.
          intro Heq. apply Hneq. rewrite Heq. exact e.
        * now right; left.
        * right. right. now apply aggregate_sound_with_queue.
    - destruct (V.eq_dec target (R.handle_variable h0)) as [-> | Hneq].
      + right. left. now left.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. eapply queued_pop_other; eauto.
        * right. left. cbn. tauto.
        * right. right. now apply aggregate_sound_with_queue.
    - destruct Htarget as [Hqueued | [[Howner | Hactive] | Hsound]].
      + now left.
      + right. right. subst target. exact Hcase0.
      + right. left. now apply continuation_active_continue.
      + now right; right.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. now apply ExitReady.queued_set_value.
      + now right; left.
      + right. right. now apply ExitReady.aggregate_sound_set_value.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. apply ExitReady.queued_get_ready.
        eapply ExitReady.queued_observe; eauto.
      + now right; left.
      + right. right. apply ExitReady.aggregate_sound_get_ready.
        eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. eapply ExitReady.queued_observe; eauto.
      + right. left. cbn. tauto.
      + right. right. eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct (V.eq_dec target (R.handle_variable h0)) as [Heq | Hneq].
      + subst target. left. unfold queued.
        apply ExitReady.queued_get_ready.
        apply ExitReady.enqueue_handle_queues_variable.
        * eapply rank_valid_observe;
            [exact (handles_rank_valid Hvalid) |exact Hcase0].
        * eapply queue_valid_observe;
            [exact (handles_queue_valid Hvalid) |exact Hcase0].
        * eapply observed_handle_valid; eauto.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. apply ExitReady.queued_get_ready,
            ExitReady.queued_enqueue_handle.
          eapply ExitReady.queued_observe; eauto.
        * now right; left.
        * right. right. apply ExitReady.aggregate_sound_get_ready,
            aggregate_sound_enqueue_handle.
          eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct (V.eq_dec target (R.handle_variable h0)) as [-> | Hneq].
      + right. left. now left.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. apply ExitReady.queued_side_ready.
          eapply ExitReady.queued_observe; eauto.
        * right. left. cbn. tauto.
        * right. right. eapply ExitReady.aggregate_sound_side_other;
            [exact Hneq |].
          eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct (V.eq_dec target (R.handle_variable h0)) as [-> | Hneq].
      + left. unfold queued.
        apply ExitReady.enqueue_handle_queues_variable.
        * apply rank_valid_side_ready.
          eapply rank_valid_observe;
            [exact (handles_rank_valid Hvalid) |exact Hcase0].
        * apply queue_valid_side_ready.
          eapply queue_valid_observe;
            [exact (handles_queue_valid Hvalid) |exact Hcase0].
        * eapply handle_valid_extended.
          -- apply rank_extends_side_ready.
          -- eapply observed_handle_valid; eauto.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. apply ExitReady.queued_enqueue_handle,
            ExitReady.queued_side_ready.
          eapply ExitReady.queued_observe; eauto.
        * now right; left.
        * right. right. apply aggregate_sound_enqueue_handle.
          eapply ExitReady.aggregate_sound_side_other; [exact Hneq |].
          eapply ExitReady.aggregate_sound_observe; eauto.
    - apply Bool.negb_false_iff in Hcase1.
      pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      destruct (V.eq_dec target (R.handle_variable h0)) as [Heq | Hneq].
      + subst target. destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. apply ExitReady.queued_side_ready.
          eapply ExitReady.queued_observe; eauto.
        * now right; left.
        * right. right. eapply ExitReady.aggregate_sound_side_covered.
          -- rewrite Hvariable. exact Hcase1.
          -- eapply ExitReady.aggregate_sound_observe; eauto.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. apply ExitReady.queued_side_ready.
          eapply ExitReady.queued_observe; eauto.
        * now right; left.
        * right. right. eapply ExitReady.aggregate_sound_side_other;
            [exact Hneq |].
          eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. eapply ExitReady.queued_observe; eauto.
      + now right; left.
      + right. right. eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. eapply ExitReady.queued_observe; eauto.
      + right. left. cbn. tauto.
      + right. right. eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct (V.eq_dec target (R.handle_variable h0)) as [Heq | Hneq].
      + subst target. left.
        assert (Hqueued : queued (R.enqueue_handle s h0)
          (R.handle_variable h0)).
        { unfold queued. apply ExitReady.enqueue_handle_queues_variable.
          - eapply rank_valid_observe;
              [exact (handles_rank_valid Hvalid) |exact Hcase0].
          - eapply queue_valid_observe;
              [exact (handles_queue_valid Hvalid) |exact Hcase0].
          - eapply observed_handle_valid; eauto. }
        unfold queued, R.materialize in *.
        destruct (R.is_materialized (R.enqueue_handle s h0) t);
          exact Hqueued.
      + destruct Htarget as [Hqueued | [Hactive | Hsound]].
        * left. unfold queued, R.materialize in *.
          destruct (R.is_materialized (R.enqueue_handle s h0) t);
            apply ExitReady.queued_enqueue_handle;
            eapply ExitReady.queued_observe; eauto.
        * now right; left.
        * right. right. apply aggregate_sound_materialize,
            aggregate_sound_enqueue_handle.
          eapply ExitReady.aggregate_sound_observe; eauto.
    - destruct Htarget as [Hqueued | [Hactive | Hsound]].
      + left. now apply ExitReady.queued_get_ready.
      + now right; left.
      + right. right. now apply ExitReady.aggregate_sound_get_ready.
    - exact Htarget.
    - exact Htarget.
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

  Theorem terminal_aggregate_sound :
    forall tf roots final,
      Sem.terminates_to tf roots final ->
      forall target, aggregate_sound final target.
  Proof.
    intros tf roots final [Hsteps Hquiet] target.
    pose proof (@aggregate_guarded_steps tf
      (R.initial_config roots) (Sem.terminal_config final)
      (initial_handles_valid roots)
      (initial_aggregate_guarded roots) Hsteps target) as Hguard.
    destruct Hguard as [Hqueued | [Hactive | Hsound]].
    - destruct Hqueued as [entry [Hentry _]].
      cbn in Hentry.
      unfold Sem.quiescent, R.queue_peek in Hquiet.
      destruct (R.queue final) as [|head tail] eqn:Hqueue.
      + exfalso. exact Hentry.
      + discriminate Hquiet.
    - contradiction.
    - exact Hsound.
  Qed.

  Definition read_event := (V.t * D.t)%type.
  Definition side_effect := (V.t * D.t)%type.

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
        rhs_trace next direct reads effects ->
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
        rhs_prefix next current reads effects ->
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
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
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
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
    - cbn. constructor. eapply IHHprefix. exact Hcurrent.
  Qed.

  Lemma rhs_prefix_snoc_spawn :
    forall original target next reads effects,
      rhs_prefix original (R.ConstraintSystem.Spawn target next)
        reads effects ->
      rhs_prefix original next reads effects.
  Proof.
    intros original target next reads effects Hprefix.
    remember (R.ConstraintSystem.Spawn target next) as current eqn:Hcurrent.
    revert target next Hcurrent.
    induction Hprefix; intros target0 next0 Hcurrent.
    - inversion Hcurrent; subst. constructor. constructor.
    - constructor. eapply IHHprefix. exact Hcurrent.
    - constructor. eapply IHHprefix. exact Hcurrent.
    - constructor. eapply IHHprefix. exact Hcurrent.
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
    - constructor. eapply IHHprefix. exact Hcurrent.
    - constructor. eapply IHHprefix. exact Hcurrent.
    - constructor. eapply IHHprefix. exact Hcurrent.
  Qed.

  Definition reader_registered
    (st : R.state) (reader target : V.t) : Prop :=
    S.mem reader (R.lookup_set (R.readers st) target) = true.

  Definition read_guarded
    (st : R.state) (owner : V.t) (event : read_event) : Prop :=
    Progress.solved st (fst event) /\
    (reader_registered st owner (fst event) \/ queued st owner) /\
    (snd event = R.sigma_value st (fst event) \/ queued st owner).

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

  Lemma lookup_update_map_same :
    forall A (table : M.t (M.t A)) outer inner value,
      M.lookup (R.lookup_map
        (R.update_map table outer inner value) outer) inner = Some value.
  Proof.
    intros. unfold R.update_map, R.lookup_map.
    rewrite ML.lookup_update_same. apply ML.lookup_update_same.
  Qed.

  Lemma value_below_join_values :
    forall value values,
      List.In value values -> D.leq value (R.join_values values) = true.
  Proof.
    intros value values Hin. induction values as [|head rest IH]; cbn in *.
    - contradiction.
    - destruct Hin as [-> | Hin].
      + apply DL.join_upper_left.
      + eapply DL.leq_trans; [now apply IH |apply DL.join_upper_right].
  Qed.

  Lemma stored_value_below_aggregate :
    forall st source target value,
      M.lookup (R.lookup_map (R.contributions st) target) source =
        Some value ->
      D.leq value (R.aggregate st target) = true.
  Proof.
    intros. unfold R.aggregate. apply value_below_join_values.
    eapply ML.lookup_values. exact H.
  Qed.

  Lemma accumulated_side_input_upper_raw :
    forall st source target raw,
      D.leq raw (R.accumulated_side_input st source target raw) = true.
  Proof.
    intros. unfold R.accumulated_side_input.
    destruct (M.lookup (R.lookup_map (R.local_sides st) source) target);
      [apply DL.join_upper_right |apply DL.leq_refl].
  Qed.

  Lemma accumulated_side_input_upper_previous :
    forall st source target raw previous,
      M.lookup (R.lookup_map (R.local_sides st) source) target =
        Some previous ->
      D.leq previous
        (R.accumulated_side_input st source target raw) = true.
  Proof.
    intros. unfold R.accumulated_side_input. rewrite H.
    apply DL.join_upper_left.
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
    apply Accounting.lookup_update_map_other_inner. exact H.
  Qed.

  Lemma stored_contribution_record_side :
    forall st source target raw,
      R.stored_contribution
        (R.record_side_payload st source target raw) source target =
      snd (U.update true target
        (R.stored_side_phase st source target)
        (R.stored_contribution st source target)
        (R.accumulated_side_input st source target raw)).
  Proof.
    intros. unfold R.record_side_payload, R.stored_contribution. cbn.
    rewrite lookup_update_map_same. reflexivity.
  Qed.

  Lemma record_side_input_below_contribution :
    forall st source target raw,
      D.leq (R.accumulated_side_input st source target raw)
        (R.stored_contribution
          (R.record_side_payload st source target raw) source target) = true.
  Proof.
    intros. rewrite stored_contribution_record_side. apply UL.update_sound.
  Qed.

  Lemma record_side_raw_below_contribution :
    forall st source target raw,
      D.leq raw
        (R.stored_contribution
          (R.record_side_payload st source target raw) source target) = true.
  Proof.
    intros. eapply DL.leq_trans.
    - apply accumulated_side_input_upper_raw.
    - apply record_side_input_below_contribution.
  Qed.

  Lemma set_value_direct_below :
    forall st owner direct,
      D.leq direct (R.sigma_value (R.set_value st owner direct) owner) = true.
  Proof.
    intros. eapply DL.leq_trans.
    - apply DL.join_upper_left.
    - apply ExitReady.set_value_candidate_below.
  Qed.

  Lemma effect_accumulated_record_new :
    forall st source target raw,
      effect_accumulated
        (R.record_side_payload st source target raw)
        source (target, raw).
  Proof.
    intros. exists (R.accumulated_side_input st source target raw). split.
    - apply local_side_record_same.
    - apply accumulated_side_input_upper_raw.
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
      rewrite Accounting.lookup_update_map_other_outer by exact Hneq.
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
      right. unfold queued in *. now apply ExitReady.queued_enqueue_handle.
    - destruct Hvalue as [Hvalue | Hqueued]; [now left |].
      right. unfold queued in *. now apply ExitReady.queued_enqueue_handle.
  Qed.

  Lemma reads_guarded_enqueue_handle :
    forall st inserted owner reads,
      reads_guarded st owner reads ->
      reads_guarded (R.enqueue_handle st inserted) owner reads.
  Proof.
    intros. eapply Forall_impl; [|exact H].
    intros. now apply read_guarded_enqueue_handle.
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
    - apply Progress.solved_materialize.
      unfold R.add_reader, st1, R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued].
      + left. apply reader_registered_materialize,
          reader_registered_add_preserved.
        unfold st1, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Hregistered.
      + right. unfold queued in *.
        now apply ExitReady.queued_get_ready.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. rewrite Payment.sigma_value_materialize.
        unfold st1, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Hvalue.
      + right. unfold queued in *.
        now apply ExitReady.queued_get_ready.
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
    - unfold R.get_ready_state. apply Progress.solved_materialize_self.
    - left. unfold R.get_ready_state.
      apply reader_registered_materialize, reader_registered_add.
    - left. reflexivity.
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

  Lemma rhs_progress_spawn :
    forall tf st owner target next,
      rhs_progress tf st owner (R.ConstraintSystem.Spawn target next) ->
      rhs_progress tf st owner next.
  Proof.
    intros tf st owner target next
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try assumption.
    eapply rhs_prefix_snoc_spawn. exact Hprefix.
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
    apply ExitReady.enqueue_handle_queues_variable.
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
    - unfold queued. apply ExitReady.queued_enqueue_all.
      unfold queued in *. now apply enqueue_queues_variable.
    - apply IH; [exact Hin |now apply rank_valid_enqueue |].
      now apply queue_valid_enqueue.
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
        rewrite Restart.readers_enqueue_all.
        rewrite ML.lookup_update_other by exact Hneq. exact Hregistered.
    - right. unfold queued in *.
      unfold R.write_changed_value. cbn.
      now apply ExitReady.queued_enqueue_all.
  Qed.

  Lemma read_guarded_write_changed_value :
    forall st reader event owner value,
      rank_valid st -> queue_valid st ->
      read_guarded st reader event ->
      read_guarded (R.write_changed_value st owner value) reader event.
  Proof.
    intros st reader [target observed] owner value Hrank Hqueue
      [Hsolved [Hread Hvalue]]. repeat split.
    - apply Progress.solved_write_changed_value. exact Hsolved.
    - eapply read_obligation_write_changed_value; eauto.
    - destruct Hvalue as [Heq | Hqueued].
      + destruct (V.eq_dec target owner) as [-> | Hneq].
        * right. destruct Hread as [Hregistered | Hqueued].
          -- unfold R.write_changed_value. cbn. apply enqueue_all_contains.
             ++ apply SL.mem_spec. exact Hregistered.
             ++ exact Hrank.
             ++ exact Hqueue.
          -- unfold queued in *. unfold R.write_changed_value. cbn.
             now apply ExitReady.queued_enqueue_all.
        * left. unfold R.write_changed_value, R.sigma_value. cbn.
          rewrite Accounting.sigma_enqueue_all. cbn.
          rewrite ML.lookup_update_other by exact Hneq. exact Heq.
      + right. unfold queued in *. unfold R.write_changed_value. cbn.
        now apply ExitReady.queued_enqueue_all.
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
    unfold R.write_changed_value. cbn.
    rewrite Accounting.contributions_enqueue_all. exact Hrecorded.
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
    - apply set_value_direct_below.
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
      destruct Hguarded as [[actual Hlookup] [_ Hvalue]].
      destruct Hvalue as [Heq | Hqueued]; [|contradiction].
      unfold R.sigma_value in Heq. rewrite Hlookup in Heq. subst.
      constructor; [exact Hlookup |]. apply IHHtrace; assumption.
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
      | Hleft : M.lookup (R.sigma st) ?target = Some ?left,
        Hright : M.lookup (R.sigma st) ?target = Some ?right |- _ =>
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

  Lemma read_guarded_materialize :
    forall st reader event target,
      read_guarded st reader event ->
      read_guarded (R.materialize st target) reader event.
  Proof.
    intros st reader [observed value] target
      [Hsolved [Hregistered Hvalue]]. repeat split.
    - apply Progress.solved_materialize. exact Hsolved.
    - destruct Hregistered as [Hregistered | Hqueued].
      + left. now apply reader_registered_materialize.
      + right. unfold queued in *. unfold R.materialize.
        destruct (R.is_materialized st target); exact Hqueued.
    - destruct Hvalue as [Hvalue | Hqueued].
      + left. rewrite Payment.sigma_value_materialize. exact Hvalue.
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
    all: try (rewrite Accounting.lookup_update_map_other_outer
      by exact Htarget; exact Hlookup).
    all: rewrite Accounting.lookup_update_map_other_inner by exact Hneq;
      exact Hlookup.
  Qed.

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
    - rewrite Payment.sigma_value_materialize. exact Hdirect.
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
    - rewrite (@Payment.sigma_value_observe
        st observed next entry owner Hobserve). exact Hdirect.
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
    - rewrite Payment.sigma_value_start_evaluation. exact Hdirect.
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
      + apply Progress.solved_get_ready. exact Hsolved.
      + destruct Hregistered as [Hregistered | Hqueued].
        * left. unfold R.get_ready_state.
          apply reader_registered_materialize,
            reader_registered_add_preserved.
          unfold R.promote_controlled.
          destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
            exact Hregistered.
        * right. unfold queued in *.
          now apply ExitReady.queued_get_ready.
      + destruct Hvalue as [Hvalue | Hqueued].
        * left. rewrite Payment.sigma_value_get_ready. exact Hvalue.
        * right. unfold queued in *.
          now apply ExitReady.queued_get_ready.
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
    - rewrite Payment.sigma_value_get_ready. exact Hdirect.
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
    - rewrite Payment.sigma_value_set_value_other by exact Hneq.
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
    - rewrite Payment.sigma_value_side_ready. exact Hbelow.
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
    all: rewrite Accounting.lookup_update_map_other_outer by exact Hneq;
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

  Lemma rhs_progress_observe :
    forall tf st observed next entry owner body,
      R.observe st observed = (next, entry) ->
      rhs_progress tf st owner body -> rhs_progress tf next owner body.
  Proof.
    intros tf st observed next entry owner body Hobserve
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - eapply reads_guarded_observe; eauto.
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) observed);
        inversion Hobserve; subst; exact Hrecorded.
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) observed);
        inversion Hobserve; subst; exact Haccumulated.
  Qed.

  Lemma rhs_progress_enqueue_handle :
    forall tf st inserted owner body,
      rhs_progress tf st owner body ->
      rhs_progress tf (R.enqueue_handle st inserted) owner body.
  Proof.
    intros tf st inserted owner body
      [reads [effects [Hprefix [Hreads [Hrecorded Haccumulated]]]]].
    exists reads, effects. repeat split; try exact Hprefix.
    - apply reads_guarded_enqueue_handle. exact Hreads.
    - exact Hrecorded.
    - exact Haccumulated.
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
      + apply Progress.solved_get_ready. exact Hsolved.
      + destruct Hregistered as [Hregistered | Hqueued].
        * left. unfold R.get_ready_state.
          apply reader_registered_materialize,
            reader_registered_add_preserved.
          unfold R.promote_controlled.
          destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
            exact Hregistered.
        * right. unfold queued in *.
          now apply ExitReady.queued_get_ready.
      + destruct Hvalue as [Hvalue | Hqueued].
        * left. rewrite Payment.sigma_value_get_ready. exact Hvalue.
        * right. unfold queued in *.
          now apply ExitReady.queued_get_ready.
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
      Restart.continuation_ordered lower k ->
      Restart.continuation_ordered upper k.
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
      Restart.continuation_ordered upper k ->
      continuation_excludes (R.handle_variable upper) k.
  Proof.
    intros st upper k Hupper. revert upper Hupper.
    induction k; intros upper Hupper Hvalid Hordered; cbn in *; try exact I.
    all: destruct Hvalid as [Hhead_valid Htail_valid].
    all: destruct Hordered as [Hhead_order Htail_order].
    all: apply Nat.ltb_lt in Hhead_order; split.
    all: try (eapply ExitReady.valid_ranked_variables_differ; eauto).
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

  Lemma continuation_valid_observe :
    forall st observed next entry k,
      R.observe st observed = (next, entry) ->
      continuation_valid st k ->
      continuation_valid next k.
  Proof.
    intros. eapply continuation_valid_extended; [|exact H0].
    eapply rank_extends_observe; eauto.
  Qed.

  Lemma control_history_step :
    forall tf before after,
      handles_valid before ->
      Restart.control_ordered (R.cfg_control before) ->
      control_history tf (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      control_history tf (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hvalid Hordered Hhistory Hstep.
    unfold Sem.step in Hstep. cbn in Hvalid, Hordered, Hhistory, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I.
    - split.
      + apply rhs_progress_with_started, initial_rhs_progress.
      + apply continuation_history_with_started, continuation_history_start.
        * pose proof (handles_control_valid Hvalid) as Hcontrol.
          cbn in Hcontrol. eapply continuation_ordered_excludes; eauto.
          exact (proj1 Hcontrol). exact (proj2 Hcontrol).
        * exact Hhistory.
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      cbn in Hcontrol.
      assert (Hequal : h0 = h).
      { eapply same_variable_valid_handle_equal.
        - exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
        - exact (proj1 Hcontrol).
        - exact e. }
      subst h0. eapply continuation_history_pop; eauto.
      eapply continuation_ordered_excludes.
      + exact (proj1 Hcontrol).
      + exact (proj2 Hcontrol).
      + exact Hordered.
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      cbn in Hcontrol.
      assert (Hhigher : R.handle_rank h < R.handle_rank h0).
      { apply Nat.ltb_lt. eapply Restart.owner_may_pop_higher; eauto. }
      eapply continuation_history_pop; eauto.
      eapply continuation_ordered_excludes.
      + exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
      + exact (proj2 Hcontrol).
      + eapply continuation_ordered_weaken; eauto.
    - now apply continuation_history_continue.
    - eapply continuation_history_set_value.
      + exact (handles_rank_valid Hvalid).
      + exact (handles_queue_valid Hvalid).
      + exact (proj2 Hhistory).
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory |- *.
      destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_get. eapply rhs_progress_observe; eauto.
      + apply continuation_history_get_ready.
        eapply continuation_history_observe; eauto.
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory.
      destruct Hhistory as [Hprogress Hrest]. split;
        [eapply rhs_progress_observe |eapply continuation_history_observe];
        eauto.
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory |- *.
      destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_get, rhs_progress_enqueue_handle.
        eapply rhs_progress_observe; eauto.
      + apply continuation_history_get_ready,
          continuation_history_enqueue_handle.
        eapply continuation_history_observe; eauto.
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory.
      destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_side. eapply rhs_progress_observe; eauto.
      + apply continuation_history_side.
        * pose proof (handles_control_valid Hvalid) as Hcontrol.
          cbn in Hcontrol. eapply continuation_ordered_excludes.
          -- eapply handle_valid_extended.
             ++ eapply rank_extends_observe; eauto.
             ++ exact (proj1 Hcontrol).
          -- eapply continuation_valid_observe; eauto.
             exact (proj2 Hcontrol).
          -- exact Hordered.
        * eapply continuation_history_observe; eauto.
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory.
      destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_enqueue_handle, rhs_progress_side.
        eapply rhs_progress_observe; eauto.
      + apply continuation_history_enqueue_handle, continuation_history_side.
        * pose proof (handles_control_valid Hvalid) as Hcontrol.
          cbn in Hcontrol. eapply continuation_ordered_excludes.
          -- eapply handle_valid_extended.
             ++ eapply rank_extends_observe; eauto.
             ++ exact (proj1 Hcontrol).
          -- eapply continuation_valid_observe; eauto.
             exact (proj2 Hcontrol).
          -- exact Hordered.
        * eapply continuation_history_observe; eauto.
    - pose proof (@observed_handle_variable st t s h0 Hcase0)
        as Hvariable.
      rewrite <- Hvariable in Hhistory.
      destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_side. eapply rhs_progress_observe; eauto.
      + apply continuation_history_side.
        * pose proof (handles_control_valid Hvalid) as Hcontrol.
          cbn in Hcontrol. eapply continuation_ordered_excludes.
          -- eapply handle_valid_extended.
             ++ eapply rank_extends_observe; eauto.
             ++ exact (proj1 Hcontrol).
          -- eapply continuation_valid_observe; eauto.
             exact (proj2 Hcontrol).
          -- exact Hordered.
        * eapply continuation_history_observe; eauto.
    - destruct Hhistory as [Hprogress Hrest]. split.
      + eapply rhs_progress_spawn. eapply rhs_progress_observe; eauto.
      + eapply continuation_history_observe; eauto.
    - destruct Hhistory as [Hprogress Hrest]. split.
      + eapply rhs_progress_spawn. eapply rhs_progress_observe; eauto.
      + eapply continuation_history_observe; eauto.
    - destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_materialize, rhs_progress_enqueue_handle.
        eapply rhs_progress_spawn. eapply rhs_progress_observe; eauto.
      + apply continuation_history_materialize,
          continuation_history_enqueue_handle.
        eapply continuation_history_observe; eauto.
    - destruct Hhistory as [Hprogress Hrest]. split.
      + apply rhs_progress_get. exact Hprogress.
      + apply continuation_history_get_ready. exact Hrest.
    - exact Hhistory.
    - exact Hhistory.
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

  Lemma control_completed_step :
    forall tf before after,
      handles_valid before ->
      Restart.control_ordered (R.cfg_control before) ->
      control_history tf (R.cfg_state before) (R.cfg_control before) ->
      control_completed tf (R.cfg_state before) (R.cfg_control before) ->
      Sem.step tf before after ->
      control_completed tf (R.cfg_state after) (R.cfg_control after).
  Proof.
    intros tf [st control] after Hvalid Hordered Hhistory Hcompleted Hstep.
    unfold Sem.step in Hstep.
    cbn in Hvalid, Hordered, Hhistory, Hcompleted, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try exact I.
    - apply continuation_completed_with_started, continuation_completed_start.
      + pose proof (handles_control_valid Hvalid) as Hcontrol.
        cbn in Hcontrol. eapply continuation_ordered_excludes; eauto.
        exact (proj1 Hcontrol). exact (proj2 Hcontrol).
      + exact Hcompleted.
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      cbn in Hcontrol.
      assert (Hequal : h0 = h).
      { eapply same_variable_valid_handle_equal.
        - exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
        - exact (proj1 Hcontrol).
        - exact e. }
      subst h0. eapply continuation_completed_pop; eauto.
      eapply continuation_ordered_excludes.
      + exact (proj1 Hcontrol).
      + exact (proj2 Hcontrol).
      + exact Hordered.
      + exact (proj2 Hcompleted).
    - pose proof (handles_queue_valid Hvalid) as Hqueue.
      pose proof (handles_control_valid Hvalid) as Hcontrol.
      cbn in Hcontrol.
      assert (Hhigher : R.handle_rank h < R.handle_rank h0).
      { apply Nat.ltb_lt. eapply Restart.owner_may_pop_higher; eauto. }
      split.
      + eapply summary_pop_other; [exact Hcase0 | |exact (proj1 Hcompleted)].
        intro Heq. apply n. symmetry. exact Heq.
      + eapply continuation_completed_pop; eauto.
        eapply continuation_ordered_excludes.
        * exact (proj1 (@queue_pop_valid st h0 w Hqueue Hcase0)).
        * exact (proj2 Hcontrol).
        * eapply continuation_ordered_weaken; eauto.
        * exact (proj2 Hcompleted).
    - apply continuation_completed_continue. exact (proj2 Hcompleted).
    - split.
      + eapply rhs_progress_ret_summary.
        * exact (handles_rank_valid Hvalid).
        * exact (handles_queue_valid Hvalid).
        * exact (proj1 Hhistory).
      + eapply continuation_completed_set_value.
        * exact (handles_rank_valid Hvalid).
        * exact (handles_queue_valid Hvalid).
        * pose proof (handles_control_valid Hvalid) as Hcontrol.
          cbn in Hcontrol. eapply continuation_ordered_excludes; eauto.
          exact (proj1 Hcontrol). exact (proj2 Hcontrol).
        * exact Hcompleted.
    - apply continuation_completed_get_ready.
      eapply continuation_completed_observe; eauto.
    - eapply continuation_completed_observe; eauto.
    - apply continuation_completed_get_ready,
        continuation_completed_enqueue_handle.
      eapply continuation_completed_observe; eauto.
    - apply continuation_completed_side.
      + pose proof (handles_control_valid Hvalid) as Hcontrol.
        cbn in Hcontrol. eapply continuation_ordered_excludes.
        * eapply handle_valid_extended.
          -- eapply rank_extends_observe; eauto.
          -- exact (proj1 Hcontrol).
        * eapply continuation_valid_observe; eauto. exact (proj2 Hcontrol).
        * exact Hordered.
      + eapply continuation_completed_observe; eauto.
    - apply continuation_completed_enqueue_handle, continuation_completed_side.
      + pose proof (handles_control_valid Hvalid) as Hcontrol.
        cbn in Hcontrol. eapply continuation_ordered_excludes.
        * eapply handle_valid_extended.
          -- eapply rank_extends_observe; eauto.
          -- exact (proj1 Hcontrol).
        * eapply continuation_valid_observe; eauto. exact (proj2 Hcontrol).
        * exact Hordered.
      + eapply continuation_completed_observe; eauto.
    - apply continuation_completed_side.
      + pose proof (handles_control_valid Hvalid) as Hcontrol.
        cbn in Hcontrol. eapply continuation_ordered_excludes.
        * eapply handle_valid_extended.
          -- eapply rank_extends_observe; eauto.
          -- exact (proj1 Hcontrol).
        * eapply continuation_valid_observe; eauto. exact (proj2 Hcontrol).
        * exact Hordered.
      + eapply continuation_completed_observe; eauto.
    - eapply continuation_completed_observe; eauto.
    - eapply continuation_completed_observe; eauto.
    - apply continuation_completed_materialize,
        continuation_completed_enqueue_handle.
      eapply continuation_completed_observe; eauto.
    - apply continuation_completed_get_ready. exact Hcompleted.
    - exact Hcompleted.
    - exact Hcompleted.
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
    destruct (U.update true (R.handle_variable target)
      (R.stored_side_phase st (R.handle_variable owner)
        (R.handle_variable target))
      (R.stored_contribution st (R.handle_variable owner)
        (R.handle_variable target))
      (R.accumulated_side_input st (R.handle_variable owner)
        (R.handle_variable target) raw));
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank owner));
      exact Hsolved.
  Qed.

  Lemma solved_origin_step :
    forall tf before after x,
      handles_valid before ->
      Sem.step tf before after ->
      Progress.solved (R.cfg_state after) x ->
      Progress.solved (R.cfg_state before) x \/
      queued (R.cfg_state after) x \/
      control_active x (R.cfg_control after).
  Proof.
    intros tf [st control] after x Hvalid Hstep Hsolved.
    unfold Sem.step in Hstep.
    cbn in Hvalid, Hstep, Hsolved.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try (left; exact Hsolved).
    all: try match goal with
    | Hobserve : R.observe ?before ?target = (?next, ?entry),
      Hs : Progress.solved ?next ?x |- _ =>
        left; eapply solved_observe_origin; [exact Hobserve |exact Hs]
    end.
    - apply solved_start_origin in Hsolved.
      destruct Hsolved as [-> | Hsolved];
        [right; right; now left |now left].
    - apply solved_set_value_origin in Hsolved.
      destruct Hsolved as [-> | Hsolved];
        [right; right; now left |now left].
    - apply solved_get_ready_origin in Hsolved.
      assert (Hvariable : R.handle_variable h0 = t).
      { unfold R.observe in Hcase0.
        destruct (R.Ranking.observe (R.ranking st) t);
          inversion Hcase0; reflexivity. }
      destruct Hsolved as [Htarget | Hsolved].
      + left. rewrite Hvariable in Htarget. subst x.
        eapply solved_observe_origin; [exact Hcase0 |].
        apply (proj2 (Progress.solved_is_materialized s t)). exact Hcase1.
      + left. eapply solved_observe_origin; eauto.
    - apply solved_get_ready_origin in Hsolved.
      destruct Hsolved as [Htarget | Hsolved].
      + right. left. subst x. apply ExitReady.queued_get_ready.
        eapply ExitReady.enqueue_handle_queues_variable.
        * eapply rank_valid_observe;
            [exact (handles_rank_valid Hvalid) |exact Hcase0].
        * eapply queue_valid_observe;
            [exact (handles_queue_valid Hvalid) |exact Hcase0].
        * exact (@observed_handle_valid st t s h0 Hcase0).
      + left. eapply solved_observe_origin; [exact Hcase0 |exact Hsolved].
    - left. eapply solved_observe_origin; [exact Hcase0 |].
      now apply solved_side_ready_origin in Hsolved.
    - left. eapply solved_observe_origin; [exact Hcase0 |].
      now apply solved_side_ready_origin in Hsolved.
    - left. eapply solved_observe_origin; [exact Hcase0 |].
      now apply solved_side_ready_origin in Hsolved.
    - apply solved_materialize_origin in Hsolved.
      assert (Hvariable : R.handle_variable h0 = t).
      { unfold R.observe in Hcase0.
        destruct (R.Ranking.observe (R.ranking st) t);
          inversion Hcase0; reflexivity. }
      destruct Hsolved as [Htarget | Hsolved].
      + subst x. right. left.
        assert (Hqueued : queued (R.enqueue_handle s h0) t).
        { rewrite <- Hvariable.
          eapply ExitReady.enqueue_handle_queues_variable.
          - eapply rank_valid_observe;
              [exact (handles_rank_valid Hvalid) |exact Hcase0].
          - eapply queue_valid_observe;
              [exact (handles_queue_valid Hvalid) |exact Hcase0].
          - exact (@observed_handle_valid st t s h0 Hcase0). }
        unfold R.materialize.
        destruct (R.is_materialized (R.enqueue_handle s h0) t);
          exact Hqueued.
      + left. eapply solved_observe_origin; [exact Hcase0 |exact Hsolved].
    - apply solved_get_ready_origin in Hsolved.
      destruct Hsolved as [-> | Hsolved].
      + left. apply (proj2
          (Progress.solved_is_materialized st (R.handle_variable h0))).
        exact Hcase.
      + now left.
  Qed.

  Lemma queued_step_scheduled :
    forall tf before after x,
      handles_valid before ->
      queued (R.cfg_state before) x ->
      Sem.step tf before after ->
      queued (R.cfg_state after) x \/
      control_active x (R.cfg_control after).
  Proof.
    intros tf [st control] after x Hvalid Hqueued Hstep.
    unfold Sem.step in Hstep.
    cbn in Hvalid, Hqueued, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try (left; exact Hqueued).
    all: try match goal with
    | Hobserve : R.observe ?before ?target = (?next, ?entry)
      |- queued ?next ?x \/ _ =>
        left; eapply ExitReady.queued_observe;
          [exact Hobserve |exact Hqueued]
    end.
    all: try match goal with
    | Hpop : R.queue_pop (R.queue ?before) = Some (?popped, ?rest)
      |- queued (R.with_queue ?before ?rest) ?x \/ _ =>
        destruct (V.eq_dec x (R.handle_variable popped)) as [-> | Hneq];
        [right; cbn; tauto |left; eapply queued_pop_other; eauto]
    end.
    all: left.
    - cbn. apply ExitReady.queued_start. exact Hqueued.
    - apply ExitReady.queued_set_value. exact Hqueued.
    - apply ExitReady.queued_get_ready.
      eapply ExitReady.queued_observe; eauto.
    - apply ExitReady.queued_get_ready, ExitReady.queued_enqueue_handle.
      eapply ExitReady.queued_observe; eauto.
    - apply ExitReady.queued_side_ready.
      eapply ExitReady.queued_observe; eauto.
    - apply ExitReady.queued_enqueue_handle, ExitReady.queued_side_ready.
      eapply ExitReady.queued_observe; eauto.
    - apply ExitReady.queued_side_ready.
      eapply ExitReady.queued_observe; eauto.
    - unfold R.materialize.
      destruct (R.is_materialized (R.enqueue_handle s h0) t);
        apply ExitReady.queued_enqueue_handle;
        eapply ExitReady.queued_observe; eauto.
    - apply ExitReady.queued_get_ready. exact Hqueued.
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

  Lemma summary_step_guarded :
    forall tf before after x,
      handles_valid before ->
      summary_valid tf (R.cfg_state before) x ->
      Sem.step tf before after ->
      queued (R.cfg_state after) x \/
      control_active x (R.cfg_control after) \/
      summary_valid tf (R.cfg_state after) x.
  Proof.
    intros tf [st control] after x Hvalid Hsummary Hstep.
    unfold Sem.step in Hstep.
    cbn in Hvalid, Hstep.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?Hcase
      end;
      try discriminate; inversion Hstep; subst; cbn in *.
    all: try (right; right; exact Hsummary).
    all: try match goal with
    | Hobserve : R.observe ?before ?target = (?next, ?entry)
      |- _ \/ _ \/ summary_valid ?system ?next ?owner =>
        right; right; eapply summary_observe;
          [exact Hobserve |exact Hsummary]
    end.
    all: try match goal with
    | Hpop : R.queue_pop (R.queue ?before) = Some (?popped, ?rest)
      |- _ \/ _ \/ summary_valid ?system (R.with_queue ?before ?rest) ?owner =>
        destruct (V.eq_dec owner (R.handle_variable popped)) as [-> | Hneq];
        [right; left; cbn; tauto
        |right; right; eapply summary_pop_other; eauto]
    end.
    - destruct (V.eq_dec x (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + right. right. cbn. eapply summary_start_other; eauto.
    - destruct (V.eq_dec x (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + right. right. eapply summary_set_value_other.
        * exact (handles_rank_valid Hvalid).
        * exact (handles_queue_valid Hvalid).
        * exact Hneq.
        * exact Hsummary.
    - right. right. apply summary_get_ready.
      eapply summary_observe; eauto.
    - right. right. apply summary_get_ready, summary_enqueue_handle.
      eapply summary_observe; eauto.
    - destruct (V.eq_dec x (R.handle_variable h)) as [-> | Hneq].
      + right. left. right. now left.
      + right. right. eapply summary_side_other; [exact Hneq |].
        eapply summary_observe; eauto.
    - destruct (V.eq_dec x (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + right. right. apply summary_enqueue_handle.
        eapply summary_side_other; [exact Hneq |].
        eapply summary_observe; eauto.
    - destruct (V.eq_dec x (R.handle_variable h)) as [-> | Hneq].
      + right. left. now left.
      + right. right. eapply summary_side_other; [exact Hneq |].
        eapply summary_observe; eauto.
    - right. right. apply summary_materialize, summary_enqueue_handle.
      eapply summary_observe; eauto.
    - right. right. apply summary_get_ready. exact Hsummary.
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
          Hvalid Hqueued Hstep) as [Hqueued' | Hactive']; auto.
      + destruct (@active_step_scheduled_or_summary
          tf before after owner Hcompleted Hactive Hstep)
          as [Hactive' | Hsummary']; auto.
      + eapply summary_step_guarded; eauto.
    - now left.
    - now right; left.
  Qed.

  Definition started_solved (st : R.state) : Prop :=
    forall x, S.mem x (R.started st) = true -> Progress.solved st x.

  Lemma started_materialize :
    forall st x, R.started (R.materialize st x) = R.started st.
  Proof.
    intros st x. unfold R.materialize.
    destruct (R.is_materialized st x); reflexivity.
  Qed.

  Lemma started_enqueue :
    forall st x, R.started (R.enqueue st x) = R.started st.
  Proof.
    intros st x. unfold R.enqueue, R.observe, R.enqueue_handle.
    destruct (R.Ranking.observe (R.ranking st) x). reflexivity.
  Qed.

  Lemma started_enqueue_all :
    forall xs st, R.started (R.enqueue_all st xs) = R.started st.
  Proof.
    induction xs as [|x xs IH]; intros st; cbn.
    - reflexivity.
    - rewrite IH, started_enqueue. reflexivity.
  Qed.

  Lemma started_get_ready_state :
    forall st owner target,
      R.started (R.get_ready_state st owner target) = R.started st.
  Proof.
    intros st owner target.
    unfold R.get_ready_state, R.add_reader, R.promote_controlled,
      R.materialize.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
      destruct (R.is_materialized _ (R.handle_variable target));
      reflexivity.
  Qed.

  Lemma started_side_ready_state :
    forall st source target raw,
      R.started (R.side_ready_state st source target raw) = R.started st.
  Proof.
    intros st source target raw.
    unfold R.side_ready_state, R.record_side_payload,
      R.promote_controlled.
    destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      reflexivity.
  Qed.

  Lemma started_write_changed_value :
    forall st owner value,
      R.started (R.write_changed_value st owner value) = R.started st.
  Proof.
    intros st owner value. unfold R.write_changed_value.
    cbn. rewrite started_enqueue_all. reflexivity.
  Qed.

  Lemma started_set_value :
    forall st owner direct,
      R.started (R.set_value st owner direct) = R.started st.
  Proof.
    intros st owner direct. unfold R.set_value.
    destruct (R.equivalent _ _); [reflexivity |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (R.equivalent _ _); [reflexivity |].
      rewrite started_write_changed_value. reflexivity.
    - rewrite started_write_changed_value. reflexivity.
  Qed.

  Lemma initial_started_solved : started_solved R.empty_state.
  Proof.
    intros x Hmem. cbn in Hmem. rewrite SL.empty_spec in Hmem.
    discriminate.
  Qed.

  Lemma started_solved_step :
    forall tf before after,
      started_solved (R.cfg_state before) ->
      Sem.step tf before after ->
      started_solved (R.cfg_state after).
  Proof.
    intros tf [st control] [after_st after_control] Hstarted Hstep.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    destruct control; cbn in Hstep.
    all: repeat match type of Hstep with
      | context [match ?e with _ => _ end] =>
          destruct e eqn:?; cbn in Hstep
      end.
    all: try discriminate Hstep.
    all: inversion Hstep; subst; clear Hstep; cbn in *.
    all: intros x Hmem.
    all: try (apply Hstarted; exact Hmem).
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          unfold R.observe in Hobserve;
          destruct (R.Ranking.observe (R.ranking before) target);
          inversion Hobserve; subst; cbn in *
      end.
    all: try (cbn; apply Hstarted; exact Hmem).
    all: repeat rewrite started_get_ready_state in Hmem;
      repeat rewrite started_side_ready_state in Hmem;
      repeat rewrite started_materialize in Hmem;
      repeat rewrite started_set_value in Hmem;
      cbn in Hmem;
      eauto using Progress.solved_set_value, Progress.solved_get_ready,
        Progress.solved_side_ready, Progress.solved_enqueue_handle,
        Progress.solved_materialize.
    apply SL.add_spec in Hmem. destruct Hmem as [-> | Hmem].
    - cbn. apply Progress.solved_start_evaluation_self.
    - cbn. apply Progress.solved_start_evaluation.
      apply Hstarted. exact Hmem.
  Qed.

  Fixpoint continuation_pending
    (x : V.t) (k : R.continuation) : Prop :=
    match k with
    | R.KLoop => False
    | R.KSeedLoop remaining => List.In x remaining
    | R.KSolveOneLoop _ rest
    | R.KAfterGet _ _ _ rest
    | R.KAfterSide _ _ rest
    | R.KAfterSpawn _ _ rest => continuation_pending x rest
    end.

  Definition control_pending (x : V.t) (control : R.control) : Prop :=
    match control with
    | R.RunLoop => False
    | R.RunSeeds remaining | R.RunSeedLoop remaining => List.In x remaining
    | R.RunSolveOne owner rest =>
        x = R.handle_variable owner \/ continuation_pending x rest
    | R.RunSolveOneLoop _ rest
    | R.RunRhs _ _ rest
    | R.AfterGet _ _ _ rest
    | R.AfterSide _ _ rest
    | R.AfterSpawn _ _ rest => continuation_pending x rest
    end.

  Definition roots_guarded (roots : list V.t) (c : R.config) : Prop :=
    forall x, List.In x roots ->
      Progress.solved (R.cfg_state c) x \/
      control_pending x (R.cfg_control c).

  Lemma initial_roots_guarded :
    forall roots, roots_guarded roots (R.initial_config roots).
  Proof. intros roots x Hin. right. exact Hin. Qed.

  Lemma control_pending_step :
    forall tf x before after,
      started_solved (R.cfg_state before) ->
      control_pending x (R.cfg_control before) ->
      Sem.step tf before after ->
      Progress.solved (R.cfg_state after) x \/
      control_pending x (R.cfg_control after).
  Proof.
    intros tf x [st control] [after_st after_control]
      Hstarted Hpending Hstep.
    unfold Sem.step, R.next_config in Hstep. cbn in Hstep.
    destruct control; cbn in Hpending, Hstep.
    all: try contradiction.
    all: repeat match type of Hstep with
      | context [match ?e with _ => _ end] =>
          destruct e eqn:?; cbn in Hstep
      end.
    all: try discriminate Hstep.
    all: inversion Hstep; subst; clear Hstep; cbn in *.
    all: try tauto.
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          unfold R.observe in Hobserve;
          destruct (R.Ranking.observe (R.ranking before) target);
          inversion Hobserve; subst; cbn in *
      end.
    - destruct Hpending as [-> | Hpending].
      + left. cbn. apply Hstarted. exact Heqb.
      + now right.
    - destruct Hpending as [-> | Hpending]; tauto.
    - destruct Hpending as [-> | Hpending].
      + left. cbn. apply Progress.solved_start_evaluation_self.
      + now right.
    - right. destruct c; cbn in *; exact Hpending.
  Qed.

  Lemma roots_guarded_step :
    forall tf roots before after,
      started_solved (R.cfg_state before) ->
      roots_guarded roots before ->
      Sem.step tf before after ->
      roots_guarded roots after.
  Proof.
    intros tf roots before after Hstarted Hroots Hstep x Hin.
    destruct (Hroots x Hin) as [Hsolved | Hpending].
    - left. eapply Progress.next_config_solved_preserved; eauto.
    - eapply control_pending_step; eauto.
  Qed.

  Record invariant
    (tf : R.ConstraintSystem.system) (roots : list V.t)
    (c : R.config) : Prop := {
    invariant_handles : handles_valid c;
    invariant_ordered : Restart.control_ordered (R.cfg_control c);
    invariant_history :
      control_history tf (R.cfg_state c) (R.cfg_control c);
    invariant_completed :
      control_completed tf (R.cfg_state c) (R.cfg_control c);
    invariant_aggregate : aggregate_guarded c;
    invariant_summaries : summaries_guarded tf c;
    invariant_started : started_solved (R.cfg_state c);
    invariant_roots : roots_guarded roots c;
  }.

  Lemma initial_invariant :
    forall tf roots, invariant tf roots (R.initial_config roots).
  Proof.
    intros tf roots. constructor.
    - apply initial_handles_valid.
    - exact I.
    - exact I.
    - exact I.
    - apply initial_aggregate_guarded.
    - apply initial_summaries_guarded.
    - apply initial_started_solved.
    - apply initial_roots_guarded.
  Qed.

  Lemma invariant_step :
    forall tf roots before after,
      invariant tf roots before ->
      Sem.step tf before after ->
      invariant tf roots after.
  Proof.
    intros tf roots before after Hinv Hstep. constructor.
    - eapply next_config_handles_valid; eauto using invariant_handles.
    - eapply Restart.next_config_control_ordered; eauto using invariant_ordered.
    - eapply control_history_step; eauto using
        invariant_handles, invariant_ordered, invariant_history.
    - eapply control_completed_step; eauto using invariant_handles,
        invariant_ordered, invariant_history, invariant_completed.
    - eapply aggregate_guarded_step; eauto using
        invariant_handles, invariant_aggregate.
    - eapply summaries_guarded_step; eauto using
        invariant_handles, invariant_completed, invariant_summaries.
    - eapply started_solved_step; eauto using invariant_started.
    - eapply roots_guarded_step; eauto using
        invariant_started, invariant_roots.
  Qed.

  Lemma invariant_steps :
    forall tf roots first final,
      invariant tf roots first ->
      Sem.steps tf first final ->
      invariant tf roots final.
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

  Lemma quiescent_not_queued :
    forall st,
      Sem.quiescent st ->
      forall x, ~ queued st x.
  Proof.
    intros st Hquiet x [entry [Hentry _]].
    unfold Sem.quiescent, R.queue_peek in Hquiet.
    destruct (R.queue st) as [|head tail] eqn:Hqueue.
    - exact Hentry.
    - discriminate Hquiet.
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
    { apply quiescent_not_queued. exact Hquiet. }
    assert (Haggregate : forall target,
      D.leq (R.aggregate final target) (R.sigma_value final target) = true).
    {
      intros target. destruct (invariant_aggregate Hinv target)
        as [Hqueued | [Hactive | Hsound]].
      - contradiction (Hnotqueued target Hqueued).
      - contradiction.
      - exact Hsound.
    }
    intros owner Hin.
    assert (Hsolved : Sem.solved final owner).
    {
      destruct (invariant_roots Hinv owner Hin) as [Hsolved | Hpending].
      - exact Hsolved.
      - contradiction.
    }
    split; [exact Hsolved |].
    destruct (invariant_summaries Hinv Hsolved)
      as [Hqueued | [Hactive | Hsummary]].
    - contradiction (Hnotqueued owner Hqueued).
    - contradiction.
    - eapply summary_valid_replay; eauto.
  Qed.


  End Total.

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
  Proof. exact Total.solver_terminates. Qed.

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
      as [fuel Hfuel].
    now exists fuel, final.
  Qed.

  Theorem solve_fuel_correct :
    forall fuel tf roots final,
      R.solve_fuel fuel tf roots = Some final ->
      Sem.correct_final_state tf roots final.
  Proof.
    intros fuel tf roots final Hsolve.
    apply Total.terminal_state_correct.
    exact (@successful_run_terminates_to fuel tf roots final Hsolve).
  Qed.

  Theorem total_correct :
    forall tf roots,
      Sem.finite_system tf roots ->
      Sem.totally_correct_on tf roots.
  Proof.
    intros tf roots Hfinite.
    destruct (@sufficient_fuel tf roots Hfinite)
      as [fuel [final Hsolve]].
    exists fuel, final. split; [exact Hsolve |].
    exact (@solve_fuel_correct fuel tf roots final Hsolve).
  Qed.
End Make.

(** The existing first-discovery allocator is already an instance of the
    policy-parametric proof. *)
Module FirstDiscovery
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    ListDiscoveryOrderLaws V.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V Rk Laws :=
    ListFiniteDiscoveryOrderLaws V.
  Include Make V D U S M Rk Laws Finite DL UL SL ML.
End FirstDiscovery.

(** A fixed stateless numbering reaches the same relational proof boundary. *)
Module FixedRank
  (V : VAR)
  (D : DOMAIN)
  (U : UPDATE V D)
  (S : SET V)
  (M : MAP V)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S)
  (ML : MAP_LAWS V M).
  Module Rk := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V Rk :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V Rk Laws :=
    FixedRankFiniteDiscoveryOrderLaws V Fixed FixedLaws.
  Include Make V D U S M Rk Laws Finite DL UL SL ML.
End FixedRank.
