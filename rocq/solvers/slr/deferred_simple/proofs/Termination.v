From TcSolvers Require Export solvers.slr.deferred_simple.proofs.Correctness.
Import ListNotations.
Set Implicit Arguments.

(** Persistent update credits and the deferred scheduler's termination measure. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : DeferredSimple.FEATURES)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M) (DL : DOMAIN_LAWS D)
  (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U)
  (SUL : SIDE_UPDATE_TERMINATION_LAWS V D SU)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (DormantRankLaws : DORMANT_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws).
  Module C := Correctness.Make V D U SU S M Rk Features SL ML DL OUL SUL RankLaws.
  Import C.
  Module R := C.R.
  Module Sem := C.Sem.

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

  Lemma higher_child_returns : forall support tf roots owner target k start,
    higher_episodes_complete support tf roots owner ->
    In (R.handle_variable target) support ->
    Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true ->
    Sem.steps tf (R.initial_config roots) start ->
    R.cfg_control start = R.RunSolveOne target k ->
    exists st,
      scoped_until_steps target k tf start
        {| R.cfg_state := st; R.cfg_control := R.continue k |} /\
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.continue k |}.
  Proof.
    intros support tf roots owner target k start Hchildren Hin Hhigher Hreach Hcontrol.
    destruct (Hchildren target k start Hin Hhigher Hreach Hcontrol)
      as [st [Hsteps Hbelow]].
    exists st. split; [exact Hsteps|].
    eapply steps_transitive; [exact Hreach|]. eapply scoped_until_semantic; exact Hsteps.
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

  Lemma run_get_direct :
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
       forall value next_state,
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner (next value) k |} ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Get target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
      intros value next_state Hstep.
      assert (Hafter : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner (next value) k |}).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.

  Qed.

  Lemma run_get_child :
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
       forall observed target_handle,
      R.observe st target = (observed, target_handle) ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle) = true ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}
        {| R.cfg_state := observed;
           R.cfg_control := R.RunSolveOne target_handle
             (R.KAfterGet owner target_handle next k) |} ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Get target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
      intros observed target_handle Hobserve Hhigher Hstep.
      set (child_k := R.KAfterGet owner target_handle next k).
      set (child :=
        {| R.cfg_state := observed;
           R.cfg_control := R.RunSolveOne target_handle child_k |}).
      assert (Hchild_steps : Sem.steps tf (R.initial_config roots) child).
      { eapply Sim.steps_append_one; eauto. }
      assert (Htarget_handle :
        List.In (R.handle_variable target_handle) support).
      {
        rewrite (observed_handle_variable st target Hobserve).
        exact Htarget.
      }
      destruct (@Sim.higher_child_returns support tf roots owner target_handle
        child_k child Hchildren Htarget_handle Hhigher Hchild_steps eq_refl)
        as [child_st [Hepisode Hreturned]].
      set (returned :=
        {| R.cfg_state := child_st;
           R.cfg_control := R.continue child_k |}) in *.
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
      { eapply Sim.steps_append_one; [exact Hreturned | exact Hreturn]. }
      assert (Hdone : Sim.rhs_finishes tf owner
        (next (R.sigma_value ready (R.handle_variable target_handle))) k
        after).
      { apply Hfinish. exact Hafter. }
      eapply Sim.rhs_finishes_after_child with
        (child := child) (child_owner := target_handle)
        (child_k := child_k) (returned := returned) (after := after);
        eauto.
      - cbn. left. split; reflexivity.
      - apply Sim.ScopedContinuationGet.
      - cbn. left. split; reflexivity.

  Qed.

  Lemma run_get_known :
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
      forall rank, R.is_dormant st target = false ->
      R.Ranking.lookup (R.ranking st) target = Some rank ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Get target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Get target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
    pose proof (@run_get_direct support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hdirect.
    pose proof (@run_get_child support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hchild.
    intros rank Hdormant Hlookup.
    destruct (R.observe st target) as [observed target_handle]
          eqn:Hobserve.
        destruct (R.is_materialized observed target) eqn:Hmaterialized.
        * eapply Hdirect with
            (value := R.sigma_value
              (R.dirty_get_ready_state tf observed owner target_handle) target)
            (next_state :=
              R.dirty_get_ready_state tf observed owner target_handle).
          unfold Sem.step. cbn.
          now rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
        * destruct (Nat.ltb (R.handle_rank owner)
            (R.handle_rank target_handle)) eqn:Hhigher.
          -- eapply Hchild; eauto.
             unfold Sem.step. cbn.
             rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
          -- eapply Hdirect with
               (value := R.sigma_value
                 (R.get_ready_state
                   (R.enqueue_handle observed target_handle)
                   owner target_handle) target)
               (next_state := R.get_ready_state
                 (R.enqueue_handle observed target_handle)
                 owner target_handle).
             unfold Sem.step. cbn.
             rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
  Qed.

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
    pose proof (@run_get_direct support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hdirect.
    pose proof (@run_get_child support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hchild.
    destruct (R.is_dormant st target) eqn:Hdormant.
    - eapply Hdirect with (value := D.bottom)
        (next_state := R.add_reader st target (R.handle_variable owner)).
      unfold Sem.step. cbn. now rewrite Hdormant.
    - destruct (R.Ranking.lookup (R.ranking st) target) as [rank |]
        eqn:Hlookup.
      + eapply run_get_known; eauto.
      + destruct (andb (R.pure_bottom_rhs tf target)
          (negb (R.is_materialized st target))) eqn:Hbottom.
        * eapply Hdirect with (value := D.bottom)
            (next_state := R.add_reader (R.remember_dormant st target)
              target (R.handle_variable owner)).
          unfold Sem.step. cbn. now rewrite Hdormant, Hlookup, Hbottom.
        * destruct (R.observe st target) as [observed target_handle]
            eqn:Hobserve.
          destruct (Nat.ltb (R.handle_rank owner)
            (R.handle_rank target_handle)) eqn:Hhigher.
          -- eapply Hchild; eauto.
             unfold Sem.step. cbn.
             rewrite Hdormant, Hlookup, Hbottom, Hobserve.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
          -- eapply Hdirect with
               (value := R.sigma_value
                 (R.get_ready_state
                   (R.enqueue_handle observed target_handle)
                   owner target_handle) target)
               (next_state := R.get_ready_state
                 (R.enqueue_handle observed target_handle)
                 owner target_handle).
             unfold Sem.step. cbn.
             rewrite Hdormant, Hlookup, Hbottom, Hobserve.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
  Qed.

  Lemma run_spawn_direct :
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
       forall next_state,
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner next k |} ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Spawn target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
      intros next_state Hstep.
      assert (Hafter : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner next k |}).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.

  Qed.

  Lemma run_spawn_child :
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
       forall observed target_handle,
      R.observe st target = (observed, target_handle) ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle) = true ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}
        {| R.cfg_state := observed;
           R.cfg_control := R.RunSolveOne target_handle
             (R.KAfterSpawn owner next k) |} ->
      Sim.rhs_finishes tf owner (R.ConstraintSystem.Spawn target next) k
        {| R.cfg_state := st;
           R.cfg_control :=
             R.RunRhs owner (R.ConstraintSystem.Spawn target next) k |}.
  Proof.
    intros support tf roots owner st target next k Htarget Hchildren
      Hreachable Hfinish.
      intros observed target_handle Hobserve Hhigher Hstep.
      set (child_k := R.KAfterSpawn owner next k).
      set (child :=
        {| R.cfg_state := observed;
           R.cfg_control := R.RunSolveOne target_handle child_k |}).
      assert (Hchild_steps : Sem.steps tf (R.initial_config roots) child).
      { eapply Sim.steps_append_one; eauto. }
      assert (Htarget_handle :
        List.In (R.handle_variable target_handle) support).
      {
        rewrite (observed_handle_variable st target Hobserve).
        exact Htarget.
      }
      destruct (@Sim.higher_child_returns support tf roots owner target_handle
        child_k child Hchildren Htarget_handle Hhigher Hchild_steps eq_refl)
        as [child_st [Hepisode Hreturned]].
      set (returned :=
        {| R.cfg_state := child_st;
           R.cfg_control := R.continue child_k |}).
      set (after :=
        {| R.cfg_state := child_st;
           R.cfg_control := R.RunRhs owner next k |}).
      assert (Hreturn : Sem.step tf returned after).
      { unfold Sem.step, returned, after, child_k. reflexivity. }

      assert (Hafter : Sem.steps tf (R.initial_config roots) after).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_after_child with
        (child := child) (child_owner := target_handle)
        (child_k := child_k) (returned := returned) (after := after);
        eauto.
      - cbn. left. split; reflexivity.
      - apply Sim.ScopedContinuationSpawn.
      - cbn. left. split; reflexivity.

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
    pose proof (@run_spawn_direct support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hdirect.
    destruct Features.defer_spawns eqn:Hdefer.
    { apply Hdirect with (next_state := R.request_spawn st target).
      unfold Sem.step. cbn. now rewrite Hdefer. }
    pose proof (@run_spawn_child support tf roots owner st target next k Htarget Hchildren Hreachable Hfinish) as Hchild.
    destruct (R.is_dormant st target) eqn:Hdormant.
    - eapply Hdirect with (next_state := st).
      unfold Sem.step. cbn. rewrite Hdefer. now rewrite Hdormant.
    - destruct (R.Ranking.lookup (R.ranking st) target) as [rank |]
        eqn:Hlookup.
      + destruct (R.observe st target) as [observed target_handle]
          eqn:Hobserve.
        destruct (R.is_materialized observed target) eqn:Hmaterialized.
        * eapply Hdirect with (next_state := observed).
          unfold Sem.step. cbn. rewrite Hdefer.
          now rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
        * destruct (Nat.ltb (R.handle_rank owner)
            (R.handle_rank target_handle)) eqn:Hhigher.
          -- eapply Hchild; eauto.
             unfold Sem.step. cbn. rewrite Hdefer.
             rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
          -- eapply Hdirect with (next_state := R.materialize
               (R.enqueue_handle observed target_handle) target).
             unfold Sem.step. cbn. rewrite Hdefer.
             rewrite Hdormant, Hlookup, Hobserve, Hmaterialized.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
      + destruct (andb (R.pure_bottom_rhs tf target)
          (negb (R.is_materialized st target))) eqn:Hbottom.
        * eapply Hdirect with
            (next_state := R.remember_dormant st target).
          unfold Sem.step. cbn. rewrite Hdefer. now rewrite Hdormant, Hlookup, Hbottom.
        * destruct (R.observe st target) as [observed target_handle]
            eqn:Hobserve.
          destruct (Nat.ltb (R.handle_rank owner)
            (R.handle_rank target_handle)) eqn:Hhigher.
          -- eapply Hchild; eauto.
             unfold Sem.step. cbn. rewrite Hdefer.
             rewrite Hdormant, Hlookup, Hbottom, Hobserve.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
          -- eapply Hdirect with (next_state := R.materialize
               (R.enqueue_handle observed target_handle) target).
             unfold Sem.step. cbn. rewrite Hdefer.
             rewrite Hdormant, Hlookup, Hbottom, Hobserve.
             destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
               try discriminate; try rewrite Hhigher; reflexivity.
  Qed.

  Lemma run_side_direct :
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
       forall next_state,
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner next k |} ->
      Sim.rhs_finishes tf owner
        (R.ConstraintSystem.Side target raw next) k
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}.
  Proof.
    intros support tf roots owner st target raw next k Htarget Hchildren
      Hreachable Hfinish.
      intros next_state Hstep.
      assert (Hafter : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := next_state;
           R.cfg_control := R.RunRhs owner next k |}).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_one_step; eauto.
      cbn. left. split; reflexivity.

  Qed.

  Lemma run_side_child :
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
      forall observed target_handle,
      R.observe st target = (observed, target_handle) ->
       forall child_state,
      Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle) = true ->
      Sem.step tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}
        {| R.cfg_state := child_state;
           R.cfg_control := R.RunSolveOne target_handle
             (R.KAfterSide owner next k) |} ->
      Sim.rhs_finishes tf owner
        (R.ConstraintSystem.Side target raw next) k
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner
             (R.ConstraintSystem.Side target raw next) k |}.
  Proof.
    intros support tf roots owner st target raw next k Htarget Hchildren
      Hreachable Hfinish.
    intros observed target_handle Hobserve.
      intros child_state Hhigher Hstep.
      set (child_k := R.KAfterSide owner next k).
      set (child :=
        {| R.cfg_state := child_state;
           R.cfg_control := R.RunSolveOne target_handle child_k |}).
      assert (Hchild_steps : Sem.steps tf (R.initial_config roots) child).
      { eapply Sim.steps_append_one; eauto. }
      assert (Htarget_handle :
        List.In (R.handle_variable target_handle) support).
      {
        rewrite (observed_handle_variable st target Hobserve).
        exact Htarget.
      }
      destruct (@Sim.higher_child_returns support tf roots owner target_handle
        child_k child Hchildren Htarget_handle Hhigher Hchild_steps eq_refl)
        as [child_st [Hepisode Hreturned]].
      set (returned :=
        {| R.cfg_state := child_st;
           R.cfg_control := R.continue child_k |}).
      set (after :=
        {| R.cfg_state := child_st;
           R.cfg_control := R.RunRhs owner next k |}).
      assert (Hreturn : Sem.step tf returned after).
      { unfold Sem.step, returned, after, child_k. reflexivity. }

      assert (Hafter : Sem.steps tf (R.initial_config roots) after).
      { eapply Sim.steps_append_one; eauto. }
      eapply Sim.rhs_finishes_after_child with
        (child := child) (child_owner := target_handle)
        (child_k := child_k) (returned := returned) (after := after);
        eauto.
      - cbn. left. split; reflexivity.
      - apply Sim.ScopedContinuationSide.
      - cbn. left. split; reflexivity.

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
    pose proof (@run_side_direct support tf roots owner st target raw next k Htarget Hchildren Hreachable Hfinish) as Hdirect.
    pose proof (@run_side_child support tf roots owner st target raw next k Htarget Hchildren Hreachable Hfinish observed target_handle Hobserve) as Hchild.
    destruct (R.is_dormant st target) eqn:Hdormant.
    - destruct (andb
        (Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle))
        (negb (R.is_materialized observed target))) eqn:Hchild_case.
      + apply Bool.andb_true_iff in Hchild_case as
          [Hhigher Hunmaterialized].
        apply (Hchild ready); [exact Hhigher |].
        unfold Sem.step, ready in *. cbn. rewrite Hobserve, Hdormant.
        destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
          try discriminate;
          rewrite Hhigher, Hunmaterialized; reflexivity.
      + eapply Hdirect with
          (next_state := R.enqueue_handle ready target_handle).
        unfold Sem.step, ready in *. cbn. rewrite Hobserve, Hdormant.
        destruct (R.handle_rank target_handle); cbn in Hchild_case |- *;
          try rewrite Hchild_case; reflexivity.
    - destruct (R.aggregate_grew observed ready target) eqn:Hchanged.
      + destruct (andb
          (Nat.ltb (R.handle_rank owner) (R.handle_rank target_handle))
          (negb (R.is_materialized observed target))) eqn:Hchild_case.
        * apply Bool.andb_true_iff in Hchild_case as
            [Hhigher Hunmaterialized].
          apply (Hchild (R.mark_side_dirty ready target));
            [exact Hhigher |].
          unfold Sem.step, ready in *. cbn.
          rewrite Hobserve, Hdormant, Hchanged.
          destruct (R.handle_rank target_handle); cbn in Hhigher |- *;
            try discriminate;
            rewrite Hhigher, Hunmaterialized; reflexivity.
        * eapply Hdirect with
            (next_state := R.enqueue_handle
              (R.mark_side_dirty ready target) target_handle).
          unfold Sem.step, ready in *. cbn.
          rewrite Hobserve, Hdormant, Hchanged.
          destruct (R.handle_rank target_handle); cbn in Hchild_case |- *;
            try rewrite Hchild_case; reflexivity.
      + eapply Hdirect with (next_state := ready).
        unfold Sem.step, ready in *. cbn.
        now rewrite Hobserve, Hdormant, Hchanged.
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
    OUL.remaining_changes
      (R.stored_phase st owner) (R.sigma_value st owner).

  Definition side_credit
    (st : R.state) (source target : V.t) : nat :=
    SUL.remaining_changes
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
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      cbn; auto.
    apply SL.add_spec. now right.
  Qed.

  Lemma controlled_mark_side_dirty :
    forall st target,
      R.controlled (R.mark_side_dirty st target) = R.controlled st.
  Proof. intros. reflexivity. Qed.

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

  Lemma controlled_cancel_dirty_target :
    forall st target,
      R.controlled (R.cancel_dirty_target st target) = R.controlled st.
  Proof. intros. reflexivity. Qed.

  Lemma controlled_try_dirty_read_mono :
    forall tf st owner target next x,
      R.try_dirty_read tf st owner target = Some next ->
      S.mem x (R.controlled st) = true ->
      S.mem x (R.controlled next) = true.
  Proof.
    intros tf st owner target next x Hread Hcontrolled.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst;
      repeat rewrite controlled_write_changed_value; cbn.
    all: try exact Hcontrolled.
    all: apply SL.add_spec; now right.
  Qed.

  Lemma controlled_dirty_get_ready_mono :
    forall tf st owner target x,
      S.mem x (R.controlled st) = true ->
      S.mem x
        (R.controlled (R.dirty_get_ready_state tf st owner target)) = true.
  Proof.
    intros tf st owner target x Hcontrolled.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : S.mem x (R.controlled prepared) = true).
    { subst prepared. unfold R.get_control_state, R.materialize,
        R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); cbn; auto.
      all: apply SL.add_spec; now right. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - change (S.mem x (R.controlled next) = true).
      eapply controlled_try_dirty_read_mono; eauto.
    - change (S.mem x (R.controlled prepared) = true). exact Hprepared.
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
      eauto using controlled_get_ready_mono, controlled_dirty_get_ready_mono,
        controlled_side_ready_mono.
    all: try match goal with
      | Hobs : R.observe ?before ?target = (?next, ?entry) |- _ =>
          assert (Hobserved : S.mem x (R.controlled next) = true)
            by (rewrite (@controlled_observe before target next entry Hobs);
                exact Hcontrolled)
      end.
    all: try (rewrite controlled_materialize; exact Hcontrolled).
    all: try (apply controlled_get_ready_mono; exact Hobserved).
    all: try (apply controlled_dirty_get_ready_mono; exact Hobserved).
    all: try (apply controlled_side_ready_mono; exact Hobserved).
    all: try (rewrite controlled_materialize; exact Hobserved).
    all: try (rewrite controlled_set_value; exact Hcontrolled).
    all: try (rewrite controlled_mark_side_dirty; exact Hobserved).
    all: try (rewrite controlled_mark_side_dirty; exact Hcontrolled).
    all: try first [exact Hobserved | exact Hcontrolled].
    unfold R.request_spawn. destruct (S.mem t (R.requested_spawns st)); exact Hcontrolled.
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
    R.aggregate_grew st (R.side_ready_state st source target raw)
      (R.handle_variable target) = true.

  Lemma equivalent_refl : forall value, OUL.equivalent value value.
  Proof. intros. split; apply DL.leq_refl. Qed.

  Lemma equivalent_sym :
    forall left right, OUL.equivalent left right -> OUL.equivalent right left.
  Proof. intros left right [Hlr Hrl]. now split. Qed.

  Lemma equivalent_trans :
    forall first second third,
      OUL.equivalent first second -> OUL.equivalent second third ->
      OUL.equivalent first third.
  Proof.
    intros first second third [H12 H21] [H23 H32]. split;
      eapply DL.leq_trans; eauto.
  Qed.

  Lemma join_congruent :
    forall left left' right right',
      OUL.equivalent left left' -> OUL.equivalent right right' ->
      OUL.equivalent (D.join left right) (D.join left' right').
  Proof.
    intros left left' right right' [Hleft Hleft'] [Hright Hright'].
    split; apply DL.join_least.
    - eapply DL.leq_trans; [exact Hleft | apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hright | apply DL.join_upper_right].
    - eapply DL.leq_trans; [exact Hleft' | apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hright' | apply DL.join_upper_right].
  Qed.

  Lemma join_bottom_left :
    forall value, OUL.equivalent (D.join D.bottom value) value.
  Proof.
    intros. split; [apply DL.join_least | apply DL.join_upper_right];
      auto using DL.bottom_least, DL.leq_refl.
  Qed.

  Lemma join_swap :
    forall left right rest,
      OUL.equivalent (D.join left (D.join right rest))
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
      OUL.equivalent (R.join_values values) (R.join_values values').
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
      OUL.equivalent value (R.stored_contribution st source target) ->
      OUL.equivalent
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

  Lemma aggregate_row_update_below :
    forall st source target value,
      D.leq value (R.aggregate st target) = true ->
      D.leq
        (R.aggregate (R.with_contributions st
          (R.update_map (R.contributions st) target source value)) target)
        (R.aggregate st target) = true.
  Proof.
    intros st source target value Hvalue.
    unfold R.aggregate. cbn. rewrite lookup_map_update_same_row.
    set (row := R.lookup_map (R.contributions st) target) in *.
    destruct (ML.values_update row source value)
      as [rest [Hupdated Hprevious]].
    destruct (join_values_permutation Hupdated) as [Hnew _].
    eapply DL.leq_trans; [exact Hnew |]. cbn.
    apply DL.join_least; [exact Hvalue |].
    destruct (M.lookup row source) as [previous |] eqn:Hlookup.
    - destruct (join_values_permutation Hprevious) as [_ Hrest].
      eapply DL.leq_trans; [apply DL.join_upper_right |exact Hrest].
    - exact (proj2 (join_values_permutation Hprevious)).
  Qed.

  Lemma aggregate_record_side_below :
    forall st source target raw,
      D.leq (snd (side_update_result st source target raw))
        (R.aggregate st target) = true ->
      D.leq
        (R.aggregate (R.record_side_payload st source target raw) target)
        (R.aggregate st target) = true.
  Proof.
    intros st source target raw Hbelow.
    unfold R.record_side_payload, side_update_result. cbn.
    change (D.leq
      (R.aggregate (R.with_contributions st
        (R.update_map (R.contributions st) target source
          (snd (SU.update source target
            (R.stored_side_phase st source target)
            (R.stored_contribution st source target)
            (R.accumulated_side_input st source target raw)
            (R.aggregate st target))))) target)
      (R.aggregate st target) = true).
    eapply aggregate_row_update_below. exact Hbelow.
  Qed.

  Lemma side_grows_update_exposed :
    forall st source target raw,
      side_grows st source target raw ->
      D.leq
        (snd (side_update_result st (R.handle_variable source)
          (R.handle_variable target) raw))
        (R.aggregate st (R.handle_variable target)) = false.
  Proof.
    intros st source target raw Hgrows.
    destruct (D.leq
      (snd (side_update_result st (R.handle_variable source)
        (R.handle_variable target) raw))
      (R.aggregate st (R.handle_variable target))) eqn:Hexposed;
      [|reflexivity].
    pose proof (@aggregate_record_side_below st
      (R.handle_variable source) (R.handle_variable target) raw Hexposed)
      as Hcovered.
    unfold side_grows, R.aggregate_grew in Hgrows.
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
      fst (side_update_result st source target raw).
  Proof.
    intros. unfold R.record_side_payload, R.stored_side_phase. cbn.
    rewrite lookup_map_update_same_row, ML.lookup_update_same. reflexivity.
  Qed.

  Lemma stored_contribution_record_same :
    forall st source target raw,
      R.stored_contribution (R.record_side_payload st source target raw)
        source target =
      snd (side_update_result st source target raw).
  Proof.
    intros. unfold R.record_side_payload, R.stored_contribution. cbn.
    rewrite lookup_map_update_same_row, ML.lookup_update_same. reflexivity.
  Qed.

  Lemma stored_contribution_below_aggregate :
    forall st source target,
      D.leq (R.stored_contribution st source target)
        (R.aggregate st target) = true.
  Proof.
    intros st source target.
    unfold R.stored_contribution, R.aggregate.
    destruct (M.lookup (R.lookup_map (R.contributions st) target) source)
      as [value |] eqn:Hlookup.
    - apply ML.lookup_values in Hlookup.
      induction (M.values (R.lookup_map (R.contributions st) target))
        as [|head rest IH]; cbn in *; [contradiction |].
      destruct Hlookup as [-> | Hin].
      + apply DL.join_upper_left.
      + eapply DL.leq_trans; [apply IH; exact Hin |].
        apply DL.join_upper_right.
    - apply DL.bottom_least.
  Qed.

  Lemma side_credit_record_same_nonincreasing :
    forall st source target raw,
      Measure.side_credit (R.record_side_payload st source target raw)
        source target <= Measure.side_credit st source target.
  Proof.
    intros. unfold Measure.side_credit.
    rewrite stored_side_phase_record_same,
      stored_contribution_record_same.
    apply SUL.remaining_changes_nonincreasing.
    apply stored_contribution_below_aggregate.
  Qed.

  Lemma side_credit_record_same_decreases :
    forall st source target raw,
      D.leq (snd (side_update_result st source target raw))
        (R.aggregate st target) = false ->
      Measure.side_credit (R.record_side_payload st source target raw)
        source target < Measure.side_credit st source target.
  Proof.
    intros. unfold Measure.side_credit.
    rewrite stored_side_phase_record_same,
      stored_contribution_record_same.
    apply SUL.exposed_change_consumes.
    - apply stored_contribution_below_aggregate.
    - exact H.
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
    rewrite (@lookup_update_map_other_outer SU.phase
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
    rewrite (@lookup_update_map_other_inner SU.phase
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
    pose proof (side_grows_update_exposed Hgrows) as Hexposed.
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
      R.equivalent left right = true -> OUL.equivalent left right.
  Proof.
    intros left right Hequivalent. unfold R.equivalent in Hequivalent.
    now apply Bool.andb_true_iff.
  Qed.

  Lemma equivalent_false :
    forall left right,
      R.equivalent left right = false -> ~ OUL.equivalent left right.
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
      pose proof (OUL.remaining_changes_nonincreasing owner
        (R.stored_phase st owner) old candidate) as Hle.
      rewrite Hupdate in Hle. cbn in Hle.
      pose proof (@OUL.remaining_changes_extensional phase value old
        (@equivalent_true value old Hstutter)) as Heq.
      change (OUL.remaining_changes phase old <=
        OUL.remaining_changes (R.stored_phase st owner) old).
      lia.
    - unfold Measure.ordinary_credit.
      rewrite stored_phase_write_changed,
        sigma_value_write_changed_same.
      unfold R.stored_phase. cbn. rewrite ML.lookup_update_same.
      pose proof (OUL.remaining_changes_nonincreasing owner
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
      ~ OUL.equivalent
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
          ~ OUL.equivalent
            (snd (U.update false owner (R.stored_phase st owner)
              old candidate)) old).
        { rewrite Hupdate. cbn. now apply equivalent_false. }
        pose proof (@OUL.update_change_consumes owner
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
      ~ OUL.equivalent
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
      destruct (side_update_result st (R.handle_variable source)
        (R.handle_variable target) raw);
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

  Lemma charged_update_credit_add_reader :
    forall support st target owner,
      Measure.charged_update_credit support
        (R.add_reader st target owner) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

  Lemma charged_update_credit_remember_dormant :
    forall support st target,
      Measure.charged_update_credit support
        (R.remember_dormant st target) =
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

  Lemma charged_update_credit_mark_side_dirty :
    forall support st target,
      Measure.charged_update_credit support (R.mark_side_dirty st target) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

  Lemma charged_update_credit_cancel_dirty_target :
    forall support st target,
      Measure.charged_update_credit support (R.cancel_dirty_target st target) =
      Measure.charged_update_credit support st.
  Proof. reflexivity. Qed.

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

  Lemma uncontrolled_count_add_reader :
    forall support st target owner,
      Measure.uncontrolled_count support (R.add_reader st target owner) =
      Measure.uncontrolled_count support st.
  Proof.
    induction support as [|x rest IH]; intros; cbn; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma unmaterialized_count_mark_side_dirty :
    forall support st target,
      Measure.unmaterialized_count support (R.mark_side_dirty st target) =
      Measure.unmaterialized_count support st.
  Proof.
    induction support as [|x rest IH]; intros; cbn; [reflexivity |].
    rewrite IH. reflexivity.
  Qed.

  Lemma uncontrolled_count_mark_side_dirty :
    forall support st target,
      Measure.uncontrolled_count support (R.mark_side_dirty st target) =
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

  Lemma charged_update_credit_promote_existing :
    forall support st variable,
      S.mem variable (R.controlled st) = true ->
      Measure.charged_update_credit support (R.promote_controlled st variable) =
      Measure.charged_update_credit support st.
  Proof.
    intros support st variable Hcontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
    unfold Measure.charged_ordinary_credit, Measure.ordinary_credit,
      R.promote_controlled. cbn.
    now rewrite Accounting.mem_add_existing.
  Qed.

  Lemma charged_update_credit_promote_started_existing :
    forall support st started variable,
      S.mem variable (R.controlled st) = true ->
      Measure.charged_update_credit support
        (R.promote_controlled (R.with_started st started) variable) =
      Measure.charged_update_credit support st.
  Proof.
    intros support st started variable Hcontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    - apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      unfold Measure.charged_ordinary_credit, Measure.ordinary_credit,
        R.promote_controlled. cbn.
      now rewrite Accounting.mem_add_existing.
  Qed.

  Lemma charged_update_credit_phases_promote_started_existing :
    forall support st started variable phases,
      S.mem variable (R.controlled st) = true ->
      Measure.charged_update_credit support
        (R.with_phases
          (R.promote_controlled (R.with_started st started) variable)
          phases) =
      Measure.charged_update_credit support (R.with_phases st phases).
  Proof.
    intros support st started variable phases Hcontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    - apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      unfold Measure.charged_ordinary_credit, Measure.ordinary_credit,
        R.promote_controlled. cbn.
      now rewrite Accounting.mem_add_existing.
  Qed.

  Lemma charged_update_credit_write_promote_started_existing :
    forall support st started target phases value,
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      Measure.charged_update_credit support
        (R.write_changed_value
          (R.cancel_dirty_target
            (R.with_phases
              (R.promote_controlled (R.with_started st started)
                (R.handle_variable target)) phases) target)
          (R.handle_variable target) value) =
      Measure.charged_update_credit support
        (R.write_changed_value (R.with_phases st phases)
          (R.handle_variable target) value).
  Proof.
    intros support st started target phases value Hcontrolled.
    unfold Measure.charged_update_credit,
      Measure.charged_ordinary_credit_sum, Measure.side_credit_sum.
    f_equal.
    - apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      unfold Measure.charged_ordinary_credit.
      repeat rewrite Measure.controlled_write_changed_value.
      unfold R.promote_controlled. cbn.
      rewrite Accounting.mem_add_existing by exact Hcontrolled.
      unfold Measure.ordinary_credit.
      repeat rewrite Accounting.stored_phase_write_changed.
      destruct (V.eq_dec observed (R.handle_variable target)) as [-> | Hneq].
      + repeat rewrite Accounting.sigma_value_write_changed_same. reflexivity.
      + repeat rewrite Accounting.sigma_value_write_changed_other
          by exact Hneq. reflexivity.
    - apply Accounting.sum_over_pointwise_eq. intros source Hsource.
      apply Accounting.sum_over_pointwise_eq. intros observed Hobserved.
      repeat rewrite Accounting.side_credit_write_changed. reflexivity.
  Qed.

  Lemma charged_update_credit_try_dirty_read_nonincreasing :
    forall support tf st owner target next,
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      R.try_dirty_read tf st owner target = Some next ->
      Measure.charged_update_credit support next <=
      Measure.charged_update_credit support st.
  Proof.
    intros support tf st owner target next Hcontrolled Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try (rewrite Hcontrolled in Heqb0; discriminate).
    all: pose proof
      (@Accounting.charged_update_credit_set_value_controlled_nonincreasing
        support st (R.handle_variable target) t Hcontrolled) as Hnon.
    all: unfold R.set_value in Hnon.
    all: rewrite Heqb2 in Hnon; cbn in Hnon.
    all: try rewrite Hcontrolled in Hnon; cbn in Hnon.
    - rewrite charged_update_credit_cancel_dirty_target,
        charged_update_credit_promote_started_existing by exact Hcontrolled.
      lia.
    - rewrite charged_update_credit_cancel_dirty_target,
        charged_update_credit_phases_promote_started_existing
          by exact Hcontrolled.
      change (R.stored_phase st (R.handle_variable target)) with
        (R.stored_phase
          (R.promote_controlled
            (R.with_started st
              (S.add (R.handle_variable target) (R.started st)))
            (R.handle_variable target))
          (R.handle_variable target)) in Hnon.
      rewrite Heqb4 in Hnon. exact Hnon.
    - rewrite charged_update_credit_write_promote_started_existing
        by exact Hcontrolled.
      change (R.stored_phase st (R.handle_variable target)) with
        (R.stored_phase
          (R.promote_controlled
            (R.with_started st
              (S.add (R.handle_variable target) (R.started st)))
            (R.handle_variable target))
          (R.handle_variable target)) in Hnon.
      rewrite Heqb4 in Hnon. exact Hnon.
  Qed.

  Lemma controlled_try_dirty_read_target :
    forall tf st owner target next,
      R.try_dirty_read tf st owner target = Some next ->
      S.mem (R.handle_variable target) (R.controlled next) = true.
  Proof.
    intros tf st owner target next Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst;
      repeat rewrite Measure.controlled_write_changed_value; cbn;
      apply SL.add_spec; now left.
  Qed.

  Lemma dirty_get_ready_target_controlled_from_count :
    forall support tf st owner target,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      S.mem (R.handle_variable target)
        (R.controlled (R.dirty_get_ready_state tf st owner target)) = true ->
      S.mem (R.handle_variable target) (R.controlled st) = true.
  Proof.
    intros support tf st owner target Hnodup Htarget Hcount Hafter.
    destruct (S.mem (R.handle_variable target) (R.controlled st))
      eqn:Hbefore; [reflexivity |].
    exfalso.
    pose proof (@Measure.uncontrolled_count_strict_from_mono
      support st (R.dirty_get_ready_state tf st owner target)
      (R.handle_variable target) Hnodup Htarget
      (fun observed Hobserved =>
        @Measure.controlled_dirty_get_ready_mono
          tf st owner target observed Hobserved)
      Hbefore Hafter) as Hstrict.
    lia.
  Qed.

  Lemma charged_update_credit_prepared_from_count : forall support st owner target,
    NoDup support -> In (R.handle_variable target) support ->
    Measure.uncontrolled_count support (R.materialize (R.get_control_state st owner target)
      (R.handle_variable target)) = Measure.uncontrolled_count support st ->
    Measure.charged_update_credit support (R.materialize (R.get_control_state st owner target)
      (R.handle_variable target)) <= Measure.charged_update_credit support st.
  Proof.
    intros support st owner target Hnodup Htarget Hprepared_count.
      rewrite charged_update_credit_materialize.
      unfold R.get_control_state in Hprepared_count |- *.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        [lia |].
      destruct (S.mem (R.handle_variable target) (R.controlled st))
        eqn:Hcontrolled.
      + rewrite charged_update_credit_promote_existing
          by exact Hcontrolled. lia.
      + exfalso.
        pose proof (@Measure.uncontrolled_count_strict_from_mono
          support st
          (R.materialize
            (R.promote_controlled st (R.handle_variable target))
            (R.handle_variable target))
          (R.handle_variable target) Hnodup Htarget
          (fun observed Hobserved =>
            ltac:(unfold R.materialize, R.promote_controlled;
              destruct (R.is_materialized _ _); cbn;
              apply SL.add_spec; now right))
          Hcontrolled
          ltac:(unfold R.materialize, R.promote_controlled;
            destruct (R.is_materialized _ _); cbn;
            apply SL.add_spec; now left)) as Hstrict.
        lia.
  Qed.

  Lemma charged_update_credit_dirty_get_ready_from_count :
    forall support tf st owner target,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf st owner target) <=
      Measure.charged_update_credit support st.
  Proof.
    intros support tf st owner target Hnodup Htarget Hcount.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - rewrite charged_update_credit_add_reader.
      assert (Hafter : S.mem (R.handle_variable target)
        (R.controlled (R.add_reader next (R.handle_variable target)
          (R.handle_variable owner))) = true).
      { unfold R.add_reader. cbn.
        eapply controlled_try_dirty_read_target; eauto. }
      assert (Hbefore : S.mem (R.handle_variable target)
        (R.controlled st) = true).
      { eapply dirty_get_ready_target_controlled_from_count;
          [exact Hnodup |exact Htarget |exact Hcount |].
        unfold R.dirty_get_ready_state. fold prepared. rewrite Hread.
        exact Hafter. }
      assert (Hprepared_controlled : S.mem (R.handle_variable target)
        (R.controlled prepared) = true).
      { subst prepared. unfold R.get_control_state, R.materialize,
          R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          destruct (R.is_materialized _ _); cbn;
          try exact Hbefore;
          now rewrite Accounting.mem_add_existing. }
      pose proof (@charged_update_credit_try_dirty_read_nonincreasing
        support tf prepared owner target next Hprepared_controlled Hread)
        as Htry.
      assert (Hprepared_credit : Measure.charged_update_credit support
        prepared = Measure.charged_update_credit support st).
      { subst prepared.
        rewrite charged_update_credit_materialize.
        unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          [reflexivity |].
        now apply charged_update_credit_promote_existing. }
      lia.
    - rewrite charged_update_credit_add_reader. subst prepared.
      apply charged_update_credit_prepared_from_count; [exact Hnodup|exact Htarget|].
      unfold R.dirty_get_ready_state in Hcount. rewrite Hread in Hcount.
      rewrite uncontrolled_count_add_reader in Hcount. exact Hcount.
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

  Lemma charged_update_credit_request_spawn : forall support st target,
    Measure.charged_update_credit support (R.request_spawn st target) =
    Measure.charged_update_credit support st.
  Proof.
    intros. unfold R.request_spawn. destruct (S.mem target (R.requested_spawns st)); reflexivity.
  Qed.

  Lemma observed_dirty_get_credit_nonincreasing : forall support tf before target observed entry owner,
    R.observe before target = (observed, entry) -> NoDup support -> In target support ->
    Measure.uncontrolled_count support (R.dirty_get_ready_state tf observed owner entry) =
      Measure.uncontrolled_count support before ->
    Measure.charged_update_credit support (R.dirty_get_ready_state tf observed owner entry) <=
      Measure.charged_update_credit support before.
  Proof.
    intros support tf before target observed entry owner Ho Hn Hi Hcount.
    rewrite <- (@charged_update_credit_observe support before target observed entry Ho).
    apply charged_update_credit_dirty_get_ready_from_count; [exact Hn| |].
    - now rewrite (@observed_handle_variable before target observed entry Ho).
    - now rewrite (@uncontrolled_count_observe support before target observed entry Ho).
  Qed.

  Lemma charged_update_credit_step_nonincreasing : forall support tf before after,
    NoDup support -> E.control_in support (R.cfg_control before) -> Sem.step tf before after ->
    Measure.unmaterialized_count support (R.cfg_state after) = Measure.unmaterialized_count support (R.cfg_state before) ->
    Measure.uncontrolled_count support (R.cfg_state after) = Measure.uncontrolled_count support (R.cfg_state before) ->
    Measure.charged_update_credit support (R.cfg_state after) <= Measure.charged_update_credit support (R.cfg_state before).
  Proof.
    intros support tf [st control] after Hnodup Hsupported Hstep Hmaterialized Hcontrolled.
    unfold Sem.step in Hstep. cbn in Hstep, Hsupported.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?Hcase
      | context [if ?condition then _ else _] => destruct condition eqn:?Hcase
      end; try discriminate; inversion Hstep; subst; cbn in Hsupported, Hmaterialized, Hcontrolled |- *.
    all: repeat rewrite ?uncontrolled_count_enqueue_handle, ?uncontrolled_count_mark_side_dirty in Hcontrolled.
    all: repeat rewrite ?charged_update_credit_with_queue, ?charged_update_credit_with_started,
      ?charged_update_credit_start_evaluation, ?charged_update_credit_add_reader,
      ?charged_update_credit_remember_dormant, ?charged_update_credit_enqueue_handle,
      ?charged_update_credit_mark_side_dirty, ?charged_update_credit_request_spawn.
    all: try lia; try apply charged_update_credit_set_value_nonincreasing.
    all: try solve [match goal with Ho : Sem.R.observe ?st ?x = (?next, ?entry) |- _ =>
      rewrite (@charged_update_credit_observe support st x next entry Ho); lia end].
    all: repeat match type of Hsupported with _ /\ _ => destruct Hsupported as [? Hsupported] end.
    all: unfold E.handle_in in *.
    all: try match goal with Hrhs : Sem.rhs_supported _ _ |- _ => inversion Hrhs; subst end.
    all: try solve [eapply observed_enqueued_get_ready_credit_nonincreasing; eauto].
    all: try solve [eapply observed_get_ready_credit_nonincreasing; eauto].
    all: try solve [eapply observed_dirty_get_credit_nonincreasing; eauto].
    all: try solve [eapply observed_side_ready_credit_nonincreasing; eauto].
    all: try solve [match goal with Ho : Sem.R.observe ?before ?target = (?observed, ?entry) |- _ =>
      rewrite (@observed_enqueued_materialize_credit support before target observed entry Ho); lia end].
    all: try solve [rewrite charged_update_credit_get_ready_from_count; eauto; lia].
    apply Nat.le_refl.
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
      E.control_in support (R.cfg_control before) ->
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
      E.control_in support (R.cfg_control before) ->
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
        E.control_in support (R.cfg_control first) ->
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
        E.control_in support (R.cfg_control first) ->
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
      OUL.equivalent
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
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
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

  Lemma sigma_value_cancel_dirty_target_payment :
    forall st target observed,
      R.sigma_value (R.cancel_dirty_target st target) observed =
      R.sigma_value st observed.
  Proof. reflexivity. Qed.

  Lemma sigma_value_promote_started_payment :
    forall st started variable observed,
      R.sigma_value
        (R.promote_controlled (R.with_started st started) variable) observed =
      R.sigma_value st observed.
  Proof. reflexivity. Qed.

  Lemma sigma_value_phases_promote_started_payment :
    forall st started variable phases observed,
      R.sigma_value
        (R.with_phases
          (R.promote_controlled (R.with_started st started) variable)
          phases) observed =
      R.sigma_value st observed.
  Proof. reflexivity. Qed.

  Lemma charged_update_credit_try_dirty_read_decreases :
    forall support tf st owner target next,
      List.In (R.handle_variable target) support ->
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      R.try_dirty_read tf st owner target = Some next ->
      ~ OUL.equivalent
          (R.sigma_value next (R.handle_variable target))
          (R.sigma_value st (R.handle_variable target)) ->
      Measure.charged_update_credit support next <
      Measure.charged_update_credit support st.
  Proof.
    intros support tf st owner target next Htarget Hcontrolled Hread Hchanges.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try rewrite sigma_value_cancel_dirty_target_payment in Hchanges.
    all: try (rewrite Accounting.sigma_value_write_changed_same in Hchanges).
    all: try rewrite sigma_value_promote_started_payment in Hchanges.
    all: try rewrite sigma_value_phases_promote_started_payment in Hchanges.
    all: cbn in Hchanges.
    all: try (exfalso; apply Hchanges; apply Accounting.equivalent_refl).
    all: try (rewrite Hcontrolled in Heqb0; discriminate).
    pose proof
      (@Accounting.charged_update_credit_set_value_controlled_decreases
        support st (R.handle_variable target) t Htarget Hcontrolled)
      as Hstrict.
    unfold R.set_value in Hstrict.
    rewrite Heqb2 in Hstrict. cbn in Hstrict.
    try rewrite Hcontrolled in Hstrict. cbn in Hstrict.
    change (R.stored_phase st (R.handle_variable target)) with
      (R.stored_phase
        (R.promote_controlled
          (R.with_started st
            (S.add (R.handle_variable target) (R.started st)))
          (R.handle_variable target))
        (R.handle_variable target)) in Hstrict.
    rewrite Heqb4 in Hstrict.
    rewrite charged_update_credit_write_promote_started_existing
      by exact Hcontrolled.
    apply Hstrict.
    rewrite Accounting.sigma_value_write_changed_same.
    exact Hchanges.
  Qed.

  Lemma sigma_value_try_dirty_read_other_payment :
    forall tf st owner target next observed,
      R.try_dirty_read tf st owner target = Some next ->
      observed <> R.handle_variable target ->
      R.sigma_value next observed = R.sigma_value st observed.
  Proof.
    intros tf st owner target next observed Hread Hneq.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try rewrite sigma_value_cancel_dirty_target_payment.
    all: try rewrite Accounting.sigma_value_write_changed_other by exact Hneq.
    all: try rewrite sigma_value_promote_started_payment.
    all: try rewrite sigma_value_phases_promote_started_payment.
    all: reflexivity.
  Qed.

  Lemma try_dirty_read_target_sigma_same_from_credit :
    forall support tf st owner target next,
      List.In (R.handle_variable target) support ->
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      R.try_dirty_read tf st owner target = Some next ->
      Measure.charged_update_credit support next =
        Measure.charged_update_credit support st ->
      R.sigma_value next (R.handle_variable target) =
        R.sigma_value st (R.handle_variable target).
  Proof.
    intros support tf st owner target next Htarget Hcontrolled Hread Hcredit.
    pose proof Hread as Hread_original.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try (rewrite Hcontrolled in Heqb0; discriminate).
    all: try rewrite sigma_value_cancel_dirty_target_payment.
    all: try rewrite Accounting.sigma_value_write_changed_same.
    all: try rewrite sigma_value_promote_started_payment.
    all: try rewrite sigma_value_phases_promote_started_payment.
    all: try reflexivity.
    exfalso.
    pose proof (@charged_update_credit_try_dirty_read_decreases
      support tf st owner target _ Htarget Hcontrolled Hread_original)
      as Hstrict.
    specialize (Hstrict ltac:(
      rewrite Accounting.sigma_value_write_changed_same;
      now apply Accounting.equivalent_false)).
    lia.
  Qed.

  Lemma controlled_prepared_credit : forall support st owner target,
    S.mem (R.handle_variable target) (R.controlled st) = true ->
    let prepared := R.materialize (R.get_control_state st owner target)
      (R.handle_variable target) in
    S.mem (R.handle_variable target) (R.controlled prepared) = true /\
    Measure.charged_update_credit support prepared =
      Measure.charged_update_credit support st.
  Proof.
    intros support st owner target Hcontrolled prepared. split.
    - subst prepared. unfold R.get_control_state, R.materialize,
        R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        destruct (R.is_materialized _ _); cbn;
        try exact Hcontrolled;
        now rewrite Accounting.mem_add_existing.
    - subst prepared. rewrite charged_update_credit_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        [reflexivity |].
      now apply charged_update_credit_promote_existing.
  Qed.

  Lemma unpaid_observed_dirty_get_sigma_same :
    forall support tf before target next target_handle owner observed,
      R.observe before target = (next, target_handle) ->
      List.In observed support ->
      S.mem observed (R.controlled before) = true ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf next owner target_handle) =
        Measure.charged_update_credit support before ->
      R.sigma_value
        (R.dirty_get_ready_state tf next owner target_handle) observed =
      R.sigma_value before observed.
  Proof.
    intros support tf before target next target_handle owner observed
      Hobserve Hobserved Hcontrolled Hcredit.
    assert (Hnext_credit : Measure.charged_update_credit support next =
      Measure.charged_update_credit support before).
    { eapply charged_update_credit_observe; eauto. }
    assert (Hnext_sigma : R.sigma_value next observed =
      R.sigma_value before observed).
    { eapply sigma_value_observe; eauto. }
    unfold R.dirty_get_ready_state in Hcredit |- *.
    set (prepared := R.materialize
      (R.get_control_state next owner target_handle)
      (R.handle_variable target_handle)).
    destruct (R.try_dirty_read tf prepared owner target_handle)
      as [flushed |] eqn:Hread.
    - fold prepared in Hcredit. rewrite Hread in Hcredit.
      rewrite charged_update_credit_add_reader in Hcredit.
      destruct (V.eq_dec observed (R.handle_variable target_handle))
        as [-> | Hneq].
      + change (R.sigma_value flushed (R.handle_variable target_handle) =
          R.sigma_value before (R.handle_variable target_handle)).
        assert (Hnext_controlled :
          S.mem (R.handle_variable target_handle) (R.controlled next) = true).
        { rewrite (@Measure.controlled_observe
            before target next target_handle Hobserve).
          exact Hcontrolled. }
        destruct (@controlled_prepared_credit support next owner target_handle
          Hnext_controlled) as [Hprepared_controlled Hprepared_credit].
        fold prepared in Hprepared_credit.
        rewrite (@try_dirty_read_target_sigma_same_from_credit
          support tf prepared owner target_handle flushed
          Hobserved
          Hprepared_controlled Hread ltac:(lia)).
        subst prepared. rewrite sigma_value_materialize.
        unfold R.get_control_state, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner)
          (R.handle_rank target_handle)); cbn; exact Hnext_sigma.
      + change (R.sigma_value flushed observed =
          R.sigma_value before observed).
        rewrite (@sigma_value_try_dirty_read_other_payment
          tf prepared owner target_handle flushed observed Hread Hneq).
        subst prepared. rewrite sigma_value_materialize.
        unfold R.get_control_state, R.promote_controlled.
        destruct (Nat.ltb (R.handle_rank owner)
          (R.handle_rank target_handle)); cbn; exact Hnext_sigma.
    - change (R.sigma_value prepared observed =
        R.sigma_value before observed). subst prepared.
      rewrite sigma_value_materialize.
      unfold R.get_control_state, R.promote_controlled.
      destruct (Nat.ltb (R.handle_rank owner)
        (R.handle_rank target_handle)); cbn; exact Hnext_sigma.
  Qed.

  Lemma unpaid_step_controlled_sigma_same :
    forall support tf before after observed,
      E.control_in support (R.cfg_control before) ->
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
    all: try (unfold R.request_spawn;
      match goal with |- context [if ?test then _ else _] => destruct test end;
      reflexivity).
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |-
          R.sigma_value
            (R.dirty_get_ready_state ?tf ?next ?owner ?entry) ?observed = _ =>
          eapply (@unpaid_observed_dirty_get_sigma_same
            support tf before target next entry owner observed); eauto
      end.
    all: try change (R.sigma_value s observed = R.sigma_value st observed).
    all: try change (R.sigma_value (R.side_ready_state s h h0 t0) observed =
      R.sigma_value st observed).
    all: try rewrite sigma_value_get_ready.
    all: try rewrite sigma_value_side_ready.
    all: try rewrite sigma_value_materialize.
    all: try change (R.sigma_value s observed = R.sigma_value st observed).
    all: try match goal with
      | Hobserve : R.observe ?before ?target = (?next, ?entry) |- _ =>
          rewrite (@sigma_value_observe before target next entry observed Hobserve)
      end.
    all: try reflexivity.
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

  Lemma steps_supported : forall support tf before after,
    (forall owner, In owner support ->
      Sem.rhs_supported (fun x => In x support) (tf owner)) ->
    E.config_in support before -> Sem.steps tf before after ->
    supported_steps support tf before after.
  Proof.
    intros support tf before after Htf Hbefore Hsteps.
    induction Hsteps; [constructor|].
    econstructor; [exact (proj2 Hbefore)|exact H|].
    apply IHHsteps. eapply E.next_config_in; eauto.
  Qed.

  Lemma reachable_steps_supported :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      Sem.steps tf (R.initial_config roots) before ->
      Sem.steps tf before after ->
      supported_steps (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite before after Hprefix Hsteps.
    eapply steps_supported; [apply Sem.system_supported| |exact Hsteps].
    eapply E.steps_in; [apply Sem.system_supported| |exact Hprefix].
    split; [apply E.empty_state_in|exact (Sem.initial_supported finite)].
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
        E.control_in support (R.cfg_control first) ->
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
      assert (Hconfig : E.config_in (Sem.support finite) first).
      { eapply E.steps_in; [apply Sem.system_supported| |exact Hprefix].
        split; [apply E.empty_state_in|exact (Sem.initial_supported finite)]. }
      pose proof (proj2 Hconfig) as Hsupported.
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

  End Payment.
  Module Dependencies.
  Lemma observed_ranking :
    forall st x next entry,
      R.observe st x = (next, entry) ->
      R.Ranking.observe (R.ranking st) x =
        (R.ranking next, R.handle_rank entry).
  Proof.
    intros st x next entry Hobserve. unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) x);
      inversion Hobserve. reflexivity.
  Qed.


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
      (exists reader_rank,
        R.Ranking.lookup (R.ranking st) reader = Some reader_rank /\
        R.Ranking.lookup (R.ranking st) dependency = None) \/
      ranked_before st reader dependency.

  Lemma is_dormant_rank_unobserved :
    forall st variable,
      R.is_dormant st variable = true ->
      R.Ranking.lookup (R.ranking st) variable = None.
  Proof.
    intros st variable Hdormant. unfold R.is_dormant in Hdormant.
    apply Bool.andb_true_iff in Hdormant as [_ Hrest].
    apply Bool.andb_true_iff in Hrest as [_ Hrank].
    destruct (R.Ranking.lookup (R.ranking st) variable);
      inversion Hrank. reflexivity.
  Qed.

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
      (forall variable,
        R.Ranking.lookup (R.ranking after) variable =
        R.Ranking.lookup (R.ranking before) variable) ->
      (forall dependency,
        R.lookup_set (R.readers after) dependency =
        R.lookup_set (R.readers before) dependency) ->
      controlled_included before after ->
      readers_ranked before ->
      readers_ranked after.
  Proof.
    intros before after Hextends Hranks Hreaders Hincluded Hranked
      dependency reader Hregistered Hnoncontrolled.
    destruct (Hranked dependency reader) as
      [[reader_rank [Hreader Hdependency]] | Hbefore].
    - unfold reader_registered in *. now rewrite Hreaders in Hregistered.
    - eapply noncontrolled_reflect; eauto.
    - left. exists reader_rank. now rewrite Hranks, Hranks.
    - right. now apply ranked_before_extended with (before := before).
  Qed.

  Lemma readers_ranked_promote :
    forall st variable,
      readers_ranked st -> readers_ranked (R.promote_controlled st variable).
  Proof.
    intros st variable Hranked.
    eapply (@readers_ranked_weaken st (R.promote_controlled st variable)).
    - apply rank_extends_same_ranking. reflexivity.
    - reflexivity.
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
      + right. exists (R.handle_rank reader), (R.handle_rank dependency).
        repeat split; auto.
      + apply Hranked; assumption.
    - rewrite ML.lookup_update_other in Hregistered by exact Hneq.
      apply Hranked; assumption.
  Qed.

  Lemma readers_ranked_add_unranked_reader :
    forall st dependency reader,
      R.Ranking.lookup (R.ranking st) dependency = None ->
      handle_valid st reader ->
      readers_ranked st ->
      readers_ranked (R.add_reader st dependency
        (R.handle_variable reader)).
  Proof.
    intros st dependency reader Hdependency Hreader Hranked
      observed current Hregistered Hnoncontrolled.
    unfold reader_registered, R.add_reader, R.lookup_set in Hregistered.
    cbn in Hregistered, Hnoncontrolled.
    destruct (V.eq_dec observed dependency) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hregistered.
      apply SL.add_spec in Hregistered.
      destruct Hregistered as [Hequal | Hregistered].
      + subst current. left. exists (R.handle_rank reader). auto.
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
    destruct (side_update_result st source target raw).
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

  Lemma readers_ranked_mark_side_dirty :
    forall st target,
      readers_ranked st -> readers_ranked (R.mark_side_dirty st target).
  Proof. intros st target Hranked. exact Hranked. Qed.

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

  Lemma unranked_reader_observe : forall st target next entry dependency reader reader_rank,
    R.observe st target = (next, entry) ->
    R.Ranking.lookup (R.ranking st) reader = Some reader_rank ->
    R.Ranking.lookup (R.ranking st) dependency = None ->
    (exists rank, R.Ranking.lookup (R.ranking next) reader = Some rank /\
      R.Ranking.lookup (R.ranking next) dependency = None) \/
    ranked_before next reader dependency.
  Proof.
    intros st target next entry dependency reader reader_rank Hobserve Hreader Hdependency.
    destruct (V.eq_dec dependency target) as [-> | Hneq].
      + right. exists reader_rank, (R.handle_rank entry).
        repeat split.
        * exact (@RankLaws.observe_preserves
            (R.ranking st) target (R.ranking next)
            (R.handle_rank entry) reader reader_rank
            (@observed_ranking st target next entry Hobserve) Hreader).
        * exact (@RankLaws.observe_lookup
            (R.ranking st) target (R.ranking next)
            (R.handle_rank entry)
            (@observed_ranking st target next entry Hobserve)).
        * eapply DormantRankLaws.observe_fresh_above.
          -- exact Hdependency.
          -- exact (@observed_ranking st target next entry Hobserve).
          -- exact Hreader.
      + destruct (R.Ranking.lookup (R.ranking st) target)
          as [target_rank |] eqn:Htarget.
        * pose proof (@RankLaws.observe_existing
            (R.ranking st) target target_rank Htarget) as Hexisting.
          pose proof (@observed_ranking st target next entry Hobserve)
            as Hobserved.
          rewrite Hexisting in Hobserved. inversion Hobserved; subst.
          left. exists reader_rank. split; assumption.
        * left. exists reader_rank. split.
          -- exact (@RankLaws.observe_preserves
               (R.ranking st) target (R.ranking next)
               (R.handle_rank entry) reader reader_rank
               (@observed_ranking st target next entry Hobserve) Hreader).
          -- eapply DormantRankLaws.observe_fresh_preserves_absent.
             ++ exact Htarget.
             ++ exact (@observed_ranking st target next entry Hobserve).
             ++ exact Hneq.
             ++ exact Hdependency.
  Qed.

  Lemma readers_ranked_observe :
    forall st target next entry,
      readers_ranked st ->
      R.observe st target = (next, entry) ->
      readers_ranked next.
  Proof.
    intros st target next entry Hranked Hobserve dependency reader
      Hregistered Hnoncontrolled.
    assert (Hregistered_before : reader_registered st reader dependency).
    {
      unfold reader_registered, R.lookup_set in *.
      now rewrite (@readers_observe st target next entry Hobserve)
        in Hregistered.
    }
    assert (Hnoncontrolled_before :
      S.mem dependency (R.controlled st) = false).
    {
      rewrite (@Measure.controlled_observe st target next entry Hobserve)
        in Hnoncontrolled. exact Hnoncontrolled.
    }
    destruct (Hranked dependency reader Hregistered_before
      Hnoncontrolled_before) as
      [[reader_rank [Hreader Hdependency]] | Hbefore].
    - eapply unranked_reader_observe; eauto.
    - right. eapply ranked_before_extended.
      + exact (@rank_extends_observe st target next entry Hobserve).
      + exact Hbefore.
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

  Lemma readers_ranked_remember_dormant :
    forall st variable,
      readers_ranked st -> readers_ranked (R.remember_dormant st variable).
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
    intros st owner value Hranked.
    unfold R.write_changed_value.
    set (middle := R.enqueue_all
      (R.with_sigma st (M.update (R.sigma st) owner value))
      (S.elements (R.lookup_set (R.readers st) owner))).
    assert (Hmiddle : readers_ranked middle).
    {
      unfold middle. apply readers_ranked_enqueue_all.
      exact Hranked.
    }
    intros dependency reader Hregistered Hnoncontrolled.
    apply Hmiddle.
    - unfold reader_registered, R.lookup_set in Hregistered |- *. cbn in *.
      destruct (V.eq_dec dependency owner) as [-> | Hneq].
      + rewrite ML.lookup_update_same, SL.empty_spec in Hregistered.
        discriminate.
      + now rewrite ML.lookup_update_other in Hregistered by exact Hneq.
    - exact Hnoncontrolled.
  Qed.

  Lemma readers_ranked_cancel_dirty_target :
    forall st target,
      readers_ranked st -> readers_ranked (R.cancel_dirty_target st target).
  Proof. intros st target Hranked. exact Hranked. Qed.

  Lemma readers_ranked_try_dirty_read :
    forall tf st owner target next,
      readers_ranked st ->
      R.try_dirty_read tf st owner target = Some next ->
      readers_ranked next.
  Proof.
    intros tf st owner target next Hranked Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst;
      eauto 8 using readers_ranked_with_started,
        readers_ranked_promote,
        readers_ranked_with_phases, readers_ranked_write_changed,
        readers_ranked_cancel_dirty_target.
  Qed.

  Lemma prepared_noncontrolled_order : forall st owner target next,
    controlled_included
      (R.materialize (R.get_control_state st owner target)
        (R.handle_variable target)) next ->
    S.mem (R.handle_variable target) (R.controlled next) = false ->
    Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true.
  Proof.
    intros st owner target next Hincluded Hnoncontrolled.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target))
      eqn:Horder; [reflexivity|].
    pose proof (@noncontrolled_reflect _ next (R.handle_variable target)
      Hincluded Hnoncontrolled) as Hprepared.
    unfold R.get_control_state, R.materialize in Hprepared.
    rewrite Horder in Hprepared. destruct (R.is_materialized _ _); cbn in Hprepared.
    all: assert (S.mem (R.handle_variable target)
      (S.add (R.handle_variable target) (R.controlled st)) = true)
      by (apply SL.add_spec; now left).
    all: congruence.
  Qed.

  Lemma readers_ranked_dirty_get_ready :
    forall tf st owner target,
      handle_valid st owner ->
      handle_valid st target ->
      readers_ranked st ->
      readers_ranked (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target Howner Htarget Hranked.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hprepared : readers_ranked prepared).
    { unfold prepared. apply readers_ranked_materialize.
      unfold R.get_control_state.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        auto using readers_ranked_promote. }
    assert (Hextends : rank_extends st prepared).
    { eapply (@rank_extends_trans st
        (R.get_control_state st owner target) prepared).
      - unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          [apply rank_extends_refl | apply rank_extends_same_ranking;
           reflexivity].
      - unfold prepared. apply rank_extends_materialize. }
    assert (Horder : forall next,
      controlled_included prepared next ->
      S.mem (R.handle_variable target) (R.controlled next) = false ->
      Nat.ltb (R.handle_rank owner) (R.handle_rank target) = true).
    { intros next Hincluded Hnoncontrolled.
      eapply prepared_noncontrolled_order; eauto. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - eapply readers_ranked_add_reader.
      + eapply handle_valid_extended;
          [eapply rank_extends_try_dirty_read; eauto|].
        eapply handle_valid_extended; eauto.
      + eapply handle_valid_extended;
          [eapply rank_extends_try_dirty_read; eauto|].
        eapply handle_valid_extended; eauto.
      + eapply readers_ranked_try_dirty_read; eauto.
      + apply Horder. intros x Hx.
        eapply Measure.controlled_try_dirty_read_mono; eauto.
    - eapply readers_ranked_add_reader.
      + eapply handle_valid_extended; eauto.
      + eapply handle_valid_extended; eauto.
      + exact Hprepared.
      + apply Horder. intros x Hx. exact Hx.
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

  Lemma readers_ranked_observed_dirty_get_ready :
    forall tf st target next entry owner,
      handle_valid st owner -> readers_ranked st ->
      R.observe st target = (next, entry) ->
      readers_ranked (R.dirty_get_ready_state tf next owner entry).
  Proof.
    intros tf st target next entry owner Howner Hranked Hobserve.
    eapply readers_ranked_dirty_get_ready.
    - eapply handle_valid_extended;
        [exact (@rank_extends_observe st target next entry Hobserve)|exact Howner].
    - exact (@observed_handle_valid st target next entry Hobserve).
    - eapply readers_ranked_observe; eauto.
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
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try (unfold R.request_spawn;
      match goal with |- context [if ?test then _ else _] => destruct test end;
      exact Hranked).
    all: eauto 4 using readers_ranked_with_queue, readers_ranked_with_started,
      readers_ranked_start_evaluation, readers_ranked_set_value,
      readers_ranked_add_unranked_reader, is_dormant_rank_unobserved,
      readers_ranked_remember_dormant, readers_ranked_observed_dirty_get_ready,
      readers_ranked_observed_get_ready, readers_ranked_observed_enqueued_get_ready,
      readers_ranked_mark_side_dirty, readers_ranked_side_ready,
      readers_ranked_enqueue_handle, readers_ranked_materialize,
      readers_ranked_observe, readers_ranked_get_ready.
    apply readers_ranked_enqueue_handle, readers_ranked_mark_side_dirty,
      readers_ranked_side_ready. eapply readers_ranked_observe; eauto.
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

  Lemma reachable_config_supported :
    forall tf roots (finite : Sem.finite_system tf roots) after,
      Sem.steps tf (R.initial_config roots) after ->
      E.config_in (Sem.support finite) after.
  Proof.
    intros tf roots finite after Hsteps.
    eapply E.steps_in; [apply Sem.system_supported| |exact Hsteps].
    split; [apply E.empty_state_in|exact (Sem.initial_supported finite)].
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
       ~ OUL.equivalent
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
      destruct (Hranked (R.handle_variable owner) queued
        Hreader Hcontrolled) as
        [[reader_rank [_ Hunranked]] | Hbefore].
      + rewrite (proj1 (handles_control_valid
          (reachable_handles_valid Hreachable))) in Hunranked.
        discriminate.
      + exact Hbefore.
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

  Lemma queued_variable_cancel_dirty_target_inv :
    forall st target variable,
      queued_variable (R.cancel_dirty_target st target) variable ->
      queued_variable st variable.
  Proof.
    intros st target variable [entry [Hentry Hvariable]].
    exists entry. split; [|exact Hvariable].
    unfold R.cancel_dirty_target in Hentry. cbn in Hentry.
    now apply queue_remove_rank_members in Hentry.
  Qed.

  Lemma unpaid_try_dirty_read_queue_subset :
    forall support tf st owner target next,
      List.In (R.handle_variable target) support ->
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      R.try_dirty_read tf st owner target = Some next ->
      Measure.charged_update_credit support next =
        Measure.charged_update_credit support st ->
      forall variable,
        queued_variable next variable -> queued_variable st variable.
  Proof.
    intros support tf st owner target next Htarget Hcontrolled Hread Hcredit
      variable Hqueued.
    pose proof Hread as Hread_original.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try (rewrite Hcontrolled in Heqb0; discriminate).
    all: try (apply queued_variable_cancel_dirty_target_inv in Hqueued;
      exact Hqueued).
    exfalso.
    pose proof (@Payment.charged_update_credit_try_dirty_read_decreases
      support tf st owner target _ Htarget Hcontrolled Hread_original)
      as Hstrict.
    specialize (Hstrict ltac:(
      rewrite Accounting.sigma_value_write_changed_same;
      now apply Accounting.equivalent_false)).
    lia.
  Qed.

  Lemma unpaid_try_dirty_read_queue_entries_subset :
    forall support tf st owner target next,
      List.In (R.handle_variable target) support ->
      S.mem (R.handle_variable target) (R.controlled st) = true ->
      R.try_dirty_read tf st owner target = Some next ->
      Measure.charged_update_credit support next =
        Measure.charged_update_credit support st ->
      forall entry,
        List.In entry (R.queue next) -> List.In entry (R.queue st).
  Proof.
    intros support tf st owner target next Htarget Hcontrolled Hread Hcredit
      entry Hqueued.
    pose proof Hread as Hread_original.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] => destruct condition eqn:?
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst; cbn in *.
    all: try (rewrite Hcontrolled in Heqb0; discriminate).
    all: try (apply queue_remove_rank_members in Hqueued; exact Hqueued).
    exfalso.
    pose proof (@Payment.charged_update_credit_try_dirty_read_decreases
      support tf st owner target _ Htarget Hcontrolled Hread_original)
      as Hstrict.
    specialize (Hstrict ltac:(
      rewrite Accounting.sigma_value_write_changed_same;
      now apply Accounting.equivalent_false)).
    lia.
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
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
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

  Lemma unpaid_observed_side_mark_cannot_grow :
    forall support tf st observed source target target_variable raw
      before_control after_control,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      List.In target_variable support ->
      R.observe st target_variable = (observed, target) ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := before_control |}
        {| R.cfg_state :=
             R.mark_side_dirty
               (R.side_ready_state observed source target raw)
               target_variable;
           R.cfg_control := after_control |} ->
      ~ Accounting.side_grows observed source target raw.
  Proof.
    intros support tf st observed source target target_variable raw
      before_control after_control Hnodup Hsource Htarget Hobserve
      [_ [_ [Hcontrolled Hcredit]]] Hgrows.
    assert (Htarget_handle :
      List.In (R.handle_variable target) support).
    { rewrite (@observed_handle_variable st target_variable observed target
        Hobserve). exact Htarget. }
    cbn in Hcontrolled, Hcredit.
    rewrite Payment.uncontrolled_count_mark_side_dirty in Hcontrolled.
    rewrite <- (@Payment.uncontrolled_count_observe
      support st target_variable observed target Hobserve) in Hcontrolled.
    pose proof (@Payment.side_ready_stable_from_count
      support observed source target raw Hnodup Hsource Hcontrolled) as Hstable.
    pose proof (@Accounting.charged_update_credit_side_ready_decreases
      support observed source target raw Hsource Htarget_handle Hstable Hgrows)
      as Hstrict.
    rewrite Payment.charged_update_credit_mark_side_dirty in Hcredit.
    rewrite <- (@Payment.charged_update_credit_observe
      support st target_variable observed target Hobserve) in Hcredit.
    cbn in Hcredit. lia.
  Qed.

  Lemma unpaid_observed_side_mark_enqueue_cannot_grow :
    forall support tf st observed source target target_variable raw
      before_control after_control,
      NoDup support ->
      List.In (R.handle_variable source) support ->
      List.In target_variable support ->
      R.observe st target_variable = (observed, target) ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st; R.cfg_control := before_control |}
        {| R.cfg_state := R.enqueue_handle
             (R.mark_side_dirty
               (R.side_ready_state observed source target raw)
               target_variable) target;
           R.cfg_control := after_control |} ->
      ~ Accounting.side_grows observed source target raw.
  Proof.
    intros support tf st observed source target target_variable raw
      before_control after_control Hnodup Hsource Htarget Hobserve
      [_ [_ [Hcontrolled Hcredit]]] Hgrows.
    assert (Htarget_handle : List.In (R.handle_variable target) support).
    { rewrite (@observed_handle_variable st target_variable observed target
        Hobserve). exact Htarget. }
    cbn in Hcontrolled, Hcredit.
    rewrite Payment.uncontrolled_count_enqueue_handle,
      Payment.uncontrolled_count_mark_side_dirty in Hcontrolled.
    rewrite <- (@Payment.uncontrolled_count_observe
      support st target_variable observed target Hobserve) in Hcontrolled.
    pose proof (@Payment.side_ready_stable_from_count
      support observed source target raw Hnodup Hsource Hcontrolled) as Hstable.
    pose proof (@Accounting.charged_update_credit_side_ready_decreases
      support observed source target raw Hsource Htarget_handle Hstable Hgrows)
      as Hstrict.
    rewrite Payment.charged_update_credit_enqueue_handle,
      Payment.charged_update_credit_mark_side_dirty in Hcredit.
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
    destruct (side_update_result st (R.handle_variable active)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank active));
      exact Hqueued.
  Qed.

  Lemma queue_at_most_mark_side_dirty :
    forall owner st target,
      queue_at_most owner st ->
      queue_at_most owner (R.mark_side_dirty st target).
  Proof. intros owner st target Hqueue; exact Hqueue. Qed.

  Lemma queued_variable_mark_side_dirty_inv :
    forall st target variable,
      queued_variable (R.mark_side_dirty st target) variable ->
      queued_variable st variable.
  Proof. intros st target variable Hqueued; exact Hqueued. Qed.

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

  Lemma unpaid_dirty_get_queue_subset :
    forall support tf st owner target variable,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.charged_update_credit support st ->
      queued_variable (R.dirty_get_ready_state tf st owner target) variable ->
      queued_variable st variable.
  Proof.
    intros support tf st owner target variable Hnodup Htarget Hcount Hcredit
      Hqueued.
    pose proof Hcount as Hcount_original.
    unfold R.dirty_get_ready_state in Hcount, Hcredit, Hqueued.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - fold prepared in Hcount, Hcredit, Hqueued.
      rewrite Hread in Hcount, Hcredit, Hqueued.
      rewrite Payment.uncontrolled_count_add_reader in Hcount.
      rewrite Payment.charged_update_credit_add_reader in Hcredit.
      change (queued_variable next variable) in Hqueued.
      assert (Hbefore : S.mem (R.handle_variable target)
        (R.controlled st) = true).
      { eapply Payment.dirty_get_ready_target_controlled_from_count;
          [exact Hnodup | exact Htarget | exact Hcount_original |].
        unfold R.dirty_get_ready_state. fold prepared. rewrite Hread.
        unfold R.add_reader. cbn.
        eapply Payment.controlled_try_dirty_read_target; eauto. }
      destruct (@Payment.controlled_prepared_credit support st owner target Hbefore)
        as [Hprepared_controlled Hprepared_credit].
      fold prepared in Hprepared_credit.
      apply (@unpaid_try_dirty_read_queue_subset support tf prepared owner
        target next Htarget Hprepared_controlled Hread ltac:(lia)
        variable) in Hqueued.
      subst prepared. unfold R.get_control_state in Hqueued.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        now apply queued_variable_materialize_inv in Hqueued.
    - fold prepared in Hqueued. rewrite Hread in Hqueued.
      change (queued_variable prepared variable) in Hqueued.
      subst prepared. unfold R.get_control_state in Hqueued.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        now apply queued_variable_materialize_inv in Hqueued.
  Qed.

  Lemma unpaid_dirty_get_queue_entries_subset :
    forall support tf st owner target entry,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.charged_update_credit support st ->
      List.In entry (R.queue (R.dirty_get_ready_state tf st owner target)) ->
      List.In entry (R.queue st).
  Proof.
    intros support tf st owner target entry Hnodup Htarget Hcount Hcredit
      Hqueued.
    pose proof Hcount as Hcount_original.
    unfold R.dirty_get_ready_state in Hcount, Hcredit, Hqueued.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    destruct (R.try_dirty_read tf prepared owner target)
      as [next |] eqn:Hread.
    - fold prepared in Hcount, Hcredit, Hqueued.
      rewrite Hread in Hcount, Hcredit, Hqueued.
      rewrite Payment.uncontrolled_count_add_reader in Hcount.
      rewrite Payment.charged_update_credit_add_reader in Hcredit.
      change (List.In entry (R.queue next)) in Hqueued.
      assert (Hbefore : S.mem (R.handle_variable target)
        (R.controlled st) = true).
      { eapply Payment.dirty_get_ready_target_controlled_from_count;
          [exact Hnodup | exact Htarget | exact Hcount_original |].
        unfold R.dirty_get_ready_state. fold prepared. rewrite Hread.
        unfold R.add_reader. cbn.
        eapply Payment.controlled_try_dirty_read_target; eauto. }
      destruct (@Payment.controlled_prepared_credit support st owner target Hbefore)
        as [Hprepared_controlled Hprepared_credit].
      fold prepared in Hprepared_credit.
      apply (@unpaid_try_dirty_read_queue_entries_subset support tf prepared
        owner target next Htarget Hprepared_controlled Hread ltac:(lia)
        entry) in Hqueued.
      subst prepared. unfold R.get_control_state in Hqueued.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        unfold R.materialize in Hqueued;
        destruct (R.is_materialized _ _); exact Hqueued.
    - fold prepared in Hqueued. rewrite Hread in Hqueued.
      change (List.In entry (R.queue prepared)) in Hqueued.
      subst prepared. unfold R.get_control_state in Hqueued.
      destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
        unfold R.materialize in Hqueued;
        destruct (R.is_materialized _ _); exact Hqueued.
  Qed.

  Lemma unpaid_dirty_get_preserves_queue_at_most :
    forall support tf st owner target,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      queue_at_most owner st ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.charged_update_credit support st ->
      queue_at_most owner (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros support tf st owner target Hnodup Htarget Hqueue Hcount Hcredit
      variable Hqueued.
    apply Hqueue.
    eapply unpaid_dirty_get_queue_entries_subset; eauto.
  Qed.

  Lemma unpaid_dirty_get_preserves_unqueued :
    forall support tf st owner target variable,
      NoDup support ->
      List.In (R.handle_variable target) support ->
      ~ queued_variable st variable ->
      Measure.uncontrolled_count support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.uncontrolled_count support st ->
      Measure.charged_update_credit support
        (R.dirty_get_ready_state tf st owner target) =
        Measure.charged_update_credit support st ->
      ~ queued_variable
        (R.dirty_get_ready_state tf st owner target) variable.
  Proof.
    intros support tf st owner target variable Hnodup Htarget Hnotqueued
      Hcount Hcredit Hqueued.
    apply Hnotqueued.
    eapply unpaid_dirty_get_queue_subset; eauto.
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
    destruct (side_update_result st (R.handle_variable source)
      (R.handle_variable target) raw);
      destruct (Nat.ltb (R.handle_rank target) (R.handle_rank source));
      reflexivity.
  Qed.

  Lemma is_materialized_mark_side_dirty :
    forall st target observed,
      R.is_materialized (R.mark_side_dirty st target) observed =
      R.is_materialized st observed.
  Proof.
    reflexivity.
  Qed.

  Lemma is_materialized_observe :
    forall st target next entry variable,
      R.observe st target = (next, entry) ->
      R.is_materialized next variable = R.is_materialized st variable.
  Proof.
    intros st target next entry variable Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.Ranking.observe (R.ranking st) target);
      inversion Hobserve. reflexivity.
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

  Definition materialized_ranked (st : R.state) : Prop :=
    forall variable value,
      M.lookup (R.sigma st) variable = Some value ->
      exists rank,
        R.Ranking.lookup (R.ranking st) variable = Some rank.

  Lemma observed_unranked_unmaterialized :
    forall st target observed entry,
      materialized_ranked st ->
      R.Ranking.lookup (R.ranking st) target = None ->
      R.observe st target = (observed, entry) ->
      R.is_materialized observed target = false.
  Proof.
    intros st target observed entry Hranked Hlookup Hobserve.
    rewrite (@is_materialized_observe st target observed entry target
      Hobserve).
    unfold R.is_materialized.
    destruct (M.lookup (R.sigma st) target) as [value |] eqn:Hsigma;
      [|reflexivity].
    destruct (Hranked target value Hsigma) as [rank Hrank].
    rewrite Hlookup in Hrank. discriminate.
  Qed.

  Lemma dormant_observe_forces_recursive :
    forall st owner target observed entry,
      handle_valid st owner ->
      R.is_dormant st target = true ->
      R.observe st target = (observed, entry) ->
      andb (Nat.ltb (R.handle_rank owner) (R.handle_rank entry))
        (negb (R.is_materialized observed target)) = true.
  Proof.
    intros st owner target observed entry Howner Hdormant Hobserve.
    unfold R.is_dormant in Hdormant.
    apply Bool.andb_true_iff in Hdormant as [_ Hdormant].
    apply Bool.andb_true_iff in Hdormant as [Hsigma Hlookup].
    destruct (M.lookup (R.sigma st) target) eqn:Hsigma_lookup;
      try discriminate.
    destruct (R.Ranking.lookup (R.ranking st) target) eqn:Hrank_lookup;
      try discriminate.
    assert (Habove : Nat.ltb (R.handle_rank owner)
      (R.handle_rank entry) = true).
    {
      exact (@DormantRankLaws.observe_fresh_above
        (R.ranking st) target (R.ranking observed) (R.handle_rank entry)
        (R.handle_variable owner) (R.handle_rank owner)
        Hrank_lookup (@observed_ranking st target observed entry Hobserve)
        Howner).
    }
    assert (Hunmaterialized : R.is_materialized observed target = false).
    {
      rewrite (@is_materialized_observe st target observed entry target
        Hobserve).
      unfold R.is_materialized. rewrite Hsigma_lookup. reflexivity.
    }
    rewrite Habove, Hunmaterialized. reflexivity.
  Qed.

  Lemma materialized_ranked_preserved :
    forall before after,
      rank_extends before after ->
      R.sigma after = R.sigma before ->
      materialized_ranked before ->
      materialized_ranked after.
  Proof.
    intros before after Hextends Hsigma Hranked variable value Hlookup.
    rewrite Hsigma in Hlookup.
    destruct (Hranked variable value Hlookup) as [rank Hrank].
    exists rank. now apply Hextends.
  Qed.

  Lemma materialized_ranked_materialize :
    forall st variable,
      (exists rank,
        R.Ranking.lookup (R.ranking st) variable = Some rank) ->
      materialized_ranked st ->
      materialized_ranked (R.materialize st variable).
  Proof.
    intros st variable Hvariable Hranked. unfold R.materialize.
    destruct (R.is_materialized st variable); [exact Hranked |].
    intros observed value Hlookup. cbn in Hlookup |- *.
    destruct (V.eq_dec observed variable) as [-> | Hneq].
    - rewrite ML.lookup_update_same in Hlookup. inversion Hlookup; subst.
      exact Hvariable.
    - rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      now apply Hranked with (value := value).
  Qed.

  Lemma materialized_ranked_observe :
    forall st variable next entry,
      R.observe st variable = (next, entry) ->
      materialized_ranked st -> materialized_ranked next.
  Proof.
    intros st variable next entry Hobserve Hranked.
    eapply materialized_ranked_preserved.
    - exact (@rank_extends_observe st variable next entry Hobserve).
    - unfold R.observe in Hobserve.
      destruct (R.Ranking.observe (R.ranking st) variable);
        inversion Hobserve. reflexivity.
    - exact Hranked.
  Qed.

  Lemma materialized_ranked_get_ready :
    forall st owner target,
      handle_valid st target ->
      materialized_ranked st ->
      materialized_ranked (R.get_ready_state st owner target).
  Proof.
    intros st owner target Htarget Hranked. unfold R.get_ready_state.
    destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target)).
    - apply materialized_ranked_materialize; [|exact Hranked].
      exists (R.handle_rank target). exact Htarget.
    - apply materialized_ranked_materialize.
      + exists (R.handle_rank target). exact Htarget.
      + exact Hranked.
  Qed.

  Lemma materialized_ranked_enqueue_handle :
    forall st entry,
      materialized_ranked st ->
      materialized_ranked (R.enqueue_handle st entry).
  Proof.
    intros st entry Hranked. eapply materialized_ranked_preserved.
    - apply rank_extends_enqueue_handle.
    - reflexivity.
    - exact Hranked.
  Qed.

  Lemma materialized_ranked_side_ready :
    forall st source target raw,
      materialized_ranked st ->
      materialized_ranked (R.side_ready_state st source target raw).
  Proof.
    intros st source target raw Hranked.
    eapply materialized_ranked_preserved.
    - apply rank_extends_side_ready.
    - unfold R.side_ready_state, R.record_side_payload,
        R.promote_controlled.
      repeat
        match goal with
        | |- context [if ?condition then _ else _] => destruct condition
        | |- context [let '(_, _) := ?pair in _] => destruct pair
        end;
        reflexivity.
    - exact Hranked.
  Qed.

  Lemma materialized_ranked_mark_side_dirty :
    forall st target,
      materialized_ranked st ->
      materialized_ranked (R.mark_side_dirty st target).
  Proof. intros st target Hranked. exact Hranked. Qed.

  Lemma materialized_ranked_observe_enqueue_materialize :
    forall st variable observed entry,
      R.observe st variable = (observed, entry) ->
      materialized_ranked st ->
      materialized_ranked
        (R.materialize (R.enqueue_handle observed entry) variable).
  Proof.
    intros st variable observed entry Hobserve Hranked.
    apply materialized_ranked_materialize.
    - rewrite <- (@observed_handle_variable st variable observed entry
        Hobserve).
      exists (R.handle_rank entry).
      eapply handle_valid_extended.
      + apply rank_extends_enqueue_handle.
      + exact (@observed_handle_valid st variable observed entry Hobserve).
    - apply materialized_ranked_enqueue_handle.
      eapply materialized_ranked_observe; eauto.
  Qed.

  Lemma materialized_ranked_write_changed :
    forall st owner value,
      (exists rank,
        R.Ranking.lookup (R.ranking st) owner = Some rank) ->
      materialized_ranked st ->
      materialized_ranked (R.write_changed_value st owner value).
  Proof.
    intros st owner value Howner Hranked observed stored Hlookup.
    unfold R.write_changed_value in Hlookup. cbn in Hlookup.
    rewrite Accounting.sigma_enqueue_all in Hlookup.
    destruct (V.eq_dec observed owner) as [-> | Hneq].
    - change (M.lookup (M.update (R.sigma st) owner value) owner =
        Some stored) in Hlookup.
      rewrite ML.lookup_update_same in Hlookup. inversion Hlookup; subst.
      destruct Howner as [rank Howner]. exists rank.
      exact (@rank_extends_write_changed st owner stored owner rank Howner).
    - change (M.lookup (M.update (R.sigma st) owner value) observed =
        Some stored) in Hlookup.
      rewrite ML.lookup_update_other in Hlookup by exact Hneq.
      destruct (Hranked observed stored Hlookup) as [rank Hobserved].
      exists rank.
      exact (@rank_extends_write_changed st owner value observed rank Hobserved).
  Qed.

  Lemma materialized_ranked_cancel_dirty_target :
    forall st target,
      materialized_ranked st ->
      materialized_ranked (R.cancel_dirty_target st target).
  Proof. intros st target Hranked. exact Hranked. Qed.

  Lemma materialized_ranked_try_dirty_read :
    forall tf st owner target next,
      handle_valid st target ->
      materialized_ranked st ->
      R.try_dirty_read tf st owner target = Some next ->
      materialized_ranked next.
  Proof.
    intros tf st owner target next Htarget Hranked Hread.
    unfold R.try_dirty_read in Hread.
    repeat
      match type of Hread with
      | context [if ?condition then _ else _] =>
          destruct condition eqn:?
      | context [match ?subject with _ => _ end] =>
          destruct subject eqn:?
      | context [let '(_, _) := ?pair in _] => destruct pair eqn:?
      end;
      try discriminate; inversion Hread; subst;
      eauto 8 using materialized_ranked_write_changed,
        materialized_ranked_cancel_dirty_target.
  Qed.

  Lemma materialized_ranked_dirty_get_ready :
    forall tf st owner target,
      handle_valid st target ->
      materialized_ranked st ->
      materialized_ranked (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros tf st owner target Htarget Hranked.
    unfold R.dirty_get_ready_state.
    set (prepared := R.materialize
      (R.get_control_state st owner target) (R.handle_variable target)).
    assert (Hextends : rank_extends st prepared).
    { eapply (@rank_extends_trans st
        (R.get_control_state st owner target) prepared).
      - unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          [apply rank_extends_refl | apply rank_extends_same_ranking;
           reflexivity].
      - unfold prepared. apply rank_extends_materialize. }
    assert (Htarget_prepared : handle_valid prepared target).
    { eapply handle_valid_extended; eauto. }
    assert (Hprepared : materialized_ranked prepared).
    { unfold prepared. apply materialized_ranked_materialize.
      - exists (R.handle_rank target). unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Htarget.
      - unfold R.get_control_state.
        destruct (Nat.ltb (R.handle_rank owner) (R.handle_rank target));
          exact Hranked. }
    destruct (R.try_dirty_read tf prepared owner target) as [next|] eqn:Hread.
    - change (materialized_ranked next).
      eapply materialized_ranked_try_dirty_read; eauto.
    - change (materialized_ranked prepared). exact Hprepared.
  Qed.

  Lemma materialized_ranked_set_value :
    forall st owner direct,
      (exists rank,
        R.Ranking.lookup (R.ranking st) owner = Some rank) ->
      materialized_ranked st ->
      materialized_ranked (R.set_value st owner direct).
  Proof.
    intros st owner direct Howner Hranked. unfold R.set_value.
    destruct (R.equivalent
      (D.join direct (R.aggregate st owner)) (R.sigma_value st owner));
      [exact Hranked |].
    destruct (S.mem owner (R.controlled st)).
    - destruct (U.update false owner (R.stored_phase st owner)
        (R.sigma_value st owner) (D.join direct (R.aggregate st owner)))
        as [phase output]. cbn.
      destruct (R.equivalent output (R.sigma_value st owner)).
      + exact Hranked.
      + apply materialized_ranked_write_changed; assumption.
    - apply materialized_ranked_write_changed; assumption.
  Qed.

  Lemma initial_materialized_ranked :
    materialized_ranked (R.cfg_state (R.initial_config nil)).
  Proof.
    intros variable value Hlookup.
    change (M.lookup (M.empty D.t) variable = Some value) in Hlookup.
    rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Lemma materialized_ranked_started : forall st owner started,
    handle_valid st owner -> materialized_ranked st ->
    materialized_ranked (R.with_started
      (R.start_evaluation st (R.handle_variable owner)) started).
  Proof.
    intros st owner started Howner Hranked.
    unfold R.start_evaluation, R.reset_local_sides.
    apply materialized_ranked_materialize; [eexists; exact Howner|exact Hranked].
  Qed.

  Lemma materialized_ranked_enqueued_get : forall st target next entry owner,
    R.observe st target = (next, entry) -> materialized_ranked st ->
    materialized_ranked (R.get_ready_state (R.enqueue_handle next entry) owner entry).
  Proof.
    intros st target next entry owner Hobserve Hranked.
    apply materialized_ranked_get_ready.
    - eapply handle_valid_extended; [apply rank_extends_enqueue_handle|].
      eapply observed_handle_valid; eauto.
    - apply materialized_ranked_enqueue_handle. eapply materialized_ranked_observe; eauto.
  Qed.

  Lemma materialized_ranked_step :
    forall tf before after,
      handles_valid before ->
      materialized_ranked (R.cfg_state before) ->
      Sem.step tf before after ->
      materialized_ranked (R.cfg_state after).
  Proof.
    intros tf [st control] after Hvalid Hranked Hstep.
    destruct Hvalid as [Hrank_valid Hqueue_valid Hcontrol_valid].
    unfold Sem.step in Hstep. cbn in Hstep, Hcontrol_valid.
    destruct control; cbn in Hstep;
      repeat
        match type of Hstep with
        | context [match ?subject with _ => _ end] =>
            destruct subject eqn:?Hcase
        | context [if ?condition then _ else _] =>
            destruct condition eqn:?Hcase
        end;
      try discriminate; inversion Hstep; subst; cbn in Hcontrol_valid |- *.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try exact Hranked.
    all: try (unfold R.request_spawn;
      match goal with |- context [if ?test then _ else _] => destruct test end;
      exact Hranked).
    all: try (apply materialized_ranked_enqueue_handle).
    all: try (apply materialized_ranked_mark_side_dirty).
    all: try (apply materialized_ranked_side_ready).
    all: eauto 4 using materialized_ranked_set_value, materialized_ranked_get_ready,
      materialized_ranked_dirty_get_ready, materialized_ranked_observe,
      observed_handle_valid, materialized_ranked_observe_enqueue_materialize,
      materialized_ranked_enqueued_get, materialized_ranked_started.
  Qed.

  Lemma materialized_ranked_steps :
    forall tf before after,
      handles_valid before ->
      materialized_ranked (R.cfg_state before) ->
      Sem.steps tf before after ->
      materialized_ranked (R.cfg_state after).
  Proof.
    intros tf before after Hvalid Hranked Hsteps.
    induction Hsteps.
    - exact Hranked.
    - apply IHHsteps.
      + eapply next_config_handles_valid; eauto.
      + eapply materialized_ranked_step; eauto.
  Qed.

  Lemma reachable_materialized_ranked :
    forall tf roots after,
      Sem.steps tf (R.initial_config roots) after ->
      materialized_ranked (R.cfg_state after).
  Proof.
    intros tf roots after Hsteps.
    eapply materialized_ranked_steps; eauto.
    - apply initial_handles_valid.
    - apply initial_materialized_ranked.
  Qed.

  Lemma root_step_has_shape :
    forall tf owner base before after,
      control_at_owner_root owner base (R.cfg_control before) ->
      queue_at_most owner (R.cfg_state before) ->
      ~ queued_variable (R.cfg_state before) (R.handle_variable owner) ->
      materialized_ranked (R.cfg_state before) ->
      Sem.step tf before after ->
      root_step_shape owner base after.
  Proof.
    intros tf owner base [st control] after Hroot Hqueue Hunqueued
      Hmaterialized_ranked Hstep.
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
    all: try solve [exfalso; eapply queue_at_most_excludes_higher_pop; eauto].
    all: eapply RootStepFreshChild; [reflexivity |]; cbn.
    all: repeat match goal with
      | H : andb _ _ = true |- _ =>
          apply Bool.andb_true_iff in H; destruct H
      | H : negb _ = true |- _ =>
          apply Bool.negb_true_iff in H
      end.
    all: try rewrite is_materialized_mark_side_dirty,
      is_materialized_side_ready.
    all: try rewrite is_materialized_side_ready.
    all: match goal with
      | Hobserve : R.observe ?before ?target = (?observed, ?entry) |- _ =>
          rewrite (@observed_handle_variable before target observed entry
            Hobserve);
          first [assumption |
            eapply observed_unranked_unmaterialized; eauto]
      end.
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

  Lemma unpaid_observed_get_queue_subset :
    forall support tf st observed owner target variable next k after_control,
      NoDup support ->
      E.control_in support (R.RunRhs owner (R.ConstraintSystem.Get variable next) k) ->
      R.observe st variable = (observed, target) ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Get variable next) k |}
        {| R.cfg_state := R.dirty_get_ready_state tf observed owner target;
           R.cfg_control := after_control |} ->
      incl (R.queue (R.dirty_get_ready_state tf observed owner target)) (R.queue st).
  Proof.
    intros support tf st observed owner target variable next k after_control
      Hnodup [_ [Hrhs _]] Ho [_ [_ [Hcount Hcredit]]] entry Hin.
    destruct (Payment.rhs_supported_get_inv Hrhs) as [Htarget _].
    rewrite <- (@queue_observe st variable observed target Ho).
    eapply unpaid_dirty_get_queue_entries_subset; [exact Hnodup| | | |exact Hin].
    - now rewrite (@observed_handle_variable st variable observed target Ho).
    - rewrite (@Payment.uncontrolled_count_observe support st variable observed target Ho).
      exact Hcount.
    - rewrite (@Payment.charged_update_credit_observe support st variable observed target Ho).
      exact Hcredit.
  Qed.

  Lemma unpaid_side_enqueue_no_growth :
    forall support tf st observed owner target variable raw next k after_control,
      NoDup support ->
      E.control_in support (R.RunRhs owner (R.ConstraintSystem.Side variable raw next) k) ->
      R.observe st variable = (observed, target) ->
      Payment.unpaid_step support tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (R.ConstraintSystem.Side variable raw next) k |}
        {| R.cfg_state := R.enqueue_handle
             (R.mark_side_dirty (R.side_ready_state observed owner target raw) variable) target;
           R.cfg_control := after_control |} ->
      R.aggregate_grew observed (R.side_ready_state observed owner target raw) variable = true ->
      False.
  Proof.
    intros support tf st observed owner target variable raw next k after_control
      Hnodup [Howner [Hrhs _]] Ho Hunpaid Hgrows.
    destruct (Payment.rhs_supported_side_inv Hrhs) as [Htarget _].
    eapply (@unpaid_observed_side_mark_enqueue_cannot_grow
      support tf st observed owner target variable raw);
      [exact Hnodup|exact Howner|exact Htarget|exact Ho|exact Hunpaid|].
    unfold Accounting.side_grows.
    rewrite (@observed_handle_variable st variable observed target Ho). exact Hgrows.
  Qed.

  Lemma dormant_side_cannot_enqueue : forall st owner variable observed target,
    handle_valid st owner -> R.is_dormant st variable = true ->
    R.observe st variable = (observed, target) ->
    andb (Nat.ltb (R.handle_rank owner) (R.handle_rank target))
      (negb (R.is_materialized observed variable)) = false -> False.
  Proof.
    intros st owner variable observed target Howner Hdormant Ho Hnot.
    rewrite (@dormant_observe_forces_recursive st owner variable observed target
      Howner Hdormant Ho) in Hnot. discriminate.
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
    all: try (unfold R.request_spawn;
      match goal with |- context [if ?test then _ else _] => destruct test end;
      exact Hqueue).
    all: try (apply queue_at_most_start_evaluation; exact Hqueue).
    all: try (apply queue_at_most_get_ready; exact Hqueue).
    all: try solve [eauto 4 using queue_at_most_pop, queue_at_most_start_evaluation,
      queue_at_most_get_ready, queue_at_most_observe, queue_at_most_side_ready,
      queue_at_most_mark_side_dirty, unpaid_ret_preserves_queue_at_most].
    all: try solve [first [apply queue_at_most_get_ready|apply queue_at_most_materialize];
      apply queue_at_most_enqueue_handle;
      [eapply observed_not_higher_is_at_most;
        [exact (handles_rank_valid Hhandles)
        |exact (proj1 (handles_control_valid Hhandles))|eassumption|assumption]
      |eapply queue_at_most_observe; eauto]].
    all: try solve [intros entry Hin; apply Hqueue;
      eapply unpaid_observed_get_queue_subset;
      [exact (Sem.support_nodup finite)|exact (proj2 Hsupported)
      |eassumption|exact Hunpaid|exact Hin]].
    - exfalso.
      eapply dormant_side_cannot_enqueue;
        [exact (proj1 (handles_control_valid Hhandles))|exact Hcase1|exact Hcase0|exact Hcase2].
    - exfalso.
      eapply unpaid_side_enqueue_no_growth;
        [exact (Sem.support_nodup finite)|exact (proj2 Hsupported)
        |eassumption|exact Hunpaid|assumption].
    all: try assumption.
  Qed.

  Lemma unmaterialized_enqueue_preserves_unqueued :
    forall tf roots st owner body k target observed entry,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunRhs owner body k |} ->
      R.observe st target = (observed, entry) ->
      R.is_materialized observed target = false ->
      ~ queued_variable st (R.handle_variable owner) ->
      ~ queued_variable (R.enqueue_handle observed entry) (R.handle_variable owner).
  Proof.
    intros tf roots st owner body k target observed entry Hreach Ho Hfresh Hnot Hqueued.
    destruct (@queued_variable_enqueue_handle_origin observed entry
      (R.handle_variable owner) Hqueued) as [Hequal|Hold].
    - eapply (@reachable_observed_unmaterialized_not_owner
        tf roots st owner body k target observed entry Hreach Ho Hfresh).
      symmetry. exact Hequal.
    - apply Hnot. eapply queued_variable_observe_inv; eauto.
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
    all: try apply queued_variable_mark_side_dirty_inv in Hqueued.
    all: try contradiction.
    all: try (destruct Hroot as [-> ->]).
    all: try (apply Hunqueued; exact Hqueued).
    all: try (unfold R.request_spawn in Hqueued;
      match type of Hqueued with context [if ?test then _ else _] => destruct test end;
      apply Hunqueued; exact Hqueued).
    all: try change (queued_variable (R.start_evaluation st (R.handle_variable owner))
      (R.handle_variable owner)) in Hqueued.
    all: repeat match type of Hqueued with
      | queued_variable (R.get_ready_state _ _ _) _ =>
          apply queued_variable_get_ready_inv in Hqueued
      | queued_variable (R.side_ready_state _ _ _ _) _ =>
          apply queued_variable_side_ready_inv in Hqueued
      | queued_variable (R.materialize _ _) _ =>
          apply queued_variable_materialize_inv in Hqueued
      | queued_variable (R.start_evaluation _ _) _ =>
          apply queued_variable_start_evaluation_inv in Hqueued
      end.
    all: try solve [apply Hunqueued; eauto 3 using queued_variable_observe_inv,
      queued_variable_pop_inv].
    all: try solve [eapply unpaid_ret_preserves_unqueued; eauto].
    all: try solve [eapply unmaterialized_enqueue_preserves_unqueued;
      [exact Hreachable|eassumption|
       first [assumption|eapply observed_unranked_unmaterialized;
         [exact (reachable_materialized_ranked Hreachable)|eassumption|eassumption]]
      |exact Hunqueued|exact Hqueued]].
    all: try solve [apply Hunqueued; destruct Hqueued as [entry [Hin Heq]];
      exists entry; split; [|exact Heq];
      eapply unpaid_observed_get_queue_subset;
      [exact (Sem.support_nodup finite)|exact (proj2 Hsupported)
      |eassumption|exact Hunpaid|exact Hin]].
    all: try exact (R.handle_variable owner).
    - pose proof (reachable_handles_valid Hreachable) as Hhandles.
      eapply dormant_side_cannot_enqueue;
        [exact (proj1 (handles_control_valid Hhandles))|exact Hcase1|exact Hcase0|exact Hcase2].
    - eapply unpaid_side_enqueue_no_growth;
        [exact (Sem.support_nodup finite)|exact (proj2 Hsupported)
        |eassumption|exact Hunpaid|assumption].
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

  Import ControlStack.

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
        Hroot Hqueue Hunqueued
        (reachable_materialized_ranked Hreachable) (proj1 H1)) as Hshape.
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

  End Dependencies.

  Definition ranking_generated support st := RankFinite.generated support (R.ranking st).

  Lemma generated_observe : forall support st target next entry,
    ranking_generated support st -> In target support ->
    R.observe st target = (next, entry) -> ranking_generated support next.
  Proof.
    intros support st target next entry Hg Hin Ho.
    eapply RankFinite.generated_observe; [exact Hg|exact Hin|].
    exact (@Dependencies.observed_ranking st target next entry Ho).
  Qed.

  Lemma generated_enqueue_all : forall support xs st,
    incl xs support -> ranking_generated support st ->
    ranking_generated support (R.enqueue_all st xs).
  Proof.
    intros support xs. induction xs as [|x xs IH]; intros st Hin Hg; [exact Hg|].
    cbn. apply IH; [intros y Hy; apply Hin; now right|].
    unfold R.enqueue. destruct (R.observe st x) as [next entry] eqn:Ho.
    change (ranking_generated support next). eapply generated_observe;
      [exact Hg|apply Hin; now left|exact Ho].
  Qed.

  Lemma generated_write : forall support st owner value,
    E.state_in support st -> ranking_generated support st ->
    ranking_generated support (R.write_changed_value st owner value).
  Proof.
    intros support st owner value Hstate Hg. unfold R.write_changed_value.
    apply generated_enqueue_all; [|exact Hg].
    intros reader Hin. apply SL.mem_spec in Hin.
    exact (@E.state_readers_in support st Hstate owner reader Hin).
  Qed.

  Lemma generated_set_value : forall support st owner direct,
    E.state_in support st -> ranking_generated support st ->
    ranking_generated support (R.set_value st owner direct).
  Proof.
    intros support st owner direct Hstate Hg. unfold R.set_value.
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    | |- context [let '(_, _) := ?pair in _] => destruct pair
    end; try exact Hg.
    all: apply generated_write; [now apply E.with_phases_in|exact Hg] ||
      now apply generated_write.
  Qed.

  Lemma generated_materialize : forall support st target,
    ranking_generated support st -> ranking_generated support (R.materialize st target).
  Proof. intros. unfold R.materialize. destruct (R.is_materialized _ _); assumption. Qed.

  Lemma generated_get_control : forall support st owner target,
    ranking_generated support st -> ranking_generated support (R.get_control_state st owner target).
  Proof. intros. unfold R.get_control_state. destruct (Nat.ltb _ _); assumption. Qed.

  Lemma generated_get_ready : forall support st owner target,
    ranking_generated support st -> ranking_generated support (R.get_ready_state st owner target).
  Proof.
    intros. unfold R.get_ready_state. apply generated_materialize.
    destruct (Nat.ltb _ _); assumption.
  Qed.

  Lemma generated_start_evaluation : forall support st owner,
    ranking_generated support st -> ranking_generated support (R.start_evaluation st owner).
  Proof. intros. unfold R.start_evaluation, R.reset_local_sides. now apply generated_materialize. Qed.

  Lemma generated_side_ready : forall support st owner target raw,
    ranking_generated support st -> ranking_generated support (R.side_ready_state st owner target raw).
  Proof.
    intros. unfold R.side_ready_state, R.record_side_payload.
    destruct (side_update_result st (R.handle_variable owner) (R.handle_variable target) raw),
      (Nat.ltb (R.handle_rank target) (R.handle_rank owner)); assumption.
  Qed.

  Lemma generated_try_dirty_read : forall support tf st owner target next,
    E.state_in support st -> ranking_generated support st ->
    R.try_dirty_read tf st owner target = Some next -> ranking_generated support next.
  Proof.
    intros support tf st owner target next Hstate Hg Hread.
    unfold R.try_dirty_read in Hread.
    repeat match type of Hread with
    | context [match ?subject with _ => _ end] => destruct subject eqn:?
    end; try discriminate; inversion Hread; subst; try exact Hg.
    all: apply generated_write; [|exact Hg].
    all: apply E.cancel_dirty_target_in.
    all: eauto 4 using E.with_phases_in, E.promote_controlled_in, E.with_started_in.
  Qed.

  Lemma generated_dirty_get_ready : forall support tf st owner target,
    E.state_in support st -> ranking_generated support st ->
    ranking_generated support (R.dirty_get_ready_state tf st owner target).
  Proof.
    intros support tf st owner target Hstate Hg. unfold R.dirty_get_ready_state.
    destruct (R.try_dirty_read tf _ _ _) as [next|] eqn:Hread.
    - change (ranking_generated support next). eapply generated_try_dirty_read;
        [| |exact Hread].
      + now apply E.materialize_in, E.get_control_state_in.
      + now apply generated_materialize, generated_get_control.
    - apply generated_materialize, generated_get_control. exact Hg.
  Qed.

  Lemma generated_step : forall support tf before after,
    E.config_in support before -> ranking_generated support (R.cfg_state before) ->
    Sem.step tf before after -> ranking_generated support (R.cfg_state after).
  Proof.
    intros support tf [st control] after [Hstate Hcontrol] Hg Hstep.
    unfold Sem.step in Hstep. cbn in Hstep, Hcontrol.
    destruct control; cbn in Hstep;
      repeat match type of Hstep with
      | context [match ?subject with _ => _ end] => destruct subject eqn:?
      end; try discriminate; inversion Hstep; subst; cbn in Hcontrol |- *.
    all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: repeat match goal with
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Get _ _) |- _ => inversion Hrhs; clear Hrhs
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Side _ _ _) |- _ => inversion Hrhs; clear Hrhs
    | Hrhs : Sem.rhs_supported _ (R.ConstraintSystem.Spawn _ _) |- _ => inversion Hrhs; clear Hrhs
    end.
    all: try match goal with Hroots : incl (?root :: _) ?sup |- _ =>
      assert (In root sup) by (apply Hroots; now left) end.
    all: try match goal with Ho : R.observe ?before ?target = (?next, ?entry),
      Hg0 : ranking_generated ?sup ?before |- _ =>
      assert (ranking_generated sup next) by (eapply generated_observe; eauto);
      assert (E.state_in sup next) by (eapply E.observe_in; eauto)
    end.
    all: try exact Hg.
    all: try (unfold R.request_spawn;
      match goal with |- context [if ?test then _ else _] => destruct test end; exact Hg).
    all: try (apply generated_start_evaluation; exact Hg).
    all: try (apply generated_get_ready; exact Hg).
    all: try (apply generated_set_value; assumption).
    all: try (apply generated_materialize; assumption).
    all: try (apply generated_side_ready; assumption).
    all: eauto 3 using generated_get_ready, generated_dirty_get_ready,
      generated_materialize, generated_side_ready.
  Qed.

  Lemma reachable_ranking_generated : forall tf roots (finite : Sem.finite_system tf roots) after,
    Sem.steps tf (R.initial_config roots) after -> ranking_generated (Sem.support finite) (R.cfg_state after).
  Proof.
    intros tf roots finite after Hsteps.
    assert (Hinitial : ranking_generated (Sem.support finite) (R.cfg_state (R.initial_config roots)))
      by apply RankFinite.generated_empty.
    assert (Hsupport : E.config_in (Sem.support finite) (R.initial_config roots)).
    { split; [apply E.empty_state_in|exact (Sem.initial_supported finite)]. }
    induction Hsteps; [exact Hinitial|]. apply IHHsteps.
    - eapply generated_step; eauto.
    - eapply E.next_config_in; [apply Sem.system_supported|exact Hsupport|exact H].
  Qed.

  Lemma reachable_rank_bound : forall tf roots (finite : Sem.finite_system tf roots) after x rank,
    Sem.steps tf (R.initial_config roots) after ->
    R.Ranking.lookup (R.ranking (R.cfg_state after)) x = Some rank ->
    rank < RankFinite.bound (Sem.support finite).
  Proof.
    intros tf roots finite after x rank Hsteps Hlookup.
    eapply RankFinite.generated_lookup_bound;
      [exact (handles_rank_valid (reachable_handles_valid Hsteps))
      |exact (reachable_ranking_generated finite Hsteps)|exact Hlookup].
  Qed.

  Module Total.
  Import Dependencies.

  Lemma queue_is_supported : forall support st,
    E.state_in support st -> forall entry,
      In entry (R.queue st) -> In (R.handle_variable entry) support.
  Proof.
    intros support st Hstate entry Hin.
    exact (proj1 (Forall_forall _ _) (E.state_queue_in Hstate) entry Hin).
  Qed.

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
    eapply C.reachable_drain_aggregate_bounded; eauto.
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

  Lemma boundary_prepend : forall tf owner base first next,
    Sim.scoped_until_steps owner base tf first next ->
    solve_loop_boundary tf owner base next -> solve_loop_boundary tf owner base first.
  Proof.
    intros tf owner base first next Hprefix [[st [Hsteps Hbelow]]|
      [st [tail [Hsteps [Hmay [Hpop Hbelow]]]]]].
    - left. exists st. split; [eapply Sim.scoped_until_transitive; eauto|exact Hbelow].
    - right. exists st, tail. repeat split; try assumption.
      eapply Sim.scoped_until_transitive; eauto.
  Qed.

  Lemma solve_loop_exit_boundary : forall tf roots owner base st,
    reachable_exit_ready tf roots ->
    Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |} ->
    R.owner_may_still_be_queued st owner = false ->
    solve_loop_boundary tf owner base
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots owner base st Hexit Hreachable Hmay.
    left. exists st. split.
    - econstructor; [cbn; left; split; reflexivity| |constructor].
      unfold Sem.step. cbn. now rewrite Hmay, (Hexit st owner base Hreachable Hmay).
    - pose proof (reachable_handles_valid Hreachable) as Hvalid.
      exact (@reachable_owner_may_false_queue_below tf roots _ owner Hreachable
        (proj1 (handles_control_valid Hvalid)) Hmay).
  Qed.

  Lemma solve_loop_self_boundary : forall tf roots owner base st next tail,
    Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |} ->
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (next, tail) ->
    R.handle_variable next = R.handle_variable owner ->
    solve_loop_boundary tf owner base
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots owner base st next tail Hreachable Hmay Hpop Hsame.
    pose proof (reachable_handles_valid Hreachable) as Hhandles.
    assert (next = owner).
    { eapply same_variable_valid_handle_equal; [| |exact Hsame].
      - eapply queue_pop_valid; [exact (handles_queue_valid Hhandles)|exact Hpop].
      - exact (proj1 (handles_control_valid Hhandles)). }
    subst next. right. exists st, tail. repeat split; try assumption.
    - constructor.
    - eapply popped_started_strictly_below; eauto.
  Qed.

  Lemma solve_loop_higher_child : forall tf roots (finite : Sem.finite_system tf roots)
    owner base st next tail,
    Sim.higher_episodes_complete (Sem.support finite) tf roots owner ->
    Sem.steps tf (R.initial_config roots)
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |} ->
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (next, tail) ->
    R.handle_variable next <> R.handle_variable owner ->
    exists done,
      Sim.scoped_until_steps owner base tf
        {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |}
        {| R.cfg_state := done; R.cfg_control := R.RunSolveOneLoop owner base |} /\
      queue_strictly_below next done /\
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := done; R.cfg_control := R.RunSolveOneLoop owner base |}.
  Proof.
    intros tf roots finite owner base st next tail Hchildren Hreachable Hmay Hpop Hneq.
    assert (Hhigher : Nat.ltb (R.handle_rank owner) (R.handle_rank next) = true)
      by (eapply ControlStack.owner_may_pop_higher; eauto).
    assert (Hmember : In next (R.queue st)).
    { unfold R.queue_pop in Hpop. destruct (R.queue st); try discriminate.
      inversion Hpop; subst. now left. }
    pose proof (queue_is_supported (proj1 (reachable_config_supported finite Hreachable))
      next Hmember) as Hsupported.
    set (child := {| R.cfg_state := R.with_queue st tail;
      R.cfg_control := R.RunSolveOne next (R.KSolveOneLoop owner base) |}).
    assert (Hstep : Sem.step tf
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |} child).
    { unfold Sem.step, child. cbn. rewrite Hmay, Hpop.
      destruct (V.eq_dec (R.handle_variable next) (R.handle_variable owner));
        [contradiction|reflexivity]. }
    assert (Hchild : Sem.steps tf (R.initial_config roots) child)
      by (eapply Sim.steps_append_one; eauto).
    destruct (Hchildren next (R.KSolveOneLoop owner base) child Hsupported Hhigher Hchild eq_refl)
      as [done [Hepisode Hbelow]].
    exists done. split.
    - econstructor; [cbn; left; split; reflexivity|exact Hstep|].
      eapply Sim.scoped_until_lift; [apply Sim.ScopedContinuationSolve|exact Hepisode].
    - split; [exact Hbelow|]. eapply Sim.steps_transitive; [exact Hchild|].
      exact (Sim.scoped_until_semantic Hepisode).
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
    intros tf roots finite owner base Hexit Hchildren upper st Hbelow Hreachable.
    remember (R.handle_rank upper) as rank eqn:Hrank.
    revert upper st Hrank Hbelow Hreachable.
    induction rank using (well_founded_induction_type Nat.lt_wf_0).
    intros upper st Hrank Hbelow Hreachable.
    destruct (R.owner_may_still_be_queued st owner) eqn:Hmay.
    2: { eapply solve_loop_exit_boundary; eauto. }
    destruct (owner_may_true_pop st owner Hmay) as [next [tail Hpop]].
    destruct (V.eq_dec (R.handle_variable next) (R.handle_variable owner)) as [Hsame|Hneq].
    - eapply solve_loop_self_boundary; eauto.
    - destruct (@solve_loop_higher_child tf roots finite owner base st next tail
        Hchildren Hreachable Hmay Hpop Hneq) as [done [Hpath [Hdone_below Hdone]]].
      eapply boundary_prepend; [exact Hpath|].
      eapply (H (R.handle_rank next)) with (upper := next);
        [|reflexivity|exact Hdone_below|exact Hdone].
      rewrite Hrank. apply Hbelow. unfold R.queue_pop in Hpop.
      destruct (R.queue st); try discriminate. inversion Hpop; subst. now left.
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
    2: { eapply solve_loop_exit_boundary; eauto. }
    destruct (owner_may_true_pop st owner Hmay) as [next [tail Hpop]].
    destruct (V.eq_dec (R.handle_variable next) (R.handle_variable owner)) as [Hsame|Hneq].
    - eapply solve_loop_self_boundary; eauto.
    - destruct (@solve_loop_higher_child tf roots finite owner base st next tail
        Hchildren Hreachable Hmay Hpop Hneq) as [done [Hpath [Hbelow Hdone]]].
      eapply boundary_prepend; [exact Hpath|].
      eapply bounded_solve_loop_reaches_boundary; eauto.
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
      (fun x => In x (Sem.support finite))
      (tf (R.handle_variable owner))).
    {
      now apply Sem.system_supported.
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

  Lemma restart_owner_steps : forall tf owner base st tail,
    R.owner_may_still_be_queued st owner = true ->
    R.queue_pop (R.queue st) = Some (owner, tail) ->
    Sim.scoped_until_steps owner base tf
      {| R.cfg_state := st; R.cfg_control := R.RunSolveOneLoop owner base |}
      {| R.cfg_state := started_evaluation (R.with_queue st tail) owner;
         R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}.
  Proof.
    intros tf owner base st tail Hmay Hpop.
    econstructor.
    - cbn. left. split; reflexivity.
    - unfold Sem.step. cbn. rewrite Hmay, Hpop.
      destruct (V.eq_dec (R.handle_variable owner) (R.handle_variable owner));
        [reflexivity|contradiction].
    - econstructor.
      + cbn. left. split; reflexivity.
      + unfold Sem.step, started_evaluation. reflexivity.
      + constructor.
  Qed.

  Lemma restarted_round_decreases :
    forall tf roots (finite : Sem.finite_system tf roots)
      owner base st pop_state tail,
      queue_strictly_below owner st ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |} ->
      Sim.scoped_until_steps owner base tf
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}
        {| R.cfg_state := pop_state; R.cfg_control := R.RunSolveOneLoop owner base |} ->
      R.owner_may_still_be_queued pop_state owner = true ->
      R.queue_pop (R.queue pop_state) = Some (owner, tail) ->
      Measure.round_measure_lt (Sem.support finite)
        {| R.cfg_state := started_evaluation (R.with_queue pop_state tail) owner;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}
        {| R.cfg_state := st;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}.
  Proof.
    intros tf roots finite owner base st pop_state tail Hbelow Hreachable
      Hboundary Hmay Hpop.
    apply Payment.round_decreases_measure.
    eapply Payment.round_decreases_left.
    - eapply Dependencies.scoped_restart_decreases; eauto.
    - eapply Payment.supported_steps_nonincreasing.
      + exact (Sem.support_nodup finite).
      + eapply Payment.reachable_steps_supported.
        * eapply Sim.steps_transitive; [exact Hreachable|].
          exact (Sim.scoped_until_semantic Hboundary).
        * exact (Sim.scoped_until_semantic
            (@restart_owner_steps tf owner base pop_state tail Hmay Hpop)).
  Qed.

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
    - pose proof (@restart_owner_steps tf owner base pop_state tail Hmay Hpop)
        as Hadmin.
      assert (Hnext_reachable : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := started_evaluation (R.with_queue pop_state tail) owner;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}).
      { eapply Sim.steps_transitive; [exact Hreachable|].
        eapply Sim.scoped_until_semantic.
        eapply Sim.scoped_until_transitive; eauto. }
      assert (Hdecrease := @restarted_round_decreases tf roots finite owner
        base st pop_state tail Hbelow Hreachable Hboundary Hmay Hpop).
      specialize (IH _ Hdecrease).
      unfold owner_round_complete in IH.
      destruct (IH _ base eq_refl Hnext_reachable Hnext_below)
        as [final [Hrest Hfinal_below]].
      exists final. split; [|exact Hfinal_below].
      eapply Sim.scoped_until_transitive; [exact Hboundary|].
      eapply Sim.scoped_until_transitive; eauto.
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
    - pose proof (@restart_owner_steps tf owner base pop_state tail Hmay Hpop)
        as Hadmin.
      assert (Hnext : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := started_evaluation (R.with_queue pop_state tail) owner;
           R.cfg_control := R.RunRhs owner (tf (R.handle_variable owner)) base |}).
      { eapply Sim.steps_transitive; [exact Hstarted|].
        eapply Sim.scoped_until_semantic.
        eapply Sim.scoped_until_transitive; eauto. }
      pose proof (@reachable_owner_rounds_complete
        tf roots finite owner Howner Hchildren) as Hcomplete.
      unfold owner_round_complete in Hcomplete.
      destruct (Hcomplete _ _ base eq_refl Hnext Hnext_below)
        as [final [Hrest Hfinal_below]].
      exists final. split; [|exact Hfinal_below].
      econstructor.
      + cbn. left. split; reflexivity.
      + exact Hstart.
      + eapply Sim.scoped_until_transitive; [exact Hboundary|].
        eapply Sim.scoped_until_transitive; eauto.
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
      apply (queue_is_supported Hstate owner). eapply queue_pop_member; exact Hpop. }
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

  Lemma discovered_seed_reaches_drained :
    forall tf roots (finite : Sem.finite_system tf roots) remaining root st,
      (forall next_state,
        Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := next_state; R.cfg_control := R.RunSeeds remaining |} ->
        exists final, Sem.steps tf
          {| R.cfg_state := next_state; R.cfg_control := R.RunSeeds remaining |}
          (Sem.terminal_config final) /\ R.queue_pop (R.queue final) = None) ->
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds (root :: remaining) |} ->
       forall observed owner,
        R.observe st root = (observed, owner) ->
        Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunSeeds (root :: remaining) |}
          {| R.cfg_state := observed;
             R.cfg_control :=
               R.RunSolveOne owner (R.KSeedLoop remaining) |} ->
        exists final,
          Sem.steps tf
            {| R.cfg_state := st;
               R.cfg_control := R.RunSeeds (root :: remaining) |}
            (Sem.terminal_config final) /\ R.queue_pop (R.queue final) = None.
  Proof.
    intros tf roots finite remaining root st IH Hreachable.
        intros observed owner Hobserve Hstep.
        assert (Hroot : List.In (R.handle_variable owner)
          (Sem.support finite)).
        { pose proof (reachable_config_supported finite Hreachable)
            as [_ Hcontrol]. cbn in Hcontrol.
          rewrite (@observed_handle_variable st root observed owner Hobserve).
          apply Hcontrol. now left. }
        set (child :=
          {| R.cfg_state := observed;
             R.cfg_control := R.RunSolveOne owner (R.KSeedLoop remaining) |}).
        assert (Hchild : Sem.steps tf (R.initial_config roots) child).
        { eapply Sim.steps_append_one; eauto. }
        destruct (@all_episodes_complete tf roots finite owner
          (R.KSeedLoop remaining) child Hroot Hchild eq_refl)
          as [done [Hepisode Hbelow]].
        assert (Hdone : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := done;
             R.cfg_control := base_control (Some remaining) |}).
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
        - exact (Sim.scoped_until_semantic Hepisode).
        - eapply Sim.steps_transitive; [exact Hdrain |].
          econstructor; eauto.
      
  Qed.

  Theorem seeds_reach_drained :
    forall tf roots (finite : Sem.finite_system tf roots) remaining st,
      Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |} ->
      exists final,
        Sem.steps tf
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |}
          (Sem.terminal_config final) /\ R.queue_pop (R.queue final) = None.
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
      + exact Hempty.
    - pose proof (@discovered_seed_reaches_drained tf roots finite remaining root st
        IH Hreachable) as Hdiscover.
      destruct (orb (S.mem root (R.started st)) (R.is_dormant st root))
        eqn:Hskip.
      + assert (Hstep : Sem.step tf
          {| R.cfg_state := st;
             R.cfg_control := R.RunSeeds (root :: remaining) |}
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |}).
        { unfold Sem.step. cbn. rewrite Hskip. reflexivity. }
        assert (Hnext : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st; R.cfg_control := R.RunSeeds remaining |}).
        { eapply Sim.steps_append_one; eauto. }
        destruct (IH st Hnext) as [final [Hrest Hquiet]].
        exists final. split; [|exact Hquiet]. econstructor; eauto.
      + destruct (R.Ranking.lookup (R.ranking st) root) eqn:Hlookup.
        * destruct (R.observe st root) as [observed owner] eqn:Hobserve.
          eapply Hdiscover; [reflexivity |].
          unfold Sem.step. cbn. rewrite Hskip, Hlookup, Hobserve. reflexivity.
        * destruct (andb (R.pure_bottom_rhs tf root)
            (negb (R.is_materialized st root))) eqn:Hdormant.
          -- set (next := R.remember_dormant st root).
             assert (Hstep : Sem.step tf
               {| R.cfg_state := st;
                  R.cfg_control := R.RunSeeds (root :: remaining) |}
               {| R.cfg_state := next; R.cfg_control := R.RunSeeds remaining |}).
             { unfold Sem.step, next. cbn.
               rewrite Hskip, Hlookup, Hdormant. reflexivity. }
             assert (Hnext : Sem.steps tf (R.initial_config roots)
               {| R.cfg_state := next; R.cfg_control := R.RunSeeds remaining |}).
             { eapply Sim.steps_append_one; eauto. }
             destruct (IH next Hnext) as [final [Hrest Hquiet]].
             exists final. split; [|exact Hquiet]. econstructor; eauto.
          -- destruct (R.observe st root) as [observed owner] eqn:Hobserve.
             eapply Hdiscover; [reflexivity |].
             unfold Sem.step. cbn.
             rewrite Hskip, Hlookup, Hdormant, Hobserve. reflexivity.
  Qed.

  Lemma reachable_steps_spawn_credit : forall tf roots (finite : Sem.finite_system tf roots) before after,
    Sem.steps tf (R.initial_config roots) before -> Sem.steps tf before after ->
    E.spawn_credit (Sem.support finite) (R.cfg_state after) <=
      E.spawn_credit (Sem.support finite) (R.cfg_state before).
  Proof.
    intros tf roots finite before after Hreach Hsteps.
    eapply E.steps_spawn_credit; [apply Sem.system_supported| |exact Hsteps].
    exact (reachable_config_supported finite Hreach).
  Qed.

  Definition loop_terminates tf roots (st : R.state) : Prop :=
    Sem.steps tf (R.initial_config roots) (Sem.terminal_config st) ->
    exists final, Sem.steps tf (Sem.terminal_config st) (Sem.terminal_config final) /\
      Sem.quiescent final.

  Theorem loop_reaches_terminal : forall tf roots (finite : Sem.finite_system tf roots) st,
    loop_terminates tf roots st.
  Proof.
    intros tf roots finite.
    apply (well_founded_induction_type
      (well_founded_ltof R.state (E.spawn_credit (Sem.support finite)))).
    intros st IH Hreachable.
    destruct (@drain_queue_complete tf roots finite None st Hreachable)
      as [drained [Hdrain Hempty]].
    assert (Hdrained : Sem.steps tf (R.initial_config roots) (Sem.terminal_config drained)).
    { eapply Sim.steps_transitive; eauto. }
    destruct (R.pending_spawns drained) as [|target rest] eqn:Hpending.
    - exists drained. split; [exact Hdrain|]. split; [|exact Hpending].
      unfold R.queue_pop in Hempty. unfold R.queue_peek.
      destruct (R.queue drained); [reflexivity|discriminate].
    - set (dispatched := R.with_spawns drained rest (R.requested_spawns drained)).
      assert (Hdispatch : Sem.step tf (Sem.terminal_config drained)
        {| R.cfg_state := dispatched; R.cfg_control := R.RunSeeds [target] |}).
      { unfold Sem.step, Sem.terminal_config, dispatched. cbn.
        now rewrite Hempty, Hpending. }
      assert (Hseed : Sem.steps tf (R.initial_config roots)
        {| R.cfg_state := dispatched; R.cfg_control := R.RunSeeds [target] |}).
      { eapply Sim.steps_append_one; eauto. }
      destruct (@seeds_reach_drained tf roots finite [target] dispatched Hseed)
        as [next [Hseeds Hnext_empty]].
      assert (Hless : ltof R.state (E.spawn_credit (Sem.support finite)) next st).
      { unfold ltof.
        pose proof (@reachable_steps_spawn_credit tf roots finite _ _ Hreachable Hdrain) as Hd.
        pose proof (@reachable_steps_spawn_credit tf roots finite _ _ Hseed Hseeds) as Hs.
        pose proof (@E.dispatch_decreases_credit (Sem.support finite) drained target rest Hpending) as Hc.
        cbn in Hd, Hs. unfold dispatched in Hs. unfold E.spawn_credit in Hc |- *. cbn in Hc |- *. lia. }
      destruct (IH next Hless ltac:(eapply Sim.steps_transitive; eauto))
        as [final [Hrest Hquiet]].
      exists final. split; [|exact Hquiet].
      eapply Sim.steps_transitive; [exact Hdrain|]. econstructor; [exact Hdispatch|].
      eapply Sim.steps_transitive; eauto.
  Qed.

  Theorem solver_reaches_terminal : forall tf roots (finite : Sem.finite_system tf roots),
    exists final, Sem.steps tf (R.initial_config roots) (Sem.terminal_config final) /\
      Sem.quiescent final.
  Proof.
    intros tf roots finite.
    destruct (@seeds_reach_drained tf roots finite roots R.empty_state (Sem.StepsRefl _ _))
      as [drained [Hseeds Hempty]].
    destruct (@loop_reaches_terminal tf roots finite drained Hseeds) as [final [Hloop Hquiet]].
    exists final. split; [eapply Sim.steps_transitive; eauto|exact Hquiet].
  Qed.

  Theorem solver_terminates : forall tf roots, Sem.finite_system tf roots ->
    exists final, Sem.terminates_to tf roots final.
  Proof. intros tf roots finite. exact (solver_reaches_terminal finite). Qed.

  End Total.

  Theorem total_correct : forall tf roots (finite : Sem.finite_system tf roots),
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.correct_final_state tf roots final /\ Sem.quiescent final.
  Proof.
    intros tf roots finite.
    destruct (Total.solver_reaches_terminal finite) as [final [Hsteps Hquiet]].
    destruct (E.steps_have_exact_fuel Hsteps) as [fuel Hfuel].
    assert (Hrun : R.solve_fuel fuel tf roots = Some final).
    { unfold R.solve_fuel. rewrite Hfuel.
      destruct Hquiet as [Hqueue Hpending].
      unfold R.terminal_state, Sem.terminal_config. cbn. now rewrite Hqueue, Hpending. }
    exists fuel, final. split; [exact Hrun|]. split; [|exact Hquiet].
    exact (proj1 (@C.successful_run_correct fuel tf roots final Hrun)).
  Qed.

  Theorem sufficient_fuel : forall tf roots (finite : Sem.finite_system tf roots),
    exists fuel final, forall extra, R.solve_fuel (fuel + extra) tf roots = Some final.
  Proof.
    intros tf roots finite. destruct (total_correct finite) as [fuel [final [Hrun _]]].
    exists fuel, final. now apply E.successful_run_more_fuel.
  Qed.

  Definition scheduling_round_key support config :=
    (E.spawn_credit support (R.cfg_state config), Measure.round_key support config).

  Definition scheduling_round_key_lt :=
    slexprod nat (nat * (nat * nat)) lt Measure.round_key_lt.

  Definition scheduling_round_lt support (after before : R.config) :=
    scheduling_round_key_lt (scheduling_round_key support after)
      (scheduling_round_key support before).

  Lemma scheduling_round_well_founded : forall support,
    well_founded (scheduling_round_lt support).
  Proof.
    intros. unfold scheduling_round_lt. apply wf_inverse_image.
    unfold scheduling_round_key_lt. apply wf_slexprod.
    - apply Nat.lt_wf_0.
    - apply Measure.round_key_lt_well_founded.
  Qed.

  Lemma scheduling_round_dispatch : forall support st target pending before after,
    R.cfg_state before = st ->
    R.cfg_state after = R.with_spawns st pending (R.requested_spawns st) ->
    R.pending_spawns st = target :: pending -> scheduling_round_lt support after before.
  Proof.
    intros support st target pending before after Hb Ha Hp.
    unfold scheduling_round_lt, scheduling_round_key_lt, scheduling_round_key.
    apply left_slex. rewrite Ha, Hb. eapply E.dispatch_decreases_credit; exact Hp.
  Qed.

  Lemma scheduling_round_request : forall support st target before after,
    R.cfg_state before = st -> R.cfg_state after = R.request_spawn st target ->
    In target support -> S.mem target (R.requested_spawns st) = false ->
    scheduling_round_lt support after before.
  Proof.
    intros support st target before after Hb Ha Hin Hfresh.
    unfold scheduling_round_lt, scheduling_round_key_lt, scheduling_round_key.
    apply left_slex. rewrite Ha, Hb. now apply E.fresh_request_decreases_credit.
  Qed.

  Lemma scheduling_round_step : forall support tf before after,
    NoDup support -> E.control_in support (R.cfg_control before) ->
    E.state_in support (R.cfg_state after) -> Sem.step tf before after ->
    scheduling_round_lt support after before \/
    scheduling_round_key support after = scheduling_round_key support before.
  Proof.
    intros support tf before after Hn Hcontrol Hstate Hstep.
    pose proof (@E.next_config_spawn_credit support tf before after Hstep
      (E.state_requested_in Hstate)) as Hcredit.
    destruct (Nat.eq_dec (E.spawn_credit support (R.cfg_state after))
      (E.spawn_credit support (R.cfg_state before))) as [Heq|Hneq].
    - destruct (@Payment.step_decreases_or_unpaid support tf before after Hn Hcontrol Hstep)
        as [Hdecrease|[_ [Hm [Hc Hu]]]].
      + left. unfold scheduling_round_lt, scheduling_round_key_lt, scheduling_round_key.
        rewrite Heq. apply right_slex. now apply Payment.round_decreases_measure.
      + right. unfold scheduling_round_key, Measure.round_key. now rewrite Heq, Hm, Hc, Hu.
    - left. unfold scheduling_round_lt, scheduling_round_key_lt, scheduling_round_key.
      apply left_slex. lia.
  Qed.
  Lemma scheduling_round_preserved_steps :
    forall tf roots (finite : Sem.finite_system tf roots) before after,
      Sem.steps tf (R.initial_config roots) before ->
      Sem.steps tf before after ->
      scheduling_round_key (Sem.support finite) after =
        scheduling_round_key (Sem.support finite) before ->
      Payment.supported_unpaid_steps (Sem.support finite) tf before after.
  Proof.
    intros tf roots finite before after Hprefix Hsteps Hequal.
    destruct (@Payment.reachable_steps_decrease_or_unpaid
      tf roots finite before after Hprefix Hsteps) as [Hstrict|Hunpaid];
      [|exact Hunpaid].
    unfold scheduling_round_key, Measure.round_key in Hequal.
    injection Hequal as Hu Hc Hv Hspawn.
    unfold Payment.round_decreases in Hstrict. lia.
  Qed.

  Theorem scheduling_round_preserved_controlled_values :
    forall tf roots (finite : Sem.finite_system tf roots) before after observed,
      Sem.steps tf (R.initial_config roots) before ->
      Sem.steps tf before after ->
      scheduling_round_key (Sem.support finite) after =
        scheduling_round_key (Sem.support finite) before ->
      In observed (Sem.support finite) ->
      S.mem observed (R.controlled (R.cfg_state before)) = true ->
      R.sigma_value (R.cfg_state after) observed =
        R.sigma_value (R.cfg_state before) observed.
  Proof.
    intros tf roots finite before after observed Hprefix Hsteps Hequal Hin Hcontrol.
    eapply Payment.supported_unpaid_steps_controlled_sigma_same;
      [exact Hin|exact Hcontrol|].
    eapply scheduling_round_preserved_steps; eauto.
  Qed.
End Make.
