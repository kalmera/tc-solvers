From Stdlib Require Import List Bool.
From TcSolvers Require Import
  common.Assumptions common.BoxUpdate
  solvers.slr.restarting.proofs.Correctness
  solvers.slr.restarting.proofs.NarrowingStabilityProof.

Set Implicit Arguments.

Module Make (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Stability := NarrowingStabilityProof.Make V D WN.
  Module U := Stability.U.

  Module WithLaws
    (S : SET V) (M : MAP V) (Features : Restarting.FEATURES)
    (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (UL : UPDATE_LAWS V D U) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

    Module N := Stability.FirstDiscovery S M Features DL WNL UL SL ML.
    Module C := N.Total.
    Module R := N.R.
    Module Sem := N.Sem.
    Module H := C.CommitHistory.

    Definition equivalent := UL.equivalent.
    Definition narrowing_fixed (_owner : V.t) (input value : D.t) : Prop :=
      equivalent (WN.narrow value input) value.

    (** The phase may change on the repeated update. Only its value matters. *)
    Definition value_idempotent : Prop :=
      forall owner phase old input,
        let result := U.update false owner phase old input in
        equivalent
          (snd (U.update false owner (fst result) (snd result) input))
          (snd result).

    Lemma equivalent_refl : forall x, equivalent x x.
    Proof. intro x. split; apply DL.leq_refl. Qed.
    Lemma equivalent_sym : forall x y, equivalent x y -> equivalent y x.
    Proof. intros x y [Hxy Hyx]. split; assumption. Qed.
    Lemma equivalent_trans : forall x y z,
      equivalent x y -> equivalent y z -> equivalent x z.
    Proof.
      intros x y z [Hxy Hyx] [Hyz Hzy]. split;
        eapply DL.leq_trans; eassumption.
    Qed.

    Lemma join_bottom : forall direct,
      equivalent (D.join direct D.bottom) direct.
    Proof.
      intro direct. split.
      - apply DL.join_least; [apply DL.leq_refl |apply DL.bottom_least].
      - apply DL.join_upper_left.
    Qed.

    Lemma fixed_diagonal : forall owner input value,
      equivalent input value -> narrowing_fixed owner input value.
    Proof.
      intros owner input value [Hinput Hvalue]. split.
      - apply WNL.narrow_upper. exact Hinput.
      - eapply DL.leq_trans; [exact Hvalue |].
        apply WNL.narrow_lower. exact Hinput.
    Qed.

    Lemma fixed_transport : forall owner input value input' value',
      D.leq input value = true ->
      equivalent input input' -> equivalent value value' ->
      narrowing_fixed owner input value ->
      narrowing_fixed owner input' value'.
    Proof.
      intros owner input value input' value' Hle Hin Hval Hfixed.
      assert (Hle' : D.leq input' value' = true).
      { eapply DL.leq_trans; [exact (proj2 Hin) |].
        eapply DL.leq_trans; [exact Hle |exact (proj1 Hval)]. }
      pose proof (@UL.update_extensional false owner U.BoxN
        value value' input input' Hval Hin) as Hext.
      unfold U.update in Hext. rewrite Hle, Hle' in Hext. cbn in Hext.
      eapply equivalent_trans; [apply equivalent_sym; exact Hext |].
      eapply equivalent_trans; [exact Hfixed |exact Hval].
    Qed.

    Lemma idempotent_update_fixed : forall owner phase old input next value,
      value_idempotent ->
      U.update false owner phase old input = (next, value) ->
      U.avoids_fallback next ->
      narrowing_fixed owner input value.
    Proof.
      intros owner phase old input next value Hid Hupdate Hsafe.
      specialize (Hid owner phase old input). rewrite Hupdate in Hid. cbn in Hid.
      pose proof (UL.update_sound false owner phase old input) as Hsound.
      rewrite Hupdate in Hsound. cbn in Hsound.
      destruct next; try contradiction;
        unfold U.update in Hid; rewrite Hsound in Hid; exact Hid.
    Qed.

    Lemma set_value_fixed : forall st fr direct st' fr',
      value_idempotent ->
      R.aggregate st (R.frame_owner fr) = D.bottom ->
      R.set_value st fr direct = (st', fr') ->
      U.avoids_fallback (R.frame_phase fr') ->
      narrowing_fixed (R.frame_owner fr) direct
        (R.sigma_value st' (R.frame_owner fr)).
    Proof.
      intros st fr direct st' fr' Hid Hbottom Hset Hsafe.
      unfold R.set_value in Hset. rewrite Hbottom in Hset.
      set (owner := R.frame_owner fr) in *.
      set (candidate := D.join direct D.bottom) in *.
      set (old := R.sigma_value st owner) in *.
      assert (Hinput : equivalent candidate direct) by apply join_bottom.
      destruct (R.equivalent candidate old) eqn:Hcandidate.
      - inversion Hset; subst. apply fixed_diagonal.
        apply Bool.andb_true_iff in Hcandidate.
        eapply equivalent_trans; [apply equivalent_sym; exact Hinput |exact Hcandidate].
      - destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
        + destruct (U.update false owner (R.frame_phase fr) old candidate)
            as [next value] eqn:Hupdate. cbn in Hset.
          destruct (R.equivalent value old) eqn:Hvalue;
            inversion Hset; subst; cbn in Hsafe.
          * eapply fixed_transport; [|exact Hinput | |].
            -- pose proof (UL.update_sound false owner (R.frame_phase fr)
                 old candidate) as Hsound. rewrite Hupdate in Hsound. exact Hsound.
            -- apply Bool.andb_true_iff in Hvalue. exact Hvalue.
            -- eapply idempotent_update_fixed; eassumption.
          * rewrite C.sigma_value_with_readers, C.sigma_value_enqueue_all,
              C.sigma_value_update_same.
            eapply fixed_transport; [|exact Hinput |apply equivalent_refl |].
            -- pose proof (UL.update_sound false owner (R.frame_phase fr)
                 old candidate) as Hsound. rewrite Hupdate in Hsound. exact Hsound.
            -- eapply idempotent_update_fixed; eassumption.
        + cbn in Hset. rewrite Hcandidate in Hset. inversion Hset; subst.
          rewrite C.sigma_value_with_readers, C.sigma_value_enqueue_all,
            C.sigma_value_update_same.
          apply fixed_diagonal. apply equivalent_sym. exact Hinput.
    Qed.

    Lemma reachable_commit_fixed : forall tf roots
      (finite : Sem.finite_system tf roots) c,
      value_idempotent -> N.ordinary_monotonic_system tf ->
      Sem.steps tf (R.initial_config roots) c ->
      H.commit_property narrowing_fixed c.
    Proof.
      intros tf roots finite [st control] Hid Hordinary Hreach
        fr direct k Hcontrol st' fr' Hset. cbn in Hcontrol. subst control.
      eapply set_value_fixed; [exact Hid | |exact Hset |].
      - exact (@N.ordinary_reachable_aggregate_bottom tf roots finite
          {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |}
          (R.frame_owner fr) Hordinary Hreach).
      - assert (Hnext : Sem.steps tf (R.initial_config roots)
          {| R.cfg_state := st'; R.cfg_control := R.RunDrain fr' k |}).
        { eapply C.Termination.steps_append_one; [exact Hreach |].
          change (R.set_value st fr direct = (st', fr')) in Hset.
          unfold Sem.step. cbn -[R.set_value]. rewrite Hset. reflexivity. }
        exact (proj1 (@N.first_discovery_ordinary_avoids_fallback
          tf roots finite Hordinary _ Hnext)).
    Qed.

    Theorem successful_run_fixed : forall fuel tf roots final
      (finite : Sem.finite_system tf roots),
      value_idempotent -> N.ordinary_monotonic_system tf ->
      R.solve_fuel fuel tf roots = Some final ->
      forall owner, Sem.solved final owner ->
      exists direct reads effects,
        Sem.rhs_eval final (tf owner) direct reads effects /\
        narrowing_fixed owner direct (R.sigma_value final owner).
    Proof.
      intros fuel tf roots final finite Hid Hordinary Hrun owner Hsolved.
      pose proof (@C.successful_run_terminates_to fuel tf roots final Hrun) as Hterm.
      assert (Hcommits : forall c,
        Sem.steps tf (R.initial_config roots) c -> H.commit_property narrowing_fixed c).
      { intros c Hreach. eapply reachable_commit_fixed; eassumption. }
      pose proof (@H.terminal_invariant narrowing_fixed tf roots final Hcommits Hterm)
        as Hinv.
      destruct Hterm as [_ Hquiet].
      destruct (H.invariant_summaries Hinv Hsolved) as [Hqueued |[Hactive |Hsummary]].
      - exfalso. exact (@C.quiescent_not_queued final owner Hquiet Hqueued).
      - contradiction.
      - destruct Hsummary as [_ [direct [reads [effects
          [Htrace [Hreads [_ [_ Hfixed]]]]]]]].
        exists direct, reads, effects. split; [|exact Hfixed].
        eapply C.rhs_trace_replay; [exact Htrace |].
        eapply C.guarded_reads_agree; eassumption.
    Qed.

    Theorem total_correct_and_fixed : forall tf roots,
      Sem.finite_system tf roots -> value_idempotent ->
      N.ordinary_monotonic_system tf ->
      exists fuel final,
        R.solve_fuel fuel tf roots = Some final /\
        Sem.correct_final_state tf roots final /\
        forall owner, Sem.solved final owner ->
        exists direct reads effects,
          Sem.rhs_eval final (tf owner) direct reads effects /\
          narrowing_fixed owner direct (R.sigma_value final owner).
    Proof.
      intros tf roots finite Hid Hordinary.
      destruct (@C.sufficient_fuel tf roots finite) as [fuel [final Hrun]].
      exists fuel, final. split; [exact Hrun |]. split.
      - exact (@C.solve_fuel_correct fuel tf roots final Hrun).
      - eapply successful_run_fixed; eassumption.
    Qed.
  End WithLaws.
End Make.
