From Stdlib Require Import Lia Arith.PeanoNat
  Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product.
From TcSolvers Require Import
  common.Interfaces
  common.Assumptions
  common.BoxUpdate
  common.FiniteHeight
  common.SideUpdate.

Set Implicit Arguments.

(** Preserve the base policy's phase transition, but replace a widening-like
    update by a join when the new contribution is already covered globally. *)
Module ReluctantSideUpdate
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D) <: SIDE_UPDATE V D.

  Definition phase := Base.phase.

  Definition initial_phase (_source target : V.t) : phase :=
    Base.initial_phase true target.

  Definition update
    (_source target : V.t) (current : phase)
    (old input aggregate : D.t) : phase * D.t :=
    let base := Base.update true target current old input in
    if D.leq input old then base
    else if D.leq input aggregate
    then (fst base, D.join old input)
    else base.
End ReluctantSideUpdate.

Module ReluctantOneBoxSideUpdate
  (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module Base := OneBoxUpdate V D WN.
  Include ReluctantSideUpdate V D Base.
End ReluctantOneBoxSideUpdate.

Module ReluctantSideUpdateSoundLaws
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (DL : DOMAIN_LAWS D) (BaseLaws : UPDATE_LAWS V D Base).

  Module SU := ReluctantSideUpdate V D Base.

  Lemma update_sound :
    forall source target phase old input aggregate,
      D.leq input
        (snd (SU.update source target phase old input aggregate)) = true.
  Proof.
    intros source target phase old input aggregate.
    unfold SU.update.
    destruct (D.leq input old); [apply BaseLaws.update_sound |].
    destruct (D.leq input aggregate).
    - cbn. apply DL.join_upper_right.
    - apply BaseLaws.update_sound.
  Qed.

  Lemma covered_join_replay_uses_base :
    forall source target phase old input aggregate next_aggregate,
      D.leq input old = false ->
      D.leq input aggregate = true ->
      let next := SU.update source target phase old input aggregate in
      SU.update source target (fst next) (snd next)
        input next_aggregate =
      Base.update true target (fst next) (snd next) input.
  Proof.
    intros source target phase old input aggregate next_aggregate
      Hnew Hcovered.
    unfold SU.update at 1. rewrite Hnew, Hcovered. cbn.
    unfold SU.update. now rewrite DL.join_upper_right.
  Qed.
End ReluctantSideUpdateSoundLaws.

Module ReluctantSideUpdateUpperBoundLaws
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (DL : DOMAIN_LAWS D)
  (BaseUpper : UPPER_BOUND_UPDATE_LAWS V D Base).

  Module SU := ReluctantSideUpdate V D Base.

  Lemma update_preserves_upper_bound :
    forall source target phase old input aggregate upper,
      D.leq old upper = true ->
      D.leq input upper = true ->
      D.leq
        (snd (SU.update source target phase old input aggregate))
        upper = true.
  Proof.
    intros source target phase old input aggregate upper Hold Hinput.
    unfold SU.update.
    destruct (D.leq input old);
      [now apply BaseUpper.update_preserves_upper_bound |].
    destruct (D.leq input aggregate).
    - cbn. now apply DL.join_least.
    - now apply BaseUpper.update_preserves_upper_bound.
  Qed.
End ReluctantSideUpdateUpperBoundLaws.

Module ReluctantSideUpdateTerminationLaws
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (DL : DOMAIN_LAWS D) (BaseLaws : UPDATE_LAWS V D Base)
  (Covered : COVERED_JOIN_CREDIT_LAWS V D Base BaseLaws).

  Module SU := ReluctantSideUpdate V D Base.
  Module Sound := ReluctantSideUpdateSoundLaws V D Base DL BaseLaws.

  Definition update_sound := Sound.update_sound.
  Definition equivalent := BaseLaws.equivalent.
  Definition remaining_changes := BaseLaws.remaining_changes.
  Definition remaining_changes_extensional :=
    BaseLaws.remaining_changes_extensional.

  Lemma remaining_changes_nonincreasing :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <=
      remaining_changes phase old.
  Proof.
    intros source target phase old input aggregate Hold.
    unfold SU.update, remaining_changes.
    destruct (D.leq input old) eqn:Hinput.
    - apply BaseLaws.remaining_changes_nonincreasing.
    - destruct (D.leq input aggregate) eqn:Hcovered.
      + cbn. eapply Covered.covered_join_nonincreasing; eauto.
      + apply BaseLaws.remaining_changes_nonincreasing.
  Qed.

  Lemma exposed_change_consumes :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      D.leq
        (snd (SU.update source target phase old input aggregate))
        aggregate = false ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <
      remaining_changes phase old.
  Proof.
    intros source target phase old input aggregate Hold Hexposed.
    unfold SU.update, remaining_changes in *.
    destruct (D.leq input old) eqn:Hinput.
    - apply BaseLaws.update_change_consumes.
      intros [Hnew_old _].
      assert (Hcovered : D.leq
        (snd (Base.update true target phase old input)) aggregate = true).
      { eapply DL.leq_trans; eauto. }
      pose proof (eq_trans (eq_sym Hexposed) Hcovered) as Hfalse.
      discriminate Hfalse.
    - destruct (D.leq input aggregate) eqn:Hcovered.
      + cbn in Hexposed.
        pose proof (@DL.join_least old input aggregate Hold Hcovered)
          as Hjoin.
        pose proof (eq_trans (eq_sym Hexposed) Hjoin) as Hfalse.
        discriminate Hfalse.
      + apply BaseLaws.update_change_consumes.
        intros [Hnew_old _].
        assert (Hcontra : D.leq
          (snd (Base.update true target phase old input)) aggregate = true).
        { eapply DL.leq_trans; eauto. }
        pose proof (eq_trans (eq_sym Hexposed) Hcontra) as Hfalse.
        discriminate Hfalse.
  Qed.

  Lemma neutral_change_is_covered :
    forall source target phase old input aggregate,
      ~ equivalent
        (snd (SU.update source target phase old input aggregate)) old ->
      remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) =
      remaining_changes phase old ->
      D.leq input old = false /\ D.leq input aggregate = true.
  Proof.
    intros source target phase old input aggregate Hchange Hcredit.
    unfold SU.update, remaining_changes in Hchange, Hcredit.
    destruct (D.leq input old) eqn:Hnew.
    - pose proof (@BaseLaws.update_change_consumes true target phase old
        input Hchange) as Hstrict.
      change (BaseLaws.remaining_changes
        (fst (Base.update true target phase old input))
        (snd (Base.update true target phase old input)) =
        BaseLaws.remaining_changes phase old) in Hcredit.
      exfalso. rewrite Hcredit in Hstrict. lia.
    - destruct (D.leq input aggregate) eqn:Hcovered.
      + now split.
      + pose proof (@BaseLaws.update_change_consumes true target phase old
          input Hchange) as Hstrict.
        change (BaseLaws.remaining_changes
          (fst (Base.update true target phase old input))
          (snd (Base.update true target phase old input)) =
          BaseLaws.remaining_changes phase old) in Hcredit.
        exfalso. rewrite Hcredit in Hstrict. lia.
  Qed.

  Lemma covered_join_repeat_change_consumes :
    forall source target phase old input aggregate next_aggregate,
      D.leq input old = false ->
      D.leq input aggregate = true ->
      let first := SU.update source target phase old input aggregate in
      let second := SU.update source target (fst first) (snd first)
        input next_aggregate in
      ~ equivalent (snd second) (snd first) ->
      remaining_changes (fst second) (snd second) <
      remaining_changes (fst first) (snd first).
  Proof.
    intros source target phase old input aggregate next_aggregate
      Hnew Hcovered first second Hchange.
    pose proof (@Sound.covered_join_replay_uses_base
      source target phase old input aggregate next_aggregate
      Hnew Hcovered) as Hreplay.
    change (second = Base.update true target (fst first) (snd first)
      input) in Hreplay.
    rewrite Hreplay in Hchange |- *.
    apply BaseLaws.update_change_consumes. exact Hchange.
  Qed.

  Definition fixed_input_credit (phase : SU.phase) (old input : D.t) : nat :=
    2 * remaining_changes phase old +
      (if D.leq input old then 0 else 1).

  Lemma fixed_input_credit_nonincreasing :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      fixed_input_credit
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) input <=
      fixed_input_credit phase old input.
  Proof.
    intros source target phase old input aggregate Hold.
    pose proof (@remaining_changes_nonincreasing source target phase
      old input aggregate Hold) as Hcredit.
    pose proof (@Sound.update_sound source target phase old input
      aggregate) as Hsound.
    change (D.leq input
      (snd (SU.update source target phase old input aggregate)) = true)
      in Hsound.
    unfold fixed_input_credit. rewrite Hsound.
    destruct (D.leq input old); lia.
  Qed.

  Lemma changed_fixed_input_credit_decreases :
    forall source target phase old input aggregate,
      D.leq old aggregate = true ->
      ~ equivalent
        (snd (SU.update source target phase old input aggregate)) old ->
      fixed_input_credit
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) input <
      fixed_input_credit phase old input.
  Proof.
    intros source target phase old input aggregate Hold Hchange.
    pose proof (@remaining_changes_nonincreasing source target phase
      old input aggregate Hold) as Hnoninc.
    destruct (Nat.eq_dec
      (remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)))
      (remaining_changes phase old)) as [Heq|Hneq].
    - destruct (@neutral_change_is_covered source target phase old
        input aggregate Hchange Heq) as [Hnew _].
      pose proof (@Sound.update_sound source target phase old input
        aggregate) as Hsound.
      change (D.leq input
        (snd (SU.update source target phase old input aggregate)) = true)
        in Hsound.
      unfold fixed_input_credit. rewrite Hnew, Hsound. lia.
    - assert (Hstrict : remaining_changes
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) <
        remaining_changes phase old) by lia.
      unfold fixed_input_credit.
      destruct (D.leq input old);
        destruct (D.leq input
          (snd (SU.update source target phase old input aggregate)));
        lia.
  Qed.

  Inductive changed_writes (source target : V.t) (input : D.t) :
    nat -> SU.phase -> D.t -> Prop :=
  | changed_writes_zero : forall phase old,
      changed_writes source target input 0 phase old
  | changed_writes_step : forall n phase old aggregate,
      D.leq old aggregate = true ->
      ~ equivalent
        (snd (SU.update source target phase old input aggregate)) old ->
      changed_writes source target input n
        (fst (SU.update source target phase old input aggregate))
        (snd (SU.update source target phase old input aggregate)) ->
      changed_writes source target input (S n) phase old.

  Theorem fixed_input_changed_writes_bounded :
    forall source target input n phase old,
      changed_writes source target input n phase old ->
      n <= fixed_input_credit phase old input.
  Proof.
    intros source target input n phase old Hrun.
    induction Hrun.
    - lia.
    - pose proof (@changed_fixed_input_credit_decreases
        source target phase old input aggregate H H0) as Hdecrease.
      lia.
  Qed.

  Definition input_reset_measure
    (primary : nat) (phase : SU.phase) (old input : D.t) :=
    (primary, fixed_input_credit phase old input).

  Definition input_reset_relation :=
    Relation_Operators.slexprod nat nat lt lt.

  Theorem input_reset_relation_well_founded :
    well_founded input_reset_relation.
  Proof.
    unfold input_reset_relation.
    apply wf_slexprod; apply Nat.lt_wf_0.
  Qed.

  Lemma changed_fixed_input_measure_decreases :
    forall primary source target phase old input aggregate,
      D.leq old aggregate = true ->
      ~ equivalent
        (snd (SU.update source target phase old input aggregate)) old ->
      input_reset_relation
        (input_reset_measure primary
          (fst (SU.update source target phase old input aggregate))
          (snd (SU.update source target phase old input aggregate)) input)
        (input_reset_measure primary phase old input).
  Proof.
    intros primary source target phase old input aggregate Hold Hchange.
    apply Relation_Operators.right_slex.
    eapply changed_fixed_input_credit_decreases; eauto.
  Qed.

  Lemma changed_input_measure_decreases :
    forall before after phase old input next_phase next_old next_input,
      after < before ->
      input_reset_relation
        (input_reset_measure after next_phase next_old next_input)
        (input_reset_measure before phase old input).
  Proof.
    intros before after phase old input next_phase next_old next_input Hless.
    apply Relation_Operators.left_slex. exact Hless.
  Qed.
End ReluctantSideUpdateTerminationLaws.
