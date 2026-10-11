From Stdlib Require Import ZArith Lia.
From TcSolvers Require Export common.DefaultUpdate common.ThresholdInterval.
From TcSolvers Require Import common.Assumptions common.SideUpdate common.ReluctantUpdate.

Set Implicit Arguments.

(** A concrete default-policy instance on the infinite-height threshold domain.
    All credits are constructive; the initial copy needs twelve credits. *)
Module ThresholdDefaultUpdate (V : VAR).
  Module D := ThresholdIntervalDomain.
  Module DL := ThresholdIntervalDomainLaws.
  Module WN := ThresholdWidenNarrow.
  Module Policy := DefaultUpdateLaws V D WN.
  Module U := Policy.U.
  Module Reference := ThresholdOneBoxUpdateLaws V.

  Lemma joined_widen : forall old input,
    WN.widen old (D.join old input) = WN.widen old input.
  Proof.
    intros old input. destruct old, input; cbn [D.join]; try reflexivity.
    - unfold WN.widen. cbn [D.leq]. now rewrite Z.leb_refl.
    - unfold WN.widen. cbn [D.leq].
      destruct (Z.leb upper0 upper) eqn:Hle.
      + apply Z.leb_le in Hle. rewrite Z.max_l by exact Hle.
        now rewrite Z.leb_refl.
      + apply Z.leb_gt in Hle. rewrite Z.max_r by lia.
        assert (Hnot : Z.leb upper0 upper = false) by (apply Z.leb_gt; lia).
        now rewrite Hnot.
  Qed.

  (** The phase translation lets the joined box reuse the existing threshold
      proofs without identifying separately generated inductive phase types. *)
  Module JoinedBoxLaws <: UPDATE_LAWS V D U.Base.
    Definition reference_phase (phase : U.Base.phase) : Reference.U.phase :=
      match phase with
      | U.Base.BoxW => Reference.U.BoxW
      | U.Base.BoxN => Reference.U.BoxN
      | U.Base.Widen => Reference.U.Widen
      end.

    Lemma value_update : forall is_side variable phase old input,
      snd (U.Base.update is_side variable phase old input) =
      snd (Reference.U.update is_side variable (reference_phase phase) old input).
    Proof.
      intros is_side variable [] old input;
        unfold U.Base.update, Reference.U.update; cbn [reference_phase];
        try destruct (D.leq input old); cbn; try reflexivity; apply joined_widen.
    Qed.

    Lemma phase_update : forall is_side variable phase old input,
      reference_phase (fst (U.Base.update is_side variable phase old input)) =
      fst (Reference.U.update is_side variable (reference_phase phase) old input).
    Proof.
      intros is_side variable [] old input;
        unfold U.Base.update, Reference.U.update;
        try destruct (D.leq input old); reflexivity.
    Qed.

    Definition equivalent := Reference.equivalent.
    Definition equivalent_eq := Reference.equivalent_eq.

    Lemma update_sound : forall is_side variable phase old input,
      D.leq input (snd (U.Base.update is_side variable phase old input)) = true.
    Proof. intros. rewrite value_update. apply Reference.update_sound. Qed.

    Lemma update_extensional : forall is_side variable phase old old' input input',
      equivalent old old' -> equivalent input input' ->
      equivalent
        (snd (U.Base.update is_side variable phase old input))
        (snd (U.Base.update is_side variable phase old' input')).
    Proof. intros. rewrite !value_update. now apply Reference.update_extensional. Qed.

    Lemma update_stutter_closed : forall is_side variable phase old input,
      equivalent (snd (U.Base.update is_side variable phase old input)) old ->
      forall old' input', equivalent old' old -> equivalent input' input ->
      equivalent
        (snd (U.Base.update is_side variable
          (fst (U.Base.update is_side variable phase old input)) old' input')) old'.
    Proof.
      intros is_side variable phase old input Hstable old' input' Hold Hinput.
      rewrite value_update in Hstable |- *.
      rewrite phase_update. now apply Reference.update_stutter_closed.
    Qed.

    Definition remaining_changes (phase : U.Base.phase) (old : D.t) :=
      Reference.remaining_changes (reference_phase phase) old.

    Lemma remaining_changes_extensional : forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.
    Proof. intros. now apply Reference.remaining_changes_extensional. Qed.

    Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
      remaining_changes
        (fst (U.Base.update is_side variable phase old input))
        (snd (U.Base.update is_side variable phase old input)) <=
      remaining_changes phase old.
    Proof.
      intros. unfold remaining_changes. rewrite phase_update, value_update.
      apply Reference.remaining_changes_nonincreasing.
    Qed.

    Lemma update_change_consumes : forall is_side variable phase old input,
      ~ equivalent (snd (U.Base.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.Base.update is_side variable phase old input))
        (snd (U.Base.update is_side variable phase old input)) <
      remaining_changes phase old.
    Proof.
      intros is_side variable phase old input Hchange.
      unfold remaining_changes. rewrite phase_update, value_update.
      rewrite value_update in Hchange. now apply Reference.update_change_consumes.
    Qed.
  End JoinedBoxLaws.

  Module CopyCredit <: COPY_CREDIT_BOUND V D U.Base JoinedBoxLaws.
    Definition bound := 11.
    Lemma initial_credit_bounded : forall variable value,
      JoinedBoxLaws.remaining_changes (U.Base.initial_phase false variable) value <= bound.
    Proof.
      intros variable value.
      change (7 + ThresholdWideningCredit.remaining value <= 11).
      pose proof (ThresholdWideningCredit.remaining_bounded value). lia.
    Qed.
  End CopyCredit.

  Module BaseLaws := Policy.WithLaws DL ThresholdWidenNarrowLaws JoinedBoxLaws CopyCredit.
  Module Base := U.
  Module OrdinaryLaws := OrdinaryUpdateTerminationAdapter V D Base BaseLaws.

  Module Covered <: COVERED_JOIN_CREDIT_LAWS V D Base BaseLaws.
    Lemma covered_join_nonincreasing : forall target phase old input aggregate,
      D.leq old aggregate = true -> D.leq input old = false ->
      D.leq input aggregate = true ->
      BaseLaws.remaining_changes (fst (Base.update true target phase old input))
        (D.join old input) <= BaseLaws.remaining_changes phase old.
    Proof.
      intros target [] old input aggregate Hold Hnew Hcovered; cbn.
      - change (JoinedBoxLaws.remaining_changes U.Base.BoxW (D.join old input) <=
          S CopyCredit.bound).
        eapply Nat.le_trans.
        + exact (CopyCredit.initial_credit_bounded target (D.join old input)).
        + apply Nat.le_succ_diag_r.
      - unfold JoinedBoxLaws.remaining_changes. rewrite JoinedBoxLaws.phase_update.
        now apply Reference.Covered.covered_join_nonincreasing with (aggregate := aggregate).
    Qed.
  End Covered.

  Module SideUpdate := ReluctantSideUpdate V D Base.
  Module SideLaws := ReluctantSideUpdateTerminationLaws V D Base DL BaseLaws Covered.
End ThresholdDefaultUpdate.
