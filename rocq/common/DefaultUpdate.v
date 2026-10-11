From Stdlib Require Import Lia.
From TcSolvers Require Import common.Assumptions common.BoxUpdate.

Set Implicit Arguments.

(** Goblint's default policy: ordinary values copy once before entering a
    widening/narrowing box; side contributions widen from their first update.
    Widening receives the join of the old value and the new input, matching
    [catching_up/goblint_qsolver_update.ml]. *)
Module DefaultUpdate (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D)
  <: UPDATE V D.

  Module JoinedWN.
    Definition widen (old input : D.t) := WN.widen old (D.join old input).
    Definition narrow := WN.narrow.
  End JoinedWN.
  Module Base := OneBoxUpdate V D JoinedWN.

  Inductive phase_state := Copy | Box (current : Base.phase).
  Definition phase := phase_state.
  Definition BoxW := Box Base.BoxW.
  Definition BoxN := Box Base.BoxN.
  Definition Widen := Box Base.Widen.

  Definition initial_phase (is_side : bool) (_variable : V.t) : phase :=
    if is_side then Widen else Copy.

  Definition update (is_side : bool) (variable : V.t)
    (current : phase) (old input : D.t) : phase * D.t :=
    match current with
    | Copy => (BoxW, input)
    | Box current =>
        let next := Base.update is_side variable current old input in
        (Box (fst next), snd next)
    end.
End DefaultUpdate.

(** A copy can jump to any value. Its credit therefore covers the largest
    possible credit at entry to the box, plus the copy itself. *)
Module Type COPY_CREDIT_BOUND
  (V : VAR) (D : DOMAIN) (Base : UPDATE V D)
  (BaseLaws : UPDATE_LAWS V D Base).
  Parameter bound : nat.
  Parameter initial_credit_bounded : forall variable value,
    BaseLaws.remaining_changes (Base.initial_phase false variable) value <= bound.
End COPY_CREDIT_BOUND.

Module DefaultUpdateLaws (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module U := DefaultUpdate V D WN.

  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (BaseLaws : UPDATE_LAWS V D U.Base)
    (CopyCredit : COPY_CREDIT_BOUND V D U.Base BaseLaws)
    <: UPDATE_LAWS V D U.

    Definition equivalent := BaseLaws.equivalent.

    Lemma update_sound : forall is_side variable phase old input,
      D.leq input (snd (U.update is_side variable phase old input)) = true.
    Proof.
      intros is_side variable [] old input; cbn.
      - apply DL.leq_refl.
      - apply BaseLaws.update_sound.
    Qed.

    Lemma update_extensional : forall is_side variable phase old old' input input',
      equivalent old old' -> equivalent input input' ->
      equivalent
        (snd (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old' input')).
    Proof.
      intros is_side variable [] old old' input input' Hold Hinput; cbn.
      - exact Hinput.
      - now apply BaseLaws.update_extensional.
    Qed.

    Lemma update_stutter_closed : forall is_side variable phase old input,
      equivalent (snd (U.update is_side variable phase old input)) old ->
      forall old' input', equivalent old' old -> equivalent input' input ->
      equivalent
        (snd (U.update is_side variable
          (fst (U.update is_side variable phase old input)) old' input')) old'.
    Proof.
      intros is_side variable [] old input Hstable old' input' Hold Hinput.
      - cbn in Hstable |- *.
        assert (Hle : D.leq input' old' = true).
        { eapply DL.leq_trans; [exact (proj1 Hinput) |].
          eapply DL.leq_trans; [exact (proj1 Hstable) |exact (proj2 Hold)]. }
        unfold U.Base.update. rewrite Hle. cbn.
        split.
        + now apply WNL.narrow_upper.
        + eapply DL.leq_trans; [exact (proj1 Hold) |].
          eapply DL.leq_trans; [exact (proj2 Hstable) |].
          eapply DL.leq_trans; [exact (proj2 Hinput) |].
          now apply WNL.narrow_lower.
      - cbn in Hstable |- *.
        now apply BaseLaws.update_stutter_closed.
    Qed.

    Definition remaining_changes (phase : U.phase) (old : D.t) : nat :=
      match phase with
      | U.Copy => S CopyCredit.bound
      | U.Box current => BaseLaws.remaining_changes current old
      end.

    Lemma remaining_changes_extensional : forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.
    Proof.
      intros [] old old' Heq; cbn; [reflexivity |].
      now apply BaseLaws.remaining_changes_extensional.
    Qed.

    Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <=
      remaining_changes phase old.
    Proof.
      intros is_side variable [] old input; cbn.
      - pose proof (CopyCredit.initial_credit_bounded variable input) as H.
        change (BaseLaws.remaining_changes U.Base.BoxW input <= CopyCredit.bound) in H.
        lia.
      - apply BaseLaws.remaining_changes_nonincreasing.
    Qed.

    Lemma update_change_consumes : forall is_side variable phase old input,
      ~ equivalent (snd (U.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <
      remaining_changes phase old.
    Proof.
      intros is_side variable [] old input Hchange; cbn in Hchange |- *.
      - pose proof (CopyCredit.initial_credit_bounded variable input) as H.
        change (BaseLaws.remaining_changes U.Base.BoxW input <= CopyCredit.bound) in H.
        lia.
      - now apply BaseLaws.update_change_consumes.
    Qed.
  End WithLaws.
End DefaultUpdateLaws.
