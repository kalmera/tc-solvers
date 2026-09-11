From TcSolvers Require Import common.Interfaces.

Set Implicit Arguments.

(** Widening and narrowing operations for the zero-copy, one-box update.
    As in Goblint, widening receives the join of the old value and the new
    input as its second argument. *)
Module Type WIDEN_NARROW (D : DOMAIN).
  Parameter widen : D.t -> D.t -> D.t.
  Parameter narrow : D.t -> D.t -> D.t.
End WIDEN_NARROW.

Module Type WIDEN_NARROW_LAWS
  (D : DOMAIN) (WN : WIDEN_NARROW D).

  Parameter widen_upper_old :
    forall old input,
      D.leq old (WN.widen old (D.join old input)) = true.

  Parameter widen_upper_input :
    forall old input,
      D.leq input (WN.widen old (D.join old input)) = true.

  Parameter narrow_lower :
    forall old input,
      D.leq input old = true ->
      D.leq input (WN.narrow old input) = true.

  Parameter narrow_upper :
    forall old input,
      D.leq input old = true ->
      D.leq (WN.narrow old input) old = true.
End WIDEN_NARROW_LAWS.

(** [BoxUpdate] with zero copy phases and one widening/narrowing box.

    [BoxW] widens until it receives an input below the old value.
    [BoxN] narrows while inputs remain below the old value.  An increasing
    input in [BoxN] enters the permanent fallback phase [Widen]. *)
Module OneBoxUpdate
  (V : VAR)
  (D : DOMAIN)
  (WN : WIDEN_NARROW D).

  Inductive phase_state : Type :=
  | BoxW
  | BoxN
  | Widen.

  Definition phase := phase_state.

  Definition initial_phase
    (_is_side : bool) (_variable : V.t) : phase :=
    BoxW.

  Definition joined_widen (old input : D.t) : D.t :=
    WN.widen old (D.join old input).

  Definition update
    (_is_side : bool) (_variable : V.t)
    (current : phase) (old input : D.t) : phase * D.t :=
    match current with
    | BoxW =>
        if D.leq input old
        then (BoxN, WN.narrow old input)
        else (BoxW, joined_widen old input)
    | BoxN =>
        if D.leq input old
        then (BoxN, WN.narrow old input)
        else (Widen, joined_widen old input)
    | Widen =>
        (Widen, joined_widen old input)
    end.

  Definition avoids_fallback (current : phase) : Prop :=
    current <> Widen.

  Definition admissible_input
    (current : phase) (old input : D.t) : Prop :=
    current = BoxN ->
    D.leq input old = true.

  Lemma initial_avoids_fallback :
    forall is_side variable,
      avoids_fallback (initial_phase is_side variable).
  Proof.
    intros is_side variable Hfallback.
    discriminate.
  Qed.

  Lemma update_enters_fallback :
    forall is_side variable current old input,
      fst (update is_side variable current old input) = Widen ->
      current = Widen \/
      (current = BoxN /\ D.leq input old = false).
  Proof.
    intros is_side variable current old input Hupdate.
    destruct current.
    - unfold update in Hupdate.
      destruct (D.leq input old); discriminate.
    - right. split; [reflexivity |].
      unfold update in Hupdate.
      destruct (D.leq input old) eqn:Hle;
        [discriminate | reflexivity].
    - now left.
  Qed.

  Lemma admissible_update_avoids_fallback :
    forall is_side variable current old input,
      avoids_fallback current ->
      admissible_input current old input ->
      avoids_fallback
        (fst (update is_side variable current old input)).
  Proof.
    intros is_side variable current old input Hsafe Hadmissible.
    destruct current.
    - unfold update, avoids_fallback.
      destruct (D.leq input old); discriminate.
    - specialize (Hadmissible eq_refl).
      unfold update, avoids_fallback.
      now rewrite Hadmissible.
    - contradiction.
  Qed.

  Lemma boxn_update_is_narrowing :
    forall is_side variable old input,
      D.leq input old = true ->
      update is_side variable BoxN old input =
        (BoxN, WN.narrow old input).
  Proof.
    intros is_side variable old input Hle.
    unfold update.
    now rewrite Hle.
  Qed.

End OneBoxUpdate.
