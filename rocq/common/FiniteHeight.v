From Stdlib Require Import Lia.
From TcSolvers Require Import common.Assumptions.

Set Implicit Arguments.

(** A constructive finite-height witness.  [remaining_height] decreases on
    every strict ascending step and is insensitive to domain equivalence. *)
Module Type FINITE_HEIGHT_LAWS (D : DOMAIN) (DL : DOMAIN_LAWS D).
  Definition equivalent (left right : D.t) : Prop :=
    D.leq left right = true /\ D.leq right left = true.

  Parameter remaining_height : D.t -> nat.

  Parameter remaining_height_extensional :
    forall left right,
      equivalent left right ->
      remaining_height left = remaining_height right.

  Parameter strict_ascent_decreases :
    forall lower upper,
      D.leq lower upper = true ->
      ~ equivalent upper lower ->
      remaining_height upper < remaining_height lower.
End FINITE_HEIGHT_LAWS.

(** The finite-height update performs ordinary Kleene iteration: it retains
    the old value and joins in the newly computed input. *)
Module JoinUpdate (V : VAR) (D : DOMAIN) <: UPDATE V D.
  Definition phase : Type := unit.
  Definition initial_phase (_ : bool) (_ : V.t) : phase := tt.
  Definition update
    (_ : bool) (_ : V.t) (_ : phase) (old input : D.t) : phase * D.t :=
    (tt, D.join old input).
End JoinUpdate.

Module JoinUpdateLaws
  (V : VAR)
  (D : DOMAIN)
  (DL : DOMAIN_LAWS D)
  (FH : FINITE_HEIGHT_LAWS D DL).

  Module U := JoinUpdate V D.

  Definition equivalent (left right : D.t) : Prop :=
    D.leq left right = true /\ D.leq right left = true.

  Lemma equivalent_finite_height :
    forall left right,
      equivalent left right ->
      FH.equivalent left right.
  Proof. intros left right H. exact H. Qed.

  Definition update_sound :
    forall is_side variable phase old input,
      D.leq input
        (snd (U.update is_side variable phase old input)) = true.
  Proof. intros. apply DL.join_upper_right. Qed.

  Definition update_extensional :
    forall is_side variable phase old old' input input',
      equivalent old old' ->
      equivalent input input' ->
      equivalent
        (snd (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old' input')).
  Proof.
    intros is_side variable phase old old' input input'
      [Hold Hold'] [Hinput Hinput'].
    cbn. split; apply DL.join_least.
    - eapply DL.leq_trans; [exact Hold |apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hinput |apply DL.join_upper_right].
    - eapply DL.leq_trans; [exact Hold' |apply DL.join_upper_left].
    - eapply DL.leq_trans; [exact Hinput' |apply DL.join_upper_right].
  Qed.

  Definition update_stutter_closed :
    forall is_side variable phase old input,
      equivalent
        (snd (U.update is_side variable phase old input)) old ->
      forall old' input',
        equivalent old' old ->
        equivalent input' input ->
        equivalent
          (snd (U.update is_side variable
            (fst (U.update is_side variable phase old input))
            old' input'))
          old'.
  Proof.
    intros is_side variable phase old input [Hjoin _]
      old' input' [Hold' Hold] [Hinput' _].
    cbn in *. split.
    - apply DL.join_least; [apply DL.leq_refl |].
      eapply DL.leq_trans; [exact Hinput' |].
      eapply DL.leq_trans; [apply DL.join_upper_right |].
      eapply DL.leq_trans; [exact Hjoin |exact Hold].
    - apply DL.join_upper_left.
  Qed.

  Definition remaining_changes (_ : U.phase) (old : D.t) : nat :=
    FH.remaining_height old.

  Definition remaining_changes_extensional :
    forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.
  Proof.
    intros phase old old' Hequivalent.
    apply FH.remaining_height_extensional.
    now apply equivalent_finite_height.
  Qed.

  Definition remaining_changes_nonincreasing :
    forall is_side variable phase old input,
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <=
      remaining_changes phase old.
  Proof.
    intros is_side variable phase old input.
    unfold remaining_changes, U.update. cbn.
    destruct (D.leq (D.join old input) old) eqn:Hback.
    - rewrite (FH.remaining_height_extensional
        (left := D.join old input) (right := old)).
      + apply le_n.
      + split; [exact Hback |apply DL.join_upper_left].
    - assert (Hstrict :
        FH.remaining_height (D.join old input) <
        FH.remaining_height old).
      { apply FH.strict_ascent_decreases.
        - apply DL.join_upper_left.
        - intros [Hcontra _]. congruence. }
      lia.
  Qed.

  Definition update_change_consumes :
    forall is_side variable phase old input,
      ~ equivalent
          (snd (U.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <
      remaining_changes phase old.
  Proof.
    intros is_side variable phase old input Hchange.
    unfold remaining_changes, U.update in *. cbn in *.
    apply FH.strict_ascent_decreases.
    - apply DL.join_upper_left.
    - exact Hchange.
  Qed.
End JoinUpdateLaws.

(** Updates used in a least-solution proof may not jump above a common upper
    bound.  This separates minimality from the termination-specific phase
    accounting in [UPDATE_LAWS]. *)
Module Type UPPER_BOUND_UPDATE_LAWS
  (V : VAR) (D : DOMAIN) (U : UPDATE V D).
  Parameter update_preserves_upper_bound :
    forall is_side variable phase old input upper,
      D.leq old upper = true ->
      D.leq input upper = true ->
      D.leq
        (snd (U.update is_side variable phase old input)) upper = true.
End UPPER_BOUND_UPDATE_LAWS.

Module JoinUpdateUpperBoundLaws
  (V : VAR) (D : DOMAIN) (DL : DOMAIN_LAWS D).

  Module U := JoinUpdate V D.

  Definition update_preserves_upper_bound :
    forall is_side variable phase old input upper,
      D.leq old upper = true ->
      D.leq input upper = true ->
      D.leq
        (snd (U.update is_side variable phase old input)) upper = true.
  Proof. intros. cbn. now apply DL.join_least. Qed.
End JoinUpdateUpperBoundLaws.
