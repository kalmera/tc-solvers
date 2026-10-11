From Stdlib Require Import ZArith Lia.
From TcSolvers Require Import
  common.Assumptions
  common.BoxUpdate
  common.SideUpdate
  common.ReluctantUpdate
  common.StrongWidening.

Set Implicit Arguments.
Open Scope Z_scope.

(** The infinite-height domain of upper intervals [-infinity, upper], plus
    bottom.  Widening uses the finite thresholds -10, 0, and 10. *)
Inductive threshold_upper : Type :=
| TEmpty
| TUpTo (upper : Z)
| TAny.

Module ThresholdIntervalDomain <: DOMAIN.
  Definition t := threshold_upper.
  Definition bottom := TEmpty.

  Definition leq (left right : t) : bool :=
    match left, right with
    | TEmpty, _ => true
    | _, TAny => true
    | TUpTo x, TUpTo y => Z.leb x y
    | _, _ => false
    end.

  Definition join (left right : t) : t :=
    match left, right with
    | TEmpty, x | x, TEmpty => x
    | TAny, _ | _, TAny => TAny
    | TUpTo x, TUpTo y => TUpTo (Z.max x y)
    end.
End ThresholdIntervalDomain.

Module ThresholdIntervalDomainLaws <: DOMAIN_LAWS ThresholdIntervalDomain.
  Module D := ThresholdIntervalDomain.

  Lemma leq_refl : forall x, D.leq x x = true.
  Proof. intros []; cbn; auto using Z.leb_refl. Qed.

  Lemma leq_trans : forall x y z,
    D.leq x y = true -> D.leq y z = true -> D.leq x z = true.
  Proof.
    intros [] [] []; cbn; intros; try discriminate; try reflexivity.
    apply Z.leb_le in H. apply Z.leb_le in H0. apply Z.leb_le. lia.
  Qed.

  Lemma bottom_least : forall x, D.leq D.bottom x = true.
  Proof. now intros []. Qed.

  Lemma join_upper_left : forall x y, D.leq x (D.join x y) = true.
  Proof.
    intros [] []; cbn; try reflexivity; try apply Z.leb_refl.
    apply Z.leb_le. apply Z.le_max_l.
  Qed.

  Lemma join_upper_right : forall x y, D.leq y (D.join x y) = true.
  Proof.
    intros [] []; cbn; try reflexivity; try apply Z.leb_refl.
    apply Z.leb_le. apply Z.le_max_r.
  Qed.

  Lemma join_least : forall x y z,
    D.leq x z = true -> D.leq y z = true ->
    D.leq (D.join x y) z = true.
  Proof.
    intros [] [] []; cbn; intros; try discriminate; try reflexivity;
      try apply Z.leb_refl; try assumption.
    apply Z.leb_le in H. apply Z.leb_le in H0. apply Z.leb_le.
    now apply Z.max_lub.
  Qed.

  Lemma join_commutative : forall x y,
    D.leq (D.join x y) (D.join y x) = true /\
    D.leq (D.join y x) (D.join x y) = true.
  Proof.
    intros x y.
    assert (Heq : D.join x y = D.join y x).
    { destruct x, y; cbn; try reflexivity. f_equal. apply Z.max_comm. }
    rewrite Heq. split; apply leq_refl.
  Qed.

  Lemma join_associative : forall x y z,
    D.leq (D.join (D.join x y) z) (D.join x (D.join y z)) = true /\
    D.leq (D.join x (D.join y z)) (D.join (D.join x y) z) = true.
  Proof.
    intros x y z.
    assert (Heq : D.join (D.join x y) z = D.join x (D.join y z)).
    { destruct x, y, z; cbn; try reflexivity. f_equal. symmetry.
      apply Z.max_assoc. }
    rewrite Heq. split; apply leq_refl.
  Qed.
End ThresholdIntervalDomainLaws.

Module ThresholdWidenNarrow <: WIDEN_NARROW ThresholdIntervalDomain.
  Module D := ThresholdIntervalDomain.

  Definition next_threshold (value : Z) : threshold_upper :=
    if Z.leb value (-10) then TUpTo (-10)
    else if Z.leb value 0 then TUpTo 0
    else if Z.leb value 10 then TUpTo 10
    else TAny.

  Definition widen (old input : D.t) : D.t :=
    if D.leq input old then old
    else match input with
      | TEmpty => old
      | TUpTo value => next_threshold value
      | TAny => TAny
      end.

  Definition narrow (old input : D.t) : D.t :=
    match old with
    | TAny => input
    | _ => old
    end.
End ThresholdWidenNarrow.

Module ThresholdWidenNarrowLaws
  <: WIDEN_NARROW_LAWS ThresholdIntervalDomain ThresholdWidenNarrow.
  Module D := ThresholdIntervalDomain.
  Module WN := ThresholdWidenNarrow.

  Lemma widen_upper_old : forall old input,
    D.leq old (WN.widen old input) = true.
  Proof.
    intros old input. unfold WN.widen, WN.next_threshold.
    destruct old, input; cbn;
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?
      end;
      cbn; try reflexivity.
    all: try discriminate;
      repeat match goal with
      | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
      | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
      end;
      lia.
  Qed.

  Lemma widen_upper_input : forall old input,
    D.leq input (WN.widen old input) = true.
  Proof.
    intros old input. unfold WN.widen, WN.next_threshold.
    destruct old, input; cbn;
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?
      end;
      cbn; try reflexivity.
    all: try discriminate;
      repeat match goal with
      | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
      | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
      end;
      lia.
  Qed.

  Lemma narrow_lower : forall old input,
    D.leq input old = true -> D.leq input (WN.narrow old input) = true.
  Proof.
    intros old input H. destruct old; cbn; [exact H |exact H |].
    apply ThresholdIntervalDomainLaws.leq_refl.
  Qed.

  Lemma narrow_upper : forall old input,
    D.leq input old = true -> D.leq (WN.narrow old input) old = true.
  Proof.
    intros old input H. destruct old; cbn; try reflexivity.
    all: try apply Z.leb_refl; try exact H.
  Qed.
End ThresholdWidenNarrowLaws.

Close Scope Z_scope.

Module ThresholdWideningCredit.
  Module D := ThresholdIntervalDomain.
  Module WN := ThresholdWidenNarrow.
  Module Bridge := StrongWidening.Make D WN ThresholdIntervalDomainLaws.

  Definition remaining (value : D.t) : nat :=
    match value with
    | TEmpty => 4
    | TUpTo upper =>
        if Z.ltb upper (-10) then 4
        else if Z.ltb upper 0 then 3
        else if Z.ltb upper 10 then 2
        else 1
    | TAny => 0
    end.

  Lemma remaining_bounded : forall value, remaining value <= 4.
  Proof.
    intros value. destruct value; unfold remaining;
      repeat match goal with
      | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y)
      end; cbn; lia.
  Qed.

  Lemma remaining_antitone : forall old next,
    D.leq old next = true -> remaining next <= remaining old.
  Proof.
    intros old next Hle.
    destruct old, next; cbn in Hle |-; try discriminate; try lia.
    all: unfold remaining; cbn; try lia.
    - destruct (Z.ltb upper (-10)) eqn:H1;
        destruct (Z.ltb upper 0) eqn:H2;
        destruct (Z.ltb upper 10) eqn:H3; cbn; lia.
    - apply Z.leb_le in Hle.
      destruct (Z.ltb upper (-10)) eqn:H1;
        destruct (Z.ltb upper 0) eqn:H2;
        destruct (Z.ltb upper 10) eqn:H3;
        destruct (Z.ltb upper0 (-10)) eqn:H4;
        destruct (Z.ltb upper0 0) eqn:H5;
        destruct (Z.ltb upper0 10) eqn:H6; cbn;
        repeat match goal with
        | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
        | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
        end; lia.
  Qed.

  Lemma uncovered_widening_strict : forall old input,
    D.leq input old = false ->
    remaining (Bridge.widened old input) < remaining old.
  Proof.
    intros old input Huncovered.
    unfold Bridge.widened, WN.widen.
    destruct old, input; cbn in Huncovered |-; try discriminate; try lia.
    unfold WN.next_threshold.
    all: cbv [ThresholdIntervalDomain.join ThresholdIntervalDomain.leq
      WN.next_threshold remaining] in *.
    - destruct (upper <=? -10)%Z eqn:H1;
        destruct (upper <=? 0)%Z eqn:H2;
        destruct (upper <=? 10)%Z eqn:H3; cbn;
        repeat match goal with
        | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
        | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
        end; lia.
    - lia.
    - apply Z.leb_gt in Huncovered.
      assert (Hnot : (upper0 <=? upper)%Z = false) by
        (apply Z.leb_gt; lia).
      rewrite Hnot.
      destruct (upper0 <=? -10)%Z eqn:H1;
        destruct (upper0 <=? 0)%Z eqn:H2;
        destruct (upper0 <=? 10)%Z eqn:H3; cbn;
        destruct (upper <? -10)%Z eqn:H4;
        destruct (upper <? 0)%Z eqn:H5;
        destruct (upper <? 10)%Z eqn:H6; cbn;
        repeat match goal with
        | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
        | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
        | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
        | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
        end; lia.
    - destruct (upper <? -10)%Z;
        destruct (upper <? 0)%Z;
        destruct (upper <? 10)%Z; cbn; lia.
  Qed.

  Lemma uncovered_widening_consumes : forall old input next,
    D.leq input old = false ->
    D.leq (Bridge.widened old input) next = true ->
    remaining next < remaining old.
  Proof.
    intros old input next Huncovered Hnext.
    eapply Nat.le_lt_trans with
      (m := remaining (Bridge.widened old input)).
    - now apply remaining_antitone.
    - now apply uncovered_widening_strict.
  Qed.
End ThresholdWideningCredit.

Module ThresholdStrongWideningBridge :=
  StrongWidening.Make
    ThresholdIntervalDomain ThresholdWidenNarrow
    ThresholdIntervalDomainLaws.

Module ThresholdStrongWidening.
  Module Proof :=
    ThresholdStrongWideningBridge.QuantitativeBridge ThresholdWideningCredit.
  Include Proof.
End ThresholdStrongWidening.

Module ThresholdOneBoxUpdate (V : VAR) :=
  OneBoxUpdate V ThresholdIntervalDomain ThresholdWidenNarrow.

Module ThresholdOneBoxUpdateLaws (V : VAR).
  Module D := ThresholdIntervalDomain.
  Module WN := ThresholdWidenNarrow.
  Module U := ThresholdOneBoxUpdate V.

  Definition equivalent (left right : D.t) : Prop :=
    D.leq left right = true /\ D.leq right left = true.

  Lemma equivalent_eq : forall left right,
    equivalent left right -> left = right.
  Proof.
    intros left right [Hlr Hrl].
    destruct left, right; cbn in Hlr, Hrl; try discriminate; try reflexivity.
    apply Z.leb_le in Hlr. apply Z.leb_le in Hrl.
    f_equal. lia.
  Qed.

  Lemma update_sound : forall is_side variable phase old input,
    D.leq input (snd (U.update is_side variable phase old input)) = true.
  Proof.
    intros is_side variable phase old input.
    destruct phase; unfold U.update.
    - destruct (D.leq input old) eqn:Hle; cbn.
      + now apply ThresholdWidenNarrowLaws.narrow_lower.
      + apply ThresholdWidenNarrowLaws.widen_upper_input.
    - destruct (D.leq input old) eqn:Hle; cbn.
      + now apply ThresholdWidenNarrowLaws.narrow_lower.
      + apply ThresholdWidenNarrowLaws.widen_upper_input.
    - cbn. apply ThresholdWidenNarrowLaws.widen_upper_input.
  Qed.

  Lemma update_extensional : forall is_side variable phase old old' input input',
    equivalent old old' -> equivalent input input' ->
    equivalent
      (snd (U.update is_side variable phase old input))
      (snd (U.update is_side variable phase old' input')).
  Proof.
    intros is_side variable phase old old' input input' Hold Hinput.
    apply equivalent_eq in Hold. apply equivalent_eq in Hinput. subst.
    split; apply ThresholdIntervalDomainLaws.leq_refl.
  Qed.

  Lemma update_stutter_closed : forall is_side variable phase old input,
    equivalent (snd (U.update is_side variable phase old input)) old ->
    forall old' input', equivalent old' old -> equivalent input' input ->
    equivalent
      (snd (U.update is_side variable
        (fst (U.update is_side variable phase old input)) old' input')) old'.
  Proof.
    intros is_side variable phase old input Hstable old' input' Hold Hinput.
    apply equivalent_eq in Hold. apply equivalent_eq in Hinput. subst old' input'.
    assert (Hle : D.leq input old = true).
    { destruct Hstable as [Hnew_old _].
      eapply ThresholdIntervalDomainLaws.leq_trans.
      - apply update_sound.
      - exact Hnew_old. }
    apply equivalent_eq in Hstable.
    destruct phase; unfold U.update in *.
    - rewrite Hle in *. cbn in *. rewrite Hstable.
      split; apply ThresholdIntervalDomainLaws.leq_refl.
    - rewrite Hle in *. cbn in *. rewrite Hstable.
      split; apply ThresholdIntervalDomainLaws.leq_refl.
    - cbn in *. rewrite Hstable.
      split; apply ThresholdIntervalDomainLaws.leq_refl.
  Qed.

  Definition narrow_slot (value : D.t) : nat :=
    match value with TAny => 1 | _ => 0 end.

  Definition remaining_changes (phase : U.phase) (old : D.t) : nat :=
    match phase with
    | U.BoxW => 7 + ThresholdWideningCredit.remaining old
    | U.BoxN => 5 + narrow_slot old
    | U.Widen => ThresholdWideningCredit.remaining old
    end.

  Lemma remaining_changes_extensional : forall phase old old',
    equivalent old old' ->
    remaining_changes phase old = remaining_changes phase old'.
  Proof.
    intros phase old old' Heq. apply equivalent_eq in Heq. now subst.
  Qed.

  Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
    remaining_changes
      (fst (U.update is_side variable phase old input))
      (snd (U.update is_side variable phase old input)) <=
    remaining_changes phase old.
  Proof.
    intros is_side variable phase old input.
    destruct phase; unfold U.update.
    - destruct (D.leq input old) eqn:Hle; cbn.
      + unfold remaining_changes, narrow_slot,
          ThresholdWidenNarrow.narrow, ThresholdWideningCredit.remaining.
        destruct old, input; cbn in Hle |-; try discriminate; lia.
      + unfold remaining_changes. repeat apply le_n_S.

        apply ThresholdWideningCredit.remaining_antitone.
        apply ThresholdWidenNarrowLaws.widen_upper_old.
    - destruct (D.leq input old) eqn:Hle; cbn.
      + unfold remaining_changes, narrow_slot,
          ThresholdWidenNarrow.narrow, ThresholdWideningCredit.remaining.
        destruct old, input; cbn in Hle |-; try discriminate; lia.
      + unfold remaining_changes.
        assert (Hmono :
          ThresholdWideningCredit.remaining (WN.widen old input) <=
          ThresholdWideningCredit.remaining old).
        { apply ThresholdWideningCredit.remaining_antitone.

          apply ThresholdWidenNarrowLaws.widen_upper_old. }
        pose proof (ThresholdWideningCredit.remaining_bounded old) as Hfour.
        lia.
    - cbn. unfold remaining_changes.
      apply ThresholdWideningCredit.remaining_antitone.
      apply ThresholdWidenNarrowLaws.widen_upper_old.
  Qed.

  Lemma widen_uncovered_strict : forall old input,
    D.leq input old = false ->
    ThresholdWideningCredit.remaining (WN.widen old input) <
    ThresholdWideningCredit.remaining old.
  Proof.
    intros old input Huncovered.
    eapply ThresholdWideningCredit.uncovered_widening_consumes.
    - exact Huncovered.
    - apply ThresholdIntervalDomainLaws.leq_refl.
  Qed.

  Lemma update_change_consumes : forall is_side variable phase old input,
    ~ equivalent (snd (U.update is_side variable phase old input)) old ->
    remaining_changes
      (fst (U.update is_side variable phase old input))
      (snd (U.update is_side variable phase old input)) <
    remaining_changes phase old.
  Proof.
    intros is_side variable phase old input Hchange.
    destruct phase; unfold U.update in *.
    - destruct (D.leq input old) eqn:Hle; cbn in *.
      + unfold remaining_changes, narrow_slot,
          ThresholdWidenNarrow.narrow, ThresholdWideningCredit.remaining.
        destruct old, input; cbn in Hle, Hchange |-; try discriminate;
          repeat match goal with
          | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y)
          end; cbn; lia.
      + unfold remaining_changes.
        pose proof (@widen_uncovered_strict
          old input Hle) as Hstrict.
        lia.
    - destruct (D.leq input old) eqn:Hle; cbn in *.
      + unfold remaining_changes, narrow_slot,
          ThresholdWidenNarrow.narrow, ThresholdWideningCredit.remaining,
          equivalent in Hchange.
        destruct old, input; cbn in Hle, Hchange |-; try discriminate;
          repeat match goal with
          | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y)
          end; cbn; lia.
      + unfold remaining_changes.
        pose proof
          (ThresholdWideningCredit.remaining_bounded
            (WN.widen old input)) as Hfour.
        lia.
    - cbn in *. unfold remaining_changes.
      destruct (D.leq input old) eqn:Hle.
      + exfalso. apply Hchange.
        unfold WN.widen, ThresholdWidenNarrow.widen.
        rewrite Hle.
        split; apply ThresholdIntervalDomainLaws.leq_refl.
      + eapply ThresholdWideningCredit.uncovered_widening_consumes.
        * exact Hle.
        * apply ThresholdIntervalDomainLaws.leq_refl.
  Qed.

  Module Covered.
    Lemma covered_join_nonincreasing : forall target phase old input aggregate,
      D.leq old aggregate = true ->
      D.leq input old = false ->
      D.leq input aggregate = true ->
      remaining_changes
        (fst (U.update true target phase old input))
        (D.join old input) <=
      remaining_changes phase old.
    Proof.
      intros target phase old input aggregate Hold Hinput Hcovered.
      destruct phase; unfold U.update.
      - rewrite Hinput. cbn. unfold remaining_changes.
        assert (Hmono :
          ThresholdWideningCredit.remaining (D.join old input) <=
          ThresholdWideningCredit.remaining old).
        { apply ThresholdWideningCredit.remaining_antitone.
          apply ThresholdIntervalDomainLaws.join_upper_left. }
        lia.
      - rewrite Hinput. cbn. unfold remaining_changes.
        assert (Hmono :
          ThresholdWideningCredit.remaining (D.join old input) <=
          ThresholdWideningCredit.remaining old).
        { apply ThresholdWideningCredit.remaining_antitone.
          apply ThresholdIntervalDomainLaws.join_upper_left. }
        pose proof (ThresholdWideningCredit.remaining_bounded old) as Hfour.
        lia.
      - cbn. unfold remaining_changes.
        apply ThresholdWideningCredit.remaining_antitone.
        apply ThresholdIntervalDomainLaws.join_upper_left.
    Qed.
  End Covered.
End ThresholdOneBoxUpdateLaws.

Module ThresholdReluctantOneBox (V : VAR).
  Module BaseLaws := ThresholdOneBoxUpdateLaws V.
  Module Base := BaseLaws.U.
  Module OrdinaryLaws := OrdinaryUpdateTerminationAdapter
    V ThresholdIntervalDomain Base BaseLaws.
  Module Covered := BaseLaws.Covered.
  Module SideUpdate := ReluctantSideUpdate V ThresholdIntervalDomain Base.
  Module SideLaws := ReluctantSideUpdateTerminationLaws
    V ThresholdIntervalDomain Base ThresholdIntervalDomainLaws BaseLaws Covered.
End ThresholdReluctantOneBox.
