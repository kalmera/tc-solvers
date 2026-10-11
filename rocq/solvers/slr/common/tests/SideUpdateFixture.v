From Stdlib Require Import Lia.
From TcSolvers Require Import
  common.Assumptions
  common.BoxUpdate
  common.SideUpdate
  common.ReluctantUpdate.

Module TV <: VAR.
  Definition t := unit.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof. decide equality. Defined.
End TV.

Inductive three := Low | Mid | High.

Module TD <: DOMAIN.
  Definition t := three.
  Definition bottom := Low.
  Definition leq (left right : t) : bool :=
    match left, right with
    | Low, _ | Mid, Mid | Mid, High | High, High => true
    | _, _ => false
    end.
  Definition join (left right : t) : t :=
    match left, right with
    | High, _ | _, High => High
    | Mid, _ | _, Mid => Mid
    | Low, Low => Low
    end.
End TD.

Module TDLaws <: DOMAIN_LAWS TD.
  Lemma leq_refl : forall x, TD.leq x x = true.
  Proof. now destruct x. Qed.

  Lemma leq_trans : forall x y z,
    TD.leq x y = true -> TD.leq y z = true -> TD.leq x z = true.
  Proof. now destruct x, y, z. Qed.

  Lemma bottom_least : forall x, TD.leq TD.bottom x = true.
  Proof. now destruct x. Qed.

  Lemma join_upper_left : forall x y, TD.leq x (TD.join x y) = true.
  Proof. now destruct x, y. Qed.

  Lemma join_upper_right : forall x y, TD.leq y (TD.join x y) = true.
  Proof. now destruct x, y. Qed.

  Lemma join_least : forall x y z,
    TD.leq x z = true -> TD.leq y z = true ->
    TD.leq (TD.join x y) z = true.
  Proof. now destruct x, y, z. Qed.

  Lemma join_commutative : forall x y,
    TD.leq (TD.join x y) (TD.join y x) = true /\
    TD.leq (TD.join y x) (TD.join x y) = true.
  Proof. now destruct x, y. Qed.

  Lemma join_associative : forall x y z,
    TD.leq (TD.join (TD.join x y) z) (TD.join x (TD.join y z)) = true /\
    TD.leq (TD.join x (TD.join y z)) (TD.join (TD.join x y) z) = true.
  Proof. now destruct x, y, z. Qed.
End TDLaws.

Module TWN <: WIDEN_NARROW TD.
  Definition widen (old input : three) : three :=
    if TD.leq input old then old else High.
  Definition narrow (_old input : three) := input.
End TWN.

Module TWNLaws <: WIDEN_NARROW_LAWS TD TWN.
  Lemma widen_upper_old : forall old input,
    TD.leq old (TWN.widen old input) = true.
  Proof. now destruct old, input. Qed.

  Lemma widen_upper_input : forall old input,
    TD.leq input (TWN.widen old input) = true.
  Proof. now destruct old, input. Qed.

  Lemma narrow_lower : forall old input,
    TD.leq input old = true -> TD.leq input (TWN.narrow old input) = true.
  Proof. now destruct old, input. Qed.

  Lemma narrow_upper : forall old input,
    TD.leq input old = true -> TD.leq (TWN.narrow old input) old = true.
  Proof. now destruct old, input. Qed.
End TWNLaws.

Module TBase := OneBoxUpdate TV TD TWN.

Module TBaseLaws <: UPDATE_LAWS TV TD TBase.
  Definition equivalent (left right : TD.t) : Prop :=
    TD.leq left right = true /\ TD.leq right left = true.

  Lemma equivalent_eq : forall left right, equivalent left right -> left = right.
  Proof.
    intros left right H. destruct left, right; cbn in H;
      destruct H as [Hleft Hright]; try discriminate; reflexivity.
  Qed.

  Lemma update_sound : forall is_side variable phase old input,
    TD.leq input
      (snd (TBase.update is_side variable phase old input)) = true.
  Proof.
    intros. destruct phase, old, input; cbn;
      try apply TWNLaws.narrow_lower; reflexivity.
  Qed.

  Lemma update_extensional : forall is_side variable phase old old' input input',
    equivalent old old' -> equivalent input input' ->
    equivalent
      (snd (TBase.update is_side variable phase old input))
      (snd (TBase.update is_side variable phase old' input')).
  Proof.
    intros is_side variable phase old old' input input' Hold Hinput.
    apply equivalent_eq in Hold. apply equivalent_eq in Hinput.
    subst old'. subst input'. unfold equivalent.
    split; apply TDLaws.leq_refl.
  Qed.

  Lemma update_stutter_closed : forall is_side variable phase old input,
    equivalent (snd (TBase.update is_side variable phase old input)) old ->
    forall old' input', equivalent old' old -> equivalent input' input ->
    equivalent
      (snd (TBase.update is_side variable
        (fst (TBase.update is_side variable phase old input)) old' input')) old'.
  Proof.
    intros is_side variable phase old input Hstable old' input' Hold Hinput.
    apply equivalent_eq in Hstable.
    apply equivalent_eq in Hold. apply equivalent_eq in Hinput.
    subst old'. subst input'.
    destruct phase, old, input; cbn in Hstable |-;
      try discriminate; repeat split; reflexivity.
  Qed.

  Definition remaining_changes (phase : TBase.phase) (old : TD.t) : nat :=
    match phase, old with
    | TBase.BoxW, Low => 6
    | TBase.BoxW, Mid => 5
    | TBase.BoxW, High => 4
    | TBase.BoxN, Low => 1
    | TBase.BoxN, Mid => 2
    | TBase.BoxN, High => 3
    | TBase.Widen, Low => 2
    | TBase.Widen, Mid => 1
    | TBase.Widen, High => 0
    end.

  Lemma remaining_changes_extensional : forall phase old old',
    equivalent old old' ->
    remaining_changes phase old = remaining_changes phase old'.
  Proof.
    intros phase old old' H. apply equivalent_eq in H. now subst old'.
  Qed.

  Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
    remaining_changes
      (fst (TBase.update is_side variable phase old input))
      (snd (TBase.update is_side variable phase old input)) <=
    remaining_changes phase old.
  Proof. intros. destruct phase, old, input; cbn; lia. Qed.

  Lemma update_change_consumes : forall is_side variable phase old input,
    ~ equivalent (snd (TBase.update is_side variable phase old input)) old ->
    remaining_changes
      (fst (TBase.update is_side variable phase old input))
      (snd (TBase.update is_side variable phase old input)) <
    remaining_changes phase old.
  Proof.
    intros is_side variable phase old input Hchanged.
    destruct phase, old, input; cbn in *; try lia;
      exfalso; apply Hchanged; repeat split; reflexivity.
  Qed.
End TBaseLaws.

Module TCovered <: COVERED_JOIN_CREDIT_LAWS TV TD TBase TBaseLaws.
  Lemma covered_join_nonincreasing : forall target phase old input aggregate,
    TD.leq old aggregate = true ->
    TD.leq input old = false ->
    TD.leq input aggregate = true ->
    TBaseLaws.remaining_changes
      (fst (TBase.update true target phase old input))
      (TD.join old input) <=
    TBaseLaws.remaining_changes phase old.
  Proof. intros. destruct phase, old, input, aggregate; cbn in *; try lia; discriminate. Qed.
End TCovered.

Module TSU := ReluctantSideUpdate TV TD TBase.
Module TSUL := ReluctantSideUpdateTerminationLaws
  TV TD TBase TDLaws TBaseLaws TCovered.

Example toy_covered_join_is_credit_nonincreasing :
  TSUL.remaining_changes
    (fst (TSU.update tt tt TBase.BoxN Low Mid High))
    (snd (TSU.update tt tt TBase.BoxN Low Mid High)) <=
  TSUL.remaining_changes TBase.BoxN Low.
Proof. reflexivity. Qed.

Example toy_exposed_widen_consumes_credit :
  TSUL.remaining_changes
    (fst (TSU.update tt tt TBase.BoxW Low Mid Low))
    (snd (TSU.update tt tt TBase.BoxW Low Mid Low)) <
  TSUL.remaining_changes TBase.BoxW Low.
Proof. cbn. lia. Qed.
