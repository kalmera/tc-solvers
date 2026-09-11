From Stdlib Require Import List Lia Arith.PeanoNat.
From TcSolvers Require Export solvers.slr.common.DiscoveryOrder.

Import ListNotations.
Set Implicit Arguments.

(** The common proof contract deliberately omits density and the policy used
    to choose a fresh numeric rank.  It says only that observation grows a
    stable, injective partial ranking.  Both first-discovery ranks and a
    stateless fixed-rank policy can implement this contract. *)
Module Type STABLE_DISCOVERY_ORDER_LAWS
  (V : VAR) (R : DISCOVERY_ORDER V).

  Parameter valid : R.t -> Prop.

  Parameter empty_valid : valid R.empty.
  Parameter empty_lookup : forall x, R.lookup R.empty x = None.

  Parameter observe_valid :
    forall order x next rank,
      valid order ->
      R.observe order x = (next, rank) ->
      valid next.

  Parameter observe_lookup :
    forall order x next rank,
      R.observe order x = (next, rank) ->
      R.lookup next x = Some rank.

  Parameter observe_existing :
    forall order x rank,
      R.lookup order x = Some rank ->
      R.observe order x = (order, rank).

  Parameter observe_preserves :
    forall order x next rank y old_rank,
      R.observe order x = (next, rank) ->
      R.lookup order y = Some old_rank ->
      R.lookup next y = Some old_rank.

  Parameter lookup_injective :
    forall order x y rank,
      valid order ->
      R.lookup order x = Some rank ->
      R.lookup order y = Some rank ->
      x = y.
End STABLE_DISCOVERY_ORDER_LAWS.

Module Type STATELESS_RANK_LAWS
  (V : VAR) (Fixed : STATELESS_RANK V).
  Parameter rank_injective :
    forall x y, Fixed.rank x = Fixed.rank y -> x = y.
End STATELESS_RANK_LAWS.

(** Constructive finite-range consequence required by the rank-tree proof.
    [generated support order] means that [order] was obtained from [empty] by
    observing variables in [support].  The bound concerns numeric
    representation only; it does not constrain where a fresh rank is placed
    relative to existing ranks. *)
Module Type FINITE_DISCOVERY_ORDER_LAWS
  (V : VAR)
  (R : DISCOVERY_ORDER V)
  (Laws : STABLE_DISCOVERY_ORDER_LAWS V R).

  Parameter generated : list V.t -> R.t -> Prop.
  Parameter bound : list V.t -> nat.

  Parameter generated_empty :
    forall support, generated support R.empty.

  Parameter generated_observe :
    forall support order x next rank,
      generated support order ->
      List.In x support ->
      R.observe order x = (next, rank) ->
      generated support next.

  Parameter generated_lookup_bound :
    forall support order x rank,
      Laws.valid order ->
      generated support order ->
      R.lookup order x = Some rank ->
      rank < bound support.
End FINITE_DISCOVERY_ORDER_LAWS.

(** Proof contract for discovery-order implementations. *)
Module Type DISCOVERY_ORDER_LAWS
  (V : VAR) (R : DISCOVERY_ORDER V).

  Parameter valid : R.t -> Prop.

  Parameter empty_valid : valid R.empty.
  Parameter empty_size : R.size R.empty = 0.
  Parameter empty_lookup : forall x, R.lookup R.empty x = None.

  Parameter observe_valid :
    forall order x next rank,
      valid order ->
      R.observe order x = (next, rank) ->
      valid next.

  Parameter observe_lookup :
    forall order x next rank,
      R.observe order x = (next, rank) ->
      R.lookup next x = Some rank.

  Parameter observe_existing :
    forall order x rank,
      R.lookup order x = Some rank ->
      R.observe order x = (order, rank).

  Parameter observe_fresh :
    forall order x next rank,
      R.lookup order x = None ->
      R.observe order x = (next, rank) ->
      rank = R.size order /\
      R.size next = S (R.size order).

  Parameter observe_preserves :
    forall order x next rank y old_rank,
      R.observe order x = (next, rank) ->
      R.lookup order y = Some old_rank ->
      R.lookup next y = Some old_rank.

  Parameter lookup_bound :
    forall order x rank,
      valid order ->
      R.lookup order x = Some rank ->
      rank < R.size order.

  Parameter lookup_injective :
    forall order x y rank,
      valid order ->
      R.lookup order x = Some rank ->
      R.lookup order y = Some rank ->
      x = y.

  Parameter ranks_dense :
    forall order rank,
      valid order ->
      rank < R.size order ->
      exists x, R.lookup order x = Some rank.
End DISCOVERY_ORDER_LAWS.

Module ListDiscoveryOrderLaws (V : VAR).

  Module R := ListDiscoveryOrder V.

  Definition valid (order : R.t) : Prop := NoDup order.

  Lemma empty_valid : valid R.empty.
  Proof. constructor. Qed.

  Lemma empty_size : R.size R.empty = 0.
  Proof. reflexivity. Qed.

  Lemma empty_lookup : forall x, R.lookup R.empty x = None.
  Proof. reflexivity. Qed.

  Lemma lookup_none_not_in :
    forall order x,
      R.lookup order x = None <-> ~ List.In x order.
  Proof.
    induction order as [|y older IH]; intros x; cbn.
    - tauto.
    - destruct (V.eq_dec x y) as [-> | Hxy].
      + split.
        * discriminate.
        * intros Hnot. exfalso. apply Hnot. now left.
      + rewrite IH. split.
        * intros Hnot [Heq | Hin]; [congruence | contradiction].
        * intros Hnot Hin. apply Hnot. now right.
  Qed.

  Lemma lookup_some_in :
    forall order x rank,
      R.lookup order x = Some rank ->
      List.In x order.
  Proof.
    induction order as [|y older IH]; intros x rank Hlookup; cbn in Hlookup.
    - discriminate.
    - destruct (V.eq_dec x y) as [-> | Hxy].
      + left. reflexivity.
      + right. exact (IH x rank Hlookup).
  Qed.

  Lemma observe_valid :
    forall order x next rank,
      valid order ->
      R.observe order x = (next, rank) ->
      valid next.
  Proof.
    intros order x next rank Hvalid Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.lookup order x) as [old |] eqn:Hlookup.
    - inversion Hobserve; subst. exact Hvalid.
    - inversion Hobserve; subst. constructor; [|exact Hvalid].
      now apply lookup_none_not_in.
  Qed.

  Lemma observe_lookup :
    forall order x next rank,
      R.observe order x = (next, rank) ->
      R.lookup next x = Some rank.
  Proof.
    intros order x next rank Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.lookup order x) as [old |] eqn:Hlookup.
    - inversion Hobserve; subst. exact Hlookup.
    - inversion Hobserve; subst. cbn.
      destruct (V.eq_dec x x); [reflexivity | contradiction].
  Qed.

  Lemma observe_existing :
    forall order x rank,
      R.lookup order x = Some rank ->
      R.observe order x = (order, rank).
  Proof.
    intros order x rank Hlookup. unfold R.observe. now rewrite Hlookup.
  Qed.

  Lemma observe_fresh :
    forall order x next rank,
      R.lookup order x = None ->
      R.observe order x = (next, rank) ->
      rank = R.size order /\
      R.size next = S (R.size order).
  Proof.
    intros order x next rank Hlookup Hobserve.
    unfold R.observe in Hobserve. rewrite Hlookup in Hobserve.
    inversion Hobserve; subst. split; reflexivity.
  Qed.

  Lemma observe_preserves :
    forall order x next rank y old_rank,
      R.observe order x = (next, rank) ->
      R.lookup order y = Some old_rank ->
      R.lookup next y = Some old_rank.
  Proof.
    intros order x next rank y old_rank Hobserve Hold.
    unfold R.observe in Hobserve.
    destruct (R.lookup order x) as [existing |] eqn:Hx.
    - inversion Hobserve; subst. exact Hold.
    - inversion Hobserve; subst. cbn.
      destruct (V.eq_dec y x) as [-> | Hyx].
      + rewrite Hx in Hold. discriminate.
      + exact Hold.
  Qed.

  Lemma lookup_bound :
    forall order x rank,
      valid order ->
      R.lookup order x = Some rank ->
      rank < R.size order.
  Proof.
    induction order as [|y older IH]; intros x rank Hvalid Hlookup; cbn in *.
    - discriminate.
    - inversion Hvalid as [|? ? Hnot Hvalid']; subst.
      destruct (V.eq_dec x y) as [-> | Hxy].
      + inversion Hlookup; lia.
      + pose proof (IH x rank Hvalid' Hlookup) as Hbound.
        change (rank < length older) in Hbound. lia.
  Qed.

  Lemma lookup_injective :
    forall order x y rank,
      valid order ->
      R.lookup order x = Some rank ->
      R.lookup order y = Some rank ->
      x = y.
  Proof.
    induction order as [|z older IH]; intros x y rank Hvalid Hx Hy; cbn in *.
    - discriminate.
    - inversion Hvalid as [|? ? Hnot Hvalid']; subst.
      destruct (V.eq_dec x z) as [-> | Hxz];
      destruct (V.eq_dec y z) as [-> | Hyz]; try reflexivity.
      + inversion Hx; subst.
        pose proof (@lookup_bound older y (length older) Hvalid' Hy)
          as Hbound.
        change (length older < length older) in Hbound.
        lia.
      + inversion Hy; subst.
        pose proof (@lookup_bound older x (length older) Hvalid' Hx)
          as Hbound.
        change (length older < length older) in Hbound.
        lia.
      + exact (IH x y rank Hvalid' Hx Hy).
  Qed.

  Lemma lookup_rank_length :
    forall older x,
      NoDup older ->
      R.lookup (x :: older) x = Some (length older).
  Proof.
    intros older x _. cbn.
    destruct (V.eq_dec x x); [reflexivity | contradiction].
  Qed.

  Lemma ranks_dense :
    forall order rank,
      valid order ->
      rank < R.size order ->
      exists x, R.lookup order x = Some rank.
  Proof.
    induction order as [|x older IH]; intros rank Hvalid Hbound; cbn in *.
    - lia.
    - inversion Hvalid as [|? ? Hnot Hvalid']; subst.
      destruct (PeanoNat.Nat.eq_dec rank (length older)) as [-> | Hne].
      + exists x. now apply lookup_rank_length.
      + assert (rank < length older) as Hlt by lia.
        destruct (IH rank Hvalid' Hlt) as [y Hy].
        exists y. cbn.
        destruct (V.eq_dec y x) as [-> | Hyx].
        * exfalso. apply Hnot. exact (@lookup_some_in older x rank Hy).
        * exact Hy.
  Qed.
End ListDiscoveryOrderLaws.

Module ListDiscoveryOrderLawsCheck (V : VAR).
  Module R := ListDiscoveryOrder V.
  Module Laws <: DISCOVERY_ORDER_LAWS V R := ListDiscoveryOrderLaws V.
End ListDiscoveryOrderLawsCheck.

Module ListStableDiscoveryOrderLawsCheck (V : VAR).
  Module R := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    ListDiscoveryOrderLaws V.
End ListStableDiscoveryOrderLawsCheck.

Module ListFiniteDiscoveryOrderLaws (V : VAR).
  Module R := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    ListDiscoveryOrderLaws V.
  Module FullLaws := ListDiscoveryOrderLaws V.

  Definition generated (support order : list V.t) : Prop :=
    forall x, List.In x order -> List.In x support.

  Definition bound (support : list V.t) : nat := length support.

  Lemma generated_empty : forall support, generated support R.empty.
  Proof. intros support x Hin. inversion Hin. Qed.

  Lemma generated_observe :
    forall support order x next rank,
      generated support order ->
      List.In x support ->
      R.observe order x = (next, rank) ->
      generated support next.
  Proof.
    intros support order x next rank Hgenerated Hx Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.lookup order x) as [old |] eqn:Hlookup.
    - inversion Hobserve; subst. exact Hgenerated.
    - inversion Hobserve; subst. intros y [-> | Hy]; auto.
  Qed.

  Lemma generated_lookup_bound :
    forall support order x rank,
      Laws.valid order ->
      generated support order ->
      R.lookup order x = Some rank ->
      rank < bound support.
  Proof.
    intros support order x rank Hvalid Hgenerated Hlookup.
    pose proof (@FullLaws.lookup_bound order x rank Hvalid Hlookup) as Hrank.
    pose proof (NoDup_incl_length Hvalid Hgenerated) as Hlength.
    change (rank < length order) in Hrank.
    unfold bound. lia.
  Qed.
End ListFiniteDiscoveryOrderLaws.

Module ListFiniteDiscoveryOrderLawsCheck (V : VAR).
  Module R := ListDiscoveryOrder V.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    ListDiscoveryOrderLaws V.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V R Laws :=
    ListFiniteDiscoveryOrderLaws V.
End ListFiniteDiscoveryOrderLawsCheck.

(** A stateless injective numbering is a stable partial ranking when its
    values are revealed on demand. *)
Module FixedRankDiscoveryOrderLaws
  (V : VAR)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed).

  Module R := FixedRankDiscoveryOrder V Fixed.

  Definition valid (seen : R.t) : Prop := NoDup seen.

  Lemma lookup_none_not_in :
    forall seen x, R.lookup seen x = None <-> ~ List.In x seen.
  Proof.
    induction seen as [|y rest IH]; intros x; cbn.
    - tauto.
    - destruct (V.eq_dec x y) as [-> | Hxy].
      + split.
        * discriminate.
        * intros Hnot. exfalso. apply Hnot. left. reflexivity.
      + rewrite IH. split.
        * intros Hnot [-> | Hin]; [contradiction |auto].
        * intros Hnot Hin. apply Hnot. now right.
  Qed.

  Lemma lookup_some_in :
    forall seen x rank,
      R.lookup seen x = Some rank -> List.In x seen.
  Proof.
    induction seen as [|y rest IH]; intros x rank Hlookup; cbn in Hlookup.
    - discriminate.
    - destruct (V.eq_dec x y) as [-> | Hxy].
      + left. reflexivity.
      + right. exact (IH x rank Hlookup).
  Qed.

  Lemma empty_valid : valid R.empty.
  Proof. constructor. Qed.

  Lemma empty_lookup : forall x, R.lookup R.empty x = None.
  Proof. reflexivity. Qed.

  Lemma observe_valid :
    forall seen x next rank,
      valid seen -> R.observe seen x = (next, rank) -> valid next.
  Proof.
    intros seen x next rank Hvalid Hobserve. unfold R.observe in Hobserve.
    destruct (R.lookup seen x) as [old |] eqn:Hlookup.
    - now inversion Hobserve; subst.
    - inversion Hobserve; subst. constructor; [|exact Hvalid].
      now apply lookup_none_not_in.
  Qed.

  Lemma observe_lookup :
    forall seen x next rank,
      R.observe seen x = (next, rank) ->
      R.lookup next x = Some rank.
  Proof.
    intros seen x next rank Hobserve. unfold R.observe in Hobserve.
    destruct (R.lookup seen x) as [old |] eqn:Hlookup.
    - inversion Hobserve; subst. exact Hlookup.
    - inversion Hobserve; subst. cbn.
      destruct (V.eq_dec x x); [reflexivity |contradiction].
  Qed.

  Lemma observe_existing :
    forall seen x rank,
      R.lookup seen x = Some rank -> R.observe seen x = (seen, rank).
  Proof. intros seen x rank Hlookup. unfold R.observe. now rewrite Hlookup. Qed.

  Lemma observe_preserves :
    forall seen x next rank y old_rank,
      R.observe seen x = (next, rank) ->
      R.lookup seen y = Some old_rank ->
      R.lookup next y = Some old_rank.
  Proof.
    intros seen x next rank y old_rank Hobserve Hold.
    unfold R.observe in Hobserve.
    destruct (R.lookup seen x) as [existing |] eqn:Hx.
    - inversion Hobserve; subst. exact Hold.
    - inversion Hobserve; subst. cbn.
      destruct (V.eq_dec y x) as [-> | Hyx].
      + rewrite Hx in Hold. discriminate.
      + exact Hold.
  Qed.

  Lemma lookup_value :
    forall seen x rank,
      R.lookup seen x = Some rank -> rank = Fixed.rank x.
  Proof.
    induction seen as [|y rest IH]; intros x rank Hlookup; cbn in Hlookup.
    - discriminate.
    - destruct (V.eq_dec x y); [now inversion Hlookup |now eapply IH].
  Qed.

  Lemma lookup_injective :
    forall seen x y rank,
      valid seen ->
      R.lookup seen x = Some rank ->
      R.lookup seen y = Some rank -> x = y.
  Proof.
    intros seen x y rank _ Hx Hy.
    apply FixedLaws.rank_injective.
    rewrite <- (@lookup_value seen x rank Hx).
    now rewrite <- (@lookup_value seen y rank Hy).
  Qed.
End FixedRankDiscoveryOrderLaws.

Module FixedRankFiniteDiscoveryOrderLaws
  (V : VAR)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed).

  Module R := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module FullLaws := FixedRankDiscoveryOrderLaws V Fixed FixedLaws.

  Definition generated (support seen : list V.t) : Prop :=
    forall x, List.In x seen -> List.In x support.

  Definition bound (support : list V.t) : nat :=
    S (fold_right Nat.max 0 (map Fixed.rank support)).

  Lemma generated_empty : forall support, generated support R.empty.
  Proof. intros support x Hin. inversion Hin. Qed.

  Lemma generated_observe :
    forall support seen x next rank,
      generated support seen ->
      List.In x support ->
      R.observe seen x = (next, rank) ->
      generated support next.
  Proof.
    intros support seen x next rank Hgenerated Hx Hobserve.
    unfold R.observe in Hobserve.
    destruct (R.lookup seen x) as [old |] eqn:Hlookup.
    - inversion Hobserve; subst. exact Hgenerated.
    - inversion Hobserve; subst. intros y [-> | Hy]; auto.
  Qed.

  Lemma rank_le_fold_max :
    forall support x,
      List.In x support ->
      Fixed.rank x <= fold_right Nat.max 0 (map Fixed.rank support).
  Proof.
    induction support as [|y rest IH]; intros x Hin; [contradiction |].
    cbn in Hin |- *. destruct Hin as [-> | Hin].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [exact (IH x Hin) |apply Nat.le_max_r].
  Qed.

  Lemma generated_lookup_bound :
    forall support seen x rank,
      Laws.valid seen ->
      generated support seen ->
      R.lookup seen x = Some rank ->
      rank < bound support.
  Proof.
    intros support seen x rank _ Hgenerated Hlookup.
    pose proof (@FullLaws.lookup_some_in seen x rank Hlookup) as Hin.
    pose proof (@FullLaws.lookup_value seen x rank Hlookup) as ->.
    unfold bound.
    pose proof (@rank_le_fold_max support x (Hgenerated x Hin)). lia.
  Qed.
End FixedRankFiniteDiscoveryOrderLaws.

Module FixedRankDiscoveryOrderLawsCheck
  (V : VAR)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed).
  Module R := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
End FixedRankDiscoveryOrderLawsCheck.

Module FixedRankFiniteDiscoveryOrderLawsCheck
  (V : VAR)
  (Fixed : STATELESS_RANK V)
  (FixedLaws : STATELESS_RANK_LAWS V Fixed).
  Module R := FixedRankDiscoveryOrder V Fixed.
  Module Laws <: STABLE_DISCOVERY_ORDER_LAWS V R :=
    FixedRankDiscoveryOrderLaws V Fixed FixedLaws.
  Module Finite <: FINITE_DISCOVERY_ORDER_LAWS V R Laws :=
    FixedRankFiniteDiscoveryOrderLaws V Fixed FixedLaws.
End FixedRankFiniteDiscoveryOrderLawsCheck.
