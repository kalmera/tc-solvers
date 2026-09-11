From Stdlib Require Import List Bool Arith Lia.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws.

Set Implicit Arguments.

Module Type DISCOVERY_SNAPSHOT (V : VAR).
  Parameter order : list V.t.
End DISCOVERY_SNAPSHOT.

Module Type VALID_DISCOVERY_SNAPSHOT
  (V : VAR) (Snapshot : DISCOVERY_SNAPSHOT V).
  Parameter valid : NoDup Snapshot.order.
End VALID_DISCOVERY_SNAPSHOT.

(** The functional form is useful while relating a stateful run to the
    immutable order obtained from its final discovery snapshot. *)
Module FrozenRelation (V : VAR) (Base : ORDER V).
  Module Ranking := ListDiscoveryOrder V.

  Definition lt (order : list V.t) (x y : V.t) : bool :=
    match Ranking.lookup order x, Ranking.lookup order y with
    | Some x_rank, Some y_rank => Nat.ltb x_rank y_rank
    | Some _, None => true
    | None, Some _ => false
    | None, None => Base.lt x y
    end.
End FrozenRelation.

(** Freeze observed ranks into a static order. Observed variables precede all
    unobserved variables; the supplied base order resolves pairs which were
    never observed. *)
Module FrozenOrder
  (V : VAR)
  (Base : ORDER V)
  (Snapshot : DISCOVERY_SNAPSHOT V).

  Module Ranking := ListDiscoveryOrder V.
  Module Relation := FrozenRelation V Base.

  Definition lt (x y : V.t) : bool :=
    Relation.lt Snapshot.order x y.
End FrozenOrder.

Module FrozenOrderLaws
  (V : VAR)
  (Base : ORDER V)
  (BaseLaws : ORDER_LAWS V Base)
  (Snapshot : DISCOVERY_SNAPSHOT V)
  (SnapshotLaws : VALID_DISCOVERY_SNAPSHOT V Snapshot).

  Module Order := FrozenOrder V Base Snapshot.
  Module Ranking := Order.Relation.Ranking.
  Module RankingLaws := ListDiscoveryOrderLaws V.

  Lemma observed_rank_injective :
    forall x y rank,
      Ranking.lookup Snapshot.order x = Some rank ->
      Ranking.lookup Snapshot.order y = Some rank ->
      x = y.
  Proof.
    intros. eapply RankingLaws.lookup_injective; eauto.
    exact SnapshotLaws.valid.
  Qed.

  Lemma lt_irrefl :
    forall x, Order.lt x x = false.
  Proof.
    intros x. unfold Order.lt, Order.Relation.lt.
    destruct (Ranking.lookup Snapshot.order x) as [rank |].
    - apply Nat.ltb_ge. lia.
    - apply BaseLaws.lt_irrefl.
  Qed.

  Lemma lt_trans :
    forall x y z,
      Order.lt x y = true ->
      Order.lt y z = true ->
      Order.lt x z = true.
  Proof.
    intros x y z Hxy Hyz. unfold Order.lt, Order.Relation.lt in *.
    destruct (Ranking.lookup Snapshot.order x) as [xr |];
    destruct (Ranking.lookup Snapshot.order y) as [yr |];
    destruct (Ranking.lookup Snapshot.order z) as [zr |];
      cbn in *; try discriminate; try reflexivity.
    - apply Nat.ltb_lt in Hxy. apply Nat.ltb_lt in Hyz.
      apply Nat.ltb_lt. lia.
    - exact (@BaseLaws.lt_trans x y z Hxy Hyz).
  Qed.

  Lemma lt_total :
    forall x y,
      x <> y ->
      Order.lt x y = true \/ Order.lt y x = true.
  Proof.
    intros x y Hneq. unfold Order.lt, Order.Relation.lt.
    destruct (Ranking.lookup Snapshot.order x) as [xr |] eqn:Hx;
    destruct (Ranking.lookup Snapshot.order y) as [yr |] eqn:Hy;
      cbn; try tauto.
    - assert (xr <> yr).
      { intros ->. apply Hneq.
        exact (@observed_rank_injective x y yr Hx Hy). }
      destruct (Nat.ltb xr yr) eqn:Hlt.
      + now left.
      + right. apply Nat.ltb_lt. apply Nat.ltb_ge in Hlt. lia.
    - exact (@BaseLaws.lt_total x y Hneq).
  Qed.

  Lemma lt_asymmetric :
    forall x y,
      Order.lt x y = true ->
      Order.lt y x = false.
  Proof.
    intros x y Hxy. unfold Order.lt, Order.Relation.lt in *.
    destruct (Ranking.lookup Snapshot.order x) as [xr |];
    destruct (Ranking.lookup Snapshot.order y) as [yr |];
      cbn in *; try discriminate; try reflexivity.
    - apply Nat.ltb_lt in Hxy. apply Nat.ltb_ge. lia.
    - now apply BaseLaws.lt_asymmetric.
  Qed.
End FrozenOrderLaws.

Module FrozenOrderLawsCheck
  (V : VAR)
  (Base : ORDER V)
  (BaseLaws : ORDER_LAWS V Base)
  (Snapshot : DISCOVERY_SNAPSHOT V)
  (SnapshotLaws : VALID_DISCOVERY_SNAPSHOT V Snapshot).
  Module Order := FrozenOrder V Base Snapshot.
  Module Laws <: ORDER_LAWS V Order :=
    FrozenOrderLaws V Base BaseLaws Snapshot SnapshotLaws.
End FrozenOrderLawsCheck.
