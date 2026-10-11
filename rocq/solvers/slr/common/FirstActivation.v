From Stdlib Require Import Bool Lia Arith.PeanoNat.
From TcSolvers Require Export
  common.Interfaces
  solvers.slr.common.DiscoveryOrder
  solvers.slr.common.DiscoveryOrderLaws.

(** Dormant reads register dependencies before assigning the target a rank.
    When that target is eventually discovered, its fresh rank must lie above
    every rank which was already present. First-discovery ranking has this
    property; arbitrary stateless ranking does not. *)
Module Type DORMANT_DISCOVERY_ORDER_LAWS
  (V : VAR) (R : DISCOVERY_ORDER V).
  Parameter observe_fresh_above :
    forall order target next target_rank reader reader_rank,
      R.lookup order target = None ->
      R.observe order target = (next, target_rank) ->
      R.lookup order reader = Some reader_rank ->
      Nat.ltb reader_rank target_rank = true.
  Parameter observe_fresh_preserves_absent :
    forall order target next target_rank other,
      R.lookup order target = None ->
      R.observe order target = (next, target_rank) ->
      other <> target ->
      R.lookup order other = None ->
      R.lookup next other = None.
End DORMANT_DISCOVERY_ORDER_LAWS.

(** Canonical dense, append-only activation used by ranked second-paper
    solvers. A fresh variable is assigned the size of the existing order. *)
Module FirstActivation (V : VAR) := ListDiscoveryOrder V.

Module FirstActivationLaws (V : VAR).
  Include ListDiscoveryOrderLaws V.

  Lemma lookup_bound_any :
    forall order x rank,
      R.lookup order x = Some rank -> rank < R.size order.
  Proof.
    induction order as [|y older IH]; intros x rank Hlookup; cbn in *.
    - discriminate.
    - destruct (V.eq_dec x y) as [-> | Hxy].
      + inversion Hlookup. lia.
      + specialize (IH x rank Hlookup).
        change (rank < length older) in IH.
        change (rank < S (length older)). lia.
  Qed.

  Lemma observe_fresh_above :
    forall order target next target_rank reader reader_rank,
      R.lookup order target = None ->
      R.observe order target = (next, target_rank) ->
      R.lookup order reader = Some reader_rank ->
      Nat.ltb reader_rank target_rank = true.
  Proof.
    intros order target next target_rank reader reader_rank
      Htarget Hobserve Hreader.
    pose proof (@observe_fresh order target next target_rank Htarget Hobserve)
      as [Hrank _].
    rewrite Hrank. apply Nat.ltb_lt.
    exact (@lookup_bound_any order reader reader_rank Hreader).
  Qed.

  Lemma observe_fresh_preserves_absent :
    forall order target next target_rank other,
      R.lookup order target = None ->
      R.observe order target = (next, target_rank) ->
      other <> target ->
      R.lookup order other = None ->
      R.lookup next other = None.
  Proof.
    intros order target next target_rank other
      Htarget Hobserve Hneq Hother.
    unfold R.observe in Hobserve. rewrite Htarget in Hobserve.
    inversion Hobserve; subst. cbn.
    destruct (V.eq_dec other target); [contradiction |exact Hother].
  Qed.
End FirstActivationLaws.
