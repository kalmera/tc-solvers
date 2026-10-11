From Stdlib Require Import List Lia Sorting.Permutation.
From TcSolvers Require Export solvers.slr.common.tests.SideUpdateFixture.
From TcSolvers Require Import common.Collections common.instances.SolverBundles
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces.

Import ListNotations.

(* Alternative finite-domain bundles shared by the solver theorem clients. *)
Module ToySet := ListSet TV.
Module ToyMap := AssocMap TV.

Module ToySetLaws <: SET_LAWS TV ToySet.
  Lemma mem_spec : forall x xs,
    ToySet.mem x xs = true <-> List.In x (ToySet.elements xs).
  Proof.
    intros x xs. unfold ToySet.mem, ToySet.elements.
    destruct (List.in_dec TV.eq_dec x xs); split; auto; discriminate.
  Qed.

  Lemma empty_spec : forall x, ToySet.mem x ToySet.empty = false.
  Proof. intros []; reflexivity. Qed.

  Lemma add_spec : forall x y xs,
    ToySet.mem x (ToySet.add y xs) = true <->
    x = y \/ ToySet.mem x xs = true.
  Proof.
    intros [] [] xs. unfold ToySet.add, ToySet.mem.
    destruct (List.in_dec TV.eq_dec tt xs) as [Hin | Hnot].
    - destruct (List.in_dec TV.eq_dec tt xs) as [_ | Habsurd];
        [split; intro; auto |contradiction].
    - destruct (List.in_dec TV.eq_dec tt (tt :: xs)) as [_ | Habsurd].
      + split; intro; [now left |reflexivity].
      + exfalso. apply Habsurd. now left.
  Qed.
End ToySetLaws.

Module ToyMapLaws <: MAP_LAWS TV ToyMap.
  Lemma values_empty : forall A, ToyMap.values (ToyMap.empty A) = nil.
  Proof. reflexivity. Qed.

  Lemma lookup_empty : forall A x,
    ToyMap.lookup (ToyMap.empty A) x = None.
  Proof. reflexivity. Qed.

  Lemma lookup_update_same : forall A (m : ToyMap.t A) x value,
    ToyMap.lookup (ToyMap.update m x value) x = Some value.
  Proof. intros A m [] value. destruct m as [|[[] old] rest]; reflexivity. Qed.

  Lemma lookup_update_other : forall A (m : ToyMap.t A) x y value,
    x <> y -> ToyMap.lookup (ToyMap.update m y value) x = ToyMap.lookup m x.
  Proof. intros A m [] [] value Hneq. contradiction. Qed.

  Lemma lookup_values : forall A (m : ToyMap.t A) x value,
    ToyMap.lookup m x = Some value -> List.In value (ToyMap.values m).
  Proof.
    intros A m [] value Hlookup. destruct m as [|[[] old] rest]; cbn in *.
    - discriminate.
    - inversion Hlookup. now left.
  Qed.

  Lemma values_update : forall A (m : ToyMap.t A) x value,
    exists rest,
      Permutation (ToyMap.values (ToyMap.update m x value))
        (value :: rest) /\
      match ToyMap.lookup m x with
      | Some previous =>
          Permutation (ToyMap.values m) (previous :: rest)
      | None => Permutation (ToyMap.values m) rest
      end.
  Proof.
    intros A m [] value. destruct m as [|[[] old] tail].
    - exists []. split; apply Permutation_refl.
    - exists (ToyMap.values tail). split; apply Permutation_refl.
  Qed.
End ToyMapLaws.

Module ToyOUL := SideUpdate.OrdinaryUpdateTerminationAdapter
  TV TD TBase TBaseLaws.
Module ToyRestartingSUL :=
  ReluctantRestartingInterfaces.ReluctantRestartingSideUpdateTerminationLaws
  TV TD TBase TDLaws TBaseLaws TCovered.
Module ToyParameters (F : RESTARTING_FEATURES) <: TOTAL_CORRECTNESS_PARAMETERS.
  Module V := TV.
  Module D := TD.
  Module U := TBase.
  Module SU := TSU.
  Module S := ToySet.
  Module M := ToyMap.
  Module Features := F.
  Module DL := TDLaws.
  Module OUL := ToyOUL.
  Module SUL := ToyRestartingSUL.
  Module SL := ToySetLaws.
  Module ML := ToyMapLaws.
End ToyParameters.

Module ToyFiniteHeight <: FINITE_HEIGHT_LAWS TD TDLaws.
  Definition equivalent (left right : TD.t) : Prop :=
    TD.leq left right = true /\ TD.leq right left = true.

  Definition remaining_height (value : TD.t) : nat :=
    match value with Low => 2 | Mid => 1 | High => 0 end.

  Lemma remaining_height_extensional : forall left right,
    equivalent left right ->
    remaining_height left = remaining_height right.
  Proof.
    intros left right [Hleft Hright].
    now destruct left, right.
  Qed.

  Lemma strict_ascent_decreases : forall lower upper,
    TD.leq lower upper = true ->
    ~ equivalent upper lower ->
    remaining_height upper < remaining_height lower.
  Proof.
    intros lower upper Hle Hstrict.
    destruct lower, upper; cbn in *; try discriminate; try lia;
      exfalso; apply Hstrict; split; reflexivity.
  Qed.
End ToyFiniteHeight.

Module ToyLeastParameters (F : RESTARTING_FEATURES) :=
  FiniteHeightParameters TV TD ToySet ToyMap F
    TDLaws ToyFiniteHeight ToySetLaws ToyMapLaws.
