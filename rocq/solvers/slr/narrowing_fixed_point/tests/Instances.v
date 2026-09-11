From Stdlib Require Import List Bool Lia.
From TcSolvers Require Import common.Assumptions common.BoxUpdate
  solvers.slr.narrowing_fixed_point.tests.Chain
  solvers.slr.narrowing_fixed_point.proofs.FixedPoint
  solvers.slr.narrowing_fixed_point.Theorems.

Import ListNotations.
Set Implicit Arguments.

(** Any widening on the concrete chain respects equivalence. *)
Module ChainCongruence (WN : WIDEN_NARROW Chain.D)
  <: WIDEN_CONGRUENCE Chain.D WN.
  Lemma widen_congruent : forall old input input',
    Chain.D.leq input input' = true /\ Chain.D.leq input' input = true ->
    Chain.D.leq (WN.widen old input) (WN.widen old input') = true /\
    Chain.D.leq (WN.widen old input') (WN.widen old input) = true.
  Proof.
    intros old input input' H. apply Chain.UL.equivalent_eq in H.
    subst. split; apply Chain.DL.leq_refl.
  Qed.
End ChainCongruence.

Module ConcreteDescent.
  Module V := Chain.V.
  Module D := Chain.D.
  Module DL := Chain.DL.
  Module WN := Chain.WN.
  Module WNL := Chain.WNL.
  Module WC := ChainCongruence WN.
  Module Fixed := Theorems.Make V D WN.
  Module U := Fixed.U.
  Module UL <: UPDATE_LAWS V D U.
    Definition equivalent (x y : D.t) : Prop :=
      D.leq x y = true /\ D.leq y x = true.

    Lemma equivalent_eq : forall x y, equivalent x y -> x = y.
    Proof. destruct x, y; unfold equivalent; cbn; intuition discriminate. Qed.

    Lemma equivalent_refl : forall x, equivalent x x.
    Proof. intro x. split; apply DL.leq_refl. Qed.

    Lemma update_sound : forall is_side variable phase old input,
      D.leq input
        (snd (U.update is_side variable phase old input)) = true.
    Proof. intros. destruct phase, old, input; reflexivity. Qed.

    Lemma update_extensional : forall is_side variable phase old old' input input',
      equivalent old old' -> equivalent input input' ->
      equivalent
        (snd (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old' input')).
    Proof.
      intros is_side variable phase old old' input input' Hold Hinput.
      apply equivalent_eq in Hold, Hinput. subst. apply equivalent_refl.
    Qed.

    Lemma update_stutter_closed : forall is_side variable phase old input,
      equivalent (snd (U.update is_side variable phase old input)) old ->
      forall old' input', equivalent old' old -> equivalent input' input ->
      equivalent
        (snd (U.update is_side variable
          (fst (U.update is_side variable phase old input)) old' input'))
        old'.
    Proof.
      intros is_side variable phase old input Hstutter old' input' Hold Hinput.
      apply equivalent_eq in Hold, Hinput. subst old' input'.
      destruct phase, old, input; cbn in *;
        try exact Hstutter;
        unfold equivalent in *; cbn in *; intuition discriminate.
    Qed.

    Definition remaining_changes (phase : U.phase) (old : D.t) : nat :=
      match phase with
      | U.BoxW => 10 - D.rank old
      | U.BoxN => S (D.rank old)
      | U.Widen => if D.leq D.Top old then 0 else 1
      end.

    Lemma remaining_changes_extensional : forall phase old old',
      equivalent old old' ->
      remaining_changes phase old = remaining_changes phase old'.
    Proof. intros phase old old' H. apply equivalent_eq in H. now subst. Qed.

    Lemma remaining_changes_nonincreasing : forall is_side variable phase old input,
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <=
      remaining_changes phase old.
    Proof. intros. destruct phase, old, input; cbn; lia. Qed.

    Lemma update_change_consumes : forall is_side variable phase old input,
      ~ equivalent
          (snd (U.update is_side variable phase old input)) old ->
      remaining_changes
        (fst (U.update is_side variable phase old input))
        (snd (U.update is_side variable phase old input)) <
      remaining_changes phase old.
    Proof.
      intros is_side variable phase old input Hchange.
      destruct phase, old, input; cbn in *;
        try lia; exfalso; apply Hchange; split; reflexivity.
    Qed.

  End UL.
  Module FixedLaws := Fixed.WithLaws DL WNL WC UL.
  Module FixedCells := FixedLaws.WithCollections Chain.S Chain.M
    Base.AllEnabledFeatures Chain.SL Chain.ML.
  Definition total_correct_and_fixed := @FixedCells.total_correct_and_fixed.
  Import FixedCells.
  Definition fanout owner := if V.eq_dec owner 0 then
    R.ConstraintSystem.Side 1 D.One (R.ConstraintSystem.Side 2 D.Two
      (R.ConstraintSystem.Side 3 D.Three (R.ConstraintSystem.Ret D.One)))
    else R.ConstraintSystem.Ret D.Bot.
  Definition finite_fanout : Sem.finite_system fanout [0].
  Proof.
    refine (@Sem.Build_finite_system fanout [0] [0;1;2;3] _ _ _).
    - repeat constructor;cbn;intuition discriminate.
    - intros owner [->|H];[now left |contradiction].
    - intros owner Hin. unfold fanout. destruct (V.eq_dec owner 0).
      + constructor;[cbn;auto |]. constructor;[cbn;auto |].
        constructor;[cbn;auto |constructor].
      + constructor.
  Defined.
  Lemma fanout_observations owner lower upper :
    Sem.rhs_observes (fanout owner) lower ->
    Sem.rhs_observes (fanout owner) upper -> lower=upper.
  Proof.
    unfold fanout. destruct (V.eq_dec owner 0);intros Hl Hu.
    all: repeat match goal with
      H : Sem.rhs_observes (R.ConstraintSystem.Side _ _ _) _ |- _ => inversion H;subst;clear H
    | H : Sem.rhs_observes (R.ConstraintSystem.Ret _) _ |- _ => inversion H;subst;clear H
    end;reflexivity.
  Qed.
  Lemma fanout_monotone : FixedCells.monotonic_system fanout.
  Proof.
    intro owner. split;intros lower upper Hl Hu Hreads;
      pose proof (@fanout_observations owner lower upper Hl Hu) as Heq;subst upper.
    - intros target Hin;exact Hin.
    - constructor;[apply DL.leq_refl | |intros target Hin;exact Hin].
      intros target value Hin. exists value. split;[exact Hin |apply DL.leq_refl].
  Qed.
  Definition fanout_total_correct_and_fixed :=
    @FixedCells.total_correct_and_fixed fanout [0] finite_fanout fanout_monotone.
End ConcreteDescent.

Module Fanout.
  Import Chain ConcreteDescent.FixedCells.
  Definition tf := ConcreteDescent.fanout.
  Definition final := R.cfg_state (N.run_fuel 500 tf (R.initial_config [0])).

  Example solved : N.solve_fuel 500 tf [0] = Some final /\
    R.sigma_value final 0 = D.One /\ R.sigma_value final 1 = D.One /\
    R.sigma_value final 2 = D.Two /\ R.sigma_value final 3 = D.Three.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example insufficient_fuel : N.solve_fuel 0 tf [0] = None.
  Proof. reflexivity. Qed.

  Example all_owners_fixed : forall owner, In owner [0;1;2;3] ->
    WN.narrow (R.sigma_value final owner)
      (D.join (if Nat.eqb owner 0 then D.One else D.Bot)
        (R.aggregate final owner)) = R.sigma_value final owner.
  Proof.
    intros owner [<-|[<-|[<-|[<-|H]]]]; [| | | |contradiction]; vm_compute; reflexivity.
  Qed.

  Definition commit_replay := @N.actual_commit_replay.
  Definition reset_credit := @N.higher_reset_preserves_credit.
  Definition successful_correct := @ConcreteDescent.FixedCells.Internal.Replay.successful_run_correct.
End Fanout.

Print Assumptions ConcreteDescent.total_correct_and_fixed.
Print Assumptions ConcreteDescent.fanout_total_correct_and_fixed.
