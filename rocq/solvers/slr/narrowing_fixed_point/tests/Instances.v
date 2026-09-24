From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain
  common.Assumptions common.BoxUpdate
  solvers.slr.narrowing_fixed_point.Theorems.

Import ListNotations.
Set Implicit Arguments.

Module ConcreteDescent.
  Module V := Chain.V.
  Module D := Chain.D.
  Module DL := Chain.DL.
  Module WN := Chain.WN.
  Module WNL := Chain.WNL.
  Module WS := Chain.WS.
  Module Fixed := Theorems.Make V D WN.
  Module U := Fixed.U.
  Module UL := Chain.UpdateLaws U.
  Module FixedLaws := Fixed.WithLaws DL WNL WS UL.
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

(* Print Assumptions ConcreteDescent.fanout_total_correct_and_fixed. *)
