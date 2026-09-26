From Stdlib Require Import List.
From TcSolvers Require Import common.FiniteHeight
  solvers.slr.narrowing_fixed_point.NarrowingFixedPoint
  solvers.slr.narrowing_fixed_point.tests.Chain.
Import ListNotations.

Module E := Chain.
(** Value idempotency does not require phase idempotency. *)
Example replay_can_change_phase :
  E.U.update false 0 E.U.BoxW E.D.Bot E.D.One = (E.U.BoxW, E.D.Top) /\
  E.U.update false 0 E.U.BoxW E.D.Top E.D.One = (E.U.BoxN, E.D.Top).
Proof. split; reflexivity. Qed.

Module Optimized := NarrowingFixedPoint.Make E.V E.D E.U E.S E.M
  Base.AllEnabledFeatures E.DL E.UL E.SL E.ML.


Module After.
  Module N := Optimized.
  Module R := N.R.
  Definition tf (owner : E.V.t) : R.ConstraintSystem.rhs :=
    if E.V.eq_dec owner 0 then
      R.ConstraintSystem.Get 1 (fun _ => R.ConstraintSystem.Ret E.D.One)
    else R.ConstraintSystem.Get 0 (fun _ => R.ConstraintSystem.Ret E.D.Bot).
  Definition final := R.cfg_state (N.run_fuel 200 tf (R.initial_config [0])).
  Fixpoint completed_owners fuel (c : R.config) : list E.V.t :=
    match fuel with
    | 0 => []
    | S rest =>
        let current := match R.cfg_control c with
          R.RunRhs fr (R.ConstraintSystem.Ret _) _ => [R.frame_owner fr] | _ => [] end in
        match N.next_config tf c with
        | Some next => current ++ completed_owners rest next | None => current end
    end.
End After.

Example terminates : Optimized.solve_fuel 200 After.tf [0] = Some After.final.
Proof. vm_compute. reflexivity. Qed.

(** No synthetic fourth evaluation of owner 0. *)
Example completed_owners :
  After.completed_owners 200 (After.R.initial_config [0]) = [1;0;1].
Proof. vm_compute. reflexivity. Qed.

Module SelfDependency.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module N := NarrowingFixedPoint.Make E.V E.D U E.S E.M
    Base.AllEnabledFeatures E.DL UL E.SL E.ML.
  Module R := N.R.
  Definition successor value := match value with
    E.D.Bot => E.D.One | E.D.One => E.D.Two | E.D.Two => E.D.Three
    | E.D.Three | E.D.Top => E.D.Top end.
  Definition tf (_owner : E.V.t) : R.ConstraintSystem.rhs :=
    R.ConstraintSystem.Get 0 (fun value => R.ConstraintSystem.Ret (successor value)).
  Example idempotent : forall owner phase old input,
    snd (U.update false owner (fst (U.update false owner phase old input))
      (snd (U.update false owner phase old input)) input) =
    snd (U.update false owner phase old input).
  Proof. intros owner phase old input; destruct old, input; reflexivity. Qed.
  Example monotone : forall old new,
    E.D.leq old new = true -> E.D.leq (successor old) (successor new) = true.
  Proof. destruct old, new; cbn; congruence. Qed.
  Definition final := R.cfg_state (N.run_fuel 200 tf (R.initial_config [0])).
  Example retained_self_wakes : N.solve_fuel 200 tf [0] = Some final /\
    R.sigma_value final 0 = E.D.Top.
  Proof. vm_compute. split; reflexivity. Qed.
End SelfDependency.

Module Fanout.
  Module N := Optimized.
  Module R := N.R.
  Definition tf owner := if E.V.eq_dec owner 0 then
    R.ConstraintSystem.Side 1 E.D.One (R.ConstraintSystem.Side 2 E.D.Two
      (R.ConstraintSystem.Side 3 E.D.Three (R.ConstraintSystem.Ret E.D.One)))
    else R.ConstraintSystem.Ret E.D.Bot.
  Definition final := R.cfg_state (N.run_fuel 500 tf (R.initial_config [0])).
  Example solved : N.solve_fuel 500 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example all_owners_fixed : forall owner, In owner [0;1;2;3] ->
    E.WN.narrow (R.sigma_value final owner)
      (E.D.join (if Nat.eqb owner 0 then E.D.One else E.D.Bot)
        (R.aggregate final owner)) = R.sigma_value final owner.
  Proof.
    intros owner [<-|[<-|[<-|[<-|H]]]]; [| | | |contradiction]; vm_compute; reflexivity.
  Qed.
End Fanout.
