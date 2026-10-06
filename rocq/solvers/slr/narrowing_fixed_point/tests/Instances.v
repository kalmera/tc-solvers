From Stdlib Require Import List.
From TcSolvers Require Import common.FiniteHeight
  solvers.slr.narrowing_fixed_point.NarrowingFixedPoint
  solvers.slr.narrowing_fixed_point.tests.Chain.
Import ListNotations.

Module E := Chain.

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

(** Changed controlled values trigger repeated updates without a self-read. *)
Example completed_owners :
  After.completed_owners 200 (After.R.initial_config [0]) = [1;0;1;0;1;0;1;0;1;0].
Proof. vm_compute. reflexivity. Qed.

Example no_self_read_owner_is_fixed :
  After.R.sigma_value After.final 0 = E.D.One /\
  E.WN.narrow (After.R.sigma_value After.final 0) E.D.One =
    After.R.sigma_value After.final 0.
Proof. vm_compute. split; reflexivity. Qed.

Module ReaderWakeupsOnly.
  Module N := NarrowingFixedPoint.Make E.V E.D E.U E.S E.M
    Base.ReaderWakeupsOnlyFeatures E.DL E.UL E.SL E.ML.
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
  Example fewer_evaluations :
    N.solve_fuel 200 tf [0] = Some final /\
    completed_owners 200 (R.initial_config [0]) = [1;0;1].
  Proof. vm_compute. split; reflexivity. Qed.
  Example fixedness_requires_recomputation :
    R.sigma_value final 0 = E.D.Top /\
    E.WN.narrow (R.sigma_value final 0) E.D.One <> R.sigma_value final 0.
  Proof. vm_compute. split; [reflexivity |discriminate]. Qed.
End ReaderWakeupsOnly.

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
  Example monotone : forall old new,
    E.D.leq old new = true -> E.D.leq (successor old) (successor new) = true.
  Proof. destruct old, new; cbn; congruence. Qed.
  Definition final := R.cfg_state (N.run_fuel 200 tf (R.initial_config [0])).
  Example retained_self_wakes : N.solve_fuel 200 tf [0] = Some final /\
    R.sigma_value final 0 = E.D.Top.
  Proof. vm_compute. split; reflexivity. Qed.
  Module Off := NarrowingFixedPoint.Make E.V E.D U E.S E.M
    Base.ReaderWakeupsOnlyFeatures E.DL UL E.SL E.ML.
  Definition off_tf (_owner : E.V.t) : Off.R.ConstraintSystem.rhs :=
    Off.R.ConstraintSystem.Get 0 (fun value => Off.R.ConstraintSystem.Ret (successor value)).
  Definition off_final := Off.R.cfg_state (Off.run_fuel 200 off_tf (Off.R.initial_config [0])).
  Example retained_self_wakes_without_recomputation :
    Off.solve_fuel 200 off_tf [0] = Some off_final /\
    Off.R.sigma_value off_final 0 = E.D.Top.
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
