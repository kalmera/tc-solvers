From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain
  solvers.slr.restarting.Restarting.
Import ListNotations.

Module E := Chain.
Module Enabled := Restarting.FirstDiscovery E.V E.D E.U E.S E.M
  Restarting.AllEnabledFeatures.
Module Disabled := Restarting.FirstDiscovery E.V E.D E.U E.S E.M
  Restarting.ReaderWakeupsOnlyFeatures.

(** Owner 0 reads only 1. The back edge from 1 controls 0, whose update
    nevertheless depends on its own stored value. Slow narrowing needs
    several ordinary updates to reach One. *)
Definition enabled_tf owner : Enabled.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    Enabled.ConstraintSystem.Get 1 (fun _ => Enabled.ConstraintSystem.Ret E.D.One)
  else Enabled.ConstraintSystem.Get 0 (fun _ => Enabled.ConstraintSystem.Ret E.D.Bot).
Definition disabled_tf owner : Disabled.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    Disabled.ConstraintSystem.Get 1 (fun _ => Disabled.ConstraintSystem.Ret E.D.One)
  else Disabled.ConstraintSystem.Get 0 (fun _ => Disabled.ConstraintSystem.Ret E.D.Bot).

Example controlled_recomputation_reaches_fixedness :
  exists final,
    Enabled.solve_fuel 200 enabled_tf [0] = Some final /\
    Enabled.sigma_value final 0 = E.D.One /\
    E.WN.narrow (Enabled.sigma_value final 0) E.D.One =
      Enabled.sigma_value final 0.
Proof. eexists. vm_compute. repeat split; reflexivity. Qed.

Example reader_wakeups_alone_leave_unfinished_narrowing :
  exists final,
    Disabled.solve_fuel 200 disabled_tf [0] = Some final /\
    Disabled.sigma_value final 0 = E.D.Top /\
    E.WN.narrow (Disabled.sigma_value final 0) E.D.One <>
      Disabled.sigma_value final 0.
Proof. eexists. vm_compute. repeat split; congruence. Qed.
