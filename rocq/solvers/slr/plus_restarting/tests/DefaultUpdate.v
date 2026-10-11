From Stdlib Require Import List ZArith.
From TcSolvers Require Import
  common.instances.Chain
  solvers.slr.reluctant_restarting.DefaultUpdate
  solvers.slr.plus_restarting.Theorems.
Import ListNotations.

Module E := Chain.
Module I := ThresholdReluctantRestartingDefault E.V.
Module Features <: PlusRestarting.FEATURES.
  Definition recompute_controlled := false.
  Definition defer_spawns := true.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End Features.
Module Parameters <: TOTAL_CORRECTNESS_PARAMETERS.
  Module V := E.V.
  Module D := ThresholdIntervalDomain.
  Module S := E.S.
  Module M := E.M.
  Module Features := Features.
  Module DL := ThresholdIntervalDomainLaws.
  Module SL := E.SL.
  Module ML := E.ML.
  Module U := I.Base.
  Module SU := I.SideUpdate.
  Module OUL := I.OrdinaryLaws.
  Module SUL := I.SideLaws.
End Parameters.
Module Correct := Theorems.Make Parameters.
Module R := Correct.Solver.R.

Definition tf (_owner : E.V.t) : R.ConstraintSystem.rhs :=
  R.ConstraintSystem.Get 0 (fun _ => R.ConstraintSystem.Ret (TUpTo 5)).

Example controlled_owner_keeps_first_copy_precision :
  exists final,
    R.solve_fuel 100 tf [0] = Some final /\ R.sigma_value final 0 = TUpTo 5.
Proof. eexists. vm_compute. split; reflexivity. Qed.

Goal True. idtac "Plus Restarting (SLR-TC+) with DefaultUpdate proven with assumptions:". Abort.
Print Assumptions Correct.total_correct.
