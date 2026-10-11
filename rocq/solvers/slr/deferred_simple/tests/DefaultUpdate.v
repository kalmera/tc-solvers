From Stdlib Require Import List ZArith.
From TcSolvers Require Import
  common.instances.Chain common.instances.DefaultUpdate
  solvers.slr.deferred_simple.Theorems.
Import ListNotations.

Module E := Chain.
Module I := ThresholdDefaultUpdate E.V.
Module Parameters <: ASCENDING_TOTAL_CORRECTNESS_PARAMETERS.
  Module V := E.V.
  Module D := I.D.
  Module U := I.Base.
  Module SU := I.SideUpdate.
  Module S := E.S.
  Module M := E.M.
  Module Features := SolverFeatures.AllEnabledFeatures.
  Module DL := I.DL.
  Module OUL := I.OrdinaryLaws.
  Module ASUL := I.SideLaws.
  Module SL := E.SL.
  Module ML := E.ML.
End Parameters.
Module Correct := Theorems.Make Parameters.
Module R := Correct.Internal.R.

(** A self-read controls the owner, so its first commit uses the default
    copy rather than immediately rounding 5 up to the widening threshold 10. *)
Definition tf (_owner : E.V.t) : R.ConstraintSystem.rhs :=
  R.ConstraintSystem.Get 0 (fun _ => R.ConstraintSystem.Ret (TUpTo 5)).

Example controlled_owner_keeps_first_copy_precision :
  exists final,
    R.solve_fuel 100 tf [0] = Some final /\ R.sigma_value final 0 = TUpTo 5.
Proof. eexists. vm_compute. split; reflexivity. Qed.

Goal True. idtac "FIFO-Deferred Simple with DefaultUpdate proven with assumptions:". Abort.
Print Assumptions Correct.total_correct.
