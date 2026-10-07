From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain
  solvers.slr.narrowing_fixed_point.Theorems.
Import ListNotations.

Module E := Chain.
Module Q := Theorems.Instances.FixedCells.
Module P := Q.P.

(** Assumption reports for the main public results cover their dependencies. *)
Print Assumptions Q.total_correct.
Print Assumptions Theorems.Instances.Least.total_least_solution.
Print Assumptions Q.monotonic_avoids_fallback.
Print Assumptions Q.total_correct_and_fixed.

Module N := P.N.
Module R := P.R.
Definition tf (owner : E.V.t) : R.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    R.ConstraintSystem.Get 1 (fun _ => R.ConstraintSystem.Ret E.D.One)
  else R.ConstraintSystem.Get 0 (fun _ => R.ConstraintSystem.Ret E.D.Bot).
Definition final := R.cfg_state (N.run_fuel 200 tf (R.initial_config [0])).
Example controlled_owner_reaches_narrowing_fixedpoint :
  N.solve_fuel 200 tf [0] = Some final /\ R.sigma_value final 0 = E.D.One.
Proof. vm_compute. split; reflexivity. Qed.

(** A source must retry for a changed cell even when another source masks it
    in the incoming aggregate. Both sources finish with stable contributions. *)
Definition masked_tf (owner : E.V.t) : R.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    R.ConstraintSystem.Side 2 E.D.Top (R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Bot))
  else if E.V.eq_dec owner 1 then
    R.ConstraintSystem.Side 2 E.D.One (R.ConstraintSystem.Ret E.D.Bot)
  else R.ConstraintSystem.Ret E.D.Bot.
Definition masked_final := R.cfg_state (N.run_fuel 500 masked_tf (R.initial_config [0])).
Example masked_cell_source_finishes :
  N.solve_fuel 500 masked_tf [0] = Some masked_final /\
  R.stored_contribution masked_final 0 2 = E.D.Top /\
  R.stored_contribution masked_final 1 2 = E.D.One /\
  R.sigma_value masked_final 2 = E.D.Top.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The finite-chain narrowing is deliberately not idempotent. The controlled
    owner above has no direct self-read, and needs repeated recomputation. *)
Example slow_narrowing_requires_more_than_one_update :
  E.WN.narrow E.D.Top E.D.One = E.D.Three /\
  E.WN.narrow (E.WN.narrow E.D.Top E.D.One) E.D.One = E.D.Two.
Proof. vm_compute; split; reflexivity. Qed.
Example controlled_owner_is_narrowing_fixed :
  E.WN.narrow (R.sigma_value final 0) (E.D.join E.D.One (R.aggregate final 0)) = R.sigma_value final 0.
Proof. vm_compute; reflexivity. Qed.
