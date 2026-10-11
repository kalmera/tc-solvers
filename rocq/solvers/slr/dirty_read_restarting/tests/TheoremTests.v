From Stdlib Require Import List.
From TcSolvers Require Import solvers.slr.common.tests.ToySolverFixture
  solvers.slr.dirty_read_restarting.Theorems.
Import ListNotations.

(* This alternative bundle exercises the public certificates independently
   of the common finite-chain instances. *)

Module NoSidePhaseRestartFeatures <: DirtyReadRestarting.FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := true.
  Definition recompute_controlled := true.
  Definition defer_spawns := true.
End NoSidePhaseRestartFeatures.

Module SidePhaseRestartFeatures <: DirtyReadRestarting.FEATURES.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := true.
  Definition recompute_controlled := true.
  Definition defer_spawns := true.
End SidePhaseRestartFeatures.

Module Parameters := ToyParameters NoSidePhaseRestartFeatures.
Module RestartParameters := ToyParameters SidePhaseRestartFeatures.
Module ToyTotal := Theorems.Make Parameters.
Module ToyTotalWithRestarts := Theorems.Make RestartParameters.
Module R := ToyTotal.Internal.R.
Module Sem := ToyTotal.Internal.Sem.

Definition toy_system (_ : TV.t) : R.ConstraintSystem.rhs :=
  R.ConstraintSystem.Ret Mid.

Definition toy_finite : ToyTotal.Solver.Sem.finite_system toy_system [tt].
Proof.
  refine {| Sem.support := [tt] |}.
  - constructor; [intros Hin; inversion Hin |constructor].
  - intros [] _. now left.
  - intros [] _. constructor.
Defined.

Example finite_toy_executes :
  match R.solve_fuel 30 toy_system [tt] with
  | Some final => R.sigma_value final tt = Mid
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition audited_total_correct := ToyTotal.total_correct.
Definition audited_total_correct_with_restarts :=
  ToyTotalWithRestarts.total_correct.

Module LeastParameters := ToyLeastParameters NoSidePhaseRestartFeatures.
Module ToyLeast := Theorems.LeastSolutionMake LeastParameters.
Definition audited_leastness := ToyLeast.Certificates.leastness.

Example finite_toy_is_totally_correct :
  exists fuel final, R.solve_fuel fuel toy_system [tt] = Some final /\
    ToyTotal.Spec.correct_final_state toy_system [tt] final.
Proof. exact (ToyTotal.total_correct toy_finite). Qed.

Definition toy_restart_system (_ : TV.t) :
  ToyTotalWithRestarts.Internal.R.ConstraintSystem.rhs :=
  ToyTotalWithRestarts.Internal.R.ConstraintSystem.Ret Mid.

Definition toy_restart_finite :
  ToyTotalWithRestarts.Solver.Sem.finite_system toy_restart_system [tt].
Proof.
  refine {| ToyTotalWithRestarts.Internal.Sem.support := [tt] |}.
  - constructor; [intros Hin; inversion Hin |constructor].
  - intros [] _. now left.
  - intros [] _. constructor.
Defined.

Example finite_toy_with_restarts_is_totally_correct :
  exists fuel final, ToyTotalWithRestarts.Solver.View.solve_fuel fuel toy_restart_system [tt] = Some final /\
    ToyTotalWithRestarts.Spec.correct_final_state toy_restart_system [tt] final.
Proof. exact (ToyTotalWithRestarts.total_correct toy_restart_finite). Qed.

Goal True. idtac "dirty read restarting audited_total_correct proven with assumptions:". Abort.
Print Assumptions audited_total_correct.
Goal True. idtac "dirty read restarting audited_total_correct_with_restarts proven with assumptions:". Abort.
Print Assumptions audited_total_correct_with_restarts.
Goal True. idtac "dirty read restarting audited_leastness proven with assumptions:". Abort.
Print Assumptions audited_leastness.
