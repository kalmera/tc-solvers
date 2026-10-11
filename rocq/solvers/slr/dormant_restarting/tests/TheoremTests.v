From Stdlib Require Import List.
From TcSolvers Require Import solvers.slr.common.tests.ToySolverFixture
  solvers.slr.dormant_restarting.Theorems.
Import ListNotations.

(* This alternative bundle exercises the public certificates independently
   of the common finite-chain instances. *)

Module Parameters := ToyParameters SolverFeatures.AllEnabledFeatures.
Module ToyTotal := Theorems.Make Parameters.
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

Module LeastParameters := ToyLeastParameters SolverFeatures.AllEnabledFeatures.
Module ToyLeast := Theorems.LeastSolutionMake LeastParameters.
Definition audited_leastness := ToyLeast.Certificates.leastness.

Example finite_toy_is_totally_correct :
  exists fuel final, R.solve_fuel fuel toy_system [tt] = Some final /\
    ToyTotal.Spec.correct_final_state toy_system [tt] final.
Proof. exact (ToyTotal.total_correct toy_finite). Qed.
