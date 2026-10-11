From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain
  solvers.slr.simple.Theorems solvers.slr.restarting.Theorems
  solvers.slr.narrowing_fixed_point.Theorems
  solvers.slr.reluctant_restarting.Theorems solvers.slr.dormant_restarting.Theorems
  solvers.slr.dirty_read_restarting.Theorems solvers.slr.deferred_simple.Theorems.
Import ListNotations.
Set Implicit Arguments.

(** A root spawns a reader, the reader spawns a child, and the child spawns
    the already materialized reader. These cover recursive and already materialized spawns. *)
Module Simple.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.

  (** The previous numerical replay accepts this root even though its spawn
      is missing. Both strengthened post-solution definitions reject it. *)
  Definition root_only := R.set_value
    (R.materialize (R.cfg_state (R.initial_config [0])) 0) 0 E.D.One.
  Definition root_observation : Sem.observation :=
    {| Sem.Observation.observed_direct := E.D.One;
       Sem.Observation.observed_reads := [];
       Sem.Observation.observed_sides := [];
       Sem.Observation.observed_spawns := [1] |}.
  Lemma observes_missing_spawn :
    Sem.observes_at (R.sigma_value root_only) (tf 0) root_observation.
  Proof.
    split.
    - unfold tf, root_observation.
      apply Sem.ObserveSpawn with (result :=
        {| Sem.Observation.observed_direct := E.D.One;
           Sem.Observation.observed_reads := [];
           Sem.Observation.observed_sides := [];
           Sem.Observation.observed_spawns := [] |}). constructor.
    - intros target value Hin. contradiction.
  Qed.
  Example numeric_replay_omits_spawn :
    Sem.rhs_eval root_only (tf 0) E.D.One [] [].
  Proof. constructor. constructor. Qed.
  Example numeric_bounds_hold_without_spawn :
    E.D.leq E.D.One (R.sigma_value root_only 0) = true.
  Proof. vm_compute. reflexivity. Qed.
  Example root_only_is_not_post_solution :
    ~ Sem.post_solution_on tf [0] (R.sigma_value root_only).
  Proof.
    intros Hpost.
    destruct (Hpost 0 (or_introl eq_refl) root_observation observes_missing_spawn)
      as [_ [_ Hspawns]].
    specialize (Hspawns 1 (or_introl eq_refl)).
    cbn in Hspawns. destruct Hspawns as [Hbad | Hbad]; [discriminate |contradiction].
  Qed.
  Example incomplete_owner_is_rejected : ~ C.Spec.owner_post_solution tf root_only 0.
  Proof.
    intros [_ [_ Hspawns]].
    assert (Hobs : C.Solver.Sem.observes_at (C.Solver.View.sigma_value root_only)
      (tf 0) root_observation).
    { split.
      - unfold tf, root_observation.
        apply Sem.ConstraintSemantics.ObserveSpawn with (result :=
          {| Sem.Observation.observed_direct := E.D.One;
             Sem.Observation.observed_reads := [];
             Sem.Observation.observed_sides := [];
             Sem.Observation.observed_spawns := [] |}). constructor.
      - intros target value Hin. contradiction. }
    destruct (Hspawns root_observation Hobs 1 (or_introl eq_refl))
      as [value Hlookup].
    vm_compute in Hlookup. discriminate.
  Qed.
End Simple.

Module Restarting.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Restarting.

Module Narrowing.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Internal.Sem.
  Module Run := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Instances.Correct.Internal.N.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Narrowing.



Module Reluctant.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.reluctant_restarting.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Reluctant.

Module Dormant.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.dormant_restarting.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Dormant.

Module DirtyRead.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.dirty_read_restarting.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End DirtyRead.

Module DeferredSimple.
  Module E := Chain.
  Module C.
    Module Solver := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.Solver.
    Module Spec := SolverContracts.ForSolver E.V E.D Solver.
    Definition successful_run_correct := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.successful_run_correct.
  End C.
  Module R := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.Internal.R.
  Module Sem := TcSolvers.solvers.slr.deferred_simple.Theorems.Instances.Correct.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End DeferredSimple.

Module ImmediateSimple.
  Module Features <: RESTARTING_FEATURES.
    Definition recompute_controlled := true.
    Definition defer_spawns := false.
    Definition restart_side_phases := true.
    Definition eliminate_dead_sides := true.
  End Features.
  Module Parameters := ChainParameters Features.
  Module C := TcSolvers.solvers.slr.deferred_simple.Theorems.Make Parameters.
  Module E := Chain.
  Module R := C.Internal.R.
  Module Sem := C.Internal.Sem.
  Module Run := R.
  Definition tf owner : R.ConstraintSystem.rhs :=
    match owner with
    | 0 => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.One)
    | 1 => R.ConstraintSystem.Get 0
        (fun value => R.ConstraintSystem.Spawn 2 (R.ConstraintSystem.Ret value))
    | _ => R.ConstraintSystem.Spawn 1 (R.ConstraintSystem.Ret E.D.Two)
    end.
  Definition final := R.cfg_state (Run.run_fuel 300 tf (R.initial_config [0])).
  Example successful : Run.solve_fuel 300 tf [0] = Some final.
  Proof. vm_compute. reflexivity. Qed.
  Example spawned_descendants_solved : C.Spec.solved final 1 /\ C.Spec.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.Spec.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.Spec.owner_post_solution tf final 1 /\ C.Spec.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End ImmediateSimple.
