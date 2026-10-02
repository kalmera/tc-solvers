From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.instances.IdempotentChain
  solvers.slr.simple.Theorems solvers.slr.restarting.Theorems
  solvers.slr.narrowing_fixed_point.Theorems.
Import ListNotations.
Set Implicit Arguments.

(** A root spawns a reader, the reader spawns a child, and the child spawns
    the already materialized reader. These cover recursive and already materialized spawns. *)
Module Simple.
  Module C := TcSolvers.solvers.slr.simple.Theorems.Instances.Correct.
  Module E := Chain.
  Module R := C.R.
  Module Sem := C.Sem.
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
  Example spawned_descendants_solved : C.solved final 1 /\ C.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.owner_post_solution tf final 1 /\ C.owner_post_solution tf final 2.
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
  Example incomplete_owner_is_rejected : ~ C.owner_post_solution tf root_only 0.
  Proof.
    intros [_ [_ Hspawns]].
    destruct (Hspawns root_observation observes_missing_spawn 1 (or_introl eq_refl))
      as [value Hlookup].
    vm_compute in Hlookup. discriminate.
  Qed.
End Simple.

Module Restarting.
  Module C := TcSolvers.solvers.slr.restarting.Theorems.Instances.Correct.
  Module E := Chain.
  Module R := C.R.
  Module Sem := C.Sem.
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
  Example spawned_descendants_solved : C.solved final 1 /\ C.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.owner_post_solution tf final 1 /\ C.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Restarting.

Module Narrowing.
  Module C := TcSolvers.solvers.slr.narrowing_fixed_point.Theorems.Correctness IdempotentChain.V IdempotentChain.D IdempotentChain.U IdempotentChain.S IdempotentChain.M Base.AllEnabledFeatures IdempotentChain.DL IdempotentChain.UL IdempotentChain.SL IdempotentChain.ML.
  Module E := IdempotentChain.
  Module R := C.R.
  Module Sem := C.Sem.
  Module Run := C.N.
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
  Example spawned_descendants_solved : C.solved final 1 /\ C.solved final 2.
  Proof. vm_compute. split; eexists; reflexivity. Qed.
  Example spawn_closed_result : C.correct_final_state tf [0] final.
  Proof. exact (@C.successful_run_correct 300 tf [0] final successful). Qed.
  Example spawned_descendants_satisfied :
    C.owner_post_solution tf final 1 /\ C.owner_post_solution tf final 2.
  Proof.
    destruct spawn_closed_result as [_ Hpost].
    split; apply Hpost; exact (proj1 spawned_descendants_solved) ||
      exact (proj2 spawned_descendants_solved).
  Qed.
End Narrowing.

