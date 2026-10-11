From Stdlib Require Import List Arith.PeanoNat.
From TcSolvers Require Import
  common.Collections common.ReluctantUpdate
  solvers.slr.plus_restarting.PlusRestarting.
Import ListNotations.

Module V <: VAR.
  Definition t := nat.
  Definition eq_dec := Nat.eq_dec.
End V.
Module D <: DOMAIN.
  Definition t := nat.
  Definition bottom := 0.
  Definition join := Nat.max.
  Definition leq := Nat.leb.
End D.
Module U <: UPDATE V D.
  Definition phase := unit.
  Definition initial_phase (_ : bool) (_ : nat) := tt.
  Definition update (_ : bool) (_ : nat) (_ : phase) (_old input : nat) :=
    (tt, input).
End U.
Module SU := ReluctantSideUpdate V D U.
Module S := ListSet V.
Module M := AssocMap V.



Module KeepDead <: FEATURES.
  Definition recompute_controlled := false.
  Definition defer_spawns := true.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := false.
End KeepDead.
Module KeepPhases <: FEATURES.
  Definition recompute_controlled := false.
  Definition defer_spawns := true.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := true.
End KeepPhases.
Module KeepBoth <: FEATURES.
  Definition recompute_controlled := false.
  Definition defer_spawns := true.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End KeepBoth.
Module DefaultTests.
  Module R := PlusRestarting.Make V D U SU S M AllEnabledFeatures.
  Import R.ConstraintSystem.

  Example dormant_roots_remain_rankless :
    match R.solve_fuel 100 (fun _ => Ret 0) [1; 1] with
    | Some st => R.Ranking.lookup (R.ranking st) 1 = None /\
                 M.lookup (R.sigma st) 1 = None /\
                 S.mem 1 (R.dormant_bottom st) = true
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition transfer (x : nat) : rhs :=
    match x with
    | 0 => Get 1 (fun d => Ret d)
    | 2 => Side 1 3 (Side 1 1 (Ret 0))
    | _ => Ret 0
    end.

  Example promotion_is_dense_and_wakes_reader :
    match R.solve_fuel 1000 transfer [0; 2] with
    | Some st =>
        R.Ranking.lookup (R.ranking st) 0 = Some 0 /\
        R.Ranking.lookup (R.ranking st) 2 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 1 = Some 2 /\
        R.sigma_value st 0 = 3 /\
        R.stored_contribution st 2 1 = 3 /\
        M.lookup (R.sigma st) 1 = Some 3
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition dirty_state : R.state :=
    let st := R.observe (R.observe (R.observe R.empty_state 0) 1) 2 in
    let st := R.materialize st 0 in
    let st := R.with_contributions st (R.update_map (R.contributions st) 0 2 3) in
    R.mark_side_dirty (R.enqueue (R.add_reader st 0 1) 0) 0.

  Example lower_dirty_read_publishes_and_defers :
    match R.try_dirty_read (fun _ => Ret 0) dirty_state 2 0 with
    | Some st =>
        R.sigma_value st 0 = 3 /\ R.queue st = [] /\
        R.deferred_wakes st = [1] /\ R.is_side_dirty st 0 = false /\
        R.queue (R.flush_deferred st) = [1]
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example self_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0) dirty_state 0 0 = None.
  Proof. reflexivity. Qed.

  Example decreasing_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0)
      (R.with_sigma dirty_state (M.update (R.sigma dirty_state) 0 4)) 2 0 = None.
  Proof. reflexivity. Qed.

End DefaultTests.
Module KeepDeadTests.
  Module R := PlusRestarting.Make V D U SU S M KeepDead.
  Import R.ConstraintSystem.

  Example dormant_roots_remain_rankless :
    match R.solve_fuel 100 (fun _ => Ret 0) [1; 1] with
    | Some st => R.Ranking.lookup (R.ranking st) 1 = None /\
                 M.lookup (R.sigma st) 1 = None /\
                 S.mem 1 (R.dormant_bottom st) = true
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition transfer (x : nat) : rhs :=
    match x with
    | 0 => Get 1 (fun d => Ret d)
    | 2 => Side 1 3 (Side 1 1 (Ret 0))
    | _ => Ret 0
    end.

  Example promotion_is_dense_and_wakes_reader :
    match R.solve_fuel 1000 transfer [0; 2] with
    | Some st =>
        R.Ranking.lookup (R.ranking st) 0 = Some 0 /\
        R.Ranking.lookup (R.ranking st) 2 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 1 = Some 2 /\
        R.sigma_value st 0 = 3 /\
        R.stored_contribution st 2 1 = 3 /\
        M.lookup (R.sigma st) 1 = Some 3
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition dirty_state : R.state :=
    let st := R.observe (R.observe (R.observe R.empty_state 0) 1) 2 in
    let st := R.materialize st 0 in
    let st := R.with_contributions st (R.update_map (R.contributions st) 0 2 3) in
    R.mark_side_dirty (R.enqueue (R.add_reader st 0 1) 0) 0.

  Example lower_dirty_read_publishes_and_defers :
    match R.try_dirty_read (fun _ => Ret 0) dirty_state 2 0 with
    | Some st =>
        R.sigma_value st 0 = 3 /\ R.queue st = [] /\
        R.deferred_wakes st = [1] /\ R.is_side_dirty st 0 = false /\
        R.queue (R.flush_deferred st) = [1]
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example self_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0) dirty_state 0 0 = None.
  Proof. reflexivity. Qed.

  Example decreasing_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0)
      (R.with_sigma dirty_state (M.update (R.sigma dirty_state) 0 4)) 2 0 = None.
  Proof. reflexivity. Qed.

End KeepDeadTests.
Module KeepPhasesTests.
  Module R := PlusRestarting.Make V D U SU S M KeepPhases.
  Import R.ConstraintSystem.

  Example dormant_roots_remain_rankless :
    match R.solve_fuel 100 (fun _ => Ret 0) [1; 1] with
    | Some st => R.Ranking.lookup (R.ranking st) 1 = None /\
                 M.lookup (R.sigma st) 1 = None /\
                 S.mem 1 (R.dormant_bottom st) = true
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition transfer (x : nat) : rhs :=
    match x with
    | 0 => Get 1 (fun d => Ret d)
    | 2 => Side 1 3 (Side 1 1 (Ret 0))
    | _ => Ret 0
    end.

  Example promotion_is_dense_and_wakes_reader :
    match R.solve_fuel 1000 transfer [0; 2] with
    | Some st =>
        R.Ranking.lookup (R.ranking st) 0 = Some 0 /\
        R.Ranking.lookup (R.ranking st) 2 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 1 = Some 2 /\
        R.sigma_value st 0 = 3 /\
        R.stored_contribution st 2 1 = 3 /\
        M.lookup (R.sigma st) 1 = Some 3
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition dirty_state : R.state :=
    let st := R.observe (R.observe (R.observe R.empty_state 0) 1) 2 in
    let st := R.materialize st 0 in
    let st := R.with_contributions st (R.update_map (R.contributions st) 0 2 3) in
    R.mark_side_dirty (R.enqueue (R.add_reader st 0 1) 0) 0.

  Example lower_dirty_read_publishes_and_defers :
    match R.try_dirty_read (fun _ => Ret 0) dirty_state 2 0 with
    | Some st =>
        R.sigma_value st 0 = 3 /\ R.queue st = [] /\
        R.deferred_wakes st = [1] /\ R.is_side_dirty st 0 = false /\
        R.queue (R.flush_deferred st) = [1]
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example self_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0) dirty_state 0 0 = None.
  Proof. reflexivity. Qed.

  Example decreasing_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0)
      (R.with_sigma dirty_state (M.update (R.sigma dirty_state) 0 4)) 2 0 = None.
  Proof. reflexivity. Qed.

End KeepPhasesTests.
Module KeepBothTests.
  Module R := PlusRestarting.Make V D U SU S M KeepBoth.
  Import R.ConstraintSystem.

  Example dormant_roots_remain_rankless :
    match R.solve_fuel 100 (fun _ => Ret 0) [1; 1] with
    | Some st => R.Ranking.lookup (R.ranking st) 1 = None /\
                 M.lookup (R.sigma st) 1 = None /\
                 S.mem 1 (R.dormant_bottom st) = true
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition transfer (x : nat) : rhs :=
    match x with
    | 0 => Get 1 (fun d => Ret d)
    | 2 => Side 1 3 (Side 1 1 (Ret 0))
    | _ => Ret 0
    end.

  Example promotion_is_dense_and_wakes_reader :
    match R.solve_fuel 1000 transfer [0; 2] with
    | Some st =>
        R.Ranking.lookup (R.ranking st) 0 = Some 0 /\
        R.Ranking.lookup (R.ranking st) 2 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 1 = Some 2 /\
        R.sigma_value st 0 = 3 /\
        R.stored_contribution st 2 1 = 3 /\
        M.lookup (R.sigma st) 1 = Some 3
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Definition dirty_state : R.state :=
    let st := R.observe (R.observe (R.observe R.empty_state 0) 1) 2 in
    let st := R.materialize st 0 in
    let st := R.with_contributions st (R.update_map (R.contributions st) 0 2 3) in
    R.mark_side_dirty (R.enqueue (R.add_reader st 0 1) 0) 0.

  Example lower_dirty_read_publishes_and_defers :
    match R.try_dirty_read (fun _ => Ret 0) dirty_state 2 0 with
    | Some st =>
        R.sigma_value st 0 = 3 /\ R.queue st = [] /\
        R.deferred_wakes st = [1] /\ R.is_side_dirty st 0 = false /\
        R.queue (R.flush_deferred st) = [1]
    | None => False
    end.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Example self_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0) dirty_state 0 0 = None.
  Proof. reflexivity. Qed.

  Example decreasing_dirty_read_remains_queued :
    R.try_dirty_read (fun _ => Ret 0)
      (R.with_sigma dirty_state (M.update (R.sigma dirty_state) 0 4)) 2 0 = None.
  Proof. reflexivity. Qed.

End KeepBothTests.

Module Immediate <: FEATURES.
  Definition recompute_controlled := false.
  Definition defer_spawns := false.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End Immediate.
Module Deferred <: FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
  Definition recompute_controlled := false.
  Definition defer_spawns := true.
End Deferred.
Module FifoTests.
  Module R := PlusRestarting.Make V D U SU S M Deferred.
  Import R.ConstraintSystem.
  Definition tf x := match x with
    | 0 => Spawn 1 (Spawn 2 (Spawn 1 (Ret 1)))
    | 1 => Spawn 3 (Ret 1)
    | 2 => Ret 2
    | _ => Ret 3 end.
  Example fifo_and_deduplication :
    match R.solve_fuel 1000 tf [0] with
    | Some st => R.Ranking.lookup (R.ranking st) 2 = Some 2 /\
        R.Ranking.lookup (R.ranking st) 3 = Some 3 /\
        R.pending_spawns st = [] /\ length (S.elements (R.requested_spawns st)) = 3
    | None => False end.
  Proof. vm_compute. repeat split; reflexivity. Qed.
  Example reads_stay_synchronous :
    match R.solve_fuel 1000 (fun x => match x with
      | 0 => Spawn 1 (Get 2 (fun d => Ret d))
      | 1 => Ret 1 | _ => Ret 2 end) [0] with
    | Some st => R.Ranking.lookup (R.ranking st) 2 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 1 = Some 2 /\ R.sigma_value st 0 = 2
    | None => False end.
  Proof. vm_compute. repeat split; reflexivity. Qed.
  Example spawn_cycle_terminates :
    match R.solve_fuel 1000 (fun x => Spawn (1-x) (Ret 1)) [0] with
    | Some st => R.pending_spawns st = [] /\ R.sigma_value st 1 = 1
    | None => False end.
  Proof. vm_compute. split; reflexivity. Qed.
  (** Before the terminal-state guard was added, these exact fuel budgets
      returned Some with spawned work still pending. *)
  Example fuel_boundaries_do_not_drop_spawns :
    R.solve_fuel 12 tf [0] = None /\
    R.solve_fuel 23 tf [0] = None /\
    R.solve_fuel 33 tf [0] = None.
  Proof. vm_compute. repeat split; reflexivity. Qed.
End FifoTests.
