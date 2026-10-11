From Stdlib Require Import List Arith.PeanoNat.
From TcSolvers Require Import
  common.Collections common.ReluctantUpdate
  solvers.slr.deferred_simple.DeferredSimple.
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



Module FifoTests.
  Module R := DeferredSimple.Make V D U SU S M DeferredFeatures.
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
  Example pending_fifo_prevents_success :
    R.terminal_state {| R.cfg_state := R.request_spawn R.empty_state 1;
                        R.cfg_control := R.RunLoop |} = None.
  Proof. reflexivity. Qed.
End FifoTests.

Module ImmediateTests.
  Module R := DeferredSimple.Make V D U SU S M ImmediateFeatures.
  Import R.ConstraintSystem.
  Example spawns_are_synchronous :
    match R.solve_fuel 1000 (fun x => match x with
      | 0 => Spawn 1 (Get 2 (fun d => Ret d))
      | 1 => Ret 1 | _ => Ret 2 end) [0] with
    | Some st => R.Ranking.lookup (R.ranking st) 1 = Some 1 /\
        R.Ranking.lookup (R.ranking st) 2 = Some 2 /\
        R.pending_spawns st = [] /\ S.elements (R.requested_spawns st) = []
    | None => False end.
  Proof. vm_compute. repeat split; reflexivity. Qed.
End ImmediateTests.

Module PersistentPhases.
  Module CountingUpdate <: UPDATE V D.
    Definition phase := nat.
    Definition initial_phase (_ : bool) (_ : nat) := 0.
    Definition update (_ : bool) (_ : nat) (phase old input : nat) :=
      (S phase, Nat.max old input).
  End CountingUpdate.
  Module Side := ReluctantSideUpdate V D CountingUpdate.
  Module R := DeferredSimple.Make V D CountingUpdate Side S M DeferredFeatures.
  Import R.ConstraintSystem.

  (** Three value changes, followed by a stable evaluation which still
      updates the source-target side cell. *)
  Example reevaluations_preserve_both_phases :
    match R.solve_fuel 1000 (fun x => match x with
      | 0 => Get 0 (fun d => let next := Nat.min 3 (S d) in
          Side 1 next (Spawn 2 (Ret next)))
      | 2 => Ret 2 | _ => Ret 0 end) [0] with
    | Some st => R.sigma_value st 0 = 3 /\ R.sigma_value st 1 = 3 /\
        R.stored_phase st 0 = 3 /\ R.stored_side_phase st 0 1 = 4 /\
        S.elements (R.requested_spawns st) = [2]
    | None => False end.
  Proof. vm_compute. repeat split; reflexivity. Qed.
End PersistentPhases.
