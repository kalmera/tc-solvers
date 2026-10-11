From Stdlib Require Import List Arith.PeanoNat.
From TcSolvers Require Import
  common.Collections common.ReluctantUpdate
  solvers.slr.dormant_restarting.DormantRestarting.
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
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := false.
End KeepDead.
Module KeepPhases <: FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := true.
End KeepPhases.
Module KeepBoth <: FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End KeepBoth.
Module DefaultTests.
  Module R := DormantRestarting.Make V D U SU S M AllEnabledFeatures.
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
End DefaultTests.
Module KeepDeadTests.
  Module R := DormantRestarting.Make V D U SU S M KeepDead.
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
End KeepDeadTests.
Module KeepPhasesTests.
  Module R := DormantRestarting.Make V D U SU S M KeepPhases.
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
End KeepPhasesTests.
Module KeepBothTests.
  Module R := DormantRestarting.Make V D U SU S M KeepBoth.
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
End KeepBothTests.
