From Stdlib Require Import List.
From TcSolvers Require Export solvers.slr.deferred_simple.proofs.Termination.
From TcSolvers Require Import solvers.slr.deferred_simple.proofs.LeastSolutionProof.
From TcSolvers Require Import common.SolverContracts common.Assumptions common.FiniteHeight common.SourceStrictness
  solvers.slr.common.FirstActivation common.SideUpdate
  solvers.slr.deferred_simple.DeferredSimple.
Import ListNotations.
Set Implicit Arguments.


(** Proof assembly for the public semantic specifications. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Features : DeferredSimple.FEATURES)
  (DL : DOMAIN_LAWS D)
  (OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U)
  (SUL : SIDE_UPDATE_TERMINATION_LAWS V D SU)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Rk := ListDiscoveryOrder V.
  Module RankLaws <: STABLE_DISCOVERY_ORDER_LAWS V Rk := FirstActivationLaws V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws V.
  Module DormantRankLaws := FirstActivationLaws V.
  Module Library := LeastSolutionProof.Make V D U SU S M Rk Features RankLaws
    RankFinite DormantRankLaws DL OUL SUL SL ML.
  Module Sem := Library.Sem.
  Module R := Library.R.
  Module Strict := SourceStrictness.Make V D DL.
  Definition source_strict_on := Strict.source_strict_on
    Sem.observes_at Sem.observed_direct Sem.observed_sides.

  Theorem successful_run_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final ->
    Sem.correct_final_state tf roots final /\
    (forall owner, Sem.solved final owner ->
      Sem.rhs_post_solution final owner (tf owner)) /\
    R.pending_spawns final = [] /\
    (forall target, S.mem target (R.requested_spawns final) = true ->
      Sem.solved final target).
  Proof. exact Library.Total.C.successful_run_correct. Qed.

  Theorem total_correct : forall tf roots (finite : Sem.finite_system tf roots),
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.correct_final_state tf roots final /\ Sem.quiescent final.
  Proof. exact Library.Total.total_correct. Qed.

  Theorem sufficient_fuel : forall tf roots (finite : Sem.finite_system tf roots),
    exists fuel final, forall extra,
      R.solve_fuel (fuel + extra) tf roots = Some final.
  Proof. exact Library.Total.sufficient_fuel. Qed.

  Module LeastSolution
    (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
    (SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU).
    Module Verified := Library.LeastSolution UBL SUBL.
    Theorem total_least_on_solved :
      forall tf roots (finite : Sem.finite_system tf roots),
      source_strict_on tf (Sem.support finite) roots ->
      Sem.system_monotone_on tf (Sem.support finite) ->
      exists fuel final,
        R.solve_fuel fuel tf roots = Some final /\
        Sem.correct_final_state tf roots final /\
        Sem.post_solution_on tf (Sem.support finite) (R.sigma_value final) /\
        forall upper, Sem.post_solution_on tf (Sem.support finite) upper ->
          forall owner, Sem.solved final owner ->
            D.leq (R.sigma_value final owner) (upper owner) = true.
    Proof. exact Verified.total_least_on_solved. Qed.
    Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
      source_strict_on tf (Sem.support finite) roots ->
      Sem.system_monotone_on tf (Sem.support finite) ->
      exists fuel final, R.solve_fuel fuel tf roots = Some final /\
        Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
    Proof.
      intros tf roots finite Hstrict Hmono.
      destruct (total_correct finite) as [fuel [final [Hrun _]]].
      exists fuel, final. split; [exact Hrun |].
      exact (@Verified.solve_fuel_least_solution fuel tf roots finite final
        Hstrict Hmono Hrun).
    Qed.
  End LeastSolution.
  Module PublicSpec := SolverContracts.ForSolver V D Library.Total.C.Solver.
  Module Certificates <: PublicSpec.VERIFIED.
    Theorem correctness : PublicSpec.Correctness.
    Proof. constructor. exact Library.Total.C.successful_run_spawn_correct. Qed.
    Theorem termination : PublicSpec.Termination.
    Proof.
      constructor; intros tf roots finite;
        destruct (total_correct finite) as [fuel [final [Hrun _]]].
      - exists final. exact (@Library.Total.C.E.successful_run_terminates_to fuel tf roots final Hrun).
      - exists fuel, final. exact Hrun.
    Qed.
  End Certificates.
End Make.
