From Stdlib Require Import List.
From TcSolvers Require Import
  common.SolverSpecifications
  common.instances.Chain
  common.Assumptions
  solvers.slr.common.DiscoveryOrderLaws
  common.FiniteHeight
  solvers.slr.simple.proofs.Correctness
  solvers.slr.simple.proofs.LeastSolutionProof.

Set Implicit Arguments.

Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V)
  (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D)
  (UL : UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := Correctness.Make
    V D U S M Rk RankLaws RankFinite DL UL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.

  Module Spec := Internal.Spec.
  Include Spec.

  Definition terminates_to := Sem.terminates_to.

  Theorem semantic_termination : forall tf roots,
    Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
  Proof. exact Internal.solver_terminates. Qed.

  Theorem sufficient_fuel : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final.
  Proof. exact Internal.sufficient_fuel. Qed.

  Theorem successful_run_correct : forall fuel tf roots final,
    R.solve_fuel fuel tf roots = Some final -> correct_final_state tf roots final.
  Proof. exact Internal.solve_fuel_spawn_correct. Qed.

  Corollary total_correct : forall tf roots,
    Sem.finite_system tf roots ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      correct_final_state tf roots final.
  Proof.
    intros tf roots finite.
    destruct (sufficient_fuel finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@successful_run_correct fuel tf roots final Hrun).
  Qed.
End Make.

Module LeastSolutionMake
  (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk)
  (RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).

  Module Internal := LeastSolutionProof.Make
    V D U S M Rk RankLaws RankFinite DL UL UBL SL ML.
  Module Sem := Internal.Sem.
  Module R := Internal.R.

  Module Strict := Internal.Strict.
  Definition source_strict_on :=
    Strict.source_strict_on Sem.observes_at Sem.observed_direct Sem.observed_sides.

  Theorem total_least_solution : forall tf roots (finite : Sem.finite_system tf roots),
    source_strict_on tf (Sem.support finite) roots ->
    Sem.system_monotone_on tf (Sem.support finite) ->
    exists fuel final, R.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof.
    intros tf roots finite Hstrict Hmono.
    destruct (@Internal.Total.sufficient_fuel tf roots finite) as [fuel [final Hrun]].
    exists fuel, final. split; [exact Hrun |].
    exact (@Internal.solve_fuel_least_solution fuel tf roots finite final Hstrict Hmono Hrun).
  Qed.
End LeastSolutionMake.

(** Concrete audits discharge the module laws; the theorems above remain generic. *)
Module Instances.
  Module E := Chain.
  Module Rk := ListDiscoveryOrder E.V.
  Module RankLaws := ListDiscoveryOrderLaws E.V.
  Module RankFinite := ListFiniteDiscoveryOrderLaws E.V.
  Module Correct := Make E.V E.D E.U E.S E.M Rk
    RankLaws RankFinite E.DL E.UL E.SL E.ML.
  Module U := JoinUpdate E.V E.D.
  Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
  Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
  Module Least := LeastSolutionMake E.V E.D U E.S E.M Rk
    RankLaws RankFinite E.DL UL UBL E.SL E.ML.
End Instances.

Goal True. idtac "SLR-TC_S total correctness proven with assumptions:". Abort.
Print Assumptions Instances.Correct.total_correct.

Goal True. idtac "SLR-TC_S leastness proven with assumptions:". Abort.
Print Assumptions Instances.Least.total_least_solution.
