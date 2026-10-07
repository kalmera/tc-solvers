From Stdlib Require Import List.
From TcSolvers Require Import common.Assumptions common.BoxUpdate common.FiniteHeight
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting_compact.Restarting
  solvers.slr.restarting_compact.Theorems.
Set Implicit Arguments.

(** These clients use the reference's functor parameters and exact theorem
    argument order. The replacement checker also compiles this same body
    against the reference namespace. *)
Module CorrectnessClient (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V) (Features : Restarting.FEATURES)
  (RL : STABLE_DISCOVERY_ORDER_LAWS V Rk) (RF : FINITE_DISCOVERY_ORDER_LAWS V Rk RL)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module C := Theorems.Make V D U S M Rk Features RL RF DL UL SL ML.
  Definition termination : forall tf roots, C.Sem.finite_system tf roots ->
    exists final, C.terminates_to tf roots final := @C.semantic_termination.
  Definition fuel : forall tf roots, C.Sem.finite_system tf roots ->
    exists fuel final, C.R.solve_fuel fuel tf roots = Some final := @C.sufficient_fuel.
  Definition correctness : forall fuel tf roots final,
    C.R.solve_fuel fuel tf roots = Some final -> C.correct_final_state tf roots final := @C.successful_run_correct.
  Definition total : forall tf roots, C.Sem.finite_system tf roots ->
    exists fuel final, C.R.solve_fuel fuel tf roots = Some final /\ C.correct_final_state tf roots final := @C.total_correct.
  Definition initial_path tf roots : C.Sem.steps tf (C.R.initial_config roots) (C.R.initial_config roots) := C.Sem.StepsRefl _ _.
End CorrectnessClient.

Module LeastClient (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V) (Features : Restarting.FEATURES)
  (RL : STABLE_DISCOVERY_ORDER_LAWS V Rk) (RF : FINITE_DISCOVERY_ORDER_LAWS V Rk RL)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U) (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module C := Theorems.LeastSolutionMake V D U S M Rk Features RL RF DL UL UBL SL ML.
  Definition least : forall tf roots (finite : C.Sem.finite_system tf roots),
    C.source_strict_on tf (C.Sem.support finite) roots ->
    C.Sem.system_monotone_on tf (C.Sem.support finite) ->
    exists fuel final, C.R.solve_fuel fuel tf roots = Some final /\
      C.Sem.least_solution_on tf (C.Sem.support finite) (C.R.sigma_value final) := @C.total_least_solution.
End LeastClient.

Module OrdinaryClient (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module F := Theorems.OrdinaryFixedPointMake V D WN.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN) (UL : UPDATE_LAWS V D F.U).
    Module WithCollections (S : SET V) (M : MAP V) (Features : Restarting.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module C := F.WithLaws DL WNL UL.
      Module Q := C.WithCollections S M Features SL ML.
      Definition fallback : forall tf roots, Q.Sem.finite_system tf roots ->
        Q.monotonic_system tf -> Q.no_side_effects tf -> Q.avoids_fallback tf roots := @Q.ordinary_avoids_fallback.
      Definition fixed : Features.recompute_controlled = true -> forall fuel tf roots final,
        Q.Sem.finite_system tf roots -> Q.monotonic_system tf -> Q.no_side_effects tf ->
        Q.R.solve_fuel fuel tf roots = Some final -> Q.narrowing_fixed tf final := @Q.successful_run_fixed.
    End WithCollections.
  End WithLaws.
End OrdinaryClient.

Print Assumptions Theorems.Instances.Correct.total_correct.
Print Assumptions Theorems.Instances.Least.total_least_solution.
Print Assumptions Theorems.Instances.Ordinary.ordinary_avoids_fallback.
Print Assumptions Theorems.Instances.OrdinaryReaderWakeups.ordinary_avoids_fallback.
Print Assumptions Theorems.Instances.ordinary_fixed.
