From Stdlib Require Import List.
From TcSolvers Require Import common.Assumptions common.BoxUpdate common.FiniteHeight
  solvers.slr.narrowing_fixed_point_compact.NarrowingFixedPoint
  solvers.slr.narrowing_fixed_point_compact.Theorems.
Set Implicit Arguments.

(** The replacement checker compiles this same client body against both
    namespaces, including the reference's proof-law algorithm arguments. *)
Module RuntimeClient (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module N := NarrowingFixedPoint.Make V D U S M Features DL UL SL ML.
  Definition path fuel tf c : N.steps tf c (N.run_fuel fuel tf c) := N.fuel_steps fuel tf c.
End RuntimeClient.

Module CorrectnessClient (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module C := Theorems.Correctness V D U S M Features DL UL SL ML.
  Definition termination : forall tf roots, C.Sem.finite_system tf roots ->
    exists final, C.terminates_to tf roots final := @C.semantic_termination.
  Definition fuel : forall tf roots, C.Sem.finite_system tf roots ->
    exists fuel final, C.N.solve_fuel fuel tf roots = Some final := @C.sufficient_fuel.
  Definition correctness : forall fuel tf roots final,
    C.N.solve_fuel fuel tf roots = Some final -> C.correct_final_state tf roots final := @C.successful_run_correct.
  Definition total : forall tf roots, C.Sem.finite_system tf roots ->
    exists fuel final, C.N.solve_fuel fuel tf roots = Some final /\ C.correct_final_state tf roots final := @C.total_correct.
End CorrectnessClient.

Module LeastClient (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U) (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module C := Theorems.LeastSolutionMake V D U S M Features DL UL UBL SL ML.
  Definition least : forall tf roots (finite : C.Sem.finite_system tf roots),
    C.source_strict_on tf (@C.Sem.support tf roots finite) roots ->
    C.Sem.system_monotone_on tf (@C.Sem.support tf roots finite) ->
    exists fuel final, C.N.solve_fuel fuel tf roots = Some final /\
      C.Sem.least_solution_on tf (@C.Sem.support tf roots finite) (C.R.sigma_value final) := @C.total_least_solution.
End LeastClient.

Module PrecisionClient (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
  Module F := Theorems.Make V D WN.
  Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
    (WS : WIDEN_STABILITY D WN) (UL : UPDATE_LAWS V D F.U).
    Module WithCollections (S : SET V) (M : MAP V) (Features : Base.FEATURES)
      (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
      Module C := F.WithLaws DL WNL WS UL.
      Module Q := C.WithCollections S M Features SL ML.
      Definition fallback : forall tf roots, Q.monotonic_system tf -> Q.avoids_fallback tf roots := @Q.monotonic_avoids_fallback.
      Definition fixed : Features.recompute_controlled = true -> forall fuel tf roots final,
        Q.monotonic_system tf -> Q.N.solve_fuel fuel tf roots = Some final -> Q.narrowing_fixed tf final := @Q.successful_run_fixed.
      Definition initial_path tf roots : Q.N.steps tf (Q.R.initial_config roots) (Q.R.initial_config roots) := Q.N.steps_refl _ _.
    End WithCollections.
  End WithLaws.
End PrecisionClient.

Print Assumptions Theorems.Instances.FixedCells.total_correct.
Print Assumptions Theorems.Instances.Least.total_least_solution.
Print Assumptions Theorems.Instances.FixedCells.E.reachable_no_fallback.
Print Assumptions Theorems.Instances.fixed_run.
