From TcSolvers Require Export common.Assumptions common.FiniteHeight
  solvers.slr.narrowing_fixed_point_compact.Proofs
  solvers.slr.narrowing_fixed_point_compact.Precision.
Set Implicit Arguments.

(** Generic UPDATE termination and correctness; the OneBox interface additionally
    exposes monotonic_avoids_fallback and successful_run_fixed. Fixedness includes
    stored incoming contributions and requires recompute_controlled = true. *)
Module Correctness := Proofs.Make.
Module Make := Precision.Make.

Module LeastSolutionMake (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
  (UBL : UPPER_BOUND_UPDATE_LAWS V D U)
  (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
  Module Internal := Proofs.Make V D U S M Features DL UL SL ML.
  Module R := Internal.R.
  Module N := Internal.N.
  Module Sem := Internal.Sem.
  Definition source_strict_on := Internal.B.source_strict_on.
  Theorem total_least_solution tf roots (finite : Sem.finite_system tf roots) :
    source_strict_on tf (Sem.support finite) roots -> Sem.system_monotone_on tf (Sem.support finite) ->
    exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      Sem.least_solution_on tf (Sem.support finite) (R.sigma_value final).
  Proof. exact (@Internal.total_least_solution tf roots finite UBL.update_preserves_upper_bound). Qed.
End LeastSolutionMake.
