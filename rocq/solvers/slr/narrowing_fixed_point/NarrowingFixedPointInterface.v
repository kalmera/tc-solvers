From Stdlib Require Import List.
From TcSolvers Require Export solvers.slr.narrowing_fixed_point.NarrowingFixedPoint common.SolverInterfaces.
From TcSolvers Require Import common.ConstraintSemantics.

Import ListNotations.
Set Implicit Arguments.

(* Law-free public views of the batched machine over a supplied core. *)
Module WithCore (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Ranks : DISCOVERY_ORDER V) (Features : Base.FEATURES)
  (Core : CORE V D U S M Ranks Features)
  <: SolverInterfaces.SOLVER V D.
  Module R := Core.
  (* Pass the core directly so opaque runtime lemmas retain its module path. *)
  Module N := NarrowingFixedPoint.WithCore V D U S M Ranks Features Core.
  Module Syntax.
    Definition rhs := R.ConstraintSystem.rhs.
    Definition Ret := R.ConstraintSystem.Ret.
    Definition Get := R.ConstraintSystem.Get.
    Definition Side := R.ConstraintSystem.Side.
    Definition Spawn := R.ConstraintSystem.Spawn.
    Definition system := V.t -> rhs.
  End Syntax.
  Module TransferSemantics := ConstraintSemantics.Make V D Syntax.
  Definition quiescent (st : R.state) := R.queue st = [].
  Definition terminal_config (st : R.state) : R.config :=
    {| R.cfg_state := st; R.cfg_control := R.RunLoop |}.
  Module Sem <: SolverInterfaces.SEMANTICS V D.
    Definition rhs := Syntax.rhs.
    Definition observation := TransferSemantics.observation.
    Definition observed_direct := TransferSemantics.observed_direct.
    Definition observed_sides := TransferSemantics.observed_sides.
    Definition observed_spawns := TransferSemantics.observed_spawns.
    Definition observes_at := TransferSemantics.observes_at.
    Definition rhs_observes := TransferSemantics.rhs_observes.
    Definition rhs_eval_with := TransferSemantics.rhs_eval_with.
    Definition rhs_dependencies_monotone := TransferSemantics.rhs_dependencies_monotone.
    Definition rhs_effects_monotone := TransferSemantics.rhs_effects_monotone.
    Definition finite_system := TransferSemantics.finite_system.
    Definition support := TransferSemantics.support.
    Definition system_monotone_on := TransferSemantics.system_monotone_on.
    Definition least_solution_on := TransferSemantics.least_solution_on.
  End Sem.
  Module View <: SolverInterfaces.SOLVER_VIEW V D Sem.
    Definition state := R.state.
    Definition lookup := fun final target => M.lookup (R.sigma final) target.
    Definition sigma_value := R.sigma_value.
    Definition solve_fuel := N.solve_fuel.
  End View.
  Module Execution <: SolverInterfaces.EXECUTION V D Sem View.
    Definition config := R.config.
    Definition initial_config := R.initial_config.
    Definition terminal_config := terminal_config.
    Definition steps := N.steps.
    Definition quiescent := quiescent.
  End Execution.
End WithCore.

Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
  (S : SET V) (M : MAP V) (Features : Base.FEATURES)
  <: SolverInterfaces.SOLVER V D.
  Module Ranks := ListDiscoveryOrder V.
  Module Core := Base.Make V D U S M Ranks Features.
  Include WithCore V D U S M Ranks Features Core.
End Make.
