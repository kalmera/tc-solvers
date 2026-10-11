From Stdlib Require Import List.
From TcSolvers Require Export solvers.slr.dormant_restarting.DormantRestarting common.SolverInterfaces.
From TcSolvers Require Import common.ConstraintSemantics common.SideUpdate.

Import ListNotations.
Set Implicit Arguments.

(* Law-free public views over one executable machine instance. *)
Module Make
  (V : VAR) (D : DOMAIN) (U : UPDATE V D) (SU : SIDE_UPDATE V D)
  (S : SET V) (M : MAP V) (Rk : DISCOVERY_ORDER V)
  (Features : FEATURES)
  <: SolverInterfaces.SOLVER V D.
  Module R := DormantRestarting.Core V D U SU S M Rk Features.
  Module Syntax.
    Definition rhs := R.ConstraintSystem.rhs.
    Definition Ret := R.ConstraintSystem.Ret.
    Definition Get := R.ConstraintSystem.Get.
    Definition Side := R.ConstraintSystem.Side.
    Definition Spawn := R.ConstraintSystem.Spawn.
    Definition system := V.t -> rhs.
  End Syntax.
  Module TransferSemantics := ConstraintSemantics.Make V D Syntax.
  Module ExecutionSemantics.
    Definition step tf before after := R.next_config tf before = Some after.
    Inductive steps tf : R.config -> R.config -> Prop :=
    | StepsRefl : forall c, steps tf c c
    | StepsStep : forall first next final,
        step tf first next -> steps tf next final -> steps tf first final.
    Definition quiescent (st : R.state) := R.queue_peek (R.queue st) = None.
    Definition terminal_config (st : R.state) : R.config :=
      {| R.cfg_state := st; R.cfg_control := R.RunLoop |}.
  End ExecutionSemantics.
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
    Definition lookup := R.semantic_lookup.
    Definition sigma_value := R.sigma_value.
    Definition solve_fuel := R.solve_fuel.
  End View.
  Module Execution <: SolverInterfaces.EXECUTION V D Sem View.
    Definition config := R.config.
    Definition initial_config := R.initial_config.
    Definition terminal_config := ExecutionSemantics.terminal_config.
    Definition steps := ExecutionSemantics.steps.
    Definition quiescent := ExecutionSemantics.quiescent.
  End Execution.
End Make.
