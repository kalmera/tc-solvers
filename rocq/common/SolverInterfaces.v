From Stdlib Require Import List.
From TcSolvers Require Export common.Interfaces common.SolverSpecifications.

Set Implicit Arguments.

(** Law-free signatures implemented by solvers. This file contains no
    certificate proofs or admitted theorem consequences. *)
Module Type SEMANTICS (V : VAR) (D : DOMAIN).
  Include SolverSpecifications.TRANSFER V D.
  Parameter observed_direct : observation -> D.t.
  Parameter finite_system : (V.t -> rhs) -> list V.t -> Type.
  Parameter support : forall tf roots, finite_system tf roots -> list V.t.
  Parameter system_monotone_on : (V.t -> rhs) -> list V.t -> Prop.
  Parameter least_solution_on :
    (V.t -> rhs) -> list V.t -> (V.t -> D.t) -> Prop.
End SEMANTICS.

(** [lookup] is semantic lookup: dormant bottom unknowns count as solved.
    [sigma_value] is the total valuation used for bounds and leastness. *)
Module Type SOLVER_VIEW (V : VAR) (D : DOMAIN) (Sem : SEMANTICS V D).
  Include SolverSpecifications.STORE V D.
  Parameter solve_fuel : nat -> (V.t -> Sem.rhs) -> list V.t -> option state.
End SOLVER_VIEW.

Module Type EXECUTION (V : VAR) (D : DOMAIN) (Sem : SEMANTICS V D)
  (R : SOLVER_VIEW V D Sem).
  Parameter config : Type.
  Parameter initial_config : list V.t -> config.
  Parameter terminal_config : R.state -> config.
  Parameter steps : (V.t -> Sem.rhs) -> config -> config -> Prop.
  Parameter quiescent : R.state -> Prop.
End EXECUTION.

(** A solver exports all three views over one machine instance. *)
Module Type SOLVER (V : VAR) (D : DOMAIN).
  Declare Module Sem : SEMANTICS V D.
  Declare Module View : SOLVER_VIEW V D Sem.
  Declare Module Execution : EXECUTION V D Sem View.
End SOLVER.
