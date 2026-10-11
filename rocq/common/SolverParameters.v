From TcSolvers Require Export
  common.Assumptions common.BoxUpdate common.FiniteHeight common.SideUpdate
  common.RestartingSideUpdate common.SolverFeatures
  solvers.slr.common.DiscoveryOrderLaws.

(** Solver-independent bundles of implementation inputs and proof laws.
    The semantic and execution views remain submodules of the solver. *)

(** Shared implementation inputs and collection/domain laws. *)
Module Type PARAMETERS.
  Declare Module V : VAR.
  Declare Module D : DOMAIN.
  Declare Module S : SET V.
  Declare Module M : MAP V.
  Declare Module Features : RESTARTING_FEATURES.
  Declare Module DL : DOMAIN_LAWS D.
  Declare Module SL : SET_LAWS V S.
  Declare Module ML : MAP_LAWS V M.
End PARAMETERS.

(** Finite-change updates used by the original solvers. *)
Module Type FINITE_UPDATE_PARAMETERS.
  Include PARAMETERS.
  Declare Module U : UPDATE V D.
  Declare Module UL : UPDATE_LAWS V D U.
End FINITE_UPDATE_PARAMETERS.

Module Type FINITE_LEAST_SOLUTION_PARAMETERS.
  Include FINITE_UPDATE_PARAMETERS.
  Declare Module UBL : UPPER_BOUND_UPDATE_LAWS V D U.
End FINITE_LEAST_SOLUTION_PARAMETERS.

Module Type RANKING_PARAMETERS (V : VAR).
  Declare Module Rk : DISCOVERY_ORDER V.
  Declare Module RankLaws : STABLE_DISCOVERY_ORDER_LAWS V Rk.
  Declare Module RankFinite : FINITE_DISCOVERY_ORDER_LAWS V Rk RankLaws.
End RANKING_PARAMETERS.

Module Type RANKED_UPDATE_PARAMETERS.
  Include FINITE_UPDATE_PARAMETERS.
  Include RANKING_PARAMETERS V.
End RANKED_UPDATE_PARAMETERS.

Module Type RANKED_LEAST_SOLUTION_PARAMETERS.
  Include FINITE_LEAST_SOLUTION_PARAMETERS.
  Include RANKING_PARAMETERS V.
End RANKED_LEAST_SOLUTION_PARAMETERS.

Module Type PARTIAL_CORRECTNESS_PARAMETERS.
  Include PARAMETERS.
  Declare Module U : UPDATE V D.
  Declare Module SU : SIDE_UPDATE V D.
  Declare Module OSL : ORDINARY_UPDATE_SOUND_LAWS V D U.
  Declare Module SSL : SIDE_UPDATE_SOUND_LAWS V D SU.
End PARTIAL_CORRECTNESS_PARAMETERS.

(** FIFO spawning uses ascending side credit rather than restarting credit. *)
Module Type ASCENDING_TOTAL_CORRECTNESS_PARAMETERS.
  Include PARAMETERS.
  Declare Module U : UPDATE V D.
  Declare Module SU : SIDE_UPDATE V D.
  Declare Module OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U.
  Declare Module ASUL : SIDE_UPDATE_TERMINATION_LAWS V D SU.
End ASCENDING_TOTAL_CORRECTNESS_PARAMETERS.

Module Type ASCENDING_LEAST_SOLUTION_PARAMETERS.
  Include ASCENDING_TOTAL_CORRECTNESS_PARAMETERS.
  Declare Module UBL : UPPER_BOUND_UPDATE_LAWS V D U.
  Declare Module SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU.
End ASCENDING_LEAST_SOLUTION_PARAMETERS.

Module Type TOTAL_CORRECTNESS_PARAMETERS.
  Include PARAMETERS.
  Declare Module U : UPDATE V D.
  Declare Module SU : SIDE_UPDATE V D.
  Declare Module OUL : ORDINARY_UPDATE_TERMINATION_LAWS V D U.
  Declare Module SUL : RESTARTING_SIDE_UPDATE_TERMINATION_LAWS V D SU.
End TOTAL_CORRECTNESS_PARAMETERS.

Module Type LEAST_SOLUTION_PARAMETERS.
  Include TOTAL_CORRECTNESS_PARAMETERS.
  Declare Module UBL : UPPER_BOUND_UPDATE_LAWS V D U.
  Declare Module SUBL : SIDE_UPPER_BOUND_UPDATE_LAWS V D SU.
End LEAST_SOLUTION_PARAMETERS.

Module Type RANKED_TOTAL_CORRECTNESS_PARAMETERS.
  Include TOTAL_CORRECTNESS_PARAMETERS.
  Include RANKING_PARAMETERS V.
End RANKED_TOTAL_CORRECTNESS_PARAMETERS.

Module Type RANKED_SIDE_LEAST_SOLUTION_PARAMETERS.
  Include LEAST_SOLUTION_PARAMETERS.
  Include RANKING_PARAMETERS V.
End RANKED_SIDE_LEAST_SOLUTION_PARAMETERS.

Module Type RANKED_PARTIAL_CORRECTNESS_PARAMETERS.
  Include PARTIAL_CORRECTNESS_PARAMETERS.
  Include RANKING_PARAMETERS V.
End RANKED_PARTIAL_CORRECTNESS_PARAMETERS.

(** Narrowing uses an existing OneBox update, so the policy and its laws
    refer to the same phase type. No solver theorem factory is required. *)
Module Type NARROWING_PARAMETERS (V : VAR) (D : DOMAIN).
  Declare Module WN : WIDEN_NARROW D.
  Declare Module WNL : WIDEN_NARROW_LAWS D WN.
  Declare Module FixedU : ONE_BOX_UPDATE V D WN.
  Declare Module FixedUL : UPDATE_LAWS V D FixedU.
  Declare Module FixedSU : SIDE_UPDATE V D.
  Declare Module FixedSUL : SIDE_UPDATE_SOUND_LAWS V D FixedSU.
End NARROWING_PARAMETERS.

Module Type ORDINARY_FIXED_POINT_PARAMETERS.
  Include PARAMETERS.
  Include NARROWING_PARAMETERS V D.
End ORDINARY_FIXED_POINT_PARAMETERS.

Module Type STABLE_FIXED_POINT_PARAMETERS.
  Include ORDINARY_FIXED_POINT_PARAMETERS.
  Declare Module WS : WIDEN_STABILITY D WN.
End STABLE_FIXED_POINT_PARAMETERS.

Module Type COMPLETE_PARAMETERS.
  Include LEAST_SOLUTION_PARAMETERS.
  Include NARROWING_PARAMETERS V D.
End COMPLETE_PARAMETERS.
