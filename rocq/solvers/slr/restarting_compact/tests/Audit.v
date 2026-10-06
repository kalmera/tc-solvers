From TcSolvers Require Import common.instances.Chain common.FiniteHeight
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting_compact.Proofs.

(** Instantiate the proof functor once. Concrete audits do not live in the
    generic proof unit, so clients do not pay for these instantiations. *)
Module E := Chain.
Module Ranks := ListDiscoveryOrder E.V.
Module RL := ListDiscoveryOrderLaws E.V.
Module RF := ListFiniteDiscoveryOrderLaws E.V.
Module U := JoinUpdate E.V E.D.
Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
Module P := Proofs.Make E.V E.D U E.S E.M Ranks Restarting.AllEnabledFeatures
  RL RF E.DL UL E.SL E.ML.

Definition successful_run_below := P.successful_run_below UBL.update_preserves_upper_bound.

Print Assumptions P.reachable_configuration_wf.
Print Assumptions P.reachable_owners_unique.
Print Assumptions P.successful_roots_materialized.
Print Assumptions P.ordinary_aggregate.
Print Assumptions P.watched_commit.
Print Assumptions P.completed_is_post_solution.
Print Assumptions P.commit_completed_observation.
Print Assumptions P.termination_iff_fuel.
Print Assumptions P.correct_successful_run_least.
Print Assumptions P.quiet_controlled_commit.
Print Assumptions P.quiet_commit_narrowing_fixed.
Print Assumptions successful_run_below.
