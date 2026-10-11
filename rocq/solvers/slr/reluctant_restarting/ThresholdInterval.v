From TcSolvers Require Import
  common.Assumptions
  common.ThresholdInterval
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces.

(** The threshold OneBox instance also satisfies the stronger restarting
    contract.  Covered joins use the shared quantitative bridge; every
    changed narrowing, dead-side update, or uncovered widening consumes the
    underlying OneBox credit. *)
Module ThresholdReluctantRestartingOneBox (V : VAR).
  Module Shared := ThresholdReluctantOneBox V.
  Module BaseLaws := Shared.BaseLaws.
  Module Base := Shared.Base.
  Module OrdinaryLaws := Shared.OrdinaryLaws.
  Module Covered := Shared.Covered.
  Module SideUpdate := Shared.SideUpdate.
  Module SideLaws := ReluctantRestartingSideUpdateTerminationLaws
    V ThresholdIntervalDomain Base ThresholdIntervalDomainLaws
    BaseLaws Covered.
End ThresholdReluctantRestartingOneBox.
