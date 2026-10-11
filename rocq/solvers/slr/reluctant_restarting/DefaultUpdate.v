From TcSolvers Require Export common.instances.DefaultUpdate.
From TcSolvers Require Import
  common.Assumptions
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces.

(** The default policy supplies the stronger side-cell termination contract
    used by reluctant, dormant, dirty-read, and plus restarting. *)
Module ThresholdReluctantRestartingDefault (V : VAR).
  Module Shared := ThresholdDefaultUpdate V.
  Module Base := Shared.Base.
  Module BaseLaws := Shared.BaseLaws.
  Module OrdinaryLaws := Shared.OrdinaryLaws.
  Module Covered := Shared.Covered.
  Module SideUpdate := Shared.SideUpdate.
  Module SideLaws := ReluctantRestartingSideUpdateTerminationLaws
    V ThresholdIntervalDomain Base ThresholdIntervalDomainLaws BaseLaws Covered.
End ThresholdReluctantRestartingDefault.
