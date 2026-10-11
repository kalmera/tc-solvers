From TcSolvers Require Export common.RestartingSideUpdate.

(** Compatibility names for existing clients. The policy laws are shared. *)
Module Type RESTARTING_SIDE_UPDATE_TERMINATION_LAWS :=
  RestartingSideUpdate.RESTARTING_SIDE_UPDATE_TERMINATION_LAWS.
Module ReluctantRestartingSideUpdateTerminationLaws :=
  RestartingSideUpdate.ReluctantRestartingSideUpdateTerminationLaws.
