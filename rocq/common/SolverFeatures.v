From TcSolvers Require Import common.Interfaces.

(** Feature switches for restarting solvers with optional spawn deferral. *)
Module Type RESTARTING_FEATURES.
  Parameter recompute_controlled : bool.
  Parameter defer_spawns : bool.
  Parameter restart_side_phases : bool.
  Parameter eliminate_dead_sides : bool.
End RESTARTING_FEATURES.

Module AllEnabledFeatures <: RESTARTING_FEATURES.
  Definition recompute_controlled := true.
  Definition defer_spawns := true.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := true.
End AllEnabledFeatures.
