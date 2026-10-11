From Stdlib Require Import ZArith Lia.
From TcSolvers Require Import
  common.Assumptions common.SideUpdate
  common.instances.Chain
  solvers.slr.reluctant_restarting.ReluctantRestartingInterfaces
  solvers.slr.reluctant_restarting.DefaultUpdate.

Module I := ThresholdReluctantRestartingDefault Chain.V.
Module U := I.Base.
Module D := ThresholdIntervalDomain.

(** Check the contracts from a separately compiled client. *)
Module UpdateLaws <: UPDATE_LAWS Chain.V D U := I.BaseLaws.
Module OrdinaryLaws <: ORDINARY_UPDATE_TERMINATION_LAWS Chain.V D U := I.OrdinaryLaws.
Module SideLaws <: SIDE_UPDATE_TERMINATION_LAWS Chain.V D I.SideUpdate := I.Shared.SideLaws.
Module RestartingSideLaws <: RESTARTING_SIDE_UPDATE_TERMINATION_LAWS
  Chain.V D I.SideUpdate := I.SideLaws.

Example ordinary_copy_is_precise :
  U.update false 0 (U.initial_phase false 0) TEmpty (TUpTo 5) =
  (U.BoxW, TUpTo 5).
Proof. reflexivity. Qed.

Example side_starts_with_widening :
  U.update true 1 (U.initial_phase true 1) TEmpty (TUpTo 5) =
  (U.Widen, TUpTo 10).
Proof. reflexivity. Qed.

Example box_enters_narrowing_then_falls_back :
  let first := U.update false 0 U.BoxW TAny (TUpTo 5) in
  let second := U.update false 0 (fst first) (snd first) (TUpTo 6) in
  first = (U.BoxN, TUpTo 5) /\ second = (U.Widen, TUpTo 10).
Proof. split; reflexivity. Qed.

Example side_widening_keeps_old_contributions :
  U.update true 1 U.Widen (TUpTo 10) (TUpTo 0) = (U.Widen, TUpTo 10).
Proof. reflexivity. Qed.

Example covered_side_growth_uses_join :
  I.SideUpdate.update 0 1 (I.SideUpdate.initial_phase 0 1)
    TEmpty (TUpTo 5) (TUpTo 10) = (U.Widen, TUpTo 5).
Proof. reflexivity. Qed.

Example uncovered_side_growth_widens :
  I.SideUpdate.update 0 1 (I.SideUpdate.initial_phase 0 1)
    TEmpty (TUpTo 5) TEmpty = (U.Widen, TUpTo 10).
Proof. reflexivity. Qed.

Example copy_consumes_credit_even_at_the_largest_box_entry :
  I.BaseLaws.remaining_changes U.BoxW TEmpty <
  I.BaseLaws.remaining_changes U.Copy TAny.
Proof. change (11 < 12). lia. Qed.

Goal True. idtac "DefaultUpdate laws proven with assumptions:". Abort.
Print Assumptions UpdateLaws.update_stutter_closed.
Print Assumptions UpdateLaws.update_change_consumes.
Print Assumptions SideLaws.exposed_change_consumes.
Print Assumptions RestartingSideLaws.noncovered_change_consumes.
