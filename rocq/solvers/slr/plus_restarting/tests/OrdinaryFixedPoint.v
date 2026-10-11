From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.ReluctantUpdate
  solvers.slr.plus_restarting.PlusRestarting.
Import ListNotations.

Module E := Chain.
Module SU := ReluctantSideUpdate E.V E.D E.U.
Module Enabled := PlusRestarting.Make E.V E.D E.U SU E.S E.M
  PlusRestarting.AllEnabledFeatures.
Module Disabled := PlusRestarting.Make E.V E.D E.U SU E.S E.M
  PlusRestarting.ReaderWakeupsOnlyFeatures.

(** The back edge controls owner 0, whose RHS never reads itself.
    Slow narrowing needs several updates with the returned phase. *)
Definition enabled_tf owner : Enabled.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    Enabled.ConstraintSystem.Get 1 (fun _ => Enabled.ConstraintSystem.Ret E.D.One)
  else Enabled.ConstraintSystem.Get 0 (fun _ => Enabled.ConstraintSystem.Ret E.D.Bot).
Definition disabled_tf owner : Disabled.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then
    Disabled.ConstraintSystem.Get 1 (fun _ => Disabled.ConstraintSystem.Ret E.D.One)
  else Disabled.ConstraintSystem.Get 0 (fun _ => Disabled.ConstraintSystem.Ret E.D.Bot).

Example controlled_recomputation_reaches_fixedness :
  exists final,
    Enabled.solve_fuel 200 enabled_tf [0] = Some final /\
    Enabled.sigma_value final 0 = E.D.One /\
    E.WN.narrow (Enabled.sigma_value final 0) E.D.One =
      Enabled.sigma_value final 0.
Proof. eexists. vm_compute. repeat split; reflexivity. Qed.

Example reader_wakeups_alone_leave_unfinished_narrowing :
  exists final,
    Disabled.solve_fuel 200 disabled_tf [0] = Some final /\
    Disabled.sigma_value final 0 = E.D.Top /\
    E.WN.narrow (Disabled.sigma_value final 0) E.D.One <>
      Disabled.sigma_value final 0.
Proof. eexists. vm_compute. repeat split; congruence. Qed.

Definition controlled_state : Enabled.state :=
  let st := Enabled.materialize (Enabled.observe Enabled.empty_state 0) 0 in
  Enabled.promote_controlled
    (Enabled.with_sigma st (E.M.update (Enabled.sigma st) 0 E.D.Top)) 0.
Definition changed_commit := Enabled.set_value controlled_state
  (Enabled.fresh_frame controlled_state 0 E.U.BoxW) E.D.One.

Example changed_commit_requeues_owner_and_returns_narrowing_phase :
  Enabled.queue (fst changed_commit) = [0] /\
  Enabled.frame_phase (snd changed_commit) = E.U.BoxN /\
  Enabled.sigma_value (fst changed_commit) 0 = E.D.Three.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example drain_preserves_returned_phase :
  match Enabled.next_config enabled_tf
    {| Enabled.cfg_state := fst changed_commit;
       Enabled.cfg_control := Enabled.RunDrain (snd changed_commit) Enabled.KLoop |} with
  | Some c => match Enabled.cfg_control c with
    | Enabled.RunRhs fr _ _ => Enabled.frame_phase fr = E.U.BoxN
    | _ => False end
  | None => False end.
Proof. vm_compute. reflexivity. Qed.

Definition stable_state := Enabled.with_sigma controlled_state
  (E.M.update (Enabled.sigma controlled_state) 0 E.D.One).
Example unchanged_commit_does_not_requeue :
  Enabled.queue (fst (Enabled.set_value stable_state
    (Enabled.fresh_frame stable_state 0 E.U.BoxN) E.D.One)) = [].
Proof. vm_compute. reflexivity. Qed.

Definition spawning_tf owner : Enabled.ConstraintSystem.rhs :=
  if E.V.eq_dec owner 0 then Enabled.ConstraintSystem.Get 1
    (fun _ => Enabled.ConstraintSystem.Spawn 2
      (Enabled.ConstraintSystem.Spawn 2 (Enabled.ConstraintSystem.Ret E.D.One)))
  else if E.V.eq_dec owner 1 then
    Enabled.ConstraintSystem.Get 0 (fun _ => Enabled.ConstraintSystem.Ret E.D.Bot)
  else Enabled.ConstraintSystem.Ret E.D.Bot.

Example recomputation_completes_duplicate_dormant_spawn :
  exists final, Enabled.solve_fuel 300 spawning_tf [0] = Some final /\
    Enabled.sigma_value final 0 = E.D.One /\
    Enabled.pending_spawns final = [] /\
    E.S.mem 2 (Enabled.dormant_bottom final) = true /\
    E.S.elements (Enabled.requested_spawns final) = [2].
Proof. eexists. vm_compute. repeat split; reflexivity. Qed.
