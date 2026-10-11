From Stdlib Require Import List ZArith Lia.
From TcSolvers Require Import
  common.Collections
  common.ReluctantUpdate
  common.ThresholdInterval
  solvers.slr.dirty_read_restarting.DirtyReadRestarting
  solvers.slr.reluctant_restarting.ThresholdInterval.

Import ListNotations.
Open Scope Z_scope.

Module V <: VAR.
  Definition t := Z.
  Definition eq_dec := Z.eq_dec.
End V.

Module I := ThresholdReluctantRestartingOneBox V.
Module D := ThresholdIntervalDomain.
Module R := DirtyReadRestarting.FirstDiscoveryAlgorithm
  V D I.Base I.SideUpdate.

Definition ranked_state : R.state :=
  R.observe (R.observe R.empty_state 2) 0.

Definition with_other_contribution (value : D.t) : R.state :=
  R.with_contributions ranked_state
    (R.update_map (R.contributions ranked_state) 2 1 value).

Definition side_config (other input : D.t) : R.config :=
  let st := with_other_contribution other in
  let fr := R.fresh_frame st 0 I.Base.BoxW in
  {| R.cfg_state := st;
     R.cfg_control := R.RunRhs fr
       (R.ConstraintSystem.Side 2 input (R.ConstraintSystem.Ret D.bottom))
       R.KLoop |}.

Definition unused_system (_ : V.t) : R.ConstraintSystem.rhs :=
  R.ConstraintSystem.Ret D.bottom.

Example covered_growth_uses_join_and_does_not_enqueue :
  match R.next_config unused_system
    (side_config (TUpTo 10) (TUpTo 5)) with
  | Some next =>
      R.stored_contribution (R.cfg_state next) 0 2 = TUpTo 5 /\
      R.aggregate (R.cfg_state next) 2 = TUpTo 10 /\
      R.queue (R.cfg_state next) = []
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example uncovered_growth_widens_and_enqueues :
  match R.next_config unused_system
    (side_config TEmpty (TUpTo 5)) with
  | Some next =>
      R.stored_contribution (R.cfg_state next) 0 2 = TUpTo 10 /\
      R.aggregate (R.cfg_state next) 2 = TUpTo 10 /\
      R.queue (R.cfg_state next) = [2]
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example repeated_side_inputs_accumulate_locally :
  let fr0 := R.fresh_frame ranked_state 0 I.Base.BoxW in
  let '(fr1, first) := R.record_side_input fr0 2 (TUpTo 0) in
  let '(_, second) := R.record_side_input fr1 2 (TUpTo 5) in
  first = TUpTo 0 /\ second = TUpTo 5.
Proof. vm_compute. auto. Qed.

Example reset_restores_initial_side_phase :
  let changed :=
    {| R.side_phase := I.Base.Widen; R.side_reset_at := Some 0 |} in
  let cells := R.update_map (R.side_cells R.empty_state) 0 2 changed in
  let reset := R.reset_cells [(0, 2)] cells in
  match R.M.lookup (R.lookup_map reset 0) 2 with
  | Some cell => R.side_phase cell = I.Base.BoxW
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example covered_branch_preserves_base_phase :
  fst (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxN
    (TUpTo 0) (TUpTo 5) (TUpTo 10)) =
  fst (I.Base.update true (2%Z) I.Base.BoxN (TUpTo 0) (TUpTo 5)).
Proof. reflexivity. Qed.

Example covered_join_credit_nonincreasing :
  (I.SideLaws.remaining_changes
      (fst (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW
        (TUpTo 0) (TUpTo 5) (TUpTo 10)))
      (snd (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW
        (TUpTo 0) (TUpTo 5) (TUpTo 10))) <=
   I.SideLaws.remaining_changes I.Base.BoxW (TUpTo 0))%nat.
Proof. reflexivity. Qed.

Example uncovered_growth_consumes_credit :
  (I.SideLaws.remaining_changes
      (fst (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW
        (TUpTo 0) (TUpTo 5) (TUpTo 0)))
      (snd (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW
        (TUpTo 0) (TUpTo 5) (TUpTo 0))) <
   I.SideLaws.remaining_changes I.Base.BoxW (TUpTo 0))%nat.
Proof. vm_compute. lia. Qed.

(** Dead-side elimination is the restarting-specific downward case. *)
Example dead_side_shrink_consumes_credit :
  (I.SideLaws.remaining_changes
      (fst (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW TAny TEmpty TAny))
      (snd (I.SideUpdate.update (0%Z) (2%Z) I.Base.BoxW TAny TEmpty TAny)) <
   I.SideLaws.remaining_changes I.Base.BoxW TAny)%nat.
Proof. vm_compute. lia. Qed.

Module FeaturesTF <: DirtyReadRestarting.FEATURES.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := false.
End FeaturesTF.
Module FeaturesFT <: DirtyReadRestarting.FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := true.
End FeaturesFT.
Module FeaturesFF <: DirtyReadRestarting.FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End FeaturesFF.

Module S := ListSet V.
Module M := AssocMap V.

(** All feature branches share the same reluctant machine interface. *)
Module MachineTT := DirtyReadRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M
  DirtyReadRestarting.AllEnabledFeatures.
Module MachineTF := DirtyReadRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M FeaturesTF.
Module MachineFT := DirtyReadRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M FeaturesFT.
Module MachineFF := DirtyReadRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M FeaturesFF.

Close Scope Z_scope.

Open Scope Z_scope.

Module DormantBase <: UPDATE V D.
  Definition phase := nat.
  Definition initial_phase (_ : bool) (_ : V.t) := 0%nat.
  Definition update
    (_ : bool) (_ : V.t) (current : nat) (old input : D.t) :=
    (Datatypes.S current, input).
End DormantBase.

Module DormantSU := ReluctantSideUpdate V D DormantBase.
Module DR := DirtyReadRestarting.FirstDiscoveryAlgorithm
  V D DormantBase DormantSU.

Definition dormant_system (owner : V.t) : DR.ConstraintSystem.rhs :=
  if Z.eq_dec owner 0 then
    DR.ConstraintSystem.Get 1
      (fun _ => DR.ConstraintSystem.Ret D.bottom)
  else if Z.eq_dec owner 1 then
    DR.ConstraintSystem.Ret D.bottom
  else if Z.eq_dec owner 2 then
    DR.ConstraintSystem.Side 1 (TUpTo 3)
      (DR.ConstraintSystem.Ret D.bottom)
  else if Z.eq_dec owner 3 then
    DR.ConstraintSystem.Spawn 1 (DR.ConstraintSystem.Ret D.bottom)
  else DR.ConstraintSystem.Ret D.bottom.

Example pure_bottom_root_is_rankless_and_unmaterialized :
  match DR.solve_fuel 20 dormant_system [1] with
  | Some final =>
      DR.is_dormant final 1 = true /\
      DR.Ranking.lookup (DR.ranking final) 1 = None /\
      DR.semantic_lookup final 1 = Some D.bottom /\
      DR.is_materialized final 1 = false
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example dormant_get_records_reader_without_target_rank :
  match DR.solve_fuel 50 dormant_system [0] with
  | Some final =>
      DR.Ranking.lookup (DR.ranking final) 0 = Some 0%nat /\
      DR.is_dormant final 1 = true /\
      DR.S.mem 0 (DR.lookup_set (DR.readers final) 1) = true
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example dormant_spawn_stays_rankless :
  match DR.solve_fuel 50 dormant_system [3] with
  | Some final =>
      DR.Ranking.lookup (DR.ranking final) 3 = Some 0%nat /\
      DR.is_dormant final 1 = true
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example incoming_side_promotes_and_publishes_dormant_target :
  match DR.solve_fuel 100 dormant_system [0; 2] with
  | Some final =>
      DR.Ranking.lookup (DR.ranking final) 0 = Some 0%nat /\
      DR.Ranking.lookup (DR.ranking final) 2 = Some 1%nat /\
      DR.Ranking.lookup (DR.ranking final) 1 = Some 2%nat /\
      DR.sigma_value final 1 = TUpTo 3 /\
      DR.S.mem 0 (DR.lookup_set (DR.readers final) 1) = true
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Focused Dirty-Read Restarting control tests. *)
Module Dirty := DirtyReadRestarting.FirstDiscoveryAlgorithm
  V D I.Base I.SideUpdate.

Definition dirty_ranked_state : Dirty.state :=
  Dirty.observe (Dirty.observe Dirty.empty_state 0) 1.

Definition pending_target_state (value : D.t) : Dirty.state :=
  let st0 := Dirty.materialize dirty_ranked_state 1 in
  let st1 := Dirty.with_contributions st0
    (Dirty.update_map (Dirty.contributions st0) 1 0 value) in
  Dirty.mark_side_dirty (Dirty.enqueue st1 1) 1.

Definition dirty_system (_ : V.t) : Dirty.ConstraintSystem.rhs :=
  Dirty.ConstraintSystem.Ret D.bottom.

Definition dirty_get_config (st : Dirty.state) : Dirty.config :=
  let fr := Dirty.fresh_frame st 0 I.Base.BoxW in
  {| Dirty.cfg_state := st;
     Dirty.cfg_control := Dirty.RunRhs fr
       (Dirty.ConstraintSystem.Get 1
         (fun _ => Dirty.ConstraintSystem.Ret D.bottom))
       Dirty.KLoop |}.

Example increasing_dirty_read_publishes_and_cancels :
  match Dirty.next_config dirty_system
    (dirty_get_config (pending_target_state (TUpTo 5))) with
  | Some next =>
      Dirty.sigma_value (Dirty.cfg_state next) 1 = TUpTo 5 /\
      Dirty.is_side_dirty (Dirty.cfg_state next) 1 = false /\
      Dirty.queue (Dirty.cfg_state next) = [] /\
      Dirty.S.mem 1 (Dirty.controlled (Dirty.cfg_state next)) = true /\
      Dirty.S.mem 0
        (Dirty.lookup_set (Dirty.readers (Dirty.cfg_state next)) 1) = true
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Definition pending_target_with_reader : Dirty.state :=
  let st := pending_target_state (TUpTo 5) in
  Dirty.with_readers st
    (Dirty.M.update (Dirty.readers st) 1
      (Dirty.S.add 2 Dirty.S.empty)).

Example dirty_read_defers_old_reader_wakeup :
  match Dirty.next_config dirty_system
    (dirty_get_config pending_target_with_reader) with
  | Some next =>
      Dirty.queue (Dirty.cfg_state next) = [] /\
      List.In 2 (Dirty.deferred_wakes (Dirty.cfg_state next))
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example deferred_reader_wakes_at_commit :
  match Dirty.next_config dirty_system
    (dirty_get_config pending_target_with_reader) with
  | Some read_next =>
      match Dirty.cfg_control read_next with
      | Dirty.RunRhs fr _ k =>
          match Dirty.next_config dirty_system
            {| Dirty.cfg_state := Dirty.cfg_state read_next;
               Dirty.cfg_control := Dirty.RunCommit fr D.bottom k |} with
          | Some commit_next =>
              List.In 2 (Dirty.queue (Dirty.cfg_state commit_next)) /\
              Dirty.deferred_wakes (Dirty.cfg_state commit_next) = []
          | None => False
          end
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. auto. Qed.

(** A stale dependency of the currently evaluated owner is a genuine wake,
    not merely a queue-frontier artefact.  The dirty publication changes the
    target, the commit flushes the owner wake, and [RunDrain] starts another
    owner round even though the owner's stored value did not change.  The
    termination proof must therefore charge this round to the consumed
    target-side obligation rather than to the owner's ordinary credit. *)
Definition pending_target_with_owner_reader : Dirty.state :=
  let st := pending_target_state (TUpTo 5) in
  Dirty.with_readers st
    (Dirty.M.update (Dirty.readers st) 1
      (Dirty.S.add 0 Dirty.S.empty)).

Example dirty_read_can_rerun_unchanged_owner :
  match Dirty.next_config dirty_system
    (dirty_get_config pending_target_with_owner_reader) with
  | Some read_next =>
      match Dirty.cfg_control read_next with
      | Dirty.RunRhs fr _ k =>
          match Dirty.next_config dirty_system
            {| Dirty.cfg_state := Dirty.cfg_state read_next;
               Dirty.cfg_control := Dirty.RunCommit fr D.bottom k |} with
          | Some commit_next =>
              match Dirty.next_config dirty_system commit_next with
              | Some rerun_next =>
                  Dirty.sigma_value (Dirty.cfg_state rerun_next) 0 =
                    Dirty.sigma_value pending_target_with_owner_reader 0 /\
                  match Dirty.cfg_control rerun_next with
                  | Dirty.RunRhs rerun _ _ => Dirty.frame_owner rerun = 0
                  | _ => False
                  end
              | None => False
              end
          | None => False
          end
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example controlled_dirty_read_uses_fresh_boxw_update :
  let st := Dirty.promote_controlled (pending_target_state (TUpTo 5)) 1 in
  match Dirty.next_config dirty_system (dirty_get_config st) with
  | Some next =>
      Dirty.sigma_value (Dirty.cfg_state next) 1 = TUpTo 10 /\
      Dirty.is_side_dirty (Dirty.cfg_state next) 1 = false /\
      Dirty.queue (Dirty.cfg_state next) = []
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example equal_dirty_read_does_not_call_the_update :
  let st0 := Dirty.materialize dirty_ranked_state 1 in
  let st1 := Dirty.mark_side_dirty (Dirty.enqueue st0 1) 1 in
  let st2 := Dirty.promote_controlled st1 1 in
  match Dirty.next_config dirty_system (dirty_get_config st2) with
  | Some next =>
      Dirty.sigma_value (Dirty.cfg_state next) 1 = TEmpty /\
      Dirty.is_side_dirty (Dirty.cfg_state next) 1 = false /\
      Dirty.queue (Dirty.cfg_state next) = []
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Module RejectUpdate <: UPDATE V D.
  Definition phase := unit.
  Definition initial_phase (_ : bool) (_ : V.t) := tt.
  Definition update
    (_ : bool) (_ : V.t) (_ : phase) (_ _ : D.t) := (tt, TEmpty).
End RejectUpdate.

Module RejectSide := ReluctantSideUpdate V D RejectUpdate.
Module RejectDirty := DirtyReadRestarting.FirstDiscoveryAlgorithm
  V D RejectUpdate RejectSide.

Definition reject_state : RejectDirty.state :=
  let st0 := RejectDirty.observe
    (RejectDirty.observe RejectDirty.empty_state 0) 1 in
  let st1 := RejectDirty.materialize st0 1 in
  let st2 := RejectDirty.with_sigma st1
    (RejectDirty.M.update (RejectDirty.sigma st1) 1 (TUpTo 5)) in
  let st3 := RejectDirty.with_contributions st2
    (RejectDirty.update_map (RejectDirty.contributions st2) 1 0 TAny) in
  RejectDirty.promote_controlled
    (RejectDirty.mark_side_dirty (RejectDirty.enqueue st3 1) 1) 1.

Definition reject_system (_ : V.t) : RejectDirty.ConstraintSystem.rhs :=
  RejectDirty.ConstraintSystem.Ret D.bottom.

Example decreasing_dirty_update_is_rejected :
  RejectDirty.try_dirty_read reject_system reject_state 0 1 = None /\
  RejectDirty.is_side_dirty reject_state 1 = true /\
  RejectDirty.queue reject_state = [1].
Proof. vm_compute. auto. Qed.

Example self_read_is_not_flushed :
  Dirty.try_dirty_read dirty_system (pending_target_state (TUpTo 5)) 1 1 =
  None.
Proof. vm_compute. reflexivity. Qed.

Definition effectful_target_system (owner : V.t) : Dirty.ConstraintSystem.rhs :=
  if Z.eq_dec owner 1 then
    Dirty.ConstraintSystem.Get 2
      (fun _ => Dirty.ConstraintSystem.Ret D.bottom)
  else Dirty.ConstraintSystem.Ret D.bottom.

Example effectful_target_is_not_flushed :
  Dirty.try_dirty_read effectful_target_system
    (pending_target_state (TUpTo 5)) 0 1 = None.
Proof. vm_compute. reflexivity. Qed.

Definition dead_dirty_state : Dirty.state :=
  let st0 := Dirty.materialize dirty_ranked_state 1 in
  Dirty.with_contributions st0
    (Dirty.update_map (Dirty.contributions st0) 1 0 TAny).

Definition dead_dirty_config : Dirty.config :=
  let fr := Dirty.fresh_frame dead_dirty_state 0 I.Base.BoxW in
  {| Dirty.cfg_state := dead_dirty_state;
     Dirty.cfg_control := Dirty.RunDead fr D.bottom [1] Dirty.KLoop |}.

Example dead_side_change_marks_target_dirty :
  match Dirty.next_config dirty_system dead_dirty_config with
  | Some next =>
      Dirty.is_side_dirty (Dirty.cfg_state next) 1 = true /\
      Dirty.queue (Dirty.cfg_state next) = [1]
  | None => False
  end.
Proof. vm_compute. auto. Qed.

Example normal_episode_clears_dirty :
  let st := pending_target_state (TUpTo 5) in
  match Dirty.next_config dirty_system
    {| Dirty.cfg_state := st;
       Dirty.cfg_control := Dirty.StartEpisode 1 Dirty.KLoop |} with
  | Some next => Dirty.is_side_dirty (Dirty.cfg_state next) 1 = false
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example same_episode_rerun_clears_dirty :
  let st := pending_target_state (TUpTo 5) in
  let fr := Dirty.fresh_frame st 1 I.Base.BoxN in
  match Dirty.next_config dirty_system
    {| Dirty.cfg_state := st;
       Dirty.cfg_control := Dirty.RunDrain fr Dirty.KLoop |} with
  | Some next =>
      Dirty.is_side_dirty (Dirty.cfg_state next) 1 = false /\
      Dirty.queue (Dirty.cfg_state next) = [] /\
      match Dirty.cfg_control next with
      | Dirty.RunRhs rerun _ _ => Dirty.frame_phase rerun = I.Base.BoxN
      | _ => False
      end
  | None => False
  end.
Proof. vm_compute. auto. Qed.
