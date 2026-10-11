From Stdlib Require Import List ZArith Lia.
From TcSolvers Require Import
  common.Collections
  common.ReluctantUpdate
  common.ThresholdInterval
  solvers.slr.dormant_restarting.DormantRestarting
  solvers.slr.reluctant_restarting.ThresholdInterval.

Import ListNotations.
Open Scope Z_scope.

Module V <: VAR.
  Definition t := Z.
  Definition eq_dec := Z.eq_dec.
End V.

Module I := ThresholdReluctantRestartingOneBox V.
Module D := ThresholdIntervalDomain.
Module R := DormantRestarting.FirstDiscoveryAlgorithm
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

Module FeaturesTF <: DormantRestarting.FEATURES.
  Definition restart_side_phases := true.
  Definition eliminate_dead_sides := false.
End FeaturesTF.
Module FeaturesFT <: DormantRestarting.FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := true.
End FeaturesFT.
Module FeaturesFF <: DormantRestarting.FEATURES.
  Definition restart_side_phases := false.
  Definition eliminate_dead_sides := false.
End FeaturesFF.

Module S := ListSet V.
Module M := AssocMap V.

(** All feature branches share the same reluctant machine interface. *)
Module MachineTT := DormantRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M
  DormantRestarting.AllEnabledFeatures.
Module MachineTF := DormantRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M FeaturesTF.
Module MachineFT := DormantRestarting.FirstDiscovery
  V D I.Base I.SideUpdate S M FeaturesFT.
Module MachineFF := DormantRestarting.FirstDiscovery
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
Module DR := DormantRestarting.FirstDiscoveryAlgorithm
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
