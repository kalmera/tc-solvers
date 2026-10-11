From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.ReluctantUpdate common.SideUpdate
  solvers.slr.plus_restarting.PlusRestarting
  solvers.slr.plus_restarting.Proofs.
Import ListNotations.

Module E := Chain.
Module Trees := ConstraintSystems.Make E.V E.D.
Module Side := ReluctantSideUpdate E.V E.D E.U.

(* Regression snapshots include scheduling and side-cell phases as well as
    final values, for both controlled-owner recomputation settings. *)
Definition ordinary owner : Trees.rhs :=
  match owner with
  | 0 => Trees.Get 1 (fun _ => Trees.Spawn 2 (Trees.Spawn 2 (Trees.Ret E.D.One)))
  | 1 => Trees.Get 0 (fun _ => Trees.Ret E.D.Bot)
  | _ => Trees.Ret E.D.Bot
  end.
Definition mixed owner : Trees.rhs :=
  match owner with
  | 0 => Trees.Get 3 (fun value => Trees.Side 2 E.D.One (Trees.Spawn 1 (Trees.Ret value)))
  | 1 => Trees.Side 3 E.D.Two (Trees.Ret E.D.Bot)
  | _ => Trees.Ret E.D.Bot
  end.
Module Scenario (Flags : PlusRestarting.FEATURES).
  Module R := PlusRestarting.Make E.V E.D E.U Side E.S E.M Flags.
  Fixpoint body (tree : Trees.rhs) : R.ConstraintSystem.rhs :=
    match tree with
    | Trees.Ret value => R.ConstraintSystem.Ret value
    | Trees.Get target next => R.ConstraintSystem.Get target (fun value => body (next value))
    | Trees.Side target value next => R.ConstraintSystem.Side target value (body next)
    | Trees.Spawn target next => R.ConstraintSystem.Spawn target (body next)
    end.
  Definition cells st := map (fun source => map (fun target =>
    let cell := R.stored_side_cell st source target in
    (R.side_phase cell, R.side_reset_at cell)) [0;1;2;3]) [0;1;2;3].
  Definition view st :=
    (R.sigma st, R.ranking st, R.queue st, R.readers st,
     R.contributions st, cells st, R.reset_at_close st,
     R.last_targets st, R.dormant_bottom st, R.controlled st,
     R.dirty_side_targets st, R.deferred_wakes st,
     R.pending_spawns st, R.requested_spawns st).
  Definition result fuel tf roots :=
    option_map view (R.solve_fuel fuel (fun owner => body (tf owner)) roots).
  Definition snapshot :=
    (R.store * R.Ranking.t * R.work_queue * R.readers_table *
     R.contribution_table * list (list (Side.phase * option E.V.t)) *
     R.reset_table * R.target_table * E.S.t * E.S.t * E.M.t bool *
     R.work_queue * list E.V.t * E.S.t)%type.
  Definition ordinary_snapshot value : option snapshot := Some
    ([(0, value); (1, E.D.Bot)], [1;0], [], [(0,[1]);(1,[0])], [],
     repeat (repeat (E.U.BoxW, @None E.V.t) 4) 4,
     [(1,[]);(0,[])], [(1,[]);(0,[])], [2], [0],
     [(0,false);(1,false)], [], [], [2]).
  Definition mixed_snapshot value : option snapshot := Some
    ([(0,E.D.Top);(2,value);(1,E.D.Bot);(3,E.D.Top)], [3;1;2;0], [],
     [(3,[0]);(2,[]);(0,[])], [(2,[(0,value)]);(3,[(1,E.D.Top)])],
     repeat (repeat (E.U.BoxW, @None E.V.t) 4) 4,
     [(0,[]);(2,[]);(1,[]);(3,[])], [(2,[]);(0,[2]);(3,[]);(1,[3])],
     [3], [1;0], [(0,false);(2,false);(1,false);(3,false)], [], [], [1]).
End Scenario.
Module Enabled := Scenario PlusRestarting.AllEnabledFeatures.
Module Disabled := Scenario PlusRestarting.ReaderWakeupsOnlyFeatures.

Example ordinary_enabled_snapshot : Enabled.result 200 ordinary [0] = Enabled.ordinary_snapshot E.D.One.
Proof. vm_compute; reflexivity. Qed.
Example ordinary_disabled_snapshot : Disabled.result 200 ordinary [0] = Disabled.ordinary_snapshot E.D.Top.
Proof. vm_compute; reflexivity. Qed.
Example side_and_spawn_enabled_snapshot : Enabled.result 300 mixed [0;1] = Enabled.mixed_snapshot E.D.Two.
Proof. vm_compute; reflexivity. Qed.
Example side_and_spawn_disabled_snapshot : Disabled.result 300 mixed [0;1] = Disabled.mixed_snapshot E.D.Three.
Proof. vm_compute; reflexivity. Qed.

Example ordinary_recomputation_finishes_narrowing :
  match Enabled.R.solve_fuel 200 (fun owner => Enabled.body (ordinary owner)) [0] with
  | Some final => Enabled.R.sigma_value final 0 = E.D.One /\
      Enabled.R.pending_spawns final = [] /\
      E.S.mem 2 (Enabled.R.dormant_bottom final) = true /\
      E.S.elements (Enabled.R.requested_spawns final) = [2]
  | None => False
  end.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example ordinary_reader_wakeups_need_an_extra_update :
  match Disabled.R.solve_fuel 200 (fun owner => Disabled.body (ordinary owner)) [0] with
  | Some final => E.WN.narrow (Disabled.R.sigma_value final 0) E.D.One <>
      Disabled.R.sigma_value final 0
  | None => False
  end.
Proof. vm_compute; discriminate. Qed.

Module Sound := OrdinaryUpdateSoundAdapter E.V E.D E.U E.UL.
Module SideSound := ReluctantSideUpdateSoundLaws E.V E.D E.U E.DL E.UL.
Module Fresh := Proofs.Make E.V E.D E.U Side E.S E.M PlusRestarting.AllEnabledFeatures
  E.DL Sound SideSound E.SL E.ML.

Module Quiet := Fresh.QuietFixedness E.UL.
Lemma onebox_safe_narrows owner phase old input : E.U.avoids_fallback phase -> E.D.leq input old = true ->
  Fresh.eqv (snd (E.U.update false owner phase old input)) (E.WN.narrow old input).
Proof.
  intros Hsafe Hbelow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
    unfold E.U.update; rewrite Hbelow; apply Fresh.eqv_refl.
Qed.

Example rerun_keeps_returned_narrowing_phase :
  let c := Enabled.R.run_fuel 39 (fun owner => Enabled.body (ordinary owner))
    (Enabled.R.initial_config [0]) in
  match Enabled.R.cfg_control c with
  | Enabled.R.RunRhs fr _ _ => Enabled.R.frame_owner fr = 0 /\
      Enabled.R.frame_phase fr = E.U.BoxN /\ Enabled.R.sigma_value (Enabled.R.cfg_state c) 0 = E.D.Three
  | _ => False
  end.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example unchanged_controlled_commit_does_not_requeue :
  let ranked := Enabled.R.observe Enabled.R.empty_state 0 in
  let controlled := Enabled.R.promote_controlled ranked 0 in
  let st := Enabled.R.with_sigma controlled (E.M.update (Enabled.R.sigma controlled) 0 E.D.One) in
  let fr := Enabled.R.fresh_frame st 0 E.U.BoxN in
  Enabled.R.set_value st fr E.D.One = (st,fr).
Proof. vm_compute; reflexivity. Qed.
Example repeated_roots_keep_the_algorithm :
  Enabled.result 200 ordinary [0;0] = Enabled.ordinary_snapshot E.D.One.
Proof. vm_compute; reflexivity. Qed.

(* Exercise the certificate theorem itself on the slow
    non-idempotent narrowing example, rather than only computing its result. *)
Definition fresh_ordinary owner : Fresh.Syntax.rhs :=
  match owner with
  | 0 => Fresh.Syntax.Get 1 (fun _ => Fresh.Syntax.Spawn 2 (Fresh.Syntax.Spawn 2 (Fresh.Syntax.Ret E.D.One)))
  | 1 => Fresh.Syntax.Get 0 (fun _ => Fresh.Syntax.Ret E.D.Bot)
  | _ => Fresh.Syntax.Ret E.D.Bot
  end.
Lemma fresh_ordinary_no_sides : Fresh.no_side_effects fresh_ordinary.
Proof.
  intros [|[|owner]] result Htrace; cbn [fresh_ordinary] in Htrace.
  all: unfold Fresh.Solver.Sem.rhs_observes in Htrace.
  all: repeat match goal with H : Fresh.Solver.TransferSemantics.rhs_observes _ _ |- _ => inversion H; subst; clear H end; reflexivity.
Qed.
Definition safe_commit_check := @Quiet.safe_commit E.U.avoids_fallback.
Definition safe_commit_test c := match Fresh.R.cfg_control c with
  | Fresh.R.RunCommit fr direct _ =>
      match Fresh.R.frame_phase (snd (Fresh.R.set_value (Fresh.R.flush_deferred (Fresh.R.cfg_state c)) fr direct)) with
      | E.U.Widen => false | _ => true end
  | _ => true end.
Lemma safe_commit_test_sound c : safe_commit_test c = true -> safe_commit_check c.
Proof.
  destruct c as [st ctrl]; destruct ctrl; unfold safe_commit_test,safe_commit_check,Quiet.safe_commit;
    cbn [Fresh.R.cfg_state Fresh.R.cfg_control]; try (intros; exact I).
  destruct (Fresh.R.frame_phase (snd (Fresh.R.set_value (Fresh.R.flush_deferred st) f t)));
    unfold E.U.avoids_fallback; intros H; discriminate.
Qed.
Lemma fresh_ordinary_safe_trace : Fresh.trace_check 200 fresh_ordinary safe_commit_test (Fresh.R.initial_config [0]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma fresh_ordinary_safe_commits final : Fresh.R.solve_fuel 200 fresh_ordinary [0] = Some final ->
  forall c, Fresh.Sem.steps fresh_ordinary (Fresh.R.initial_config [0]) c -> safe_commit_check c.
Proof.
  intro Hrun; exact (@Fresh.checked_successful_trace 200 fresh_ordinary [0] final safe_commit_test safe_commit_check
    safe_commit_test_sound Hrun fresh_ordinary_safe_trace).
Qed.
Example fresh_ordinary_fixedness_proved final : Fresh.R.solve_fuel 200 fresh_ordinary [0] = Some final ->
  Fresh.narrowing_fixed_with E.WN.narrow (fun _ _ direct => direct) fresh_ordinary final.
Proof.
  intro Hrun; exact (@Quiet.successful_run_fixed_from_safe_commits E.WN.narrow E.U.avoids_fallback
    E.WNL.narrow_lower E.WNL.narrow_upper onebox_safe_narrows 200 fresh_ordinary [0] final
    eq_refl eq_refl fresh_ordinary_no_sides (fresh_ordinary_safe_commits final Hrun) Hrun).
Qed.

Module Phases.
Definition narrowing phase := phase = E.U.BoxN.
Lemma initial_wide owner : ~ narrowing (E.U.initial_phase false owner).
Proof. discriminate. Qed.
Lemma update_safe owner phase old input : E.U.avoids_fallback phase ->
  (narrowing phase -> E.D.leq input old = true) -> E.U.avoids_fallback (fst (E.U.update false owner phase old input)).
Proof. exact (@E.U.admissible_update_avoids_fallback false owner phase old input). Qed.
Lemma update_narrow owner phase old input : E.U.avoids_fallback phase ->
  narrowing (fst (E.U.update false owner phase old input)) -> E.D.leq input old = true.
Proof.
  intros Hsafe Hnarrow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
    unfold E.U.update,narrowing in Hnarrow; destruct (E.D.leq input old) eqn:Hbelow; cbn in Hnarrow;
    try discriminate; reflexivity.
Qed.
Lemma update_descends owner phase old input : E.U.avoids_fallback phase -> E.D.leq input old = true ->
  E.D.leq (snd (E.U.update false owner phase old input)) old = true.
Proof.
  intros Hsafe Hbelow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
    unfold E.U.update; rewrite Hbelow; apply E.WNL.narrow_upper; exact Hbelow.
Qed.
Lemma safe_narrows owner phase old input : E.U.avoids_fallback phase -> E.D.leq input old = true ->
  E.D.leq (snd (E.U.update false owner phase old input)) (E.WN.narrow old input) = true /\
  E.D.leq (E.WN.narrow old input) (snd (E.U.update false owner phase old input)) = true.
Proof.
  intros Hsafe Hbelow; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
    unfold E.U.update; rewrite Hbelow; split; apply E.DL.leq_refl.
Qed.
End Phases.
Definition fresh_fixed_unbounded := @Quiet.successful_run_fixed E.WN.narrow E.U.avoids_fallback
  E.WNL.narrow_lower E.WNL.narrow_upper Phases.safe_narrows Phases.narrowing
  (fun owner => @E.U.initial_avoids_fallback false owner) Phases.initial_wide
  Phases.update_safe Phases.update_narrow Phases.update_descends.
Definition fresh_avoids_fallback := @Fresh.ordinary_wave_safe E.U.avoids_fallback Phases.narrowing
  (fun owner => @E.U.initial_avoids_fallback false owner) Phases.initial_wide
  Phases.update_safe Phases.update_narrow Phases.update_descends.

Lemma fresh_ordinary_monotone : Fresh.monotonic_system fresh_ordinary.
Proof.
  intros [|[|owner]]; split; intros lower upper Hlower Hupper Hreads;
    cbn [fresh_ordinary] in Hlower,Hupper.
  all: repeat match goal with H : Fresh.Sem.rhs_observes _ _ |- _ => inversion H; subst; clear H end.
  all: cbn; first [intros target Hin; exact Hin|
    constructor; cbn; [reflexivity|intros target low Hin; contradiction|intros target Hin; exact Hin]].
Qed.
Example fresh_ordinary_global_fixedness final : Fresh.R.solve_fuel 200 fresh_ordinary [0] = Some final ->
  Fresh.narrowing_fixed_with E.WN.narrow (fun _ _ direct => direct) fresh_ordinary final.
Proof.
  intro Hrun; exact (@fresh_fixed_unbounded 200 fresh_ordinary [0] final eq_refl eq_refl
    fresh_ordinary_monotone fresh_ordinary_no_sides Hrun).
Qed.
Example fresh_ordinary_global_avoids_fallback c :
  Fresh.Sem.steps fresh_ordinary (Fresh.R.initial_config [0]) c ->
  Forall (fun fr => E.U.avoids_fallback (Fresh.R.frame_phase fr)) (Fresh.live_frames (Fresh.R.cfg_control c)).
Proof.
  intro Hreach; exact (@fresh_avoids_fallback fresh_ordinary [0] c eq_refl fresh_ordinary_no_sides fresh_ordinary_monotone Hreach).
Qed.
