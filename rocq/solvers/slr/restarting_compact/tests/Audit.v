From Stdlib Require Import List.
From TcSolvers Require Import common.instances.Chain common.FiniteHeight
  solvers.slr.common.DiscoveryOrderLaws
  solvers.slr.restarting_compact.Proofs.

(** Instantiate the proof functor once. Concrete audits do not live in the
    generic proof unit, so clients do not pay for these instantiations. *)
Import ListNotations.
Module E := Chain.
Module Ranks := ListDiscoveryOrder E.V.
Module RL := ListDiscoveryOrderLaws E.V.
Module RF := ListFiniteDiscoveryOrderLaws E.V.
Module U := JoinUpdate E.V E.D.
Module UL := JoinUpdateLaws E.V E.D E.DL E.Height.
Module UBL := JoinUpdateUpperBoundLaws E.V E.D E.DL.
Module P := Proofs.Make E.V E.D U E.S E.M Ranks Restarting.AllEnabledFeatures
  RL RF E.DL UL E.SL E.ML.

(** Auditing total correctness and total leastness covers their intermediate
    invariants too, without repeatedly traversing the same proof terms. *)
Print Assumptions P.ordinary_aggregate.
Print Assumptions P.quiet_commit_narrowing_fixed.

Print Assumptions P.total_correct.
Definition total_least_solution tf roots (finite : P.Sem.finite_system tf roots) :=
  @P.total_least_solution tf roots finite UBL.update_preserves_upper_bound.
Print Assumptions total_least_solution.

(** A back read controls owner 0. Its two effects on owner 2 accumulate,
    and the spawned owner 3 must be included in the final post-solution. *)
Definition effects_and_spawn owner : P.Syntax.rhs :=
  match owner with
  | 0 => P.Syntax.Get 1 (fun value =>
      P.Syntax.Side 2 E.D.One (P.Syntax.Side 2 E.D.Two
        (P.Syntax.Spawn 3 (P.Syntax.Ret value))))
  | 1 => P.Syntax.Get 0 (fun _ => P.Syntax.Ret E.D.Three)
  | 2 => P.Syntax.Ret E.D.Bot
  | _ => P.Syntax.Get 2 (fun value => P.Syntax.Ret value)
  end.
Definition example_final := P.R.cfg_state
  (P.R.run_fuel 128 effects_and_spawn (P.R.initial_config [0])).
Example effects_and_spawn_terminates : P.R.solve_fuel 128 effects_and_spawn [0] = Some example_final.
Proof. vm_compute; reflexivity. Qed.
Example effects_and_spawn_values :
  P.R.sigma_value example_final 0 = E.D.Three /\
  P.R.sigma_value example_final 2 = E.D.Two /\
  P.R.sigma_value example_final 3 = E.D.Two /\
  P.R.stored_contribution example_final 0 2 = E.D.Two.
Proof. vm_compute; repeat split; reflexivity. Qed.
Example effects_and_spawn_correct : P.correct_final_state effects_and_spawn [0] example_final.
Proof. exact (@P.successful_run_correct 128 effects_and_spawn [0] example_final effects_and_spawn_terminates). Qed.

(** The incoming effect is written by a higher owner. It does not promote
    owner 0, so the strict decrease must come from incident-cell credit. *)
Definition credit_base := P.R.materialize
  (P.R.materialize (P.R.observe (P.R.observe P.R.empty_state 0) 1) 0) 1.
Definition credit_frame := P.R.fresh_frame credit_base 1 tt.
Definition incoming_write := P.R.write_side_contribution credit_base credit_frame 0 E.D.One.
Example incoming_write_changes : snd incoming_write = true.
Proof. vm_compute; reflexivity. Qed.
Example incoming_write_preserves_uncontrolled_owner : P.R.controlled (fst incoming_write) = P.R.controlled credit_base.
Proof. vm_compute; reflexivity. Qed.
Example incoming_write_consumes_round_budget :
  P.budget_lt (P.round_budget [0;1] (fst incoming_write) 0 tt)
    (P.round_budget [0;1] credit_base 0 tt).
Proof.
  eapply P.budget_write_changed with (fr := credit_frame) (target := 0) (input := E.D.One).
  - vm_compute; reflexivity.
  - cbn; auto.
  - cbn; auto.
  - right; reflexivity.
Qed.
Example already_materialized_preserves_round_budget :
  P.round_budget [0;1] (P.R.materialize credit_base 1) 0 tt = P.round_budget [0;1] credit_base 0 tt.
Proof. vm_compute; reflexivity. Qed.
Example discovering_owner_consumes_round_budget :
  P.budget_lt (P.round_budget [0;1] (P.R.materialize P.R.empty_state 1) 0 tt)
    (P.round_budget [0;1] P.R.empty_state 0 tt).
Proof. apply P.budget_materialize_new; [cbn; auto |reflexivity]. Qed.

(** One-box instances audit the ordinary results for both owner-recomputation
    settings. The production proofs remain one generic unit. *)
Module OrdinaryAudit (Features : Restarting.FEATURES).
  Module P := Proofs.Make E.V E.D E.U E.S E.M Ranks Features RL RF E.DL E.UL E.SL E.ML.
  Definition discovery : P.first_discovery_laws.
  Proof.
    constructor.
    - intros order target next rank variable Hobserve [variable_rank Hlookup].
      unfold Ranks.observe in Hobserve; destruct (Ranks.lookup order target) eqn:Htarget; inversion Hobserve; subst next rank.
      + right; exists variable_rank; exact Hlookup.
      + cbn in Hlookup; destruct (E.V.eq_dec variable target) as [Heq|Hneq].
        * left; exact Heq.
        * right; exists variable_rank; exact Hlookup.
    - intros order target next rank owner old_rank Hvalid Hfresh Howner Hobserve.
      destruct (@RL.observe_fresh order target next rank Hfresh Hobserve) as [-> _].
      exact (@RL.lookup_bound order owner old_rank Hvalid Howner).
  Qed.
  Definition phases : P.ordinary_phase_laws.
  Proof.
    refine {| P.phase_safe := E.U.avoids_fallback;
      P.phase_narrowing := fun phase => phase = E.U.BoxN |}.
    - apply E.U.initial_avoids_fallback.
    - intros owner Hnarrow; discriminate.
    - intros owner phase old input Hsafe Hinput; exact (@E.U.admissible_update_avoids_fallback false owner phase old input Hsafe Hinput).
    - intros owner phase old input Hsafe Hnarrow; destruct phase;
        cbn [E.U.update] in Hnarrow; destruct (E.D.leq input old) eqn:Hle; try discriminate; reflexivity.
    - intros owner phase old input Hsafe Hinput; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
        cbn [E.U.update]; rewrite Hinput; apply E.WNL.narrow_upper; exact Hinput.
  Defined.
  Lemma update_narrow owner phase old input : P.phase_safe phases phase -> E.D.leq input old = true ->
    snd (E.U.update false owner phase old input) = E.WN.narrow old input.
  Proof.
    intros Hsafe Hinput; destruct phase; [| |exfalso; apply Hsafe; reflexivity];
      cbn [E.U.update]; rewrite Hinput; reflexivity.
  Qed.
  Definition ordinary_avoids_fallback := @P.ordinary_avoids_fallback discovery phases.
  Definition successful_run_fixed := @P.successful_run_fixed discovery phases E.WN.narrow
    E.WNL.narrow_lower E.WNL.narrow_upper update_narrow.
  Definition total_fixed := @P.total_fixed discovery phases E.WN.narrow
    E.WNL.narrow_lower E.WNL.narrow_upper update_narrow.
  Definition controlled_constant owner : P.Syntax.rhs :=
    match owner with
    | 0 => P.Syntax.Get 1 (fun _ => P.Syntax.Ret E.D.One)
    | 1 => P.Syntax.Get 0 (fun _ => P.Syntax.Ret E.D.One)
    | _ => P.Syntax.Ret E.D.Bot
    end.

  Lemma constant_read_monotone target value :
    P.Sem.rhs_dependencies_monotone (P.Syntax.Get target (fun _ => P.Syntax.Ret value)) /\
    P.Sem.rhs_effects_monotone (P.Syntax.Get target (fun _ => P.Syntax.Ret value)).
  Proof.
    split; intros lower upper Hlower Hupper Hvalues; inversion Hlower; subst; inversion Hupper; subst.
    all: repeat match goal with H : P.Sem.rhs_observes (P.Syntax.Ret _) _ |- _ => inversion H; subst; clear H end.
    - cbn; intros x Hin; exact Hin.
    - constructor; [apply E.DL.leq_refl |intros x payload Hin; contradiction |intros x Hin; contradiction].
  Qed.
  Lemma controlled_constant_monotone : P.monotonic_system controlled_constant.
  Proof.
    intros owner; destruct owner as [|[|owner]]; cbn [controlled_constant]; try apply constant_read_monotone.
    split; intros lower upper Hlower Hupper Hvalues; inversion Hlower; subst; inversion Hupper; subst.
    - intros x Hin; contradiction.
    - constructor; [apply E.DL.leq_refl |intros x payload Hin; contradiction |intros x Hin; contradiction].
  Qed.
  Lemma controlled_constant_pure : P.no_side_effects controlled_constant.
  Proof.
    intros owner result Hobs; apply P.pure_sides with (body := controlled_constant owner); [|exact Hobs].
    destruct owner as [|[|owner]]; cbn [controlled_constant]; constructor; intro; constructor.
  Qed.
  Definition constant_final := P.R.cfg_state (P.R.run_fuel 128 controlled_constant (P.R.initial_config [0])).
End OrdinaryAudit.
Module Ordinary := OrdinaryAudit Restarting.AllEnabledFeatures.
Module ReaderWakeups := OrdinaryAudit Restarting.ReaderWakeupsOnlyFeatures.
Print Assumptions Ordinary.ordinary_avoids_fallback.
Print Assumptions ReaderWakeups.ordinary_avoids_fallback.
Print Assumptions Ordinary.successful_run_fixed.
Print Assumptions Ordinary.total_fixed.

(** The RHS has no direct self-read. The higher owner controls it, while slow
    narrowing needs several owner recomputations to reach One. *)
Example ordinary_recomputation_terminates :
  Ordinary.P.R.solve_fuel 128 Ordinary.controlled_constant [0] = Some Ordinary.constant_final.
Proof. vm_compute; reflexivity. Qed.
Example ordinary_recomputation_fixed_value :
  Ordinary.P.R.sigma_value Ordinary.constant_final 0 = E.D.One.
Proof. vm_compute; reflexivity. Qed.
Example reader_wakeups_terminate :
  ReaderWakeups.P.R.solve_fuel 128 ReaderWakeups.controlled_constant [0] = Some ReaderWakeups.constant_final.
Proof. vm_compute; reflexivity. Qed.
Example reader_wakeups_can_stop_before_fixedness :
  ReaderWakeups.P.R.sigma_value ReaderWakeups.constant_final 0 = E.D.Top /\
  E.WN.narrow (ReaderWakeups.P.R.sigma_value ReaderWakeups.constant_final 0) E.D.One = E.D.Three.
Proof. vm_compute; split; reflexivity. Qed.

Example ordinary_result_narrowing_fixed :
  Ordinary.P.narrowing_fixed E.WN.narrow Ordinary.controlled_constant Ordinary.constant_final.
Proof.
  eapply Ordinary.successful_run_fixed; [reflexivity |apply Ordinary.controlled_constant_monotone |
    apply Ordinary.controlled_constant_pure |exact ordinary_recomputation_terminates].
Qed.
