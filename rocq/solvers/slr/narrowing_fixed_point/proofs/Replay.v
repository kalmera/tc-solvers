From Stdlib Require Import List Bool Arith.PeanoNat Lia
  Wellfounded.Inverse_Image Wellfounded.Lexicographic_Product.
From TcSolvers Require Import common.Assumptions common.SolverSpecifications
  solvers.slr.narrowing_fixed_point.Base
  solvers.slr.narrowing_fixed_point.NarrowingFixedPoint
  solvers.slr.narrowing_fixed_point.proofs.AccumulatedReplay.
Import ListNotations.
Set Implicit Arguments.

(** Replay, demand, support, and termination for the batched machine.
    The state algebra follows AccumulatedReplay. Transition proofs
    handle the extra return-to-child edge through Front.step_cases, and all
    reachability uses N.steps. HigherRetry drains a finite sequence of children
    before replay; it does not assume an old-machine execution. *)
Module Make (V : VAR) (D : DOMAIN) (U : UPDATE V D)
 (S : SET V) (M : MAP V) (Features : Base.FEATURES)
 (DL : DOMAIN_LAWS D) (UL : UPDATE_LAWS V D U)
 (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
Module Front.
  Module N := NarrowingFixedPoint.Make V D U S M Features DL UL SL ML.
  Import N N.O.
  Module C := N.C.
  Module P := N.P.
  Module B := N.B.
  Module R := N.R.
  Module T := B.Termination.
  Module Sem := B.Sem.

  Lemma step_cases tf before after : N.next_config tf before = Some after ->
   C.next_config tf before = Some after \/
   exists st fr body k target rest,
   before = {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterSide fr body k)|} /\
   P.pending_above st (R.frame_owner fr) = Some (target,rest) /\
   after = P.suspend_commit tf st fr k target rest.
  Proof.
   destruct before as [st control]. intro Hstep.
   destruct control; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
   try (now left).
   destruct c; cbn -[C.next_config P.pending_above P.suspend_commit] in Hstep;
   try (now left).
   destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp;
   [|now left].
   inversion Hstep;subst. right. do 6 eexists. repeat split; eauto.
  Qed.

  Lemma preserves tf (inv : R.config -> Prop) :
   (forall before after, C.next_config tf before=Some after -> inv before -> inv after) ->
   (forall st fr body k target rest, P.pending_above st (R.frame_owner fr)=Some(target,rest) ->
   inv {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterSide fr body k)|} ->
   inv (P.suspend_commit tf st fr k target rest)) ->
   forall before after, N.next_config tf before=Some after -> inv before -> inv after.
  Proof.
   intros Hold Hresume before after Hstep Hi.
   destruct (@step_cases tf before after Hstep) as [Hbase|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - eapply Hold;eauto.
   - eapply Hresume;eauto.
  Qed.

  Lemma reachable_invariant tf roots (inv : R.config -> Prop) :
   inv (R.initial_config roots) ->
   (forall before after, N.next_config tf before=Some after -> inv before -> inv after) ->
   forall c, N.steps tf (R.initial_config roots) c -> inv c.
  Proof.
   intros Hinitial Hnext.
   assert (Hpreserve : forall first last,N.steps tf first last -> inv first -> inv last).
   { intros first last Hsteps. induction Hsteps;intro Hi;[exact Hi |].
     apply IHHsteps. eapply Hnext;eauto. }
   intros c Hr. eapply Hpreserve;eauto.
  Qed.

  Lemma resume_accumulation tf st fr body k target rest :
   P.pending_above st (R.frame_owner fr)=Some(target,rest) ->
   O.valid tf {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterSide fr body k)|} ->
   O.valid tf (P.suspend_commit tf st fr k target rest).
  Proof.
   intros Hp [Ho [Hb Hk]].
   destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop Hlt]].
   split;cbn.
   - split;[exact Hlt |]. eapply O.below_extended;[apply B.rank_extends_with_queue |exact Ho].
   - split;[split;[reflexivity |apply O.accumulation_fresh] |].
     eapply O.continuation_pop;[exact Hpop |exact Ho |now right |exact Hk].
  Qed.

  Theorem reachable_accumulation tf roots c :
   N.steps tf (R.initial_config roots) c -> O.valid tf c.
  Proof.
   apply reachable_invariant;[split;exact I |].
   apply preserves;[intros;eapply O.next_history;eauto |apply resume_accumulation].
  Qed.

  Lemma resume_materialized tf st fr body k target rest :
   T.control_owners_materialized st (R.Return (R.KAfterSide fr body k)) ->
   T.control_owners_materialized (R.with_queue st rest)
   (R.StartEpisode target (R.KAfterSide
   (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)).
  Proof.
   intro Ho. eapply (@O.same_sigma_owners st (R.with_queue st rest));
   [reflexivity |exact Ho].
  Qed.

  Theorem reachable_materialized tf roots c : N.steps tf (R.initial_config roots) c ->
   T.control_owners_materialized (R.cfg_state c) (R.cfg_control c).
  Proof.
   apply (@reachable_invariant tf roots
     (fun c => T.control_owners_materialized (R.cfg_state c) (R.cfg_control c)));
   [exact I |]. apply preserves.
   - intros before after Hstep Ho. exact (proj2 (@O.next_materialized tf before after Hstep) Ho).
   - intros. eapply resume_materialized; eassumption.
  Qed.

  Lemma next_origin tf before after : N.next_config tf before=Some after -> O.commit_origin after.
  Proof.
   intro Hstep. destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - eapply O.next_commit_origin;exact Hb.
   - exact I.
  Qed.

  Theorem reachable_origin tf roots c : N.steps tf (R.initial_config roots) c -> O.commit_origin c.
  Proof.
   apply reachable_invariant;[exact I |]. intros; eapply next_origin;eauto.
  Qed.

  Theorem commit_witness tf roots st fr direct k :
   N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
   B.completed_witness tf st fr direct.
  Proof.
   intro Hr. split.
   - apply B.materialized_solved. exact (proj1 (@reachable_materialized tf roots _ Hr)).
   - destruct (@reachable_accumulation tf roots _ Hr) as [_ [[reads [effects [Ht [Hg Hacc]]]] Hk]].
     destruct Hacc as [Hframe _].
     exists reads,effects. split;[exact Ht |]. split;[exact Hg |]. split;[|exact Hframe].
     destruct (@reachable_origin tf roots _ Hr) as [before Horigin].
     cbn in Horigin. subst st.
     change (B.recorded_effects (C.publish (S.elements (R.frame_current_targets fr)) before fr)
       (R.frame_owner fr) effects).
     apply O.publish_records_frame,Hframe.
  Qed.

  Lemma next_consistent tf before after :
   T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
   B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
   N.next_config tf before=Some after ->
   B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
  Proof.
   intros Ho Hg Hstep.
   destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - eapply O.next_consistent;eauto.
   - cbn in Hg |- *. split;[exact I |exact (proj2 Hg)].
  Qed.

  Theorem reachable_get_consistent tf roots c : N.steps tf (R.initial_config roots) c ->
   B.control_get_consistent (R.cfg_state c) (R.cfg_control c).
  Proof.
   assert (Hboth : forall c,N.steps tf (R.initial_config roots) c ->
   T.control_owners_materialized (R.cfg_state c) (R.cfg_control c) /\
   B.control_get_consistent (R.cfg_state c) (R.cfg_control c)).
   { apply reachable_invariant;[split;exact I |]. intros before after Hstep [Ho Hg]. split.
     - destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
       + exact (proj2 (@O.next_materialized tf before after Hb) Ho).
       + eapply resume_materialized;exact Ho.
     - eapply next_consistent;eauto. }
   intro Hr. exact (proj2 (Hboth c Hr)).
  Qed.

  Theorem reachable_aggregate tf roots c : N.steps tf (R.initial_config roots) c ->
   O.aggregate_guarded (R.cfg_state c) (R.cfg_control c).
  Proof.
   apply (@reachable_invariant tf roots
   (fun c=>O.aggregate_guarded (R.cfg_state c) (R.cfg_control c))).
   - intro owner. right;right. apply B.initial_aggregate_bounded.
   - apply preserves;[intros;eapply O.next_aggregate;eauto |].
     intros st fr body k target rest Hp Ha.
     apply (@O.suspend_aggregate tf st fr D.bottom k target rest Hp). exact Ha.
  Qed.

  Theorem actual_commit_summary tf roots st fr direct k after next_fr next_k :
   N.steps tf (R.initial_config roots)
   {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
   N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
   Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
   B.summary_valid tf after (R.frame_owner fr).
  Proof.
   intros Hr Hstep. pose proof (@commit_witness tf roots st fr direct k Hr) as Hcompleted.
   cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
   destruct (P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
   destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
   cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st fr direct) as [next next_frame] eqn:Hset.
   destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
   inversion Hstep;subst. apply B.summary_valid_requeue.
   eapply B.completed_witness_set_value_summary;eassumption.
  Qed.

  Theorem next_preserves_summary tf roots before after owner :
   N.steps tf (R.initial_config roots) before ->
   B.summary_valid tf (R.cfg_state before) owner ->
   N.next_config tf before=Some after ->
   O.summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
  Proof.
   intros Hr Hsummary Hstep.
   assert (Hcompleted : O.commit_completed tf (R.cfg_state before) (R.cfg_control before)).
   { destruct before as [st control]. destruct control;try exact I.
     eapply commit_witness;exact Hr. }
   destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - destruct before as [st control]. destruct control;
     try solve [eapply O.summary_fresh;[ | |exact Hsummary |exact Hb];[exact I |exact Hcompleted]].
     destruct l as [|target rest].
     + cbn -[C.publish R.publish_targets] in Hb. inversion Hb;subst.
       destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq];[right;left;now left |].
       right;right. eapply B.summary_valid_same_solver_view;
       [apply B.publish_targets_same_solver_view |].
       apply O.publish_other_summary;assumption.
     + eapply O.dead_pending_summary;eassumption.
   - eapply O.summary_pop;
     [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp)))
     |now left |exact Hsummary].
  Qed.

  Lemma next_schedule tf before after : N.next_config tf before=Some after ->
   O.schedule_step before after.
  Proof.
   intro Hstep.
   destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - eapply O.next_schedule;exact Hb.
   - intros owner Hscheduled.
     destruct (@O.suspend_schedule tf st fr D.bottom k target rest Hp owner Hscheduled)
     as [Hs|Hdischarge];[now left |].
     destruct Hdischarge as [a [b [d [e [f [g [_ [_ [Hbad _]]]]]]]]]. discriminate.
  Qed.

  Theorem next_solved_origin tf roots before after :
   N.steps tf (R.initial_config roots) before ->
   N.next_config tf before=Some after -> O.solved_origin before after.
  Proof.
   intros Hr Hstep.
   pose proof (@reachable_materialized tf roots before Hr) as Howners.
   pose proof (@reachable_get_consistent tf roots before Hr) as Hconsistent.
   destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - destruct before as [st control]. destruct control;
     try solve [eapply O.fresh_solved_origin;[ | | |exact Hb];eauto;exact I].
     destruct l as [|target rest];
     cbn -[C.publish R.publish_targets R.write_side_contribution C.requeue_source R.continue_dead] in Hb.
     + inversion Hb;subst. apply O.solved_origin_sigma. cbn. apply O.publish_sigma.
     + destruct (S.mem target (R.frame_current_targets f));
       [inversion Hb;subst;apply O.solved_origin_sigma;reflexivity |].
       destruct (R.write_side_contribution st f target D.bottom) as [next changed] eqn:Hw.
       inversion Hb;subst. apply O.solved_origin_sigma. unfold R.continue_dead.
       destruct changed;[destruct (_ && _)%bool |];cbn -[C.requeue_source];
       rewrite O.requeue_sigma;eapply T.write_side_contribution_sigma;exact Hw.
   - apply O.solved_origin_sigma;reflexivity.
  Qed.

  Lemma next_pending tf before after : N.next_config tf before=Some after -> O.pending_step before after.
  Proof.
   intro Hstep.
   destruct (@step_cases tf before after Hstep) as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
   - eapply O.next_pending;exact Hb.
   - intros owner Hpending. right;left;exact Hpending.
  Qed.

  Theorem terminal_aggregates_bounded tf roots final :
   N.steps tf (R.initial_config roots) (Sem.terminal_config final) -> Sem.quiescent final ->
   forall owner,D.leq (R.aggregate final owner) (R.sigma_value final owner)=true.
  Proof.
   intros Hr Hquiet owner.
   destruct (@reachable_aggregate tf roots (Sem.terminal_config final) Hr owner) as [Hq|[Ha|Hb]];
   [|contradiction |exact Hb].
   exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
  Qed.

  Lemma steps_append tf first middle last :
   N.steps tf first middle -> N.steps tf middle last -> N.steps tf first last.
  Proof.
   intros Hsteps Htail. induction Hsteps;[exact Htail |].
   econstructor;[exact H |apply IHHsteps,Htail].
  Qed.

  Theorem next_guarded_summary tf roots before after owner :
   N.steps tf (R.initial_config roots) before ->
   summary_guarded tf (R.cfg_state before) (R.cfg_control before) owner ->
   N.next_config tf before = Some after ->
   summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
  Proof.
   intros Hreach [Hq|[Ha|Hs]] Hstep.
   - destruct (@next_schedule tf before after Hstep owner (or_introl Hq))
     as [[Hq'|Ha']|Hcommit]; [now left |now right;left |].
     destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
     right;right. eapply actual_commit_summary; eassumption.
   - destruct (@next_schedule tf before after Hstep owner (or_intror Ha))
     as [[Hq'|Ha']|Hcommit]; [now left |now right;left |].
     destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
     right;right. eapply actual_commit_summary; eassumption.
   - eapply next_preserves_summary; eassumption.
  Qed.

  Theorem next_summaries tf roots before after :
   N.steps tf (R.initial_config roots) before ->
   summaries_guarded tf before ->
   N.next_config tf before = Some after -> summaries_guarded tf after.
  Proof.
   intros Hreach Hsummaries Hstep owner Hsolved.
   destruct (@next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
   as [Hbefore|[Hq|Ha]];[|now left |now right;left].
   eapply next_guarded_summary;[exact Hreach |apply Hsummaries,Hbefore |exact Hstep].
  Qed.

  Lemma steps_summaries tf roots first last :
   N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
   summaries_guarded tf first -> summaries_guarded tf last.
  Proof.
   intro Hsteps. induction Hsteps;intros Hreach Hsummaries;[exact Hsummaries |].
   apply IHHsteps.
   - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
   - eapply next_summaries;eassumption.
  Qed.

  Theorem reachable_summaries tf roots c :
   N.steps tf (R.initial_config roots) c -> summaries_guarded tf c.
  Proof.
   intro Hreach. eapply steps_summaries;[exact Hreach |constructor |].
   intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
  Qed.

  Theorem terminal_summaries tf roots final :
   N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
   Sem.quiescent final -> forall owner, Sem.solved final owner -> B.summary_valid tf final owner.
  Proof.
   intros Hreach Hquiet owner Hsolved.
   destruct (@reachable_summaries tf roots (Sem.terminal_config final) Hreach owner Hsolved)
   as [Hq|[Ha|Hs]];[|contradiction |exact Hs].
   exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
  Qed.

  Lemma next_roots_tracked tf roots before after :
   N.steps tf (R.initial_config roots) before ->
   roots_tracked tf roots before ->
   N.next_config tf before = Some after -> roots_tracked tf roots after.
  Proof.
   intros Hreach Hroots Hstep owner Hin. destruct (Hroots owner Hin) as [Hp|Hg].
   - destruct (@next_pending tf before after Hstep owner Hp) as [Hs|[Hp'|Ha]].
     + right. eapply reachable_summaries;[|exact Hs].
       eapply steps_append;[exact Hreach |]. econstructor;[exact Hstep |constructor].
     + now left.
     + right;right;left;exact Ha.
   - right. eapply next_guarded_summary;eassumption.
  Qed.

  Lemma steps_roots_tracked tf roots first last :
   N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
   roots_tracked tf roots first -> roots_tracked tf roots last.
  Proof.
   intro Hsteps. induction Hsteps;intros Hreach Hroots;[exact Hroots |].
   apply IHHsteps.
   - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
   - eapply next_roots_tracked;eassumption.
  Qed.

  Theorem reachable_roots_tracked tf roots c :
   N.steps tf (R.initial_config roots) c -> roots_tracked tf roots c.
  Proof.
   intro Hreach. eapply steps_roots_tracked;[exact Hreach |constructor |].
   intros owner Hin. left;exact Hin.
  Qed.

  Theorem terminal_roots_solved tf roots final :
   N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
   Sem.quiescent final -> forall owner, List.In owner roots -> Sem.solved final owner.
  Proof.
   intros Hreach Hquiet owner Hin.
   destruct (@reachable_roots_tracked tf roots (Sem.terminal_config final) Hreach owner Hin)
   as [Hp|[Hq|[Ha|Hs]]];try contradiction.
   - exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
   - exact (proj1 Hs).
  Qed.

  Theorem terminal_replay_post_solution tf roots final owner :
   N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
   Sem.quiescent final -> Sem.solved final owner ->
   (exists direct reads effects, Sem.rhs_eval final (tf owner) direct reads effects) /\
   Sem.rhs_post_solution final owner (tf owner).
  Proof.
   intros Hreach Hquiet Hsolved.
   pose proof (@terminal_summaries tf roots final Hreach Hquiet owner Hsolved) as Hsummary.
   split.
   - destruct Hsummary as [_ [direct [reads [effects [Htrace [Hreads _]]]]]].
     exists direct,reads,effects. apply B.rhs_trace_replay;[exact Htrace |].
     eapply B.guarded_reads_agree;eassumption.
   - eapply B.summary_post_solution;[exact Hquiet | |exact Hsummary].
     eapply terminal_aggregates_bounded;eassumption.
  Qed.

  Theorem successful_run_replay_post_solution fuel tf roots final :
   N.solve_fuel fuel tf roots = Some final ->
   forall owner, Sem.solved final owner ->
   (exists direct reads effects, Sem.rhs_eval final (tf owner) direct reads effects) /\
   Sem.rhs_post_solution final owner (tf owner).
  Proof.
   intro Hsolve. unfold N.solve_fuel in Hsolve.
   destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
   as [Hshape Hquiet]. intros owner Hsolved.
   eapply terminal_replay_post_solution;[|exact Hquiet |exact Hsolved].
   rewrite <- Hshape. apply N.fuel_steps.
  Qed.

  Theorem successful_run_correct fuel tf roots final :
   N.solve_fuel fuel tf roots = Some final -> Sem.correct_final_state tf roots final.
  Proof.
   intro Hsolve. pose proof (@successful_run_replay_post_solution fuel tf roots final Hsolve) as Hreplay.
   unfold N.solve_fuel in Hsolve.
   destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
   as [Hshape Hquiet]. intros owner Hin.
   assert (Hsolved : Sem.solved final owner).
   { eapply terminal_roots_solved;[|exact Hquiet |exact Hin].
     rewrite <- Hshape. apply N.fuel_steps. }
   split;[exact Hsolved |exact (proj2 (Hreplay owner Hsolved))].
  Qed.
End Front.
Import Front.
Module PS := N.O.PS.
Module C := N.C.
Module H := C.H.
Module P := C.P.
Module B := C.H.B.
Module R := C.R.
Module T := B.Termination.
Definition input fr target :=
 match M.lookup (R.frame_local_side fr) target with
 Some value => value | None => D.bottom end.
Definition effects_bounded effects (bound : V.t -> D.t) :=
 forall target value, List.In (target,value) effects -> D.leq value (bound target) = true.
Definition frame_bounded fr (bound : V.t -> D.t) :=
 forall target, D.leq (input fr target) (bound target) = true.
Definition accumulation fr effects :=
 B.frame_effects fr effects /\
 (forall bound, effects_bounded effects bound -> frame_bounded fr bound) /\
 (forall target, S.mem target (R.frame_current_targets fr) = true <->
 exists value, List.In (target,value) effects).
Lemma accumulation_fresh st owner phase : accumulation (R.fresh_frame st owner phase) [].
Proof.
 split; [intros target value Hin; contradiction |]. split.
 - intros bound Hb target. unfold input. cbn. rewrite ML.lookup_empty. apply DL.bottom_least.
 - intro target. cbn. rewrite SL.empty_spec.
   split; [discriminate |intros [value Hin]; contradiction].
Qed.
Lemma frame_bounded_record fr target raw bound :
 frame_bounded fr bound -> D.leq raw (bound target) = true ->
 frame_bounded (fst (R.record_side_input fr target raw)) bound.
Proof.
 intros Hframe Hraw observed. unfold input, R.record_side_input. cbn.
 destruct (V.eq_dec observed target) as [->|Hother].
 - rewrite ML.lookup_update_same. unfold R.accumulated_side_input.
   specialize (Hframe target). unfold input in Hframe.
   destruct (M.lookup (R.frame_local_side fr) target);
   [apply DL.join_least; assumption |exact Hraw].
 - rewrite ML.lookup_update_other by exact Hother. apply Hframe.
Qed.
Lemma accumulation_record fr effects target raw :
 accumulation fr effects ->
 accumulation (fst (R.record_side_input fr target raw)) (effects ++ [(target,raw)]).
Proof.
 intros [Hframe [Hbounded Htargets]]. split; [now apply B.frame_effects_record_side |]. split.
 - intros bound Hbound. apply frame_bounded_record.
   + apply Hbounded. intros x value Hin. apply Hbound, List.in_or_app. now left.
   + apply Hbound, List.in_or_app. right. now left.
 - intro observed. cbn. rewrite SL.add_spec, Htargets. split.
   + intros [->|[value Hin]].
     * exists raw. apply List.in_or_app. right. now left.
     * exists value. apply List.in_or_app. now left.
   + intros [value Hin]. apply List.in_app_or in Hin. destruct Hin as [Hin|[Heq|Hfalse]].
     * right. now exists value.
     * inversion Heq. now left.
     * contradiction.
Qed.
Lemma accumulation_view fr next effects :
 R.frame_local_side next = R.frame_local_side fr ->
 R.frame_current_targets next = R.frame_current_targets fr ->
 accumulation fr effects -> accumulation next effects.
Proof.
 intros Hlocal Htargets. unfold accumulation, B.frame_effects, frame_bounded,input.
 now rewrite Hlocal,Htargets.
Qed.
Definition evaluation tf st fr current :=
 exists reads effects, B.rhs_context (tf (R.frame_owner fr)) current reads effects /\
 B.guarded_reads st (R.frame_owner fr) reads /\ accumulation fr effects.
Definition completed tf st fr direct :=
 exists reads effects, B.rhs_trace (tf (R.frame_owner fr)) direct reads effects /\
 B.guarded_reads st (R.frame_owner fr) reads /\ accumulation fr effects.
Fixpoint continuation tf st k :=
 match k with
 | R.KLoop | R.KSeedLoop _ => True
 | R.KAfterGet fr target next rest =>
   evaluation tf st fr (R.ConstraintSystem.Get target next) /\ continuation tf st rest
 | R.KAfterSide fr next rest =>
   (next = tf (R.frame_owner fr) /\ accumulation fr []) /\ continuation tf st rest
 | R.KAfterSpawn fr next rest => evaluation tf st fr next /\ continuation tf st rest
 | R.KDead fr direct _ rest => completed tf st fr direct /\ continuation tf st rest
 | R.KDrain _ rest => continuation tf st rest
 end.
Definition history tf st control :=
 match control with
 | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
 | R.StartEpisode _ k | R.RunDrain _ k | R.Return k => continuation tf st k
 | R.RunRhs fr body k => evaluation tf st fr body /\ continuation tf st k
 | R.RunDead fr direct _ k | R.RunCommit fr direct k =>
   completed tf st fr direct /\ continuation tf st k
 end.
Definition valid tf c := T.control_ordered (R.cfg_state c) (R.cfg_control c) /\
 history tf (R.cfg_state c) (R.cfg_control c).
Lemma evaluation_carries tf before after fr body :
 (forall reads, B.guarded_reads before (R.frame_owner fr) reads ->
 B.guarded_reads after (R.frame_owner fr) reads) ->
 evaluation tf before fr body -> evaluation tf after fr body.
Proof.
 intros Hcarry [reads [effects [Hcontext [Hreads Hacc]]]].
 exists reads,effects. split; [exact Hcontext |]. split; [apply Hcarry,Hreads |exact Hacc].
Qed.
Lemma completed_carries tf before after fr direct :
 (forall reads, B.guarded_reads before (R.frame_owner fr) reads ->
 B.guarded_reads after (R.frame_owner fr) reads) ->
 completed tf before fr direct -> completed tf after fr direct.
Proof.
 intros Hcarry [reads [effects [Htrace [Hreads Hacc]]]].
 exists reads,effects. split; [exact Htrace |]. split; [apply Hcarry,Hreads |exact Hacc].
Qed.

Definition carries_reads := H.carries_reads.
Definition carries_same := H.carries_same.
Definition carries_trans := H.carries_trans.
Definition carries_materialize := H.carries_materialize.
Definition carries_enqueue := H.carries_enqueue.
Definition carries_observe := H.carries_observe.
Definition carries_get := H.carries_get.
Definition get_owner := H.get_owner.
Definition get_new_read := H.get_new_read.
Definition lt_extended := H.lt_extended.
Definition below_extended := H.below_extended.
Definition ordered_extended := H.ordered_extended.
Definition carries_write := H.carries_write.
Definition carries_set := H.carries_set.
Definition carries_requeue := H.carries_requeue.
Definition requeue_extends := H.requeue_extends.

  Lemma continuation_carries tf before after k : carries_reads before after ->
    continuation tf before k -> continuation tf after k.
  Proof.
    intros H. induction k; cbn; intro Hk; try exact I; try (now apply IHk).
    all: destruct Hk as [Hhead Htail]; split; try (now apply IHk).
    all: try exact Hhead.
    all: first [eapply evaluation_carries with (before := before)
      |eapply completed_carries with (before := before)];
      [exact (H (R.frame_owner f)) |exact Hhead].
  Qed.

  Lemma continuation_other tf before after upper k :
    T.continuation_below before upper k ->
    (forall owner reads, R.rank_lt before owner upper = true ->
      B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
    continuation tf before k -> continuation tf after k.
  Proof.
    revert upper. induction k; cbn; intros upper Hbelow Hcarry Hhistory; try exact I.
    all: destruct Hbelow as [Hlt Hbelow].
    all: try (destruct Hhistory as [Hhead Htail]; split).
    all: try solve [eapply evaluation_carries; [intros; eapply Hcarry; eauto |exact Hhead]
      |eapply completed_carries; [intros; eapply Hcarry; eauto |exact Hhead]
      |exact Hhead].
    all: eapply IHk; [exact Hbelow | |eassumption].
    all: intros owner reads Howner Hreads; apply Hcarry; [|exact Hreads];
      eapply T.rank_lt_trans_true; eauto.
  Qed.

  Lemma continuation_clear tf st owner k : T.continuation_below st owner k ->
    continuation tf st k -> continuation tf (P.clear_owner st owner) k.
  Proof.
    intro Hbelow. eapply continuation_other; [exact Hbelow |].
    intros reader reads Hlt Hreads. apply P.clear_other_guarded_reads; [|exact Hreads].
    now apply B.rank_lt_true_neq_correctness in Hlt.
  Qed.

  Lemma continuation_pop tf st upper popped rest k :
    R.queue_pop (R.queue st) = Some (popped,rest) ->
    T.continuation_below st upper k ->
    (popped = upper \/ R.rank_lt st upper popped = true) ->
    continuation tf st k -> continuation tf (R.with_queue st rest) k.
  Proof.
    intros Hpop Hbelow Habove. eapply continuation_other; [exact Hbelow |].
    intros owner reads Hlt Hreads. eapply B.guarded_reads_pop_other; [exact Hpop | |exact Hreads].
    apply (@B.rank_lt_true_neq_correctness st).
    destruct Habove as [->|Hhigher]; [exact Hlt |eapply T.rank_lt_trans_true; eauto].
  Qed.
  Lemma history_carries tf before after control : carries_reads before after ->
    history tf before control -> history tf after control.
  Proof.
    intro Hcarry. destruct control; cbn; intro H; try exact I;
      try solve [eapply continuation_carries; eauto].
    all: destruct H as [Hhead Htail]; split;
      try solve [eapply continuation_carries; eauto].
    all: first [eapply evaluation_carries with (before := before)
      |eapply completed_carries with (before := before)];
      [exact (Hcarry (R.frame_owner f)) |exact Hhead].
  Qed.

  Lemma valid_carries tf before after control :
    B.rank_extends before after -> carries_reads before after ->
    valid tf {| R.cfg_state := before; R.cfg_control := control |} ->
    valid tf {| R.cfg_state := after; R.cfg_control := control |}.
  Proof.
    intros Hrank Hcarry [Horder Hhistory]. split.
    - eapply ordered_extended; eauto.
    - eapply history_carries; eauto.
  Qed.


Lemma empty_evaluation tf st fr :
 accumulation fr [] -> evaluation tf st fr (tf (R.frame_owner fr)).
Proof.
 intro Hacc. exists [],[]. split; [apply B.initial_rhs_context |].
 split; [intros target value Hin; contradiction |exact Hacc].
Qed.
Lemma initial_evaluation tf st start owner phase :
 evaluation tf st (R.fresh_frame start owner phase) (tf owner).
Proof. apply empty_evaluation, accumulation_fresh. Qed.
Lemma evaluation_ret tf st fr direct :
 evaluation tf st fr (R.ConstraintSystem.Ret direct) -> completed tf st fr direct.
Proof.
 intros [reads [effects [Hcontext [Hreads Hacc]]]]. exists reads,effects.
 split; [|now split].
 specialize (Hcontext direct [] [] (B.TraceRet direct)).
 now rewrite !List.app_nil_r in Hcontext.
Qed.
Lemma evaluation_side tf st fr target value next :
 evaluation tf st fr (R.ConstraintSystem.Side target value next) ->
 evaluation tf st (fst (R.record_side_input fr target value)) next.
Proof.
 intros [reads [effects [Hcontext [Hreads Hacc]]]].
 exists reads,(effects ++ [(target,value)]). split.
 - eapply B.rhs_context_side; exact Hcontext.
 - split; [exact Hreads |now apply accumulation_record].
Qed.
Lemma evaluation_spawn tf st fr target next :
 evaluation tf st fr (R.ConstraintSystem.Spawn target next) -> evaluation tf st fr next.
Proof.
 intros [reads [effects [Hcontext [Hreads Hacc]]]]. exists reads,effects.
 split; [eapply B.rhs_context_spawn; exact Hcontext |now split].
Qed.
Lemma evaluation_get tf st fr target next after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) ->
 evaluation tf st fr (R.ConstraintSystem.Get target next) ->
 evaluation tf after next_fr (next value).
Proof.
 intros Hget [reads [effects [Hcontext [Hreads Hacc]]]].
 exists (reads ++ [(target,value)]),effects. rewrite (get_owner Hget). split.
 - eapply B.rhs_context_get; exact Hcontext.
 - split.
   + intros observed seen Hin. apply List.in_app_or in Hin. destruct Hin as [Hin|Hin].
     * exact (carries_get Hget Hreads observed seen Hin).
     * eapply (get_new_read Hget); exact Hin.
   + eapply accumulation_view; [| |exact Hacc].
     all: unfold R.complete_get in Hget; destruct (R.rank_lt st (R.frame_owner fr) target);
     inversion Hget; reflexivity.
Qed.

  Lemma get_config tf st fr target next k after next_fr value :
    R.complete_get st fr target = (after,next_fr,value) ->
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
    valid tf {| R.cfg_state := after; R.cfg_control := R.RunRhs next_fr (next value) k |}.
  Proof.
    intros Hget [Horder [Heval Hk]]. split; cbn.
    - rewrite (get_owner Hget). eapply below_extended;
        [eapply B.rank_extends_complete_get; exact Hget |exact Horder].
    - split; [eapply evaluation_get; eauto |].
      eapply continuation_carries; [exact (carries_get Hget) |exact Hk].
  Qed.

  Lemma base_get tf st fr target next k after :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} ->
    R.next_config tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |} = Some after ->
    valid tf after.
  Proof.
    intros Hvalid Hstep.
    assert (Hobs : valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Get target next) k |}).
    { eapply valid_carries; [eapply B.rank_extends_observe; reflexivity |apply carries_observe |exact Hvalid]. }
    cbn -[R.observe R.complete_get R.enqueue] in Hstep.
    destruct (negb (R.is_materialized (R.observe st target) target) &&
      R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool eqn:Hguard.
    - apply Bool.andb_true_iff in Hguard. inversion Hstep; subst. destruct Hobs as [Ho [He Hk]].
      split; cbn; [split; [exact (proj2 Hguard) |exact Ho] |now split].
    - set (current := if R.is_materialized (R.observe st target) target
        then R.observe st target else R.enqueue (R.observe st target) target) in *.
      destruct (R.complete_get current fr target) as [[next_st next_fr] value] eqn:Hget.
      inversion Hstep; subst. eapply get_config; [exact Hget |].
      subst current. destruct (R.is_materialized (R.observe st target) target); [exact Hobs |].
      eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hobs].
  Qed.

  Lemma base_spawn tf st fr target next k after :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} ->
    R.next_config tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Spawn target next) k |} = Some after ->
    valid tf after.
  Proof.
    intros Hvalid Hstep.
    assert (Hobs : valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs fr next k |}).
    { destruct Hvalid as [Ho [He Hk]]. eapply valid_carries;
        [eapply B.rank_extends_observe; reflexivity |apply carries_observe |].
      split; [exact Ho |]. split; [eapply evaluation_spawn; exact He |exact Hk]. }
    cbn -[R.observe R.materialize R.enqueue] in Hstep.
    destruct (R.is_materialized (R.observe st target) target);
      [inversion Hstep; subst; exact Hobs |].
    destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target) eqn:Hlt.
    - inversion Hstep; subst. destruct Hobs as [Ho [He Hk]].
      split; cbn; [split; assumption |now split].
    - inversion Hstep; subst. eapply valid_carries;
        [apply B.rank_extends_materialize |apply carries_materialize |].
      eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hobs].
  Qed.

  Lemma base_dead tf st fr direct pending k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct pending k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct pending k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep. destruct pending as [|target rest];
      cbn -[R.write_side_contribution R.continue_dead R.publish_targets] in Hstep.
    - inversion Hstep; subst. eapply valid_carries;
        [apply B.rank_extends_with_last_targets |apply carries_same;
          exact (proj1 (B.publish_targets_same_solver_view st fr)) |].
      split; [exact Ho |now split].
    - destruct (S.mem target (R.frame_current_targets fr));
        [inversion Hstep; subst; split; [exact Ho |now split] |].
      destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
      assert (Hnext : valid tf {| R.cfg_state := next; R.cfg_control := R.RunDead fr direct rest k |}).
      { eapply valid_carries; [eapply B.rank_extends_write_side_contribution; exact Hwrite
          |exact (carries_write Hwrite) |]. split; [exact Ho |now split]. }
      inversion Hstep; subst. unfold R.continue_dead. destruct changed; [|exact Hnext].
      destruct (R.rank_lt next (R.frame_owner fr) target && negb (R.is_materialized next target))%bool eqn:Hguard.
      + apply Bool.andb_true_iff in Hguard. destruct Hnext as [Ho' [Hc' Hk']].
        split; cbn; [split; [exact (proj1 Hguard) |exact Ho'] |now split].
      + eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hnext].
  Qed.

  Lemma base_commit tf st fr direct k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep. cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
    destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
    inversion Hstep; subst. eapply valid_carries;
      [apply requeue_extends |apply carries_requeue |].
    split; cbn.
    - rewrite (@B.set_value_frame_owner st fr direct next next_fr Hset). eapply below_extended;
        [eapply B.rank_extends_set_value; exact Hset |exact Ho].
    - eapply continuation_carries; [eapply carries_set; exact Hset |exact Hk].
  Qed.

  Lemma base_drain tf st fr k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDrain fr k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho Hk] Hstep. destruct (R.queue st) as [|target rest] eqn:Hqueue;
      cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hqueue in Hstep; cbn in Hstep.
    - inversion Hstep; subst. split.
      + apply ordered_extended with st; [apply B.rank_extends_reset_registered_cells |].
        destruct k; cbn in *; tauto.
      + eapply continuation_carries; [apply carries_same;
          exact (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr))) |exact Hk].
    - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
      + inversion Hstep; subst. split; cbn;
          [eapply below_extended; [apply B.rank_extends_with_queue |exact Ho] |].
        split; [apply initial_evaluation |]. eapply continuation_pop;
          [unfold R.queue_pop; rewrite Hqueue; reflexivity |exact Ho |now left |exact Hk].
      + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
        * inversion Hstep; subst. split; cbn.
          -- split; [exact Hlt |]. eapply below_extended;
               [apply B.rank_extends_with_queue |exact Ho].
          --
          eapply continuation_pop; [unfold R.queue_pop; rewrite Hqueue; reflexivity
            |exact Ho |now right |exact Hk].
        * inversion Hstep; subst. split.
          -- apply ordered_extended with st; [apply B.rank_extends_reset_registered_cells |].
             destruct k; cbn in *; tauto.
          -- eapply continuation_carries; [apply carries_same;
               exact (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr))) |exact Hk].
  Qed.

  Lemma base_return tf st k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.Return k |} ->
    R.next_config tf {| R.cfg_state := st; R.cfg_control := R.Return k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho Hk] Hstep. destruct k; cbn -[R.complete_get] in Hstep;
      cbn in Ho,Hk.
    all: try solve [inversion Hstep; subst; split; cbn; tauto].
    - destruct Hk as [He Hk]. destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hget.
      inversion Hstep; subst. eapply get_config; [exact Hget |]. split; [exact Ho |now split].
    - destruct Hk as [[Heq Hacc] Hk]. inversion Hstep; subst. split; [exact Ho |].
      split; [apply empty_evaluation, Hacc |exact Hk].
  Qed.


  Definition not_side control :=
    match control with R.RunRhs _ (R.ConstraintSystem.Side _ _ _) _ => False | _ => True end.

  Lemma base_step tf before after : not_side (R.cfg_control before) ->
    valid tf before -> R.next_config tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hnot Hvalid Hstep. destruct control.
    - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
        [inversion Hstep; subst; split; exact I |discriminate].
    - destruct l; cbn -[R.observe] in Hstep;
        try destruct (R.is_materialized (R.observe st t) t);
        inversion Hstep; subst; split; exact I.
    - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
        inversion Hstep; subst; split; exact I.
    - destruct Hvalid as [Ho Hk]. inversion Hstep; subst. split; cbn.
      + eapply below_extended; [apply B.rank_extends_materialize |exact Ho].
      + split; [apply initial_evaluation |].
        eapply continuation_carries; [apply carries_materialize |exact Hk].
    - destruct r.
      + inversion Hstep; subst. destruct Hvalid as [Ho [He Hk]].
        split; [exact Ho |]. split; [now apply evaluation_ret |exact Hk].
      + eapply base_get; eauto.
      + contradiction.
      + eapply base_spawn; eauto.
    - eapply base_dead; eauto.
    - eapply base_commit; eauto.
    - eapply base_drain; eauto.
    - eapply base_return; eauto.
  Qed.
  Lemma suspend_valid tf st fr direct k target rest :
    P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    valid tf (P.suspend_commit tf st fr k target rest).
  Proof.
    intros Hpending [Ho [Hc Hk]].
    destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hpending) as [_ [Hpop Hlt]].
    split; cbn.
    - split; [exact Hlt |]. eapply below_extended;
        [apply B.rank_extends_with_queue |exact Ho].
    - split; [split; [reflexivity |apply accumulation_fresh] |]. eapply continuation_pop;
        [exact Hpop |exact Ho |now right |exact Hk].
  Qed.

  Lemma precommit_step tf before after : not_side (R.cfg_control before) ->
    valid tf before -> P.next_config tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hnot Hvalid Hstep.
    destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep.
    all: try solve [eapply base_step; eauto].
    destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hpending.
    - inversion Hstep; subst. eapply suspend_valid; eauto.
    - eapply base_step; eauto.
  Qed.


Definition publication_carries := H.publication_carries.
  Lemma batched_side tf st fr target raw body k :
    valid tf {| R.cfg_state := st;
      R.cfg_control := R.RunRhs fr (R.ConstraintSystem.Side target raw body) k |} ->
    valid tf {| R.cfg_state := R.observe st target;
      R.cfg_control := R.RunRhs (fst (R.record_side_input fr target raw)) body k |}.
  Proof.
    intros [Ho [He Hk]]. eapply valid_carries;
      [eapply B.rank_extends_observe; reflexivity |apply carries_observe |].
    split; [exact Ho |]. split; [eapply evaluation_side; exact He |exact Hk].
  Qed.

  Lemma publication_extends targets st fr : B.rank_extends st (P.publish_accumulated targets st fr).
  Proof. apply P.publication_extends_ranks. Qed.

  Lemma batched_done tf st fr direct k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} ->
    valid tf {| R.cfg_state := R.publish_targets
      (P.publish_accumulated (S.elements (R.frame_current_targets fr)) st fr) fr;
      R.cfg_control := R.RunCommit fr direct k |}.
  Proof.
    intro Hvalid. eapply valid_carries;
      [apply B.rank_extends_with_last_targets |apply carries_same;
        apply (proj1 (B.publish_targets_same_solver_view _ _)) |].
    eapply valid_carries; [apply publication_extends |apply publication_carries |exact Hvalid].
  Qed.

  Lemma batched_step tf before after :
    valid tf before -> P.next_batched tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep. destruct control;
      cbn -[P.next_config R.record_side_input R.observe P.publish_accumulated R.publish_targets] in Hstep.
    all: try solve [eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I].
    - destruct r;
        try solve [eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I].
      inversion Hstep; subst. apply batched_side; exact Hvalid.
    - destruct l.
      + inversion Hstep; subst. apply batched_done; exact Hvalid.
      + eapply precommit_step; [|exact Hvalid |exact Hstep]; exact I.
  Qed.

  Lemma clear_start tf st owner k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.StartEpisode owner k |} ->
    valid tf {| R.cfg_state := P.clear_owner st owner; R.cfg_control := R.StartEpisode owner k |}.
  Proof.
    intros [Ho Hk]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - eapply continuation_clear; eauto.
  Qed.

  Lemma clear_resume tf st fr body k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.Return (R.KAfterSide fr body k) |} ->
    valid tf {| R.cfg_state := P.clear_owner st (R.frame_owner fr);
      R.cfg_control := R.Return (R.KAfterSide fr body k) |}.
  Proof.
    intros [Ho [Hbody Hk]]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - split; [exact Hbody |]. eapply continuation_clear; eauto.
  Qed.

  Lemma retry_valid tf st fr direct k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
    valid tf (P.retry_current tf st fr k).
  Proof.
    intros [Ho [Hc Hk]]. split; cbn.
    - eapply below_extended; [apply B.rank_extends_with_queue |exact Ho].
    - split; [apply initial_evaluation |]. eapply continuation_clear; eauto.
  Qed.

  Theorem fresh_step tf before after :
    valid tf before -> P.next_fresh tf before = Some after -> valid tf after.
  Proof.
    destruct before as [st control]. intros Hvalid Hstep. destruct control;
      cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
    all: try solve [eapply batched_step; eauto].
    - eapply batched_step; [eapply clear_start; exact Hvalid |exact Hstep].
    - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hpending.
      + inversion Hstep; subst. eapply suspend_valid; eauto.
      + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
        * inversion Hstep; subst. eapply retry_valid; exact Hvalid.
        * eapply batched_step; eauto.
    - destruct c; cbn -[P.next_batched] in Hstep;
        try solve [eapply batched_step; eauto].
      eapply batched_step; [eapply clear_resume; exact Hvalid |exact Hstep].
  Qed.


  Lemma dead_done_valid tf st fr direct k :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} ->
    valid tf {| R.cfg_state := R.publish_targets
      (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr;
      R.cfg_control := R.RunCommit fr direct k |}.
  Proof.
    intro Hvalid. eapply valid_carries;
      [apply B.rank_extends_with_last_targets |apply carries_same;
        exact (proj1 (B.publish_targets_same_solver_view _ _)) |].
    eapply valid_carries; [apply C.publish_extends |apply C.publish_carries |exact Hvalid].
  Qed.

  Lemma dead_pending_valid tf st fr direct target rest k after :
    valid tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} ->
    N.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct (target::rest) k |} = Some after ->
    valid tf after.
  Proof.
    intros [Ho [Hc Hk]] Hstep.
    cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
    destruct (S.mem target (R.frame_current_targets fr));
      [inversion Hstep; subst; split; [exact Ho |now split] |].
    destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
    set (queued := C.requeue_source st next (R.frame_owner fr) target) in *.
    assert (Hnext : valid tf {| R.cfg_state := queued; R.cfg_control := R.RunDead fr direct rest k |}).
    { unfold queued. eapply valid_carries; [apply C.requeue_extends |apply C.requeue_carries |].
      eapply valid_carries; [eapply B.rank_extends_write_side_contribution; exact Hwrite
        |eapply carries_write; exact Hwrite |]. split; [exact Ho |now split]. }
    inversion Hstep; subst. unfold R.continue_dead. destruct changed; [|exact Hnext].
    destruct (R.rank_lt queued (R.frame_owner fr) target && negb (R.is_materialized queued target))%bool eqn:Hguard.
    - apply Bool.andb_true_iff in Hguard. destruct Hnext as [Ho' [Hc' Hk']].
      split; cbn; [split; [exact (proj1 Hguard) |exact Ho'] |now split].
    - eapply valid_carries; [apply B.rank_extends_enqueue |apply carries_enqueue |exact Hnext].
  Qed.

  Theorem next_history tf before after :
    valid tf before -> N.next_config tf before = Some after -> valid tf after.
  Proof.
 intros Hv Hstep. eapply Front.preserves;[ | |exact Hstep |exact Hv].
    - intros. eapply N.O.next_history;eauto.
    - apply Front.resume_accumulation.
Qed.

  Theorem reachable_history tf roots c : N.steps tf (R.initial_config roots) c -> valid tf c.
  Proof.
 exact (@Front.reachable_accumulation tf roots c).
Qed.

  Lemma fuel_steps fuel tf c : N.steps tf c (N.run_fuel fuel tf c).
  Proof.
    revert c. induction fuel as [|fuel IH]; intro c; cbn; [constructor |].
    destruct (N.next_config tf c) as [next|] eqn:Hstep;
      [econstructor; [exact Hstep |apply IH] |constructor].
  Qed.


Theorem actual_commit_accumulation tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
 N.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 exists reads effects, B.Sem.rhs_eval st (tf (R.frame_owner fr)) direct reads effects /\
 accumulation fr effects.
Proof.
 intros Hreach Hstep.
 destruct (reachable_history Hreach) as [_ [[reads [effects [Htrace [Hguard Hacc]]]] _]].
 destruct (@P.fresh_commit_ready tf st fr direct k after next_fr next_k Hstep) as [_ Hclean].
 exists reads,effects. split; [|exact Hacc].
 apply B.rhs_trace_replay; [exact Htrace |].
 eapply H.guarded_reads_clean; eassumption.
Qed.
Corollary fuel_history fuel tf roots :
 valid tf (N.run_fuel fuel tf (R.initial_config roots)).
Proof. eapply reachable_history. apply fuel_steps. Qed.

Module Sem := B.Sem.
Module O := Sem.Observation.
Lemma replay_observation st body direct reads effects :
 Sem.rhs_eval st body direct reads effects ->
 exists spawns, Sem.rhs_observes body
 {| O.observed_direct := direct; O.observed_reads := reads;
 O.observed_sides := effects; O.observed_spawns := spawns |}.
Proof.
 intro Heval. induction Heval.
 - exists []. constructor.
 - destruct IHHeval as [spawns Hobs]. exists spawns. exact (@Sem.ObserveGet target value next _ Hobs).
 - destruct IHHeval as [spawns Hobs]. exists spawns. exact (@Sem.ObserveSide target value next _ Hobs).
 - destruct IHHeval as [spawns Hobs]. exists (target::spawns). exact (@Sem.ObserveSpawn target next _ Hobs).
Qed.
Lemma replay_reads st body direct reads effects :
 Sem.rhs_eval st body direct reads effects -> B.reads_agree st reads.
Proof.
 intro Heval. induction Heval; intros observed value' Hin; cbn in Hin.
 - contradiction.
 - destruct Hin as [Heq|Hin]; [inversion Heq; subst; exact H |now apply IHHeval].
 - now apply IHHeval.
 - now apply IHHeval.
Qed.
Lemma replay_read_value st body direct reads effects target value :
 Sem.rhs_eval st body direct reads effects ->
 List.In (target,value) reads -> value = R.sigma_value st target.
Proof.
 intros Heval Hin. pose proof (replay_reads Heval target value Hin) as Hlookup.
 unfold R.sigma_value. now rewrite Hlookup.
Qed.
Lemma dependency_order_gives_read_order body lower upper :
 Sem.rhs_dependencies_monotone body ->
 Sem.rhs_observes body lower -> Sem.rhs_observes body upper ->
 O.common_read_values_le lower upper ->
 O.valued_events_le (O.observed_reads lower) (O.observed_reads upper).
Proof.
 intros Hdependencies Hlower Hupper Hvalues target lower_value Hin.
 pose proof (Hdependencies lower upper Hlower Hupper Hvalues) as Hincluded.
 assert (Htarget : List.In target (List.map fst (O.observed_reads lower))).
 { apply in_map_iff. exists (target,lower_value). now split. }
 specialize (Hincluded target Htarget). apply in_map_iff in Hincluded.
 destruct Hincluded as [[upper_target upper_value] [Hequal Hinupper]].
 cbn in Hequal. subst upper_target.
 exists upper_value. split; [exact Hinupper |]. eapply Hvalues; eassumption.
Qed.
Lemma replay_effects_monotone body lower upper direct_lower reads_lower effects_lower
 direct_upper reads_upper effects_upper :
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_eval lower body direct_lower reads_lower effects_lower ->
 Sem.rhs_eval upper body direct_upper reads_upper effects_upper ->
 (forall target, D.leq (R.sigma_value lower target) (R.sigma_value upper target) = true) ->
 D.leq direct_lower direct_upper = true /\ O.valued_events_le effects_lower effects_upper.
Proof.
 intros Hdeps Heffects Hlower Hupper Hvalues.
 destruct (replay_observation Hlower) as [lower_spawns Hobslower].
 destruct (replay_observation Hupper) as [upper_spawns Hobsupper].
 assert (Hreads : O.common_read_values_le
 {| O.observed_direct := direct_lower; O.observed_reads := reads_lower;
 O.observed_sides := effects_lower; O.observed_spawns := lower_spawns |}
 {| O.observed_direct := direct_upper; O.observed_reads := reads_upper;
 O.observed_sides := effects_upper; O.observed_spawns := upper_spawns |}).
 { intros target vl vu Hl Hu. cbn in Hl,Hu.
   rewrite (@replay_read_value lower body direct_lower reads_lower effects_lower target vl Hlower Hl),
   (@replay_read_value upper body direct_upper reads_upper effects_upper target vu Hupper Hu). apply Hvalues. }
 pose proof (Heffects _ _ Hobslower Hobsupper
 (dependency_order_gives_read_order Hdeps Hobslower Hobsupper Hreads)) as Hresult.
 split; [exact (O.direct_effect_le Hresult) |exact (O.side_effects_le Hresult)].
Qed.

Lemma accumulated_effects_monotone lower upper effects_lower effects_upper :
 accumulation lower effects_lower -> accumulation upper effects_upper ->
 O.valued_events_le effects_lower effects_upper ->
 (forall target, D.leq (input lower target) (input upper target) = true) /\
 (forall target, S.mem target (R.frame_current_targets lower) = true ->
 S.mem target (R.frame_current_targets upper) = true).
Proof.
 intros [_ [Hlower Hltargets]] [Hupper [_ Hutargets]] Heffects. split.
 - apply Hlower. intros target value Hin.
   destruct (Heffects target value Hin) as [upper_value [Hu Hle]].
   destruct (Hupper target upper_value Hu) as [accumulated [Hlookup [Hcovered Hmem]]].
   unfold input. rewrite Hlookup. eapply DL.leq_trans; eassumption.
 - intros target Hmem. apply Hutargets.
   destruct (proj1 (Hltargets target) Hmem) as [value Hin].
   destruct (Heffects target value Hin) as [upper_value [Hu Hle]].
   now exists upper_value.
Qed.
Theorem commits_monotone_inputs tf roots lower frl dl kl afterl next_fl next_kl
 upper fru du ku afteru next_fu next_ku :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := lower; R.cfg_control := R.RunCommit frl dl kl |} ->
 N.next_config tf {| R.cfg_state := lower; R.cfg_control := R.RunCommit frl dl kl |} =
 Some {| R.cfg_state := afterl; R.cfg_control := R.RunDrain next_fl next_kl |} ->
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := upper; R.cfg_control := R.RunCommit fru du ku |} ->
 N.next_config tf {| R.cfg_state := upper; R.cfg_control := R.RunCommit fru du ku |} =
 Some {| R.cfg_state := afteru; R.cfg_control := R.RunDrain next_fu next_ku |} ->
 R.frame_owner frl = R.frame_owner fru ->
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fru)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fru)) ->
 (forall target, D.leq (R.sigma_value lower target) (R.sigma_value upper target) = true) ->
 D.leq dl du = true /\
 (forall target, D.leq (input frl target) (input fru target) = true) /\
 (forall target, S.mem target (R.frame_current_targets frl) = true ->
 S.mem target (R.frame_current_targets fru) = true).
Proof.
 intros Hrl Hsl Hru Hsu Howner Hdeps Heffects Hvalues.
 destruct (actual_commit_accumulation Hrl Hsl) as [rl [el [Hevall Haccl]]].
 destruct (actual_commit_accumulation Hru Hsu) as [ru [eu [Hevalu Haccu]]].
 rewrite Howner in Hevall.
 destruct (replay_effects_monotone Hdeps Heffects Hevall Hevalu Hvalues) as [Hdirect Hsides].
 split; [exact Hdirect |]. eapply accumulated_effects_monotone; eassumption.
Qed.

Lemma trace_observation body direct reads effects :
 B.rhs_trace body direct reads effects ->
 exists spawns, Sem.rhs_observes body
 {| O.observed_direct := direct; O.observed_reads := reads;
 O.observed_sides := effects; O.observed_spawns := spawns |}.
Proof.
 intro Htrace. induction Htrace.
 - exists []. constructor.
 - destruct IHHtrace as [spawns Hobs]. exists spawns.
   exact (@Sem.ObserveGet target value next _ Hobs).
 - destruct IHHtrace as [spawns Hobs]. exists spawns.
   exact (@Sem.ObserveSide target value next _ Hobs).
 - destruct IHHtrace as [spawns Hobs]. exists (target::spawns).
   exact (@Sem.ObserveSpawn target next _ Hobs).
Qed.
Lemma bottom_trace body :
 exists direct reads effects, B.rhs_trace body direct reads effects /\
 (forall target value, List.In (target,value) reads -> value = D.bottom).
Proof.
 induction body as [direct|target next IH|target value next IH|target next IH].
 - exists direct,[],[]. split; [constructor |intros x v Hin; contradiction].
 - destruct (IH D.bottom) as [direct [reads [effects [Htrace Hbottom]]]].
   exists direct,((target,D.bottom)::reads),effects. split; [now constructor |].
   intros x v [Heq|Hin]; [now inversion Heq |eapply Hbottom; exact Hin].
 - destruct IH as [direct [reads [effects [Htrace Hbottom]]]].
   exists direct,reads,((target,value)::effects). split; [now constructor |exact Hbottom].
 - destruct IH as [direct [reads [effects [Htrace Hbottom]]]].
   exists direct,reads,effects. split; [now constructor |exact Hbottom].
Qed.
Lemma prefix_effects_monotone body current prefix_reads prefix_effects upper
 direct_upper reads_upper effects_upper :
 B.rhs_context body current prefix_reads prefix_effects ->
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_eval upper body direct_upper reads_upper effects_upper ->
 (forall target value, List.In (target,value) prefix_reads ->
 D.leq value (R.sigma_value upper target) = true) ->
 O.valued_events_le prefix_effects effects_upper.
Proof.
 intros Hcontext Hdeps Heffects Hupper Hbound.
 destruct (bottom_trace current) as [direct [reads [effects [Htail Hbottom]]]].
 pose proof (Hcontext _ _ _ Htail) as Hroot.
 destruct (trace_observation Hroot) as [spawns Hlower].
 destruct (replay_observation Hupper) as [upper_spawns Hobsupper].
 assert (Hvalues : O.common_read_values_le
 {| O.observed_direct := direct; O.observed_reads := prefix_reads ++ reads;
 O.observed_sides := prefix_effects ++ effects; O.observed_spawns := spawns |}
 {| O.observed_direct := direct_upper; O.observed_reads := reads_upper;
 O.observed_sides := effects_upper; O.observed_spawns := upper_spawns |}).
 { intros target vl vu Hl Hu. cbn in Hl,Hu.
   rewrite (@replay_read_value upper body direct_upper reads_upper effects_upper target vu Hupper Hu).
   apply List.in_app_or in Hl. destruct Hl as [Hp|Hs].
   - apply Hbound,Hp.
   - rewrite (Hbottom target vl Hs). apply DL.bottom_least. }
 pose proof (Heffects _ _ Hlower Hobsupper
 (dependency_order_gives_read_order Hdeps Hlower Hobsupper Hvalues)) as Hresult.
 intros target value Hin. eapply (O.side_effects_le Hresult).
 apply List.in_or_app. now left.
Qed.
Theorem prefix_accumulated_inputs tf current fr prefix_reads prefix_effects
 upper fru direct_upper reads_upper effects_upper :
 R.frame_owner fr = R.frame_owner fru ->
 B.rhs_context (tf (R.frame_owner fr)) current prefix_reads prefix_effects ->
 accumulation fr prefix_effects -> accumulation fru effects_upper ->
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fru)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fru)) ->
 Sem.rhs_eval upper (tf (R.frame_owner fru)) direct_upper reads_upper effects_upper ->
 (forall target value, List.In (target,value) prefix_reads ->
 D.leq value (R.sigma_value upper target) = true) ->
 (forall target, D.leq (input fr target) (input fru target) = true) /\
 (forall target, S.mem target (R.frame_current_targets fr) = true ->
 S.mem target (R.frame_current_targets fru) = true).
Proof.
 intros Howner Hcontext Hacc Haccu Hdeps Heffects Hupper Hbound.
 rewrite Howner in Hcontext. eapply accumulated_effects_monotone;
 [exact Hacc |exact Haccu |].
 eapply prefix_effects_monotone; eassumption.
Qed.

Definition nonpublication control :=
 match control with R.RunDead _ _ _ _ => False | _ => True end.
Lemma base_commit_origin tf st control after fr direct k :
 nonpublication control ->
 R.next_config tf {| R.cfg_state := st; R.cfg_control := control |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunCommit fr direct k |} -> False.
Proof.
 intros Hnot Hstep. destruct control;
 cbn -[R.observe R.complete_get R.record_side_input R.write_side_contribution
 R.continue_side R.set_value R.queue_pop R.queue_peek R.reset_registered_cells] in Hstep.
 - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; discriminate.
 - destruct l as [|root rest]; [discriminate |].
   destruct (R.is_materialized (R.observe st root) root); discriminate.
 - destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; discriminate.
 - discriminate.
 - destruct r; try discriminate.
   + destruct (_ && _)%bool; [discriminate |].
     destruct (R.complete_get _ f _) as [[next next_fr] value]; discriminate.
   + destruct (R.record_side_input f t t0) as [fr1 input].
     destruct (R.write_side_contribution _ fr1 t input) as [next changed].
     unfold R.continue_side in Hstep. destruct changed; [|discriminate].
     destruct (_ && _)%bool; discriminate.
   + destruct (R.is_materialized (R.observe st t) t); [discriminate |].
     destruct (R.rank_lt (R.observe st t) (R.frame_owner f) t); discriminate.
 - exact Hnot.
 - destruct (R.set_value st f t) as [next next_fr]; discriminate.
 - destruct (R.queue_peek (R.queue st)) as [target|]; [|discriminate].
   destruct (V.eq_dec target (R.frame_owner f));
   [|destruct (R.rank_lt st (R.frame_owner f) target); [|discriminate]].
   all: destruct (R.queue_pop (R.queue st)) as [[owner rest]|]; discriminate.
 - destruct c; try discriminate.
Qed.
Lemma precommit_commit_origin tf st control after fr direct k :
 nonpublication control ->
 P.next_config tf {| R.cfg_state := st; R.cfg_control := control |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunCommit fr direct k |} -> False.
Proof.
 intros Hnot Hstep. destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep.
 all: try solve [eapply base_commit_origin; eassumption].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|];
 [discriminate |eapply base_commit_origin; eassumption].
Qed.
Lemma batched_commit_origin tf st control after fr direct k :
 nonpublication control ->
 P.next_batched tf {| R.cfg_state := st; R.cfg_control := control |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunCommit fr direct k |} -> False.
Proof.
 intros Hnot Hstep. destruct control; cbn -[P.next_config] in Hstep.
 all: try solve [eapply precommit_commit_origin; eassumption].
 - destruct r; try solve [eapply precommit_commit_origin; eassumption]. discriminate.
 - exact Hnot.
Qed.
Lemma fresh_commit_origin tf st control after fr direct k :
 nonpublication control ->
 P.next_fresh tf {| R.cfg_state := st; R.cfg_control := control |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunCommit fr direct k |} -> False.
Proof.
 intros Hnot Hstep. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
 all: try solve [eapply batched_commit_origin; [exact Hnot |exact Hstep]].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|]; [discriminate |].
   destruct (R.queue_contains (R.frame_owner f) (R.queue st)); [discriminate |].
   eapply batched_commit_origin; [|exact Hstep]; exact I.
 - destruct c; cbn -[P.next_batched] in Hstep.
   all: eapply batched_commit_origin; [|exact Hstep]; exact I.
Qed.
Lemma step_into_commit tf before after fr direct k :
 N.next_config tf before =
 Some {| R.cfg_state := after; R.cfg_control := R.RunCommit fr direct k |} ->
 exists st,
 before = {| R.cfg_state := st; R.cfg_control := R.RunDead fr direct [] k |} /\
 after = R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr.
Proof.
 intro Hstep.
 destruct (@Front.step_cases tf before
 {|R.cfg_state:=after;R.cfg_control:=R.RunCommit fr direct k|} Hstep)
 as [Hb|[st [f [body [cont [target [rest [Hbefore [Hp Hafter]]]]]]]]].
 - exact (@N.O.step_into_commit tf before after fr direct k Hb).
 - discriminate Hafter.
Qed.
Definition commit_origin c :=
 match R.cfg_control c with
 | R.RunCommit fr _ _ => exists before,
 R.cfg_state c = R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) before fr) fr
 | _ => True
 end.
Lemma next_commit_origin tf before after :
 N.next_config tf before = Some after -> commit_origin after.
Proof.
 exact (@Front.next_origin tf before after).
Qed.
Lemma steps_commit_origin tf first last :
 N.steps tf first last -> commit_origin first -> commit_origin last.
Proof.
 intro Hsteps. induction Hsteps; intro Horigin; [exact Horigin |].
 apply IHHsteps. eapply next_commit_origin; exact H.
Qed.
Theorem reachable_commit_origin tf roots st fr direct k :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
 exists before, st =
 R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) before fr) fr.
Proof.
 intro Hsteps. exact (steps_commit_origin Hsteps I).
Qed.
Theorem reachable_commit_publication_stable tf roots st fr direct k after next_fr next_k target :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
 N.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 S.mem target (R.frame_current_targets fr) = true ->
 PS.cell_stable st (R.frame_owner fr) target
 (match M.lookup (R.frame_local_side fr) target with Some value => value | None => D.bottom end).
Proof.
 intros Hreach Hstep Hmem. destruct (reachable_commit_origin Hreach) as [before ->].
 eapply PS.committing_publication_stable; [exact Hstep |exact Hmem].
Qed.
Theorem actual_commit_side_coverage tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
 N.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 exists reads effects, B.Sem.rhs_eval st (tf (R.frame_owner fr)) direct reads effects /\
 (forall target value, List.In (target,value) effects ->
 D.leq value (R.stored_contribution st (R.frame_owner fr) target) = true).
Proof.
 intros Hreach Hstep.
 destruct (actual_commit_accumulation Hreach Hstep) as [reads [effects [Heval [Hframe _]]]].
 exists reads,effects. split; [exact Heval |].
 intros target value Hin. destruct (Hframe target value Hin) as [input [Hlookup [Hle Hmem]]].
 pose proof (reachable_commit_publication_stable Hreach Hstep Hmem) as Hstable.
 apply PS.stable_covers_input in Hstable. rewrite Hlookup in Hstable.
 eapply DL.leq_trans; eassumption.
Qed.

Definition paths_below cap upper body :=
 forall lower, Sem.rhs_observes body lower ->
 O.prefix_reads_below cap (O.observed_reads lower) ->
 O.effects_le lower upper /\
 O.list_included (List.map fst (O.observed_reads lower)) (List.map fst (O.observed_reads upper)).
Lemma monotone_paths_below cap upper body :
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_observes body upper -> O.reads_at cap upper ->
 paths_below cap upper body.
Proof.
 intros Hdeps Heffects Hupper Hupperreads lower Hlower Hbound.
 assert (Hvalues : O.common_read_values_le lower upper).
 { intros target vl vu Hl Hu. rewrite (Hupperreads target vu Hu). apply Hbound,Hl. }
 split.
 - eapply Heffects; [exact Hlower |exact Hupper |].
   eapply dependency_order_gives_read_order; eassumption.
 - eapply Hdeps; eassumption.
Qed.
Lemma bottom_observation cap body :
 exists result, Sem.rhs_observes body result /\
 O.prefix_reads_below cap (O.observed_reads result).
Proof.
 destruct (bottom_trace body) as [direct [reads [effects [Htrace Hbottom]]]].
 destruct (trace_observation Htrace) as [spawns Hobs].
 eexists. split; [exact Hobs |].
 intros target value Hin. rewrite (Hbottom target value Hin). apply DL.bottom_least.
Qed.
Lemma paths_get_target cap upper target next :
 paths_below cap upper (R.ConstraintSystem.Get target next) ->
 List.In target (List.map fst (O.observed_reads upper)).
Proof.
 intro Hpaths. destruct (bottom_observation cap (next D.bottom)) as [suffix [Hobs Hbound]].
 pose proof (@Sem.ObserveGet target D.bottom next suffix Hobs) as Hwhole.
 assert (Hreads : O.prefix_reads_below cap ((target,D.bottom)::O.observed_reads suffix)).
 { intros t v [Heq|Hin]; [inversion Heq; subst; apply DL.bottom_least |apply Hbound,Hin]. }
 destruct (Hpaths _ Hwhole Hreads) as [_ Hin]. apply Hin. now left.
Qed.
Lemma paths_get_next cap upper target value next :
 paths_below cap upper (R.ConstraintSystem.Get target next) ->
 D.leq value (cap target) = true -> paths_below cap upper (next value).
Proof.
 intros Hpaths Hvalue lower Hlower Hreads.
 pose proof (@Sem.ObserveGet target value next lower Hlower) as Hwhole.
 assert (Hbound : O.prefix_reads_below cap ((target,value)::O.observed_reads lower)).
 { intros t v [Heq|Hin]; [inversion Heq; subst; exact Hvalue |apply Hreads,Hin]. }
 destruct (Hpaths _ Hwhole Hbound) as [Heffects Htargets].
 split.
 - constructor; [exact (O.direct_effect_le Heffects) |exact (O.side_effects_le Heffects) |exact (O.spawn_effects_le Heffects)].
 - intros t Hin. apply Htargets. now right.
Qed.
Lemma paths_ret cap upper direct :
 paths_below cap upper (R.ConstraintSystem.Ret direct) ->
 D.leq direct (O.observed_direct upper) = true.
Proof.
 intro Hpaths. pose proof (Sem.ObserveRet direct) as Hret.
 assert (Hreads : O.prefix_reads_below cap []) by (intros t v Hin; contradiction).
 exact (O.direct_effect_le (proj1 (Hpaths _ Hret Hreads))).
Qed.
Lemma paths_side_value cap upper target value next :
 paths_below cap upper (R.ConstraintSystem.Side target value next) ->
 exists bound, List.In (target,bound) (O.observed_sides upper) /\ D.leq value bound = true.
Proof.
 intro Hpaths. destruct (bottom_observation cap next) as [suffix [Hobs Hreads]].
 pose proof (@Sem.ObserveSide target value next suffix Hobs) as Hwhole.
 destruct (Hpaths _ Hwhole Hreads) as [Heffects _].
 apply (O.side_effects_le Heffects). now left.
Qed.
Lemma paths_side_next cap upper target value next :
 paths_below cap upper (R.ConstraintSystem.Side target value next) ->
 paths_below cap upper next.
Proof.
 intros Hpaths lower Hlower Hreads.
 destruct (Hpaths _ (@Sem.ObserveSide target value next lower Hlower) Hreads)
 as [Heffects Htargets]. split; [|exact Htargets]. constructor.
 - exact (O.direct_effect_le Heffects).
 - intros t v Hin. apply (O.side_effects_le Heffects). now right.
 - exact (O.spawn_effects_le Heffects).
Qed.
Lemma paths_spawn_target cap upper target next :
 paths_below cap upper (R.ConstraintSystem.Spawn target next) ->
 List.In target (O.observed_spawns upper).
Proof.
 intro Hpaths. destruct (bottom_observation cap next) as [suffix [Hobs Hreads]].
 destruct (Hpaths _ (@Sem.ObserveSpawn target next suffix Hobs) Hreads) as [Heffects _].
 apply (O.spawn_effects_le Heffects). now left.
Qed.
Lemma paths_spawn_next cap upper target next :
 paths_below cap upper (R.ConstraintSystem.Spawn target next) ->
 paths_below cap upper next.
Proof.
 intros Hpaths lower Hlower Hreads.
 destruct (Hpaths _ (@Sem.ObserveSpawn target next lower Hlower) Hreads)
 as [Heffects Htargets]. split; [|exact Htargets]. constructor.
 - exact (O.direct_effect_le Heffects).
 - exact (O.side_effects_le Heffects).
 - intros t Hin. apply (O.spawn_effects_le Heffects). now right.
Qed.
Lemma replay_paths_below st body direct reads effects :
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_eval st body direct reads effects ->
 exists spawns, paths_below (R.sigma_value st)
 {| O.observed_direct := direct; O.observed_reads := reads;
 O.observed_sides := effects; O.observed_spawns := spawns |} body.
Proof.
 intros Hdeps Heffects Heval.
 destruct (replay_observation Heval) as [spawns Hobs]. exists spawns.
 eapply monotone_paths_below; [exact Hdeps |exact Heffects |exact Hobs |].
 intros target value Hin.
 exact (@replay_read_value st body direct reads effects target value Heval Hin).
Qed.
Lemma bounded_side_step cap upper fr target raw next bound :
 paths_below cap upper (R.ConstraintSystem.Side target raw next) ->
 effects_bounded (O.observed_sides upper) bound ->
 frame_bounded fr bound ->
 paths_below cap upper next /\
 frame_bounded (fst (R.record_side_input fr target raw)) bound.
Proof.
 intros Hpaths Hupper Hframe. split; [eapply paths_side_next; exact Hpaths |].
 apply frame_bounded_record; [exact Hframe |].
 destruct (paths_side_value Hpaths) as [value [Hin Hle]].
 eapply DL.leq_trans; [exact Hle |apply Hupper,Hin].
Qed.

(** Materialization and frame ownership follow the repaired machine, without
    importing a base-machine reachability premise. *)
Definition materialized_step before after :=
 T.sigma_extends (R.cfg_state before) (R.cfg_state after) /\
 (T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
  T.control_owners_materialized (R.cfg_state after) (R.cfg_control after)).
Lemma base_materialized tf before after :
 R.next_config tf before = Some after -> materialized_step before after.
Proof.
 intro Hstep. split; [eapply T.next_config_sigma_extends; exact Hstep |].
 eapply T.next_config_owners_materialized; exact Hstep.
Qed.
Lemma same_sigma_owners before after control :
 R.sigma after = R.sigma before ->
 T.control_owners_materialized before control ->
 T.control_owners_materialized after control.
Proof.
 intro Heq. apply T.control_owners_materialized_mono,
 T.sigma_extends_materialized_mono, T.sigma_extends_same, Heq.
Qed.
Lemma materialized_same before after control :
 R.sigma after = R.sigma before ->
 materialized_step {|R.cfg_state:=before;R.cfg_control:=control|}
 {|R.cfg_state:=after;R.cfg_control:=control|}.
Proof. intro Heq. split; [apply T.sigma_extends_same, Heq |apply same_sigma_owners, Heq]. Qed.
Lemma materialized_trans first middle last :
 materialized_step first middle -> materialized_step middle last ->
 materialized_step first last.
Proof.
 intros [H1 Howners1] [H2 Howners2]. split.
 - eapply T.sigma_extends_trans; eassumption.
 - intro H. apply Howners2,Howners1,H.
Qed.
Lemma suspend_materialized tf st fr direct k target rest :
 materialized_step {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
 (P.suspend_commit tf st fr k target rest).
Proof.
 split; [apply T.sigma_extends_with_queue |].
 cbn. intros [Howner Hk]. split; [exact Howner |].
 eapply T.continuation_owners_materialized_mono; [|exact Hk].
 apply T.sigma_extends_materialized_mono, T.sigma_extends_with_queue.
Qed.
Lemma precommit_materialized tf before after :
 P.next_config tf before = Some after -> materialized_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_materialized; exact Hstep].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep; subst. apply suspend_materialized.
 - eapply base_materialized; exact Hstep.
Qed.
Lemma old_publish_sigma targets st fr :
 R.sigma (P.publish_accumulated targets st fr) = R.sigma st.
Proof.
 revert st. induction targets as [|target rest IH]; intro st;
 cbn -[R.write_side_contribution]; [reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 rewrite IH. destruct changed; cbn;
 eapply T.write_side_contribution_sigma; exact Hw.
Qed.
Lemma batched_materialized tf before after :
 P.next_batched tf before = Some after -> materialized_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_materialized; exact Hstep].
 - destruct r; try solve [eapply precommit_materialized; exact Hstep].
   inversion Hstep; subst. split; [apply T.sigma_extends_observe |].
   cbn. intros H. exact (@same_sigma_owners st (R.observe st t) (R.RunRhs f r c)
 (proj1 (B.same_read_view_observe st t)) H).
 - destruct l; [|eapply precommit_materialized; exact Hstep].
   inversion Hstep; subst. split.
   + apply T.sigma_extends_same. cbn. apply old_publish_sigma.
   + intro H. eapply same_sigma_owners;
     [cbn; apply old_publish_sigma |exact H].
Qed.

Lemma retry_materialized tf st fr direct k :
 materialized_step {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
 (P.retry_current tf st fr k).
Proof.
 split; [apply T.sigma_extends_with_queue |].
 cbn. intros [Howner Hk]. split; [exact Howner |].
 eapply T.continuation_owners_materialized_mono; [|exact Hk].
 apply T.sigma_extends_materialized_mono, T.sigma_extends_with_queue.
Qed.
Lemma fresh_materialized tf before after :
 P.next_fresh tf before = Some after -> materialized_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_materialized; exact Hstep].
 - eapply materialized_trans; [|eapply batched_materialized; exact Hstep].
   apply materialized_same. reflexivity.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep; subst. apply suspend_materialized.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep; subst. apply retry_materialized.
     * eapply batched_materialized; exact Hstep.
 - destruct c; cbn -[P.next_batched] in Hstep;
     try solve [eapply batched_materialized; exact Hstep].
   eapply materialized_trans; [|eapply batched_materialized; exact Hstep].
   apply materialized_same. reflexivity.
Qed.
Lemma requeue_sigma before after source target :
 R.sigma (C.requeue_source before after source target) = R.sigma after.
Proof. unfold C.requeue_source. destruct C.cell_changed; reflexivity. Qed.
Lemma finish_sigma before after fr target changed :
 R.sigma (C.finish_write before after fr target changed) = R.sigma after.
Proof. unfold C.finish_write. destruct changed; cbn; apply requeue_sigma. Qed.
Lemma publish_sigma targets st fr :
 R.sigma (C.publish targets st fr) = R.sigma st.
Proof.
 revert st. induction targets as [|target rest IH]; intro st;
 cbn -[R.write_side_contribution C.finish_write]; [reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 rewrite IH, finish_sigma. eapply T.write_side_contribution_sigma; exact Hw.
Qed.
Lemma continue_dead_materialized st fr direct target rest k changed :
 materialized_step {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct rest k|}
 (R.continue_dead st fr direct target rest k changed).
Proof.
 split; [apply T.sigma_extends_continue_dead |].
 unfold R.continue_dead. destruct changed; [|exact (fun H=>H)].
 destruct (R.rank_lt st (R.frame_owner fr) target &&
 negb (R.is_materialized st target))%bool; cbn; intro H; [exact H |].
 exact (@same_sigma_owners st (R.enqueue st target)
 (R.RunDead fr direct rest k) eq_refl H).
Qed.
Lemma next_materialized tf before after :
 N.next_config tf before = Some after -> materialized_step before after.
Proof.
 intro Hstep.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.next_materialized tf before after Hb).
 - split;[apply T.sigma_extends_with_queue |].
   intro Ho. eapply Front.resume_materialized;exact Ho.
Qed.
Lemma steps_materialized tf before after :
 N.steps tf before after -> materialized_step before after.
Proof.
 intro Hsteps. induction Hsteps.
 - split; [apply T.sigma_extends_refl |exact (fun H=>H)].
 - eapply materialized_trans; [eapply next_materialized; exact H |exact IHHsteps].
Qed.
Theorem reachable_owners_materialized tf roots c :
 N.steps tf (R.initial_config roots) c ->
 T.control_owners_materialized (R.cfg_state c) (R.cfg_control c).
Proof. intro Hsteps. apply (proj2 (steps_materialized Hsteps)). exact I. Qed.
Theorem steps_preserve_solved tf before after owner :
 N.steps tf before after -> Sem.solved (R.cfg_state before) owner ->
 Sem.solved (R.cfg_state after) owner.
Proof.
 intros Hsteps [value Hlookup].
 exact (proj1 (steps_materialized Hsteps) owner value Hlookup).
Qed.
Theorem reachable_commit_owner_solved tf roots st fr direct k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st; R.cfg_control:=R.RunCommit fr direct k|} ->
 Sem.solved st (R.frame_owner fr).
Proof.
 intro Hreach. apply B.materialized_solved.
 exact (proj1 (reachable_owners_materialized Hreach)).
Qed.

(** A completed publication records the whole frame even when some updates
    change representation or phase.  This gives an actual commit summary. *)
Lemma finish_contributions before after fr target changed :
 R.contributions (C.finish_write before after fr target changed) = R.contributions after.
Proof.
 unfold C.finish_write, C.requeue_source. destruct changed;
 destruct C.cell_changed; reflexivity.
Qed.
Lemma publish_other_row targets st fr observed :
 ~ List.In observed targets ->
 R.lookup_map (R.contributions (C.publish targets st fr)) observed =
 R.lookup_map (R.contributions st) observed.
Proof.
 revert st. induction targets as [|target rest IH]; intros st Houtside;
 cbn -[R.write_side_contribution C.finish_write]; [reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 rewrite IH by (intro Hin; apply Houtside; now right).
 rewrite finish_contributions. eapply B.write_side_contribution_other; [exact Hw |].
 intro Heq; apply Houtside; now left.
Qed.
Lemma publish_covers_input targets st fr target raw :
 List.In target targets -> M.lookup (R.frame_local_side fr) target = Some raw ->
 exists contribution,
 M.lookup (R.lookup_map (R.contributions (C.publish targets st fr)) target)
 (R.frame_owner fr) = Some contribution /\ D.leq raw contribution = true.
Proof.
 revert st target raw. induction targets as [|head rest IH];
 intros st target raw Hin Hinput; [contradiction |].
 cbn -[R.write_side_contribution C.finish_write].
 destruct (R.write_side_contribution st fr head
 (match M.lookup (R.frame_local_side fr) head with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 destruct (List.in_dec V.eq_dec target rest) as [Hrest|Houtside].
 - eapply IH; eauto.
 - destruct Hin as [->|Hin]; [|contradiction].
   rewrite publish_other_row by exact Houtside. rewrite finish_contributions.
   rewrite Hinput in Hw. eapply B.write_side_contribution_records_input; exact Hw.
Qed.
Theorem publish_records_frame st fr effects :
 B.frame_effects fr effects ->
 B.recorded_effects (C.publish (S.elements (R.frame_current_targets fr)) st fr)
 (R.frame_owner fr) effects.
Proof.
 intros Hframe target value Hin.
 destruct (Hframe target value Hin) as [raw [Hinput [Hle Hmem]]].
 apply SL.mem_spec in Hmem.
 destruct (@publish_covers_input (S.elements (R.frame_current_targets fr))
 st fr target raw Hmem Hinput) as [contribution [Hstored Hcovered]].
 exists contribution. split; [exact Hstored |].
 eapply DL.leq_trans; eassumption.
Qed.
Theorem reachable_commit_witness tf roots st fr direct k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st; R.cfg_control:=R.RunCommit fr direct k|} ->
 B.completed_witness tf st fr direct.
Proof.
 exact (@Front.commit_witness tf roots st fr direct k).
Qed.
Theorem actual_commit_summary tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st; R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st; R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after; R.cfg_control:=R.RunDrain next_fr next_k|} ->
 B.summary_valid tf after (R.frame_owner fr).
Proof.
 exact (@Front.actual_commit_summary tf roots st fr direct k after next_fr next_k).
Qed.

(** A target with an uncovered aggregate remains scheduled.  This invariant
    concerns incoming contributions; it is not the all-owner replay invariant. *)
Definition aggregate_guarded st control :=
 forall target, B.queued st target \/ B.control_active target control \/ B.aggregate_bounded st target.
Lemma base_aggregate tf before after :
 R.next_config tf before = Some after ->
 aggregate_guarded (R.cfg_state before) (R.cfg_control before) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof. intros Hstep Hguard target. eapply B.next_config_aggregate_guarded; eauto. Qed.
Lemma aggregate_same before after first next :
 R.sigma after = R.sigma before -> R.contributions after = R.contributions before ->
 (forall target, B.queued before target ->
 B.queued after target \/ B.control_active target next) ->
 (forall target, B.control_active target first -> B.control_active target next) ->
 aggregate_guarded before first -> aggregate_guarded after next.
Proof.
 intros Hsigma Hcontrib Hqueue Hactive Hguard target.
 destruct (Hguard target) as [Hq|[Ha|Hb]].
 - destruct (Hqueue target Hq); [now left |now right; left].
 - right; left. apply Hactive,Ha.
 - right; right. unfold B.aggregate_bounded, R.aggregate,R.sigma_value in *.
   now rewrite Hcontrib,Hsigma.
Qed.
Lemma suspend_aggregate tf st fr direct k target rest :
 P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 aggregate_guarded st (R.RunCommit fr direct k) ->
 aggregate_guarded (R.cfg_state (P.suspend_commit tf st fr k target rest))
 (R.cfg_control (P.suspend_commit tf st fr k target rest)).
Proof.
 intro Hpending. eapply aggregate_same; [reflexivity |reflexivity | |].
 - intros x Hq. destruct (V.eq_dec x target) as [->|Hneq]; [right; now left |].
   left. destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hpending) as [_ [Hpop _]].
   unfold B.queued,R.queue_pop in *. destruct (R.queue st) as [|head tail];
   [discriminate |]. inversion Hpop; subst. cbn in *. destruct Hq as [->|Hq]; auto; contradiction.
 - intros x Hactive. cbn in *. now right.
Qed.
Lemma precommit_aggregate tf before after :
 P.next_config tf before = Some after ->
 aggregate_guarded (R.cfg_state before) (R.cfg_control before) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hstep Hguard. destruct control;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_aggregate; eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep; subst. eapply suspend_aggregate; eauto.
 - eapply base_aggregate; eauto.
Qed.
Definition aggregate_or_queued st target :=
 B.queued st target \/ B.aggregate_bounded st target.
Lemma aggregate_or_queued_enqueue st inserted target :
 aggregate_or_queued st target -> aggregate_or_queued (R.enqueue st inserted) target.
Proof.
 intros [Hq|Hb]; [left; apply B.queued_enqueue,Hq |right; exact Hb].
Qed.
Lemma write_aggregate_or_queued st fr target raw next changed observed :
 R.write_side_contribution st fr target raw = (next,changed) ->
 aggregate_or_queued st observed ->
 aggregate_or_queued (if changed then R.enqueue next target else next) observed.
Proof.
 intros Hw [Hq|Hb].
 - assert (Hnext : B.queued next observed) by (eapply B.queued_write_side; eauto).
   destruct changed; left; [apply B.queued_enqueue,Hnext |exact Hnext].
 - destruct (V.eq_dec observed target) as [->|Hneq].
   + destruct changed; [left; unfold B.queued,R.enqueue; cbn; apply B.queue_insert_members; now left |right].
     eapply B.aggregate_bounded_write_unchanged; eassumption.
   + assert (Hnext : B.aggregate_bounded next observed)
       by (eapply B.aggregate_bounded_write_other; eauto).
     destruct changed; right; exact Hnext.
Qed.
Lemma old_publish_aggregate targets st fr observed :
 aggregate_or_queued st observed ->
 aggregate_or_queued (P.publish_accumulated targets st fr) observed.
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hguard;
 cbn -[R.write_side_contribution]; [exact Hguard |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH. eapply write_aggregate_or_queued; eassumption.
Qed.
Lemma batched_aggregate tf before after :
 P.next_batched tf before = Some after ->
 aggregate_guarded (R.cfg_state before) (R.cfg_control before) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hstep Hguard. destruct control;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_aggregate; eauto].
 - destruct r; try solve [eapply precommit_aggregate; eauto].
   inversion Hstep; subst. eapply aggregate_same;
   [exact (proj1 (B.same_read_view_observe st t))
   |exact (proj2 (B.observe_same_solver_view st t))
   |intros x Hq; left; apply B.queued_observe,Hq
   |intros x Ha; exact Ha |exact Hguard].
 - destruct l; [|eapply precommit_aggregate; eauto].
   inversion Hstep; subst. intro target.
   destruct (Hguard target) as [Hq|[Ha|Hb]]; [|right; left; exact Ha |].
   all: assert (Haq : aggregate_or_queued st target) by (first [now left |now right]).
   all: destruct (@old_publish_aggregate
     (S.elements (R.frame_current_targets f)) st f target Haq)
     as [Hq'|Hb']; [left;exact Hq'|right;right;exact Hb'].
Qed.
Lemma clear_active_aggregate st owner control :
 B.control_active owner control -> aggregate_guarded st control ->
 aggregate_guarded (P.clear_owner st owner) control.
Proof.
 intro Hactive. eapply aggregate_same; [reflexivity |reflexivity | |exact (fun _ H=>H)].
 intros target Hq. destruct (V.eq_dec target owner) as [->|Hneq].
 - right; exact Hactive.
 - left. apply P.clear_owner_members. now split.
Qed.
Lemma retry_aggregate tf st fr direct k :
 aggregate_guarded st (R.RunCommit fr direct k) ->
 aggregate_guarded (R.cfg_state (P.retry_current tf st fr k))
 (R.cfg_control (P.retry_current tf st fr k)).
Proof.
 intro Hguard. apply (@clear_active_aggregate st (R.frame_owner fr)
 (R.RunRhs (R.fresh_frame (P.clear_owner st (R.frame_owner fr))
 (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)).
 - now left.
 - exact Hguard.
Qed.
Lemma fresh_aggregate tf before after :
 P.next_fresh tf before = Some after ->
 aggregate_guarded (R.cfg_state before) (R.cfg_control before) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hstep Hguard. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_aggregate; eauto].
 - eapply batched_aggregate; [exact Hstep |].
   apply clear_active_aggregate; [now left |exact Hguard].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep; subst. eapply suspend_aggregate; eauto.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep; subst. eapply retry_aggregate; exact Hguard.
     * eapply batched_aggregate; eauto.
 - destruct c; cbn -[P.next_batched] in Hstep;
     try solve [eapply batched_aggregate; eauto].
   eapply batched_aggregate; [exact Hstep |].
   apply clear_active_aggregate; [now left |exact Hguard].
Qed.
Lemma write_finish_aggregate st fr target raw next changed observed :
 R.write_side_contribution st fr target raw = (next,changed) ->
 aggregate_or_queued st observed ->
 aggregate_or_queued (C.finish_write st next fr target changed) observed.
Proof.
 intros Hw [Hq|Hb].
 - left. apply C.finish_keeps_queued. eapply B.queued_write_side; eassumption.
 - destruct (V.eq_dec observed target) as [->|Hneq].
   + destruct changed.
     * left. unfold C.finish_write, B.queued,R.enqueue. cbn.
       apply B.queue_insert_members. now left.
     * right. unfold B.aggregate_bounded,R.aggregate,R.sigma_value.
       rewrite finish_contributions,finish_sigma.
       eapply B.aggregate_bounded_write_unchanged; eassumption.
   + right. unfold B.aggregate_bounded,R.aggregate,R.sigma_value.
     rewrite finish_contributions,finish_sigma.
     eapply B.aggregate_bounded_write_other; eassumption.
Qed.
Lemma publish_aggregate targets st fr observed :
 aggregate_or_queued st observed ->
 aggregate_or_queued (C.publish targets st fr) observed.
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hguard;
 cbn -[R.write_side_contribution C.finish_write]; [exact Hguard |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH. eapply write_finish_aggregate; eassumption.
Qed.
Lemma requeue_contributions before after source target :
 R.contributions (C.requeue_source before after source target) = R.contributions after.
Proof. unfold C.requeue_source. destruct C.cell_changed; reflexivity. Qed.
Lemma continue_dead_aggregate_core st fr direct target rest k changed :
 (forall observed, observed <> target \/ changed = false ->
 aggregate_or_queued st observed \/ B.control_active observed (R.RunDead fr direct rest k)) ->
 aggregate_guarded (R.cfg_state (R.continue_dead st fr direct target rest k changed))
 (R.cfg_control (R.continue_dead st fr direct target rest k changed)).
Proof.
 intros Hguard observed. unfold R.continue_dead. destruct changed.
 - destruct (R.rank_lt st (R.frame_owner fr) target &&
   negb (R.is_materialized st target))%bool.
   + destruct (V.eq_dec observed target) as [->|Hneq]; [right;left;now left |].
     destruct (Hguard observed (or_introl Hneq)) as [[Hq|Hb]|Ha];
     [now left |right;right;exact Hb |right;left;now right].
   + destruct (V.eq_dec observed target) as [->|Hneq].
     * left. unfold B.queued,R.enqueue. cbn. apply B.queue_insert_members. now left.
     * destruct (Hguard observed (or_introl Hneq)) as [[Hq|Hb]|Ha];
       [left;apply B.queued_enqueue,Hq |right;right;exact Hb |right;left;exact Ha].
 - destruct (Hguard observed (or_intror eq_refl)) as [[Hq|Hb]|Ha];
   [now left |right;right;exact Hb |right;left;exact Ha].
Qed.

Lemma dead_pending_aggregate tf st fr direct target rest k after :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 = Some after -> aggregate_guarded st (R.RunDead fr direct (target::rest) k) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hstep Hguard.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)); [inversion Hstep;subst;exact Hguard |].
 destruct (R.write_side_contribution st fr target D.bottom)
 as [next changed] eqn:Hw. inversion Hstep; subst.
 apply continue_dead_aggregate_core. intros observed Hcondition.
 destruct (Hguard observed) as [Hq|[Ha|Hb]]; [left;left |right;exact Ha |left;right].
 - apply C.requeue_members. left. eapply B.queued_write_side; eassumption.
 - unfold B.aggregate_bounded,R.aggregate,R.sigma_value.
   rewrite requeue_contributions,requeue_sigma.
   destruct Hcondition as [Hneq | ->].
   + eapply B.aggregate_bounded_write_other; eassumption.
   + destruct (V.eq_dec observed target) as [->|Hneq].
     * eapply B.aggregate_bounded_write_unchanged; eassumption.
     * eapply B.aggregate_bounded_write_other; eassumption.
Qed.
Theorem next_aggregate tf before after :
 N.next_config tf before = Some after ->
 aggregate_guarded (R.cfg_state before) (R.cfg_control before) ->
 aggregate_guarded (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hstep Hg. eapply (@Front.preserves tf (fun c => aggregate_guarded (R.cfg_state c) (R.cfg_control c)));[ | |exact Hstep |exact Hg].
 - intros. eapply N.O.next_aggregate;eauto.
 - intros st fr body k target rest Hp Ha.
   apply (@N.O.suspend_aggregate tf st fr D.bottom k target rest Hp). exact Ha.
Qed.
Lemma steps_aggregate tf first last :
 N.steps tf first last ->
 aggregate_guarded (R.cfg_state first) (R.cfg_control first) ->
 aggregate_guarded (R.cfg_state last) (R.cfg_control last).
Proof.
 intro Hsteps. induction Hsteps; intro Hguard; [exact Hguard |].
 apply IHHsteps. eapply next_aggregate; eassumption.
Qed.
Theorem reachable_aggregate tf roots c :
 N.steps tf (R.initial_config roots) c ->
 aggregate_guarded (R.cfg_state c) (R.cfg_control c).
Proof.
 intro Hreach. eapply steps_aggregate; [exact Hreach |].
 intro target. right;right. apply B.initial_aggregate_bounded.
Qed.
Theorem terminal_aggregates_bounded tf roots final :
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
 Sem.quiescent final ->
 forall target, D.leq (R.aggregate final target) (R.sigma_value final target) = true.
Proof.
 intros Hreach Hquiet target.
 destruct (reachable_aggregate Hreach target) as [Hq|[Ha|Hb]]; [|contradiction |exact Hb].
 exfalso. exact (@B.quiescent_not_queued final target Hquiet Hq).
Qed.

Theorem successful_run_aggregates_bounded fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall target, D.leq (R.aggregate final target) (R.sigma_value final target) = true.
Proof.
 intro Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve) as [Hshape Hquiet].
 eapply terminal_aggregates_bounded; [|exact Hquiet].
 rewrite <- Hshape. apply fuel_steps.
Qed.
(** Summaries survive scheduling unless the owner is queued or active.
    Actual commits reconstruct them from the proved publication witness. *)
Definition summary_guarded tf st control owner :=
 B.queued st owner \/ B.control_active owner control \/ B.summary_valid tf st owner.
Lemma summary_pop tf st popped rest next owner :
 R.queue_pop (R.queue st) = Some (popped,rest) ->
 B.control_active popped next -> B.summary_valid tf st owner ->
 summary_guarded tf (R.with_queue st rest) next owner.
Proof.
 intros Hpop Hactive Hsummary. destruct (V.eq_dec owner popped) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. eapply B.summary_valid_pop_other; eassumption.
Qed.
Lemma summary_clear tf st cleared next owner :
 B.control_active cleared next -> B.summary_valid tf st owner ->
 summary_guarded tf (P.clear_owner st cleared) next owner.
Proof.
 intros Hactive Hsummary. destruct (V.eq_dec owner cleared) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. destruct Hsummary as [Hsolved [direct [reads [effects
   [Htrace [Hreads [Heffects Hdirect]]]]]]].
   split; [exact Hsolved |]. exists direct,reads,effects.
   split; [exact Htrace |]. split; [eapply P.clear_other_guarded_reads; eassumption |].
   split; assumption.
Qed.
Lemma summary_get tf st fr target next k owner after :
 B.summary_valid tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : B.summary_valid tf (R.observe st target) owner)
 by (apply B.summary_valid_observe,Hsummary).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. right;right;exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. right;right.
   eapply B.summary_valid_complete_get; [exact Hg |].
   subst current. destruct (R.is_materialized (R.observe st target) target);
   [exact Hobs |apply B.summary_valid_enqueue,Hobs].
Qed.
Lemma summary_spawn tf st fr target next k owner after :
 B.summary_valid tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : B.summary_valid tf (R.observe st target) owner)
 by (apply B.summary_valid_observe,Hsummary).
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst. right;right;exact Hobs.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;right;right;[exact Hobs |].
   apply B.summary_valid_materialize,B.summary_valid_enqueue,Hobs.
Qed.
Lemma summary_drain tf st fr k owner after :
 B.summary_valid tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hq in Hstep; cbn in Hstep.
 - inversion Hstep;subst. right;right.
   eapply B.summary_valid_same_solver_view; [apply B.reset_registered_cells_same_solver_view |exact Hsummary].
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst. eapply summary_pop;
     [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. eapply summary_pop;
       [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
     * inversion Hstep;subst. right;right.
       eapply B.summary_valid_same_solver_view; [apply B.reset_registered_cells_same_solver_view |exact Hsummary].
Qed.
Lemma summary_return tf st k owner after :
 B.summary_valid tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;right;right;exact Hsummary].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. right;right. eapply B.summary_valid_complete_get; eassumption.
Qed.
Definition commit_completed tf st control :=
 match control with R.RunCommit fr direct _ => B.completed_witness tf st fr direct | _ => True end.
Lemma summary_base tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 B.summary_valid tf (R.cfg_state before) owner ->
 R.next_config tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hcompleted Hsummary Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp; [|discriminate].
   inversion Hstep;subst. eapply summary_pop; [exact Hp |now left |exact Hsummary].
 - destruct l; cbn -[R.observe] in Hstep.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + destruct (R.is_materialized (R.observe st t) t);
     inversion Hstep;subst;right;right;apply B.summary_valid_observe,Hsummary.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply summary_pop; [exact Hp |now left |exact Hsummary].
   + inversion Hstep;subst. right;right;exact Hsummary.
 - inversion Hstep;subst. right;right;apply B.summary_valid_materialize,Hsummary.
 - destruct r.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + eapply summary_get; eassumption.
   + contradiction.
   + eapply summary_spawn; eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. right;right. apply B.summary_valid_requeue.
   destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq].
   + eapply B.completed_witness_set_value_summary; [exact Hcompleted |exact Hs].
   + eapply B.summary_valid_set_value_other; eassumption.
 - eapply summary_drain; eassumption.
 - eapply summary_return; eassumption.
Qed.

Lemma clear_summary_other tf st cleared owner :
 owner <> cleared -> B.summary_valid tf st owner ->
 B.summary_valid tf (P.clear_owner st cleared) owner.
Proof.
 intros Hneq [Hsolved [direct [reads [effects [Htrace [Hreads [Heffects Hdirect]]]]]]].
 split; [exact Hsolved |]. exists direct,reads,effects.
 split; [exact Htrace |]. split; [eapply P.clear_other_guarded_reads; eassumption |].
 split; assumption.
Qed.
Lemma summary_precommit tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 B.summary_valid tf (R.cfg_state before) owner ->
 P.next_config tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hcompleted Hsummary Hstep.
 destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply summary_base; eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply summary_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
   |now left |exact Hsummary].
 - eapply summary_base; eauto.
Qed.
Lemma summary_batched tf before after owner :
 nonpublication (R.cfg_control before) ->
 commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 B.summary_valid tf (R.cfg_state before) owner ->
 P.next_batched tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hcompleted Hsummary Hstep.
 destruct control; cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply summary_precommit; [ | | |exact Hsummary |exact Hstep]; [exact I |exact Hdead |exact Hcompleted]].
 - destruct r;
   try solve [eapply summary_precommit; [ | | |exact Hsummary |exact Hstep]; [exact I |exact Hdead |exact Hcompleted]].
   inversion Hstep;subst. right;right. apply B.summary_valid_observe,Hsummary.
 - contradiction.
Qed.
Lemma summary_fresh tf before after owner :
 nonpublication (R.cfg_control before) ->
 commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 B.summary_valid tf (R.cfg_state before) owner ->
 P.next_fresh tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hcompleted Hsummary Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply summary_batched; eauto].
 - inversion Hstep;subst. destruct (V.eq_dec owner t) as [->|Hneq].
   + right;left;now left.
   + right;right. apply B.summary_valid_materialize,clear_summary_other; assumption.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply summary_pop;
     [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
     |now left |exact Hsummary].
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply summary_clear; [now left |exact Hsummary].
     * eapply summary_batched; eauto.
 - destruct c; cbn -[P.next_batched] in Hstep;
   try solve [eapply summary_batched; eauto].
   inversion Hstep;subst. apply summary_clear; [now left |exact Hsummary].
Qed.
Lemma finish_summary tf before after fr target changed owner :
 B.summary_valid tf after owner ->
 B.summary_valid tf (C.finish_write before after fr target changed) owner.
Proof.
 unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;
 intro H; auto using B.summary_valid_enqueue.
Qed.
Lemma publish_other_summary tf targets st fr owner :
 owner <> R.frame_owner fr -> B.summary_valid tf st owner ->
 B.summary_valid tf (C.publish targets st fr) owner.
Proof.
 intro Hneq. revert st. induction targets as [|target rest IH]; intros st Hsummary;
 cbn -[R.write_side_contribution C.finish_write]; [exact Hsummary |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH,finish_summary. eapply B.summary_valid_write_other_source; eassumption.
Qed.
Lemma dead_pending_summary tf st fr direct target rest k owner after :
 B.summary_valid tf st owner ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 = Some after -> summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)).
 - inversion Hstep;subst. right;right;exact Hsummary.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hneq].
   + unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;left;cbn;auto.
   + assert (Hs : B.summary_valid tf next owner)
     by (eapply B.summary_valid_write_other_source; eassumption).
     assert (Hq : B.summary_valid tf (C.requeue_source st next (R.frame_owner fr) target) owner).
     { unfold C.requeue_source. destruct C.cell_changed;
       [apply B.summary_valid_enqueue,Hs |exact Hs]. }
     unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;right;cbn;auto using B.summary_valid_enqueue.
Qed.
Theorem next_preserves_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 B.summary_valid tf (R.cfg_state before) owner ->
 N.next_config tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 exact (@Front.next_preserves_summary tf roots before after owner).
Qed.

(** The repaired scheduler cannot lose pending owner work. *)
Definition scheduled st control owner := B.queued st owner \/ B.control_active owner control.
Definition schedule_step before after :=
 forall owner, scheduled (R.cfg_state before) (R.cfg_control before) owner ->
 scheduled (R.cfg_state after) (R.cfg_control after) owner \/ B.commit_discharge before after owner.
Lemma base_schedule tf before after :
 R.next_config tf before = Some after -> schedule_step before after.
Proof.
 intros Hstep owner [Hq|Ha].
 - left. eapply B.queued_step_scheduled; eassumption.
 - destruct (@B.active_step_scheduled_or_commit tf before after owner Ha Hstep)
   as [Hq|[Ha'|Hcommit]]; [left;left |left;right |right]; assumption.
Qed.
Lemma suspend_schedule tf st fr direct k target rest :
 P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 schedule_step {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
 (P.suspend_commit tf st fr k target rest).
Proof.
 intros Hp owner [Hq|Ha]; left.
 - destruct (V.eq_dec owner target) as [->|Hneq]; [right;now left |left].
   destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop _]].
   unfold B.queued,R.queue_pop in *. destruct (R.queue st) as [|head tail] eqn:Hqueue;
   [discriminate |]. inversion Hpop;subst. cbn in *. rewrite Hqueue in Hq. destruct Hq as [->|Hq]; auto;contradiction.
 - right. cbn in *. now right.
Qed.
Lemma precommit_schedule tf before after :
 P.next_config tf before = Some after -> schedule_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_schedule;exact Hstep].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. apply suspend_schedule,Hp.
 - eapply base_schedule;exact Hstep.
Qed.
Lemma old_publish_queued targets st fr owner :
 B.queued st owner -> B.queued (P.publish_accumulated targets st fr) owner.
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hq;
 cbn -[R.write_side_contribution]; [exact Hq |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH. assert (Hnext : B.queued next owner) by (eapply B.queued_write_side; eassumption).
 destruct changed; [apply B.queued_enqueue,Hnext |exact Hnext].
Qed.
Lemma batched_schedule tf before after :
 P.next_batched tf before = Some after -> schedule_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_schedule;exact Hstep].
 - destruct r;try solve [eapply precommit_schedule;exact Hstep].
   inversion Hstep;subst. intros owner [Hq|Ha];left;
   [left;apply B.queued_observe,Hq |right;exact Ha].
 - destruct l; [|eapply precommit_schedule;exact Hstep].
   inversion Hstep;subst. intros owner [Hq|Ha];left;
   [left;apply old_publish_queued,Hq |right;exact Ha].
Qed.
Lemma clear_scheduled st cleared first next owner :
 B.control_active cleared next ->
 (B.control_active owner first -> B.control_active owner next) ->
 scheduled st first owner -> scheduled (P.clear_owner st cleared) next owner.
Proof.
 intros Hcleared Hactive [Hq|Ha]; [|right;apply Hactive,Ha].
 destruct (V.eq_dec owner cleared) as [->|Hneq].
 - right;exact Hcleared.
 - left. apply P.clear_owner_members. now split.
Qed.
Lemma fresh_schedule tf before after :
 P.next_fresh tf before = Some after -> schedule_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_schedule;exact Hstep].
 - inversion Hstep;subst. intros owner Hscheduled. left.
   assert (Hclear : scheduled (P.clear_owner st t) (R.RunRhs
     (R.fresh_frame (R.materialize (P.clear_owner st t) t) t (U.initial_phase false t)) (tf t) c) owner).
   { eapply clear_scheduled; [now left |exact (fun H=>H) |exact Hscheduled]. }
   destruct Hclear as [Hq|Ha]; [left;apply B.queued_materialize,Hq |right;exact Ha].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. apply suspend_schedule,Hp.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. intros owner Hscheduled. left.
       eapply clear_scheduled; [now left |exact (fun H=>H) |exact Hscheduled].
     * eapply batched_schedule;exact Hstep.
 - destruct c; cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_schedule;exact Hstep].
   inversion Hstep;subst. intros owner Hscheduled. left.
   eapply clear_scheduled; [now left |exact (fun H=>H) |exact Hscheduled].
Qed.
Lemma next_schedule tf before after :
 N.next_config tf before = Some after -> schedule_step before after.
Proof.
 exact (@Front.next_schedule tf before after).
Qed.
Theorem next_guarded_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 summary_guarded tf (R.cfg_state before) (R.cfg_control before) owner ->
 N.next_config tf before = Some after ->
 summary_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 exact (@Front.next_guarded_summary tf roots before after owner).
Qed.

(** A nested Get returns from the demanded owner's episode.  Frame
    materialization supplies the target value before the waiting read resumes. *)
Lemma get_consistent_sigma before after control :
 R.sigma after = R.sigma before -> B.control_get_consistent before control ->
 B.control_get_consistent after control.
Proof.
 intros Hsigma Hconsistent. destruct control;try exact Hconsistent.
 destruct c;try exact Hconsistent.
 destruct Hconsistent as [[value Hlookup] Htail]. split;[|exact Htail].
 exists value. now rewrite Hsigma.
Qed.
Lemma complete_get_consistent st fr target next k after after_fr value :
 R.complete_get st fr target = (after,after_fr,value) ->
 B.control_get_consistent st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 B.control_get_consistent after (R.RunRhs after_fr (next value) k).
Proof.
 intros Hg [Hhead Htail]. split; [|exact Htail].
 rewrite (@B.complete_get_frame_owner st fr target after after_fr value Hg). exact Hhead.
Qed.
Lemma base_read_consistent tf st fr target next k after :
 B.control_get_consistent st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hconsistent Hstep. cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. split;[reflexivity |exact Hconsistent].
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[next_st next_fr] value] eqn:Hg.
   inversion Hstep;subst. eapply complete_get_consistent;[exact Hg |exact Hconsistent].
Qed.
Lemma base_spawn_consistent tf st fr target next k after :
 B.control_get_consistent st (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hconsistent Hstep. cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target);
 [inversion Hstep;subst;exact Hconsistent |].
 destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
 inversion Hstep;subst;[split;[exact I |exact Hconsistent] |exact Hconsistent].
Qed.
Lemma drain_returns_ready st fr k :
 Sem.solved st (R.frame_owner fr) ->
 B.control_get_consistent st (R.RunDrain fr k) ->
 B.control_get_consistent (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k).
Proof.
 intros Hsolved [Hexpect Htail]. split;[|exact Htail].
 destruct k;try exact I. cbn in Hexpect. rewrite <- Hexpect.
 eapply B.solved_same_solver_view;[apply B.reset_registered_cells_same_solver_view |exact Hsolved].
Qed.
Lemma base_drain_consistent tf st fr k after :
 T.control_owners_materialized st (R.RunDrain fr k) ->
 B.control_get_consistent st (R.RunDrain fr k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 intros [Howner Howners] Hconsistent Hstep.
 assert (Hs : Sem.solved st (R.frame_owner fr)) by (apply B.materialized_solved,Howner).
 destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hq in Hstep;cbn in Hstep.
 - inversion Hstep;subst. apply drain_returns_ready;assumption.
 - destruct (V.eq_dec target (R.frame_owner fr)).
   + inversion Hstep;subst. exact Hconsistent.
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. split;[exact I |exact Hconsistent].
     * inversion Hstep;subst. apply drain_returns_ready;assumption.
Qed.
Lemma base_return_consistent tf st k after :
 B.control_get_consistent st (R.Return k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|} = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 intros [Hready Htail] Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;exact I |inversion Hstep;subst;exact Htail].
Qed.
Lemma base_consistent tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 R.next_config tf before = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hside Hdead Howners Hconsistent Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|];
   [inversion Hstep;subst;split;exact I |discriminate].
 - destruct l;cbn -[R.observe] in Hstep;try destruct (R.is_materialized (R.observe st t) t);
   inversion Hstep;subst;cbn;auto.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|];
   inversion Hstep;subst;cbn;auto.
 - inversion Hstep;subst. exact Hconsistent.
 - destruct r.
   + inversion Hstep;subst;exact Hconsistent.
   + eapply base_read_consistent;eassumption.
   + contradiction.
   + eapply base_spawn_consistent;eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. destruct Hconsistent as [Hhead Htail]. split;[|exact Htail].
   rewrite (@B.set_value_frame_owner st f t next next_fr Hs). exact Hhead.
 - eapply base_drain_consistent;eassumption.
 - eapply base_return_consistent;eassumption.
Qed.

Lemma precommit_consistent tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_config tf before = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hside Hdead Howners Hconsistent Hstep.
 destruct control;cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_consistent;eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. split;[exact I |exact Hconsistent].
 - eapply base_consistent;eauto.
Qed.
Lemma batched_consistent tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_batched tf before = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hdead Howners Hconsistent Hstep.
 destruct control;cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply precommit_consistent; [ | | | |exact Hstep]; eauto; exact I].
 - destruct r;
   try solve [eapply precommit_consistent; [ | | | |exact Hstep]; eauto; exact I].
   inversion Hstep;subst. exact Hconsistent.
 - contradiction.
Qed.
Lemma fresh_consistent tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_fresh tf before = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hdead Howners Hconsistent Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_consistent;eauto].
 - inversion Hstep;subst. exact Hconsistent.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. split;[exact I |exact Hconsistent].
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst;exact Hconsistent.
     * eapply batched_consistent;eauto.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_consistent;eauto].
   inversion Hstep;subst. exact (proj2 Hconsistent).
Qed.
Lemma next_consistent tf before after :
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 N.next_config tf before = Some after ->
 B.control_get_consistent (R.cfg_state after) (R.cfg_control after).
Proof.
 exact (@Front.next_consistent tf before after).
Qed.
Lemma steps_consistent tf first last :
 N.steps tf first last ->
 T.control_owners_materialized (R.cfg_state first) (R.cfg_control first) ->
 B.control_get_consistent (R.cfg_state first) (R.cfg_control first) ->
 B.control_get_consistent (R.cfg_state last) (R.cfg_control last).
Proof.
 intro Hsteps. induction Hsteps;intros Howners Hconsistent;[exact Hconsistent |].
 apply IHHsteps.
 - apply (proj2 (@next_materialized tf first next H)),Howners.
 - eapply next_consistent;eassumption.
Qed.
Theorem reachable_get_consistent tf roots c :
 N.steps tf (R.initial_config roots) c ->
 B.control_get_consistent (R.cfg_state c) (R.cfg_control c).
Proof. intro Hsteps. eapply steps_consistent;[exact Hsteps |exact I |exact I]. Qed.

(** Every newly materialized owner is scheduled.  The Get-return consistency
    proof rules out silently introducing an unscheduled target on return. *)
Definition solved_origin before after :=
 forall owner, Sem.solved (R.cfg_state after) owner ->
 Sem.solved (R.cfg_state before) owner \/ scheduled (R.cfg_state after) (R.cfg_control after) owner.
Lemma solved_origin_sigma before after :
 R.sigma (R.cfg_state after) = R.sigma (R.cfg_state before) -> solved_origin before after.
Proof. intros Hsigma owner [value Hv]. left. exists value. now rewrite Hsigma in Hv. Qed.
Lemma read_solved_origin tf st fr target next k after :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> solved_origin {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|} after.
Proof.
 intro Hstep. cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 set (observed := R.observe st target) in *.
 destruct (negb (R.is_materialized observed target) && R.rank_lt observed (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. apply solved_origin_sigma. subst observed.
   exact (proj1 (B.same_read_view_observe st target)).
 - set (current := if R.is_materialized observed target then observed else R.enqueue observed target) in *.
   destruct (R.complete_get current fr target) as [[next_st next_fr] value] eqn:Hg.
   inversion Hstep;subst. intros owner Hsolved.
   destruct (@B.complete_get_solved_origin current fr target next_st next_fr value owner Hg Hsolved)
   as [Hbefore| ->].
   + left. unfold current in Hbefore. destruct (R.is_materialized observed target);
     subst observed;exact (@B.solved_observe_back st target owner Hbefore).
   + unfold current. destruct (R.is_materialized observed target) eqn:Hmat.
     * left. apply (@B.solved_observe_back st target target).
       apply B.materialized_solved,Hmat.
     * right;left. eapply B.queued_complete_get;[exact Hg |].
       subst current. unfold B.queued,R.enqueue. cbn.
       apply B.queue_insert_members. now left.
Qed.
Lemma spawn_solved_origin tf st fr target next k after :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> solved_origin {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|} after.
Proof.
 intro Hstep. cbn -[R.observe R.materialize R.enqueue] in Hstep.
 set (observed := R.observe st target) in *.
 destruct (R.is_materialized observed target).
 - inversion Hstep;subst. apply solved_origin_sigma. subst observed.
   exact (proj1 (B.same_read_view_observe st target)).
 - destruct (R.rank_lt observed (R.frame_owner fr) target).
   + inversion Hstep;subst. apply solved_origin_sigma. subst observed.
     exact (proj1 (B.same_read_view_observe st target)).
   + inversion Hstep;subst. intros owner Hsolved.
     destruct (@B.materialize_solved_origin_correctness (R.enqueue observed target) target owner Hsolved)
     as [Hbefore| ->].
     * left. subst observed. exact (@B.solved_observe_back st target owner Hbefore).
     * right;left. apply B.queued_materialize. unfold B.queued,R.enqueue. cbn.
       apply B.queue_insert_members. now left.
Qed.
Lemma drain_solved_origin tf st fr k after :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} = Some after ->
 solved_origin {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} after.
Proof.
 intro Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hq in Hstep;cbn in Hstep.
 - inversion Hstep;subst. apply solved_origin_sigma.
   exact (proj1 (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr)))).
 - destruct (V.eq_dec target (R.frame_owner fr)).
   + inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
     * inversion Hstep;subst. apply solved_origin_sigma.
       exact (proj1 (proj1 (B.reset_registered_cells_same_solver_view st (R.frame_owner fr)))).
Qed.
Lemma return_solved_origin tf st k after :
 B.control_get_consistent st (R.Return k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|} = Some after ->
 solved_origin {|R.cfg_state:=st;R.cfg_control:=R.Return k|} after.
Proof.
 intros Hconsistent Hstep. destruct k;cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;apply solved_origin_sigma;reflexivity].
 destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hg.
 inversion Hstep;subst. intros owner Hsolved.
 destruct (@B.complete_get_solved_origin st f t next next_fr value owner Hg Hsolved)
 as [Hbefore| ->];left;[exact Hbefore |exact (proj1 Hconsistent)].
Qed.
Lemma base_solved_origin tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 R.next_config tf before = Some after -> solved_origin before after.
Proof.
 destruct before as [st control]. intros Hside Hdead Howners Hconsistent Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|];[|discriminate].
   inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
 - destruct l;cbn -[R.observe] in Hstep.
   + inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
   + destruct (R.is_materialized (R.observe st t) t);
     inversion Hstep;subst;apply solved_origin_sigma;
     exact (proj1 (B.same_read_view_observe st t)).
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|];
   inversion Hstep;subst;apply solved_origin_sigma;reflexivity.
 - inversion Hstep;subst. intros owner Hsolved.
   destruct (@B.materialize_solved_origin_correctness st t owner Hsolved) as [Hbefore| ->];
   [now left |right;right;now left].
 - destruct r.
   + inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
   + eapply read_solved_origin;exact Hstep.
   + contradiction.
   + eapply spawn_solved_origin;exact Hstep.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. intros owner Hsolved. B.clear_requeue_view.
   destruct (@B.set_value_solved_origin st f t next next_fr owner Hs Hsolved)
   as [Hbefore| ->];left;[exact Hbefore |].
   apply B.materialized_solved. exact (proj1 Howners).
 - eapply drain_solved_origin;exact Hstep.
 - eapply return_solved_origin;eassumption.
Qed.

Lemma origin_before_sigma before middle after :
 R.sigma (R.cfg_state middle) = R.sigma (R.cfg_state before) ->
 solved_origin middle after -> solved_origin before after.
Proof.
 intros Heq Horigin owner Hsolved. destruct (Horigin owner Hsolved) as [[value Hv]|Hs].
 - left. exists value. now rewrite Heq in Hv.
 - now right.
Qed.
Lemma precommit_solved_origin tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_config tf before = Some after -> solved_origin before after.
Proof.
 destruct before as [st control]. intros Hside Hdead Howners Hconsistent Hstep.
 destruct control;cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_solved_origin;eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
 - eapply base_solved_origin;eauto.
Qed.
Lemma batched_solved_origin tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_batched tf before = Some after -> solved_origin before after.
Proof.
 destruct before as [st control]. intros Hdead Howners Hconsistent Hstep.
 destruct control;cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply precommit_solved_origin;[ | | | |exact Hstep];eauto;exact I].
 - destruct r;
   try solve [eapply precommit_solved_origin;[ | | | |exact Hstep];eauto;exact I].
   inversion Hstep;subst. apply solved_origin_sigma.
   exact (proj1 (B.same_read_view_observe st t)).
 - contradiction.
Qed.
Lemma fresh_solved_origin tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 B.control_get_consistent (R.cfg_state before) (R.cfg_control before) ->
 P.next_fresh tf before = Some after -> solved_origin before after.
Proof.
 destruct before as [st control]. intros Hdead Howners Hconsistent Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_solved_origin;eauto].
 - eapply origin_before_sigma;[ |eapply batched_solved_origin;[ | | |exact Hstep]].
   + reflexivity.
   + exact I.
   + eapply (@same_sigma_owners st (P.clear_owner st t) (R.StartEpisode t c));[reflexivity |exact Howners].
   + exact Hconsistent.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
     * eapply batched_solved_origin;eauto.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_solved_origin;eauto].
   inversion Hstep;subst. apply solved_origin_sigma;reflexivity.
Qed.
Theorem next_solved_origin tf roots before after :
 N.steps tf (R.initial_config roots) before ->
 N.next_config tf before = Some after -> solved_origin before after.
Proof.
 exact (@Front.next_solved_origin tf roots before after).
Qed.
Lemma steps_append tf first middle last :
 N.steps tf first middle -> N.steps tf middle last -> N.steps tf first last.
Proof.
 intros Hsteps Htail. induction Hsteps;[exact Htail |].
 econstructor;[exact H |apply IHHsteps,Htail].
Qed.
Definition summaries_guarded tf c :=
 forall owner, Sem.solved (R.cfg_state c) owner ->
 summary_guarded tf (R.cfg_state c) (R.cfg_control c) owner.
Theorem next_summaries tf roots before after :
 N.steps tf (R.initial_config roots) before ->
 summaries_guarded tf before ->
 N.next_config tf before = Some after -> summaries_guarded tf after.
Proof.
 intros Hreach Hsummaries Hstep owner Hsolved.
 destruct (@next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
 as [Hbefore|[Hq|Ha]];[|now left |now right;left].
 eapply next_guarded_summary;[exact Hreach |apply Hsummaries,Hbefore |exact Hstep].
Qed.
Lemma steps_summaries tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 summaries_guarded tf first -> summaries_guarded tf last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hsummaries;[exact Hsummaries |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_summaries;eassumption.
Qed.
Theorem reachable_summaries tf roots c :
 N.steps tf (R.initial_config roots) c -> summaries_guarded tf c.
Proof.
 intro Hreach. eapply steps_summaries;[exact Hreach |constructor |].
 intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
Qed.
Theorem terminal_summaries tf roots final :
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
 Sem.quiescent final -> forall owner, Sem.solved final owner -> B.summary_valid tf final owner.
Proof.
 intros Hreach Hquiet owner Hsolved.
 destruct (@reachable_summaries tf roots (Sem.terminal_config final) Hreach owner Hsolved)
 as [Hq|[Ha|Hs]];[|contradiction |exact Hs].
 exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
Qed.

(** Root tracking and final replay use the new execution relation throughout. *)
Definition pending_step before after :=
 forall owner, B.control_pending owner (R.cfg_control before) ->
 Sem.solved (R.cfg_state after) owner \/
 B.control_pending owner (R.cfg_control after) \/ B.control_active owner (R.cfg_control after).
Lemma base_pending tf before after :
 R.next_config tf before = Some after -> pending_step before after.
Proof. intros Hstep owner Hp. eapply B.control_pending_step;eassumption. Qed.
Lemma precommit_pending tf before after :
 P.next_config tf before = Some after -> pending_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_pending;exact Hstep].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
 - eapply base_pending;exact Hstep.
Qed.
Lemma batched_pending tf before after :
 P.next_batched tf before = Some after -> pending_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_pending;exact Hstep].
 - destruct r;try solve [eapply precommit_pending;exact Hstep].
   inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
 - destruct l;[|eapply precommit_pending;exact Hstep].
   inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
Qed.
Lemma fresh_pending tf before after :
 P.next_fresh tf before = Some after -> pending_step before after.
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_pending;exact Hstep].
 - inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
     * eapply batched_pending;exact Hstep.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_pending;exact Hstep].
   inversion Hstep;subst. intros owner Hp. right;left;exact Hp.
Qed.
Lemma next_pending tf before after :
 N.next_config tf before = Some after -> pending_step before after.
Proof.
 exact (@Front.next_pending tf before after).
Qed.
Definition roots_tracked tf roots c :=
 forall owner, List.In owner roots ->
 B.control_pending owner (R.cfg_control c) \/
 summary_guarded tf (R.cfg_state c) (R.cfg_control c) owner.
Lemma next_roots_tracked tf roots before after :
 N.steps tf (R.initial_config roots) before ->
 roots_tracked tf roots before ->
 N.next_config tf before = Some after -> roots_tracked tf roots after.
Proof.
 intros Hreach Hroots Hstep owner Hin. destruct (Hroots owner Hin) as [Hp|Hg].
 - destruct (@next_pending tf before after Hstep owner Hp) as [Hs|[Hp'|Ha]].
   + right. eapply reachable_summaries;[|exact Hs].
     eapply steps_append;[exact Hreach |]. econstructor;[exact Hstep |constructor].
   + now left.
   + right;right;left;exact Ha.
 - right. eapply next_guarded_summary;eassumption.
Qed.
Lemma steps_roots_tracked tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 roots_tracked tf roots first -> roots_tracked tf roots last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hroots;[exact Hroots |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_roots_tracked;eassumption.
Qed.
Theorem reachable_roots_tracked tf roots c :
 N.steps tf (R.initial_config roots) c -> roots_tracked tf roots c.
Proof.
 intro Hreach. eapply steps_roots_tracked;[exact Hreach |constructor |].
 intros owner Hin. left;exact Hin.
Qed.
Theorem terminal_roots_solved tf roots final :
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
 Sem.quiescent final -> forall owner, List.In owner roots -> Sem.solved final owner.
Proof.
 intros Hreach Hquiet owner Hin.
 destruct (@reachable_roots_tracked tf roots (Sem.terminal_config final) Hreach owner Hin)
 as [Hp|[Hq|[Ha|Hs]]];try contradiction.
 - exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
 - exact (proj1 Hs).
Qed.
Theorem terminal_replay_post_solution tf roots final owner :
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
 Sem.quiescent final -> Sem.solved final owner ->
 (exists direct reads effects, Sem.rhs_eval final (tf owner) direct reads effects) /\
 Sem.rhs_post_solution final owner (tf owner).
Proof.
 intros Hreach Hquiet Hsolved.
 pose proof (@terminal_summaries tf roots final Hreach Hquiet owner Hsolved) as Hsummary.
 split.
 - destruct Hsummary as [_ [direct [reads [effects [Htrace [Hreads _]]]]]].
   exists direct,reads,effects. apply B.rhs_trace_replay;[exact Htrace |].
   eapply B.guarded_reads_agree;eassumption.
 - eapply B.summary_post_solution;[exact Hquiet | |exact Hsummary].
   eapply terminal_aggregates_bounded;eassumption.
Qed.
Theorem successful_run_replay_post_solution fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall owner, Sem.solved final owner ->
 (exists direct reads effects, Sem.rhs_eval final (tf owner) direct reads effects) /\
 Sem.rhs_post_solution final owner (tf owner).
Proof.
 intro Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
 as [Hshape Hquiet]. intros owner Hsolved.
 eapply terminal_replay_post_solution;[|exact Hquiet |exact Hsolved].
 rewrite <- Hshape. apply fuel_steps.
Qed.
Theorem successful_run_correct fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final -> Sem.correct_final_state tf roots final.
Proof.
 intro Hsolve. pose proof (@successful_run_replay_post_solution fuel tf roots final Hsolve) as Hreplay.
 unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
 as [Hshape Hquiet]. intros owner Hin.
 assert (Hsolved : Sem.solved final owner).
 { eapply terminal_roots_solved;[|exact Hquiet |exact Hin].
   rewrite <- Hshape. apply fuel_steps. }
 split;[exact Hsolved |exact (proj2 (Hreplay owner Hsolved))].
Qed.

(** Local starting observations for the remaining episode-descent proof. *)
Lemma recorded_effects_bounded st owner effects :
 B.recorded_effects st owner effects ->
 effects_bounded effects (R.stored_contribution st owner).
Proof.
 intros Hrecord target value Hin.
 destruct (Hrecord target value Hin) as [contribution [Hlookup Hle]].
 unfold R.stored_contribution. rewrite Hlookup. exact Hle.
Qed.
Theorem reachable_clean_replay tf roots c owner :
 N.steps tf (R.initial_config roots) c ->
 Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner ->
 ~ B.control_active owner (R.cfg_control c) ->
 exists direct reads effects,
 Sem.rhs_eval (R.cfg_state c) (tf owner) direct reads effects /\
 D.leq direct (R.sigma_value (R.cfg_state c) owner) = true /\
 effects_bounded effects (R.stored_contribution (R.cfg_state c) owner).
Proof.
 intros Hreach Hsolved Hqueue Hactive.
 destruct (@reachable_summaries tf roots c Hreach owner Hsolved) as [Hq|[Ha|Hs]];try contradiction.
 destruct Hs as [_ [direct [reads [effects [Htrace [Hreads [Hrecord Hdirect]]]]]]].
 exists direct,reads,effects. split.
 - apply B.rhs_trace_replay;[exact Htrace |]. eapply H.guarded_reads_clean;eassumption.
 - split;[exact Hdirect |apply recorded_effects_bounded,Hrecord].
Qed.
Theorem reachable_clean_paths tf roots c owner :
 N.steps tf (R.initial_config roots) c ->
 Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner ->
 ~ B.control_active owner (R.cfg_control c) ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists direct reads effects spawns,
 Sem.rhs_eval (R.cfg_state c) (tf owner) direct reads effects /\
 paths_below (R.sigma_value (R.cfg_state c))
 {|O.observed_direct:=direct;O.observed_reads:=reads;
 O.observed_sides:=effects;O.observed_spawns:=spawns|} (tf owner) /\
 D.leq direct (R.sigma_value (R.cfg_state c) owner) = true /\
 effects_bounded effects (R.stored_contribution (R.cfg_state c) owner).
Proof.
 intros Hreach Hsolved Hqueue Hactive Hdeps Heffects.
 destruct (@reachable_clean_replay tf roots c owner Hreach Hsolved Hqueue Hactive)
 as [direct [reads [effects [Heval [Hdirect Hside]]]]].
 destruct (@replay_paths_below (R.cfg_state c) (tf owner) direct reads effects Hdeps Heffects Heval)
 as [spawns Hpaths].
 exists direct,reads,effects,spawns. split;[exact Heval |].
 split;[exact Hpaths |]. split;assumption.
Qed.

(** Ranking and queue invariants must follow this execution, since the commit
    barrier examines only the greatest-ranked queue entry. *)
Lemma ranked_control_change st before after :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=before|} ->
 B.control_ranked st after ->
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=after|}.
Proof. intros [Hv Hd Hc Hdistinct Hordered] Hnext. constructor;assumption. Qed.
Lemma ranked_enqueue st control target :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.ranked st target ->
 B.configuration_ranked {|R.cfg_state:=R.enqueue st target;R.cfg_control:=control|}.
Proof.
 intros [Hv Hd Hc Hdistinct Hordered] Htarget. constructor.
 - apply B.rank_valid_enqueue,Hv.
 - apply B.state_data_ranked_enqueue;assumption.
 - eapply B.control_ranked_extended;[apply B.rank_extends_enqueue |exact Hc].
 - apply B.enqueue_distinct,Hdistinct.
 - apply B.enqueue_ordered;try assumption. exact (B.data_queue_ranked Hd).
Qed.
Lemma ranked_observe st control target :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.configuration_ranked {|R.cfg_state:=R.observe st target;R.cfg_control:=control|}.
Proof.
 intros [Hv Hd Hc Hdistinct Hordered]. constructor.
 - eapply B.rank_valid_observe;[exact Hv |reflexivity].
 - apply B.state_data_ranked_observe,Hd.
 - eapply B.control_ranked_extended;[eapply B.rank_extends_observe;reflexivity |exact Hc].
 - apply B.queue_distinct_observe,Hdistinct.
 - apply B.queue_ordered_observe;assumption.
Qed.
Lemma ranked_write st control fr target raw next changed :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 R.write_side_contribution st fr target raw = (next,changed) ->
 B.configuration_ranked {|R.cfg_state:=next;R.cfg_control:=control|}.
Proof.
 intros [Hv Hd Hc Hdistinct Hordered] Hw. constructor.
 - eapply B.rank_valid_write_side_contribution;eassumption.
 - eapply B.state_data_ranked_write_side_contribution;eassumption.
 - eapply B.control_ranked_extended;[eapply B.rank_extends_write_side_contribution;exact Hw |exact Hc].
 - eapply B.queue_distinct_write_side_contribution;eassumption.
 - eapply B.queue_ordered_write_side_contribution;eassumption.
Qed.
Lemma ranked_publish_targets st control fr :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.frame_ranked st fr ->
 B.configuration_ranked {|R.cfg_state:=R.publish_targets st fr;R.cfg_control:=control|}.
Proof.
 intros [Hv Hd Hc Hdistinct Hordered] Hframe. constructor.
 - exact Hv.
 - apply B.state_data_ranked_publish_targets;assumption.
 - eapply B.control_ranked_extended;[apply B.rank_extends_with_last_targets |exact Hc].
 - exact Hdistinct.
 - exact Hordered.
Qed.
Lemma queue_filter_ordered st test values :
 B.queue_ordered_at st values -> B.queue_ordered_at st (List.filter test values).
Proof.
 intro Hsort. induction Hsort as [|head rest Hsort IH Hall];cbn;[constructor |].
 destruct (test head);[constructor;[exact IH |] |exact IH].
 apply List.Forall_forall. intros target Hin. apply List.filter_In in Hin.
 eapply List.Forall_forall in Hall;[exact Hall |exact (proj1 Hin)].
Qed.
Lemma ranked_queue_subset st control next_queue :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 List.incl next_queue (R.queue st) ->
 List.NoDup next_queue -> B.queue_ordered_at st next_queue ->
 B.configuration_ranked {|R.cfg_state:=R.with_queue st next_queue;R.cfg_control:=control|}.
Proof.
 intros [Hv Hd Hc Hdistinct Hordered] Hin Hnodup Hsort. constructor.
 - apply B.rank_valid_with_queue,Hv.
 - apply B.state_data_ranked_with_queue;[exact Hd |].
   intros owner Hmem. apply (B.data_queue_ranked Hd),Hin,Hmem.
 - eapply B.control_ranked_extended;[apply B.rank_extends_with_queue |exact Hc].
 - exact Hnodup.
 - exact Hsort.
Qed.
Lemma ranked_clear st control owner :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.configuration_ranked {|R.cfg_state:=P.clear_owner st owner;R.cfg_control:=control|}.
Proof.
 intro Hranked. apply ranked_queue_subset;[exact Hranked | | |].
 - intros target Hin. apply List.filter_In in Hin. exact (proj1 Hin).
 - apply List.NoDup_filter. exact (B.configuration_queue_distinct Hranked).
 - apply queue_filter_ordered. exact (B.configuration_queue_ordered Hranked).
Qed.
Lemma ranked_pop st control target rest :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 R.queue_pop (R.queue st) = Some (target,rest) ->
 B.configuration_ranked {|R.cfg_state:=R.with_queue st rest;R.cfg_control:=control|}.
Proof.
 intros Hranked Hpop. apply ranked_queue_subset;[exact Hranked | | |].
 - intros owner Hin. unfold R.queue_pop in Hpop.
   destruct (R.queue st) as [|head tail] eqn:Hq;[discriminate |].
   inversion Hpop;subst. now right.
 - pose proof (B.configuration_queue_distinct Hranked) as Hdistinct.
   unfold R.queue_pop in Hpop. destruct (R.queue st) as [|head tail] eqn:Hq;[discriminate |].
   inversion Hpop;subst. unfold B.queue_distinct in Hdistinct. cbn in Hdistinct. rewrite Hq in Hdistinct.
   inversion Hdistinct;assumption.
 - exact (proj1 (@B.queue_pop_ordered st (R.queue st) target rest
   (B.configuration_queue_ordered Hranked) Hpop)).
Qed.

Lemma ranked_suspend tf st fr direct k target rest :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 B.configuration_ranked (P.suspend_commit tf st fr k target rest).
Proof.
 intros Hr Hp.
 destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop _]].
 destruct (@B.queue_pop_ranked st target rest
 (B.data_queue_ranked (B.configuration_state_data Hr)) Hpop) as [Htarget _].
 destruct (B.configuration_control_ranked Hr) as [Hframe Hk].
 eapply ranked_control_change;[eapply ranked_pop;[exact Hr |exact Hpop] |].
 cbn. split.
 - eapply B.ranked_extended;[apply B.rank_extends_with_queue |exact Htarget].
 - split.
   + eapply B.frame_ranked_extended;[apply B.rank_extends_with_queue |].
     apply B.fresh_frame_ranked;[exact (proj1 Hframe) |].
     exact (B.data_targets_ranked (B.configuration_state_data Hr)).
   + eapply B.continuation_ranked_extended;[apply B.rank_extends_with_queue |exact Hk].
Qed.
Lemma precommit_ranked tf before after :
 B.configuration_ranked before -> P.next_config tf before = Some after ->
 B.configuration_ranked after.
Proof.
 destruct before as [st control]. intros Hr Hstep. destruct control;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply B.next_config_configuration_ranked;eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply ranked_suspend;eassumption.
 - eapply B.next_config_configuration_ranked;eauto.
Qed.
Lemma ranked_old_publish targets st control fr :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.list_ranked st targets ->
 B.configuration_ranked {|R.cfg_state:=P.publish_accumulated targets st fr;R.cfg_control:=control|}.
Proof.
 revert st. induction targets as [|target rest IH];intros st Hr Htargets;
 cbn -[R.write_side_contribution];[exact Hr |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 assert (Hrank : B.rank_extends st next) by (eapply B.rank_extends_write_side_contribution;exact Hw).
 assert (Hnext : B.configuration_ranked {|R.cfg_state:=next;R.cfg_control:=control|})
 by (eapply ranked_write;eassumption).
 assert (Htarget : B.ranked next target)
 by (eapply B.ranked_extended;[exact Hrank |apply Htargets;now left]).
 apply IH.
 - destruct changed;[apply ranked_enqueue;assumption |exact Hnext].
 - eapply B.list_ranked_extended;[ |intros x Hin;apply Htargets;now right].
   eapply B.rank_extends_trans;[exact Hrank |].
   destruct changed;[apply B.rank_extends_enqueue |apply B.rank_extends_refl].
Qed.
Lemma batched_done_ranked st fr direct k :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 B.configuration_ranked
 {|R.cfg_state:=R.publish_targets (P.publish_accumulated (S.elements (R.frame_current_targets fr)) st fr) fr;
 R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intro Hr. destruct (B.configuration_control_ranked Hr) as [Hframe [_ Hk]].
 assert (Hpub : B.configuration_ranked
 {|R.cfg_state:=P.publish_accumulated (S.elements (R.frame_current_targets fr)) st fr;
 R.cfg_control:=R.RunDead fr direct [] k|}).
 { apply ranked_old_publish;[exact Hr |]. apply B.set_elements_ranked. exact (proj1 (proj2 (proj2 Hframe))). }
 eapply ranked_control_change.
 - apply ranked_publish_targets;[exact Hpub |exact (proj1 (B.configuration_control_ranked Hpub))].
 - eapply B.control_ranked_extended;[apply B.rank_extends_with_last_targets |].
   destruct (B.configuration_control_ranked Hpub) as [Hf [_ Hcont]]. now split.
Qed.
Lemma batched_ranked tf before after :
 B.configuration_ranked before -> P.next_batched tf before = Some after ->
 B.configuration_ranked after.
Proof.
 destruct before as [st control]. intros Hr Hstep. destruct control;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_ranked;eauto].
 - destruct r;try solve [eapply precommit_ranked;eauto].
   inversion Hstep;subst.
   pose proof (@ranked_observe st (R.RunRhs f (R.ConstraintSystem.Side t t0 r) c) t Hr) as Hobs.
   eapply ranked_control_change;[exact Hobs |]. cbn.
   destruct (B.configuration_control_ranked Hobs) as [Hframe Hk]. split;[|exact Hk].
   apply B.with_frame_side_ranked;[exact Hframe |].
   eapply B.observe_ranks_variable;reflexivity.
 - destruct l.
   + inversion Hstep;subst. apply batched_done_ranked,Hr.
   + eapply precommit_ranked;eauto.
Qed.
Lemma ranked_retry tf st fr direct k :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 B.configuration_ranked (P.retry_current tf st fr k).
Proof.
 intro Hr.
 pose proof (@ranked_clear st (R.RunCommit fr direct k) (R.frame_owner fr) Hr) as Hclear.
 eapply ranked_control_change;[exact Hclear |]. split.
 - apply B.fresh_frame_ranked.
   + exact (proj1 (proj1 (B.configuration_control_ranked Hclear))).
   + exact (B.data_targets_ranked (B.configuration_state_data Hclear)).
 - exact (proj2 (B.configuration_control_ranked Hclear)).
Qed.
Lemma fresh_ranked tf before after :
 B.configuration_ranked before -> P.next_fresh tf before = Some after ->
 B.configuration_ranked after.
Proof.
 destruct before as [st control]. intros Hr Hstep. destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_ranked;eauto].
 - eapply batched_ranked;[apply ranked_clear,Hr |exact Hstep].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply ranked_suspend;eassumption.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. eapply ranked_retry;exact Hr.
     * eapply batched_ranked;eauto.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_ranked;eauto].
   eapply batched_ranked;[apply ranked_clear,Hr |exact Hstep].
Qed.

Lemma ranked_requeue before st control source target :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.ranked st source ->
 B.configuration_ranked {|R.cfg_state:=C.requeue_source before st source target;R.cfg_control:=control|}.
Proof.
 intros Hr Hsource. unfold C.requeue_source. destruct C.cell_changed;
 [apply ranked_enqueue;assumption |exact Hr].
Qed.
Lemma ranked_finish before st control fr target changed :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.ranked st (R.frame_owner fr) -> B.ranked st target ->
 B.configuration_ranked {|R.cfg_state:=C.finish_write before st fr target changed;R.cfg_control:=control|}.
Proof.
 intros Hr Hsource Htarget. unfold C.finish_write. destruct changed.
 - apply ranked_enqueue;[apply ranked_requeue;assumption |].
   eapply B.ranked_extended;[apply C.requeue_extends |exact Htarget].
 - apply ranked_requeue;assumption.
Qed.
Lemma ranked_publish targets st control fr :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=control|} ->
 B.ranked st (R.frame_owner fr) -> B.list_ranked st targets ->
 B.configuration_ranked {|R.cfg_state:=C.publish targets st fr;R.cfg_control:=control|}.
Proof.
 revert st. induction targets as [|target rest IH];intros st Hr Hsource Htargets;
 cbn -[R.write_side_contribution C.finish_write];[exact Hr |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 assert (Hrank : B.rank_extends st next) by (eapply B.rank_extends_write_side_contribution;exact Hw).
 assert (Hfinish : B.rank_extends st (C.finish_write st next fr target changed))
 by (eapply B.rank_extends_trans;[exact Hrank |apply C.finish_extends]).
 apply IH.
 - apply ranked_finish.
   + eapply ranked_write;eassumption.
   + eapply B.ranked_extended;[exact Hrank |exact Hsource].
   + eapply B.ranked_extended;[exact Hrank |apply Htargets;now left].
 - eapply B.ranked_extended;[exact Hfinish |exact Hsource].
 - eapply B.list_ranked_extended;[exact Hfinish |].
   intros x Hin. apply Htargets;now right.
Qed.
Lemma dead_done_ranked st fr direct k :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 B.configuration_ranked
 {|R.cfg_state:=R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr;
 R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intro Hr. destruct (B.configuration_control_ranked Hr) as [Hframe [_ Hk]].
 assert (Hpub : B.configuration_ranked
 {|R.cfg_state:=C.publish (S.elements (R.frame_current_targets fr)) st fr;
 R.cfg_control:=R.RunDead fr direct [] k|}).
 { apply ranked_publish;[exact Hr |exact (proj1 Hframe) |].
   apply B.set_elements_ranked. exact (proj1 (proj2 (proj2 Hframe))). }
 eapply ranked_control_change.
 - apply ranked_publish_targets;[exact Hpub |exact (proj1 (B.configuration_control_ranked Hpub))].
 - eapply B.control_ranked_extended;[apply B.rank_extends_with_last_targets |].
   destruct (B.configuration_control_ranked Hpub) as [Hf [_ Hcont]]. now split.
Qed.
Lemma ranked_continue_dead st fr direct target rest k changed :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct rest k|} ->
 B.ranked st target ->
 B.configuration_ranked (R.continue_dead st fr direct target rest k changed).
Proof.
 intros Hr Htarget. unfold R.continue_dead. destruct changed;[|exact Hr].
 destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))%bool.
 - eapply ranked_control_change;[exact Hr |].
   split;[exact Htarget |exact (B.configuration_control_ranked Hr)].
 - apply ranked_enqueue;assumption.
Qed.
Lemma dead_pending_ranked tf st fr direct target rest k after :
 B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} = Some after ->
 B.configuration_ranked after.
Proof.
 intros Hr Hstep.
 destruct (B.configuration_control_ranked Hr) as [Hframe [Hpending Hk]].
 assert (Hrest : B.configuration_ranked {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct rest k|}).
 { eapply ranked_control_change;[exact Hr |].
   split;[exact Hframe |]. split;[intros x Hin;apply Hpending;now right |exact Hk]. }
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr));
 [inversion Hstep;subst;exact Hrest |].
 destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
 inversion Hstep;subst. apply ranked_continue_dead.
 - apply ranked_requeue.
   + eapply ranked_write;eassumption.
   + eapply B.ranked_extended;[eapply B.rank_extends_write_side_contribution;exact Hw |exact (proj1 Hframe)].
 - eapply B.ranked_extended;[apply C.requeue_extends |].
   eapply B.ranked_extended;[eapply B.rank_extends_write_side_contribution;exact Hw |].
   apply Hpending;now left.
Qed.
Theorem next_ranked tf before after :
 B.configuration_ranked before -> N.next_config tf before = Some after ->
 B.configuration_ranked after.
Proof.
 intros Hr Hstep.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.next_ranked tf before after Hr Hb).
 - eapply (@ranked_suspend tf st fr D.bottom k target rest);[ |exact Hp].
   eapply ranked_control_change;[exact Hr |].
   exact (B.configuration_control_ranked Hr).
Qed.
Lemma steps_ranked tf first last :
 N.steps tf first last -> B.configuration_ranked first -> B.configuration_ranked last.
Proof.
 intro Hsteps. induction Hsteps;intro Hr;[exact Hr |].
 apply IHHsteps. eapply next_ranked;eassumption.
Qed.
Theorem reachable_ranked tf roots c :
 N.steps tf (R.initial_config roots) c -> B.configuration_ranked c.
Proof.
 intro Hreach. eapply steps_ranked;[exact Hreach |apply B.initial_configuration_ranked].
Qed.

(** The actual controlled-commit guard discharges the higher frontier's
    scheduling conditions.  No frontier certificate is assumed. *)
Lemma barrier_higher_not_queued st source owner :
 B.queue_ordered st ->
 S.mem source (R.controlled st) = true ->
 P.pending_above st source = None ->
 R.rank_lt st source owner = true -> ~ B.queued st owner.
Proof.
 intros Hordered Hcontrolled Hpending Hhigher Hqueued.
 unfold P.pending_above in Hpending. rewrite Hcontrolled in Hpending.
 destruct (R.queue_pop (R.queue st)) as [[head rest]|] eqn:Hpop.
 - destruct (R.rank_lt st source head) eqn:Hhead;[discriminate |].
   pose proof (@B.queue_pop_ordered st (R.queue st) head rest Hordered Hpop) as [_ Hmax].
   unfold R.queue_pop in Hpop. destruct (R.queue st) as [|first tail] eqn:Hq;[discriminate |].
   inversion Hpop;subst. unfold B.queued in Hqueued. rewrite Hq in Hqueued.
   destruct Hqueued as [->|Hin];[congruence |].
   pose proof (@T.rank_lt_trans_true st source owner head Hhigher (Hmax owner Hin)) as Hlt.
   congruence.
 - unfold R.queue_pop in Hpop. destruct (R.queue st) as [|head rest] eqn:Hq;[|discriminate].
   unfold B.queued in Hqueued. rewrite Hq in Hqueued. contradiction.
Qed.
Lemma continuation_active_lower st upper k owner :
 T.continuation_below st upper k ->
 B.continuation_active_correctness owner k ->
 R.rank_lt st owner upper = true.
Proof.
 revert upper. induction k;intros upper Hbelow Hactive;cbn in Hbelow,Hactive;try contradiction.
 all: destruct Hbelow as [Hlt Htail].
 all: try destruct Hactive as [->|Hactive];try exact Hlt.
 all: eapply T.rank_lt_trans_true;[eapply IHk;eassumption |exact Hlt].
Qed.
Lemma higher_not_active st fr direct k owner :
 T.control_ordered st (R.RunCommit fr direct k) ->
 R.rank_lt st (R.frame_owner fr) owner = true ->
 ~ B.control_active owner (R.RunCommit fr direct k).
Proof.
 intros Horder Hhigher [Heq|Hactive].
 - subst owner. exact (@B.rank_lt_true_neq_correctness st (R.frame_owner fr) (R.frame_owner fr) Hhigher eq_refl).
 - pose proof (@continuation_active_lower st (R.frame_owner fr) k owner Horder Hactive) as Hlower.
   pose proof (@T.rank_lt_trans_true st owner (R.frame_owner fr) owner Hlower Hhigher) as Hself.
   exact (@B.rank_lt_true_neq_correctness st owner owner Hself eq_refl).
Qed.
Theorem committing_higher_clean tf roots st fr direct k after next_fr next_k owner :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true ->
 ~ B.queued st owner /\ ~ B.control_active owner (R.RunCommit fr direct k).
Proof.
 intros Hreach Hstep Hcontrolled Hhigher. split.
 - eapply barrier_higher_not_queued.
   + exact (B.configuration_queue_ordered (reachable_ranked Hreach)).
   + exact Hcontrolled.
   + exact (proj1 (@P.fresh_commit_ready tf st fr direct k after next_fr next_k Hstep)).
   + exact Hhigher.
 - eapply higher_not_active;[exact (proj1 (reachable_history Hreach)) |exact Hhigher].
Qed.
Theorem committing_higher_replay tf roots st fr direct k after next_fr next_k owner :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Sem.solved st owner ->
 exists result reads effects, Sem.rhs_eval st (tf owner) result reads effects /\
 D.leq (D.join result (R.aggregate st owner)) (R.sigma_value st owner) = true /\
 effects_bounded effects (R.stored_contribution st owner).
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved.
 destruct (@committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 destruct (@reachable_clean_replay tf roots
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} owner
 Hreach Hsolved Hqueue Hactive) as [result [reads [effects [Heval [Hresult Hside]]]]].
 exists result,reads,effects. split;[exact Heval |]. split;[|exact Hside].
 apply DL.join_least;[exact Hresult |].
 destruct (reachable_aggregate Hreach owner) as [Hq|[Ha|Hagg]];try contradiction;exact Hagg.
Qed.
Theorem committing_higher_paths tf roots st fr direct k after next_fr next_k owner :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Sem.solved st owner ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists result reads effects spawns, Sem.rhs_eval st (tf owner) result reads effects /\
 paths_below (R.sigma_value st)
 {|O.observed_direct:=result;O.observed_reads:=reads;
 O.observed_sides:=effects;O.observed_spawns:=spawns|} (tf owner) /\
 D.leq (D.join result (R.aggregate st owner)) (R.sigma_value st owner) = true /\
 effects_bounded effects (R.stored_contribution st owner).
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved Hdeps Heffects.
 destruct (@committing_higher_replay tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher Hsolved) as [result [reads [effects [Heval [Hresult Hside]]]]].
 destruct (@replay_paths_below st (tf owner) result reads effects Hdeps Heffects Heval) as [spawns Hpaths].
 exists result,reads,effects,spawns. split;[exact Heval |].
 split;[exact Hpaths |]. split;assumption.
Qed.


Definition targets_live st owner (effects : list (V.t * D.t)) :=
 forall target value, In (target,value) effects ->
 S.mem target (R.lookup_set (R.last_targets st) owner) = true.
Definition target_summary tf st owner :=
 exists direct reads effects, B.rhs_trace (tf owner) direct reads effects /\
 B.guarded_reads st owner reads /\ targets_live st owner effects.
Lemma targets_view before after owner effects :
 R.last_targets after = R.last_targets before ->
 targets_live before owner effects -> targets_live after owner effects.
Proof. intros Heq Hlive target value Hin. unfold R.lookup_set. rewrite Heq. apply Hlive with value,Hin. Qed.
Lemma target_summary_view tf before after owner :
 (forall reads, B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 R.lookup_set (R.last_targets after) owner = R.lookup_set (R.last_targets before) owner ->
 target_summary tf before owner -> target_summary tf after owner.
Proof.
 intros Hreads Htargets [direct [reads [effects [Htrace [Hguard Hlive]]]]].
 exists direct,reads,effects. split;[exact Htrace |]. split;[apply Hreads,Hguard |].
 intros target value Hin. rewrite Htargets. apply Hlive with value,Hin.
Qed.
Lemma target_summary_observe tf st owner target :
 target_summary tf st owner -> target_summary tf (R.observe st target) owner.
Proof.
 apply target_summary_view;[intros;apply H.carries_observe;assumption |].
 unfold R.observe. destruct (R.Ranking.observe (R.ranking st) target);reflexivity.
Qed.
Lemma target_summary_materialize tf st owner target :
 target_summary tf st owner -> target_summary tf (R.materialize st target) owner.
Proof.
 apply target_summary_view;[intros;apply H.carries_materialize;assumption |].
 unfold R.materialize. destruct (M.lookup (R.sigma st) target);reflexivity.
Qed.
Lemma target_summary_enqueue tf st owner target :
 target_summary tf st owner -> target_summary tf (R.enqueue st target) owner.
Proof. apply target_summary_view;[intros;apply H.carries_enqueue;assumption |reflexivity]. Qed.
Lemma target_summary_requeue tf before after source owner :
 target_summary tf after owner ->
 target_summary tf (R.requeue_changed_controlled_owner before after source) owner.
Proof. apply target_summary_view;[intros;apply H.carries_requeue;assumption |reflexivity]. Qed.
Lemma target_summary_pop_other tf st popped rest owner :
 R.queue_pop (R.queue st) = Some (popped,rest) -> owner <> popped ->
 target_summary tf st owner -> target_summary tf (R.with_queue st rest) owner.
Proof.
 intros Hpop Hneq. apply target_summary_view;[|reflexivity].
 intros. eapply B.guarded_reads_pop_other;eassumption.
Qed.
Lemma target_summary_clear_other tf st cleared owner :
 owner <> cleared -> target_summary tf st owner ->
 target_summary tf (P.clear_owner st cleared) owner.
Proof.
 intro Hneq. apply target_summary_view;[|reflexivity].
 intros. eapply P.clear_other_guarded_reads;eassumption.
Qed.
Lemma target_summary_get tf st fr target next next_fr value owner :
 R.complete_get st fr target = (next,next_fr,value) ->
 target_summary tf st owner -> target_summary tf next owner.
Proof.
 intro Hget. apply target_summary_view;[intros;eapply H.carries_get;eassumption |].
 unfold R.complete_get in Hget. inversion Hget;subst.
 unfold R.materialize. destruct (M.lookup _ target);
 destruct (R.rank_lt st (R.frame_owner fr) target);reflexivity.
Qed.
Lemma target_summary_set tf st fr direct next next_fr owner :
 R.set_value st fr direct = (next,next_fr) ->
 target_summary tf st owner -> target_summary tf next owner.
Proof.
 intro Hset. apply target_summary_view;[intros;eapply H.carries_set;eassumption |].
 unfold R.set_value in Hset.
 repeat match type of Hset with
 | context [if ?condition then _ else _] => destruct condition
 end;inversion Hset;reflexivity.
Qed.
Lemma target_summary_reset tf st scope owner :
 target_summary tf st owner ->
 target_summary tf (R.reset_registered_cells st scope) owner.
Proof.
 apply target_summary_view.
 - intros. eapply B.guarded_reads_same_view;[exact (proj1 (B.reset_registered_cells_same_solver_view st scope)) |eassumption].
 - unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity.
Qed.
Lemma target_summary_write_other tf st fr target input next changed owner :
 R.write_side_contribution st fr target input = (next,changed) ->
 owner <> R.frame_owner fr -> target_summary tf st owner -> target_summary tf next owner.
Proof.
 intros Hwrite Hneq. apply target_summary_view;[intros;eapply H.carries_write;eassumption |].
 unfold R.write_side_contribution,R.register_reset,R.promote_side_target in Hwrite.
 destruct (R.rank_lt st target (R.frame_owner fr));inversion Hwrite;reflexivity.
Qed.
Lemma target_summary_publish_other tf st fr owner :
 owner <> R.frame_owner fr -> target_summary tf st owner ->
 target_summary tf (R.publish_targets st fr) owner.
Proof.
 intro Hneq. apply target_summary_view.
 - intros. eapply B.guarded_reads_same_view;[exact (proj1 (B.publish_targets_same_solver_view st fr)) |eassumption].
 - unfold R.lookup_set. cbn. rewrite ML.lookup_update_other;[reflexivity |congruence].
Qed.

Definition target_guarded tf st control owner :=
 B.queued st owner \/ B.control_active owner control \/ target_summary tf st owner.
Lemma target_pop tf st popped rest next owner :
 R.queue_pop (R.queue st) = Some (popped,rest) ->
 B.control_active popped next -> target_summary tf st owner ->
 target_guarded tf (R.with_queue st rest) next owner.
Proof.
 intros Hpop Hactive Hsummary. destruct (V.eq_dec owner popped) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. eapply target_summary_pop_other; eassumption.
Qed.
Lemma target_clear tf st cleared next owner :
 B.control_active cleared next -> target_summary tf st owner ->
 target_guarded tf (P.clear_owner st cleared) next owner.
Proof.
 intros Hactive Hsummary. destruct (V.eq_dec owner cleared) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. apply target_summary_clear_other;assumption.
Qed.
Lemma target_get tf st fr target next k owner after :
 target_summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : target_summary tf (R.observe st target) owner)
 by (apply target_summary_observe,Hsummary).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. right;right;exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. right;right.
   eapply target_summary_get; [exact Hg |].
   subst current. destruct (R.is_materialized (R.observe st target) target);
   [exact Hobs |apply target_summary_enqueue,Hobs].
Qed.
Lemma target_spawn tf st fr target next k owner after :
 target_summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : target_summary tf (R.observe st target) owner)
 by (apply target_summary_observe,Hsummary).
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst. right;right;exact Hobs.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;right;right;[exact Hobs |].
   apply target_summary_materialize,target_summary_enqueue,Hobs.
Qed.
Lemma target_drain tf st fr k owner after :
 target_summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hq in Hstep; cbn in Hstep.
 - inversion Hstep;subst. right;right.
   apply target_summary_reset,Hsummary.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst. eapply target_pop;
     [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. eapply target_pop;
       [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
     * inversion Hstep;subst. right;right.
       apply target_summary_reset,Hsummary.
Qed.
Lemma target_return tf st k owner after :
 target_summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;right;right;exact Hsummary].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. right;right. eapply target_summary_get; eassumption.
Qed.
Lemma target_base tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 target_summary tf (R.cfg_state before) owner ->
 R.next_config tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hsummary Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp; [|discriminate].
   inversion Hstep;subst. eapply target_pop; [exact Hp |now left |exact Hsummary].
 - destruct l; cbn -[R.observe] in Hstep.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + destruct (R.is_materialized (R.observe st t) t);
     inversion Hstep;subst;right;right;apply target_summary_observe,Hsummary.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply target_pop; [exact Hp |now left |exact Hsummary].
   + inversion Hstep;subst. right;right;exact Hsummary.
 - inversion Hstep;subst. right;right;apply target_summary_materialize,Hsummary.
 - destruct r.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + eapply target_get; eassumption.
   + contradiction.
   + eapply target_spawn; eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. right;right. apply target_summary_requeue.
   eapply target_summary_set; eassumption.
 - eapply target_drain; eassumption.
 - eapply target_return; eassumption.
Qed.

Lemma target_precommit tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 target_summary tf (R.cfg_state before) owner ->
 P.next_config tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hsummary Hstep.
 destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply target_base; eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply target_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
   |now left |exact Hsummary].
 - eapply target_base; eauto.
Qed.
Lemma target_batched tf before after owner :
 nonpublication (R.cfg_control before) ->
 target_summary tf (R.cfg_state before) owner ->
 P.next_batched tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hsummary Hstep.
 destruct control; cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply target_precommit; [ | |exact Hsummary |exact Hstep]; [exact I |exact Hdead]].
 - destruct r;
   try solve [eapply target_precommit; [ | |exact Hsummary |exact Hstep]; [exact I |exact Hdead]].
   inversion Hstep;subst. right;right. apply target_summary_observe,Hsummary.
 - contradiction.
Qed.
Lemma target_fresh tf before after owner :
 nonpublication (R.cfg_control before) ->
 target_summary tf (R.cfg_state before) owner ->
 P.next_fresh tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hsummary Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply target_batched; eauto].
 - inversion Hstep;subst. destruct (V.eq_dec owner t) as [->|Hneq].
   + right;left;now left.
   + right;right. apply target_summary_materialize,target_summary_clear_other; assumption.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply target_pop;
     [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
     |now left |exact Hsummary].
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply target_clear; [now left |exact Hsummary].
     * eapply target_batched; eauto.
 - destruct c; cbn -[P.next_batched] in Hstep;
   try solve [eapply target_batched; eauto].
   inversion Hstep;subst. apply target_clear; [now left |exact Hsummary].
Qed.
Lemma finish_target_summary tf before after fr target changed owner :
 target_summary tf after owner ->
 target_summary tf (C.finish_write before after fr target changed) owner.
Proof.
 unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;
 intro H; auto using target_summary_enqueue.
Qed.
Lemma publish_other_target_summary tf targets st fr owner :
 owner <> R.frame_owner fr -> target_summary tf st owner ->
 target_summary tf (C.publish targets st fr) owner.
Proof.
 intro Hneq. revert st. induction targets as [|target rest IH]; intros st Hsummary;
 cbn -[R.write_side_contribution C.finish_write]; [exact Hsummary |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH,finish_target_summary. eapply target_summary_write_other; eassumption.
Qed.
Lemma dead_pending_target_summary tf st fr direct target rest k owner after :
 target_summary tf st owner ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 = Some after -> target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)).
 - inversion Hstep;subst. right;right;exact Hsummary.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hneq].
   + unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;left;cbn;auto.
   + assert (Hs : target_summary tf next owner)
     by (eapply target_summary_write_other; eassumption).
     assert (Hq : target_summary tf (C.requeue_source st next (R.frame_owner fr) target) owner).
     { unfold C.requeue_source. destruct C.cell_changed;
       [apply target_summary_enqueue,Hs |exact Hs]. }
     unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;right;cbn;auto using target_summary_enqueue.
Qed.
Theorem next_preserves_target_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 target_summary tf (R.cfg_state before) owner ->
 N.next_config tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach Hsummary Hstep.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { eapply target_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp)))
   |now left |exact Hsummary]. }
 clear Hstep. rename Hb into Hstep.
 destruct before as [st control]. destruct control;
 try solve [eapply target_fresh; [ |exact Hsummary |exact Hstep]; exact I].
 destruct l as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq]; [right;left;now left |].
   right;right. apply target_summary_publish_other;[exact Hneq |].
   apply publish_other_target_summary; assumption.
 - eapply (@dead_pending_target_summary tf st f t target rest c owner after); eassumption.
Qed.

(** The repaired scheduler cannot lose pending owner work. *)


Theorem reachable_commit_target_summary tf roots st fr direct k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 target_summary tf st (R.frame_owner fr).
Proof.
 intro Hreach.
 destruct (reachable_history Hreach) as [_ [[reads [effects [Htrace [Hguard Hacc]]]] _]].
 exists direct,reads,effects. split;[exact Htrace |]. split;[exact Hguard |].
 destruct (reachable_commit_origin Hreach) as [before ->].
 intros target value Hin. unfold R.lookup_set. cbn. rewrite ML.lookup_update_same.
 destruct (proj1 Hacc target value Hin) as [input [Hlookup [Hle Hmem]]]. exact Hmem.
Qed.
Theorem actual_commit_target_summary tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 target_summary tf after (R.frame_owner fr).
Proof.
 intros Hreach Hstep.
 pose proof (reachable_commit_target_summary Hreach) as Hsummary.
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_frame] eqn:Hset.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 inversion Hstep;subst. apply target_summary_requeue.
 eapply target_summary_set;eassumption.
Qed.
Theorem next_guarded_target_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 target_guarded tf (R.cfg_state before) (R.cfg_control before) owner ->
 N.next_config tf before = Some after ->
 target_guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach [Hq|[Ha|Hs]] Hstep.
 - destruct (@next_schedule tf before after Hstep owner (or_introl Hq))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_target_summary;eassumption.
 - destruct (@next_schedule tf before after Hstep owner (or_intror Ha))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_target_summary;eassumption.
 - eapply next_preserves_target_summary;eassumption.
Qed.
Definition target_summaries tf c :=
 forall owner,Sem.solved (R.cfg_state c) owner ->
 target_guarded tf (R.cfg_state c) (R.cfg_control c) owner.
Lemma next_target_summaries tf roots before after :
 N.steps tf (R.initial_config roots) before ->
 target_summaries tf before -> N.next_config tf before = Some after ->
 target_summaries tf after.
Proof.
 intros Hreach Hsummaries Hstep owner Hsolved.
 destruct (@next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
 as [Hbefore|[Hq|Ha]];[|now left |now right;left].
 eapply next_guarded_target_summary;[exact Hreach |apply Hsummaries,Hbefore |exact Hstep].
Qed.
Lemma steps_target_summaries tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 target_summaries tf first -> target_summaries tf last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hsummaries;[exact Hsummaries |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_target_summaries;eassumption.
Qed.
Theorem reachable_target_summaries tf roots c :
 N.steps tf (R.initial_config roots) c -> target_summaries tf c.
Proof.
 intro Hreach. eapply steps_target_summaries;[exact Hreach |constructor |].
 intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
Qed.
Theorem reachable_clean_target_replay tf roots c owner :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 exists direct reads effects,Sem.rhs_eval (R.cfg_state c) (tf owner) direct reads effects /\
 targets_live (R.cfg_state c) owner effects.
Proof.
 intros Hreach Hsolved Hqueue Hactive.
 destruct (@reachable_target_summaries tf roots c Hreach owner Hsolved)
 as [Hq|[Ha|[direct [reads [effects [Htrace [Hguard Hlive]]]]]]];try contradiction.
 exists direct,reads,effects. split;[|exact Hlive].
 apply B.rhs_trace_replay;[exact Htrace |].
 eapply H.guarded_reads_clean;eassumption.
Qed.


Theorem reachable_clean_replay_targets tf roots c owner direct reads effects :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 Sem.rhs_eval (R.cfg_state c) (tf owner) direct reads effects ->
 targets_live (R.cfg_state c) owner effects.
Proof.
 intros Hreach Hsolved Hqueue Hactive Heval.
 destruct (@reachable_clean_target_replay tf roots c owner Hreach Hsolved Hqueue Hactive)
 as [result [rs [es [Hreplay Hlive]]]].
 destruct (B.rhs_eval_deterministic Hreplay Heval) as [_ [_ Heq]]. now subst es.
Qed.
Theorem committing_higher_replay_targets tf roots st fr direct k after next_fr next_k owner result reads effects :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Sem.solved st owner ->
 Sem.rhs_eval st (tf owner) result reads effects -> targets_live st owner effects.
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved Heval.
 destruct (@committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 exact (@reachable_clean_replay_targets tf roots _ owner result reads effects
 Hreach Hsolved Hqueue Hactive Heval).
Qed.
Theorem successful_run_target_replay fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall owner,Sem.solved final owner ->
 exists direct reads effects,Sem.rhs_eval final (tf owner) direct reads effects /\
 targets_live final owner effects.
Proof.
 intro Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
 as [Hshape Hquiet].
 assert (Hreach : N.steps tf (R.initial_config roots) (Sem.terminal_config final)).
 { rewrite <- Hshape. apply fuel_steps. }
 intros owner Hsolved. apply (@reachable_clean_target_replay tf roots (Sem.terminal_config final) owner Hreach Hsolved).
 - exact (@B.quiescent_not_queued final owner Hquiet).
 - cbn. tauto.
Qed.

(** Spawn demands are tracked separately from RHS replay: replay itself does
    not require spawn targets to be materialized. At StartEpisode, the history
    anticipates exactly the materialization performed by the next transition. *)
Module Demand.

Definition prepend reads effects spawns (result : O.observation) : O.observation :=
 {|O.observed_direct:=O.observed_direct result;
 O.observed_reads:=reads ++ O.observed_reads result;
 O.observed_sides:=effects ++ O.observed_sides result;
 O.observed_spawns:=spawns ++ O.observed_spawns result|}.
Definition context root current reads effects spawns :=
 forall result,Sem.rhs_observes current result ->
 Sem.rhs_observes root (prepend reads effects spawns result).
Definition spawned st spawns := forall target,In target spawns -> Sem.solved st target.
Definition evaluation tf st owner current :=
 exists reads effects spawns,context (tf owner) current reads effects spawns /\
 B.guarded_reads st owner reads /\ spawned st spawns.
Definition completed tf st owner direct :=
 exists reads effects spawns,Sem.rhs_observes (tf owner)
 {|O.observed_direct:=direct;O.observed_reads:=reads;O.observed_sides:=effects;O.observed_spawns:=spawns|} /\
 B.guarded_reads st owner reads /\ spawned st spawns.
Lemma context_initial body : context body body [] [] [].
Proof. intros [direct reads effects spawns] Hobs. exact Hobs. Qed.
Lemma context_get root target next reads effects spawns value :
 context root (R.ConstraintSystem.Get target next) reads effects spawns ->
 context root (next value) (reads ++ [(target,value)]) effects spawns.
Proof.
 intros Hcontext result Hobs.
 specialize (Hcontext _ (@Sem.ObserveGet target value next result Hobs)).
 unfold prepend in *. cbn in Hcontext. rewrite <- app_assoc. exact Hcontext.
Qed.
Lemma context_side root target value next reads effects spawns :
 context root (R.ConstraintSystem.Side target value next) reads effects spawns ->
 context root next reads (effects ++ [(target,value)]) spawns.
Proof.
 intros Hcontext result Hobs.
 specialize (Hcontext _ (@Sem.ObserveSide target value next result Hobs)).
 unfold prepend in *. cbn in Hcontext. rewrite <- app_assoc. exact Hcontext.
Qed.
Lemma context_spawn root target next reads effects spawns :
 context root (R.ConstraintSystem.Spawn target next) reads effects spawns ->
 context root next reads effects (spawns ++ [target]).
Proof.
 intros Hcontext result Hobs.
 specialize (Hcontext _ (@Sem.ObserveSpawn target next result Hobs)).
 unfold prepend in *. cbn in Hcontext. rewrite <- app_assoc. exact Hcontext.
Qed.
Lemma spawned_carries before after spawns :
 T.sigma_extends before after -> spawned before spawns -> spawned after spawns.
Proof.
 intros Hsigma Hspawns target Hin. destruct (Hspawns target Hin) as [value Hlookup].
 exact (Hsigma target value Hlookup).
Qed.
Lemma evaluation_carries tf before after owner body :
 T.sigma_extends before after ->
 (forall reads,B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 evaluation tf before owner body -> evaluation tf after owner body.
Proof.
 intros Hsigma Hcarry [reads [effects [spawns [Hcontext [Hreads Hspawn]]]]].
 exists reads,effects,spawns. split;[exact Hcontext |].
 split;[apply Hcarry,Hreads |eapply spawned_carries;eassumption].
Qed.
Lemma completed_carries tf before after owner direct :
 T.sigma_extends before after ->
 (forall reads,B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 completed tf before owner direct -> completed tf after owner direct.
Proof.
 intros Hsigma Hcarry [reads [effects [spawns [Hobs [Hreads Hspawn]]]]].
 exists reads,effects,spawns. split;[exact Hobs |].
 split;[apply Hcarry,Hreads |eapply spawned_carries;eassumption].
Qed.
Lemma evaluation_initial tf st owner : evaluation tf st owner (tf owner).
Proof.
 exists [],[],[]. split;[apply context_initial |].
 split;intros target;[intros value Hin |intro Hin];contradiction.
Qed.
Lemma evaluation_ret tf st owner direct :
 evaluation tf st owner (R.ConstraintSystem.Ret direct) -> completed tf st owner direct.
Proof.
 intros [reads [effects [spawns [Hcontext [Hreads Hspawn]]]]].
 exists reads,effects,spawns. split;[|now split].
 specialize (Hcontext _ (Sem.ObserveRet direct)).
 unfold prepend in Hcontext. cbn in Hcontext.
 repeat rewrite app_nil_r in Hcontext. exact Hcontext.
Qed.
Lemma evaluation_side tf st owner target value next :
 evaluation tf st owner (R.ConstraintSystem.Side target value next) ->
 evaluation tf st owner next.
Proof.
 intros [reads [effects [spawns [Hcontext [Hreads Hspawn]]]]].
 exists reads,(effects ++ [(target,value)]),spawns.
 split;[apply context_side,Hcontext |now split].
Qed.
Lemma evaluation_spawn tf st owner target next :
 evaluation tf st owner (R.ConstraintSystem.Spawn target next) ->
 Sem.solved st target -> evaluation tf st owner next.
Proof.
 intros [reads [effects [spawns [Hcontext [Hreads Hspawn]]]]] Hsolved.
 exists reads,effects,(spawns ++ [target]). split;[apply context_spawn,Hcontext |].
 split;[exact Hreads |]. intros observed Hin. apply in_app_or in Hin.
 destruct Hin as [Hin|[->|Hin]];[apply Hspawn,Hin |exact Hsolved |contradiction].
Qed.
Lemma evaluation_get tf st fr target next after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) ->
 evaluation tf st (R.frame_owner fr) (R.ConstraintSystem.Get target next) ->
 evaluation tf after (R.frame_owner next_fr) (next value).
Proof.
 intros Hget [reads [effects [spawns [Hcontext [Hreads Hspawn]]]]].
 rewrite (@H.get_owner st fr target after next_fr value Hget).
 exists (reads ++ [(target,value)]),effects,spawns.
 split;[apply context_get,Hcontext |]. split.
 - intros observed v Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
   + eapply H.carries_get;[exact Hget |exact Hreads |exact Hin].
   + inversion Heq;subst. exact (@H.get_new_read st fr observed after next_fr v Hget observed v (or_introl eq_refl)).
   + contradiction.
 - eapply spawned_carries;[eapply T.sigma_extends_complete_get;exact Hget |exact Hspawn].
Qed.
Fixpoint continuation tf st k :=
 match k with
 | R.KLoop | R.KSeedLoop _ => True
 | R.KAfterGet fr target next rest =>
   evaluation tf st (R.frame_owner fr) (R.ConstraintSystem.Get target next) /\ continuation tf st rest
 | R.KAfterSide fr next rest => next = tf (R.frame_owner fr) /\ continuation tf st rest
 | R.KAfterSpawn fr next rest => evaluation tf st (R.frame_owner fr) next /\ continuation tf st rest
 | R.KDead fr direct _ rest => completed tf st (R.frame_owner fr) direct /\ continuation tf st rest
 | R.KDrain _ rest => continuation tf st rest
 end.
Definition history tf st control :=
 match control with
 | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
 | R.StartEpisode owner k => continuation tf (R.materialize st owner) k
 | R.RunDrain _ k | R.Return k => continuation tf st k
 | R.RunRhs fr body k => evaluation tf st (R.frame_owner fr) body /\ continuation tf st k
 | R.RunDead fr direct _ k | R.RunCommit fr direct k =>
   completed tf st (R.frame_owner fr) direct /\ continuation tf st k
 end.
Lemma continuation_carries tf before after k :
 T.sigma_extends before after -> H.carries_reads before after ->
 continuation tf before k -> continuation tf after k.
Proof.
 intros Hsigma Hcarry. induction k;cbn;intro Hk;try exact I;try (now apply IHk).
 all: destruct Hk as [Hhead Htail];split;try (now apply IHk);try exact Hhead.
 all: first [eapply evaluation_carries |eapply completed_carries];
 [exact Hsigma |exact (Hcarry (R.frame_owner f)) |exact Hhead].
Qed.
Lemma continuation_other tf before after upper k :
 T.sigma_extends before after -> T.continuation_below before upper k ->
 (forall owner,R.rank_lt before owner upper = true ->
 forall reads,B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 continuation tf before k -> continuation tf after k.
Proof.
 intros Hsigma. revert upper. induction k;intros upper Hbelow Hcarry Hk;cbn in *;try exact I.
 all: destruct Hbelow as [Hlt Hbelow].
 all: assert (Htail : continuation tf after k).
 all: try (eapply IHk;[exact Hbelow | |tauto];
 intros owner Howner;apply Hcarry;eapply T.rank_lt_trans_true;eassumption).
 all: try exact Htail.
 all: destruct Hk as [Hhead _];split;[|exact Htail];try exact Hhead.
 all: first [eapply evaluation_carries |eapply completed_carries];
 [exact Hsigma |apply Hcarry,Hlt |exact Hhead].
Qed.


Lemma continuation_clear tf st owner k :
 T.continuation_below st owner k -> continuation tf st k ->
 continuation tf (P.clear_owner st owner) k.
Proof.
 intro Hbelow. eapply continuation_other;[apply T.sigma_extends_with_queue |exact Hbelow |].
 intros reader Hlt reads Hreads. apply P.clear_other_guarded_reads;[|exact Hreads].
 now apply B.rank_lt_true_neq_correctness in Hlt.
Qed.
Lemma continuation_pop tf st upper popped rest k :
 R.queue_pop (R.queue st) = Some (popped,rest) ->
 T.continuation_below st upper k ->
 (popped = upper \/ R.rank_lt st upper popped = true) ->
 continuation tf st k -> continuation tf (R.with_queue st rest) k.
Proof.
 intros Hpop Hbelow Habove.
 eapply continuation_other;[apply T.sigma_extends_with_queue |exact Hbelow |].
 intros owner Hlt reads Hreads. eapply B.guarded_reads_pop_other;[exact Hpop | |exact Hreads].
 apply (@B.rank_lt_true_neq_correctness st).
 destruct Habove as [->|Hhigher];[exact Hlt |eapply T.rank_lt_trans_true;eauto].
Qed.
Lemma continuation_materialize tf st target k :
 continuation tf st k -> continuation tf (R.materialize st target) k.
Proof.
 eapply continuation_carries;[apply T.sigma_extends_materialize |apply H.carries_materialize].
Qed.
Lemma continuation_enqueue tf st target k :
 continuation tf st k -> continuation tf (R.enqueue st target) k.
Proof.
 eapply continuation_carries;[apply T.sigma_extends_enqueue |apply H.carries_enqueue].
Qed.
Lemma rhs_carries tf before after fr body k :
 T.sigma_extends before after -> H.carries_reads before after ->
 history tf before (R.RunRhs fr body k) -> history tf after (R.RunRhs fr body k).
Proof.
 intros Hsigma Hreads [He Hk]. split.
 - eapply evaluation_carries;[exact Hsigma |apply Hreads |exact He].
 - eapply continuation_carries;eassumption.
Qed.
Lemma dead_carries tf before after fr direct pending k :
 T.sigma_extends before after -> H.carries_reads before after ->
 history tf before (R.RunDead fr direct pending k) ->
 history tf after (R.RunDead fr direct pending k).
Proof.
 intros Hsigma Hreads [He Hk]. split.
 - eapply completed_carries;[exact Hsigma |apply Hreads |exact He].
 - eapply continuation_carries;eassumption.
Qed.
Lemma materialized_solved st target :
 R.is_materialized st target = true -> Sem.solved st target.
Proof.
 unfold R.is_materialized,Sem.solved.
 destruct (M.lookup (R.sigma st) target) as [value|] eqn:Hv;[intros _;now exists value |discriminate].
Qed.
Lemma materialize_solved st target : Sem.solved (R.materialize st target) target.
Proof.
 unfold R.materialize. destruct (M.lookup (R.sigma st) target) as [value|] eqn:Hv.
 - now exists value.
 - exists D.bottom. cbn. apply ML.lookup_update_same.
Qed.
Lemma get_config tf st fr target next k after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) ->
 history tf st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 history tf after (R.RunRhs next_fr (next value) k).
Proof.
 intros Hget [He Hk]. split;[eapply evaluation_get;eassumption |].
 eapply continuation_carries;[eapply T.sigma_extends_complete_get;exact Hget |exact (H.carries_get Hget) |exact Hk].
Qed.
Lemma base_get tf st fr target next k after :
 history tf st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hhistory Hstep.
 assert (Hobs : history tf (R.observe st target) (R.RunRhs fr (R.ConstraintSystem.Get target next) k)).
 { eapply rhs_carries;[apply T.sigma_extends_observe |apply H.carries_observe |exact Hhistory]. }
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. apply continuation_materialize. exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[next_st next_fr] value] eqn:Hget.
   inversion Hstep;subst. eapply get_config;[exact Hget |].
   subst current. destruct (R.is_materialized (R.observe st target) target);[exact Hobs |].
   eapply rhs_carries;[apply T.sigma_extends_enqueue |apply H.carries_enqueue |exact Hobs].
Qed.
Lemma base_spawn tf st fr target next k after :
 history tf st (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hhistory Hstep.
 assert (Hobs : history tf (R.observe st target) (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k)).
 { eapply rhs_carries;[apply T.sigma_extends_observe |apply H.carries_observe |exact Hhistory]. }
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
 - inversion Hstep;subst. destruct Hobs as [He Hk]. split;[|exact Hk].
   eapply evaluation_spawn;[exact He |apply materialized_solved,Hmat].
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
   + inversion Hstep;subst. destruct Hobs as [He Hk]. split.
     * eapply evaluation_spawn;[|apply materialize_solved].
       eapply evaluation_carries;[apply T.sigma_extends_materialize |apply H.carries_materialize |exact He].
     * apply continuation_materialize,Hk.
   + inversion Hstep;subst.
     assert (Hafter : history tf (R.materialize (R.enqueue (R.observe st target) target) target)
       (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k)).
     { eapply rhs_carries;[apply T.sigma_extends_materialize |apply H.carries_materialize |].
       eapply rhs_carries;[apply T.sigma_extends_enqueue |apply H.carries_enqueue |exact Hobs]. }
     destruct Hafter as [He Hk]. split;[|exact Hk].
     eapply evaluation_spawn;[exact He |apply materialize_solved].
Qed.


Lemma continue_dead_history tf st fr direct target pending k changed :
 history tf st (R.RunDead fr direct pending k) ->
 history tf (R.cfg_state (R.continue_dead st fr direct target pending k changed))
 (R.cfg_control (R.continue_dead st fr direct target pending k changed)).
Proof.
 intro Hhistory. unfold R.continue_dead. destruct changed;[|exact Hhistory].
 destruct (_ && _)%bool.
 - apply continuation_materialize. exact Hhistory.
 - eapply dead_carries;[apply T.sigma_extends_enqueue |apply H.carries_enqueue |exact Hhistory].
Qed.
Lemma base_dead tf st fr direct pending k after :
 history tf st (R.RunDead fr direct pending k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hhistory Hstep. destruct pending as [|target rest];
 cbn -[R.write_side_contribution R.continue_dead R.publish_targets] in Hstep.
 - inversion Hstep;subst. destruct Hhistory as [Hc Hk]. split.
   + eapply completed_carries;[apply T.sigma_extends_same;reflexivity
     |apply H.carries_same;exact (proj1 (B.publish_targets_same_solver_view st fr)) |exact Hc].
   + eapply continuation_carries with (before:=st);[apply T.sigma_extends_same;reflexivity
     |apply H.carries_same;exact (proj1 (B.publish_targets_same_solver_view st fr)) |exact Hk].
 - destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hhistory |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hwrite.
   inversion Hstep;subst. apply continue_dead_history.
   eapply dead_carries;[eapply T.sigma_extends_write_side_contribution;exact Hwrite
   |exact (H.carries_write Hwrite) |exact Hhistory].
Qed.
Lemma base_commit tf st fr direct k after :
 history tf st (R.RunCommit fr direct k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros [Hc Hk] Hstep. cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
 inversion Hstep;subst.
 eapply continuation_carries with (before:=next);[apply T.sigma_extends_with_queue |apply H.carries_requeue |].
 eapply continuation_carries;[eapply T.sigma_extends_set_value;exact Hset
 |exact (@H.carries_set st fr direct next next_fr Hset) |exact Hk].
Qed.
Lemma continuation_reset tf st scope k :
 continuation tf st k -> continuation tf (R.reset_registered_cells st scope) k.
Proof.
 eapply continuation_carries;[apply T.sigma_extends_reset_registered_cells |].
 apply H.carries_same. exact (proj1 (B.reset_registered_cells_same_solver_view st scope)).
Qed.
Lemma base_drain tf st fr k after :
 T.continuation_below st (R.frame_owner fr) k ->
 history tf st (R.RunDrain fr k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Horder Hk Hstep. destruct (R.queue st) as [|target rest] eqn:Hqueue;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hqueue in Hstep;cbn in Hstep.
 - inversion Hstep;subst. apply continuation_reset,Hk.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst. split;[apply evaluation_initial |].
     eapply continuation_pop;
     [unfold R.queue_pop;rewrite Hqueue;reflexivity |exact Horder |now left |exact Hk].
   + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
     * inversion Hstep;subst. apply continuation_materialize. cbn.
       eapply continuation_pop;
       [unfold R.queue_pop;rewrite Hqueue;reflexivity |exact Horder |now right |exact Hk].
     * inversion Hstep;subst. apply continuation_reset,Hk.
Qed.
Lemma base_return tf st k after :
 history tf st (R.Return k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hk Hstep. destruct k;cbn -[R.complete_get] in Hstep;cbn in Hk.
 all: try solve [inversion Hstep;subst;cbn;tauto].
 - destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hget.
   inversion Hstep;subst. eapply get_config;[exact Hget |exact Hk].
 - destruct Hk as [Heq Hk]. inversion Hstep;subst.
   split;[apply evaluation_initial |exact Hk].
Qed.
Lemma base_step tf before after :
 H.not_side (R.cfg_control before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 history tf (R.cfg_state before) (R.cfg_control before) ->
 R.next_config tf before = Some after ->
 history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hnot Horder Hhistory Hstep. destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
   [inversion Hstep;subst;exact I |discriminate].
 - destruct l;cbn -[R.observe] in Hstep;
   try destruct (R.is_materialized (R.observe st t) t);inversion Hstep;subst;exact I.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
   inversion Hstep;subst;exact I.
 - inversion Hstep;subst. split;[apply evaluation_initial |exact Hhistory].
 - destruct r.
   + inversion Hstep;subst. destruct Hhistory as [He Hk].
     split;[apply evaluation_ret,He |exact Hk].
   + eapply base_get;eassumption.
   + contradiction.
   + eapply base_spawn;eassumption.
 - eapply base_dead;eassumption.
 - eapply base_commit;eassumption.
 - exact (@base_drain tf st f c after Horder Hhistory Hstep).
 - eapply base_return;eassumption.
Qed.
Lemma suspend_history tf st fr direct k target rest :
 P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 T.continuation_below st (R.frame_owner fr) k ->
 history tf st (R.RunCommit fr direct k) ->
 history tf (R.cfg_state (P.suspend_commit tf st fr k target rest))
 (R.cfg_control (P.suspend_commit tf st fr k target rest)).
Proof.
 intros Hp Ho [Hc Hk]. unfold P.suspend_commit. cbn.
 split;[reflexivity |]. apply continuation_materialize.
 destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop Hlt]].
 eapply continuation_pop;[exact Hpop |exact Ho |now right |exact Hk].
Qed.
Lemma precommit_step tf before after :
 H.not_side (R.cfg_control before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 history tf (R.cfg_state before) (R.cfg_control before) ->
 P.next_config tf before = Some after ->
 history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hnot Ho Hhistory Hstep.
 destruct control;cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_step;eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply suspend_history;eassumption.
 - eapply base_step;eauto.
Qed.


Lemma batched_step tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 history tf (R.cfg_state before) (R.cfg_control before) ->
 P.next_batched tf before = Some after ->
 history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hdead Ho Hhistory Hstep.
 destruct control;cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply precommit_step;[ | | |exact Hstep];[exact I |exact Ho |exact Hhistory]].
 - destruct r;
   try solve [eapply precommit_step;[ | | |exact Hstep];[exact I |exact Ho |exact Hhistory]].
   inversion Hstep;subst.
   cbn -[R.observe].
   destruct Hhistory as [He Hk]. split.
   + eapply evaluation_carries;[apply T.sigma_extends_observe |apply H.carries_observe |].
     eapply evaluation_side;exact He.
   + eapply continuation_carries;[apply T.sigma_extends_observe |apply H.carries_observe |exact Hk].
 - contradiction.
Qed.
Lemma clear_materialize st owner :
 R.materialize (P.clear_owner st owner) owner =
 P.clear_owner (R.materialize st owner) owner.
Proof.
 unfold R.materialize,P.clear_owner. cbn.
 destruct (M.lookup (R.sigma st) owner);reflexivity.
Qed.
Lemma clear_start tf st owner k :
 T.continuation_below st owner k ->
 history tf st (R.StartEpisode owner k) ->
 history tf (P.clear_owner st owner) (R.StartEpisode owner k).
Proof.
 intros Ho Hk. cbn. rewrite clear_materialize. apply continuation_clear;[|exact Hk].
 eapply H.below_extended;[apply B.rank_extends_materialize |exact Ho].
Qed.
Lemma retry_history tf st fr direct k :
 T.continuation_below st (R.frame_owner fr) k ->
 history tf st (R.RunCommit fr direct k) ->
 history tf (R.cfg_state (P.retry_current tf st fr k))
 (R.cfg_control (P.retry_current tf st fr k)).
Proof.
 intros Ho [Hc Hk]. split;[apply evaluation_initial |].
 apply continuation_clear;assumption.
Qed.
Lemma fresh_step tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 history tf (R.cfg_state before) (R.cfg_control before) ->
 P.next_fresh tf before = Some after ->
 history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st control]. intros Hdead Ho Hhistory Hstep.
 destruct control;cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_step;eassumption].
 - eapply batched_step;[ | | |exact Hstep];[exact I | |].
   + eapply H.below_extended;[apply B.rank_extends_with_queue |exact Ho].
   + eapply clear_start;eassumption.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply suspend_history;eassumption.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. eapply retry_history;eassumption.
     * eapply batched_step;eassumption.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_step;[ | | |exact Hstep];[exact I |exact Ho |exact Hhistory]].
   eapply batched_step;[ | | |exact Hstep];[exact I | |].
   + eapply H.below_extended;[apply B.rank_extends_with_queue |exact Ho].
   + destruct Hhistory as [Hbody Hk]. split;[exact Hbody |].
     eapply continuation_clear;eassumption.
Qed.
Lemma requeue_carries before after source target : H.carries_reads after (C.requeue_source before after source target).
Proof.
 unfold C.requeue_source. destruct C.cell_changed;[apply H.carries_enqueue |intros owner reads Hr;exact Hr].
Qed.
Lemma finish_carries before after fr target changed : H.carries_reads after (C.finish_write before after fr target changed).
Proof.
 unfold C.finish_write. destruct changed;[|apply requeue_carries].
 eapply H.carries_trans;[apply requeue_carries |apply H.carries_enqueue].
Qed.
Lemma publish_carries targets st fr : H.carries_reads st (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[intros owner reads Hr;exact Hr |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end)) as [next changed] eqn:Hw.
 eapply H.carries_trans;[exact (H.carries_write Hw) |].
 eapply H.carries_trans;[apply finish_carries |apply IH].
Qed.
Lemma dead_step tf st fr direct pending k after :
 history tf st (R.RunDead fr direct pending k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}
 = Some after -> history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hhistory Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   destruct Hhistory as [Hc Hk].
   assert (Hs : T.sigma_extends st (R.publish_targets
     (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr)).
   { apply T.sigma_extends_same. cbn. apply publish_sigma. }
   assert (Hr : H.carries_reads st (R.publish_targets
     (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr)).
   { eapply H.carries_trans;[apply publish_carries |].
     apply H.carries_same. apply (proj1 (B.publish_targets_same_solver_view _ _)). }
   split.
   + eapply completed_carries;[exact Hs |apply Hr |exact Hc].
   + eapply continuation_carries;[exact Hs |exact Hr |exact Hk].
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hhistory |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. apply continue_dead_history.
   eapply dead_carries with (before:=next);[apply T.sigma_extends_same;apply requeue_sigma |apply requeue_carries |].
   eapply dead_carries;[eapply T.sigma_extends_write_side_contribution;exact Hw
   |exact (H.carries_write Hw) |exact Hhistory].
Qed.
Theorem next_history tf before after :
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 history tf (R.cfg_state before) (R.cfg_control before) ->
 N.next_config tf before = Some after ->
 history tf (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Ho Hhistory Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - destruct before as [st control]. destruct control;
   try solve [eapply fresh_step;[ | | |exact Hb];[exact I |exact Ho |exact Hhistory]].
   eapply dead_step;[exact Hhistory |exact Hb].
 - destruct Hhistory as [Hbody Hk]. cbn. split;[reflexivity |].
   apply continuation_materialize.
   destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop Hlt]].
   eapply continuation_pop;[exact Hpop |exact Ho |now right |exact Hk].
Qed.
Lemma steps_history tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 history tf (R.cfg_state first) (R.cfg_control first) ->
 history tf (R.cfg_state last) (R.cfg_control last).
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hhistory;[exact Hhistory |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_history;[exact (proj1 (reachable_history Hreach)) |exact Hhistory |exact H].
Qed.
Theorem reachable_history tf roots c :
 N.steps tf (R.initial_config roots) c ->
 history tf (R.cfg_state c) (R.cfg_control c).
Proof.
 intro Hreach. eapply steps_history;[exact Hreach |constructor |exact I].
Qed.


Definition summary tf st owner := exists direct,completed tf st owner direct.
Lemma summary_carries tf before after owner :
 T.sigma_extends before after ->
 (forall reads,B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 summary tf before owner -> summary tf after owner.
Proof.
 intros Hsigma Hcarry [direct Hcompleted]. exists direct.
 eapply completed_carries;eassumption.
Qed.
Lemma summary_observe tf st owner target :
 summary tf st owner -> summary tf (R.observe st target) owner.
Proof.
 eapply summary_carries;[apply T.sigma_extends_observe |apply H.carries_observe].
Qed.
Lemma summary_materialize tf st owner target :
 summary tf st owner -> summary tf (R.materialize st target) owner.
Proof.
 eapply summary_carries;[apply T.sigma_extends_materialize |apply H.carries_materialize].
Qed.
Lemma summary_enqueue tf st owner target :
 summary tf st owner -> summary tf (R.enqueue st target) owner.
Proof.
 eapply summary_carries;[apply T.sigma_extends_enqueue |apply H.carries_enqueue].
Qed.
Lemma summary_requeue tf before after source owner :
 summary tf after owner -> summary tf (R.requeue_changed_controlled_owner before after source) owner.
Proof.
 eapply summary_carries;[apply T.sigma_extends_with_queue |apply H.carries_requeue].
Qed.
Lemma summary_pop_other tf st popped rest owner :
 R.queue_pop (R.queue st) = Some (popped,rest) -> owner <> popped ->
 summary tf st owner -> summary tf (R.with_queue st rest) owner.
Proof.
 intros Hpop Hneq. eapply summary_carries;[apply T.sigma_extends_with_queue |].
 intros. eapply B.guarded_reads_pop_other;eassumption.
Qed.
Lemma summary_clear_other tf st cleared owner :
 owner <> cleared -> summary tf st owner -> summary tf (P.clear_owner st cleared) owner.
Proof.
 intro Hneq. eapply summary_carries;[apply T.sigma_extends_with_queue |].
 intros. eapply P.clear_other_guarded_reads;eassumption.
Qed.
Lemma summary_get tf st fr target next next_fr value owner :
 R.complete_get st fr target = (next,next_fr,value) ->
 summary tf st owner -> summary tf next owner.
Proof.
 intro Hget. eapply summary_carries;[eapply T.sigma_extends_complete_get;exact Hget |].
 intros. eapply H.carries_get;eassumption.
Qed.
Lemma summary_set tf st fr direct next next_fr owner :
 R.set_value st fr direct = (next,next_fr) ->
 summary tf st owner -> summary tf next owner.
Proof.
 intro Hset. eapply summary_carries;[eapply T.sigma_extends_set_value;exact Hset |].
 intros. eapply H.carries_set;eassumption.
Qed.
Lemma summary_reset tf st scope owner :
 summary tf st owner -> summary tf (R.reset_registered_cells st scope) owner.
Proof.
 eapply summary_carries;[apply T.sigma_extends_reset_registered_cells |].
 apply H.carries_same. exact (proj1 (B.reset_registered_cells_same_solver_view st scope)).
Qed.
Lemma summary_write_other tf st fr target input next changed owner :
 R.write_side_contribution st fr target input = (next,changed) ->
 owner <> R.frame_owner fr -> summary tf st owner -> summary tf next owner.
Proof.
 intros Hwrite Hneq. eapply summary_carries;[eapply T.sigma_extends_write_side_contribution;exact Hwrite |].
 intros. eapply H.carries_write;eassumption.
Qed.
Lemma summary_publish_other tf st fr owner :
 owner <> R.frame_owner fr -> summary tf st owner -> summary tf (R.publish_targets st fr) owner.
Proof.
 intro Hneq. eapply summary_carries with (before:=st);[apply T.sigma_extends_same;reflexivity |].
 apply H.carries_same. exact (proj1 (B.publish_targets_same_solver_view st fr)).
Qed.

Definition guarded tf st control owner :=
 B.queued st owner \/ B.control_active owner control \/ summary tf st owner.
Lemma guard_pop tf st popped rest next owner :
 R.queue_pop (R.queue st) = Some (popped,rest) ->
 B.control_active popped next -> summary tf st owner ->
 guarded tf (R.with_queue st rest) next owner.
Proof.
 intros Hpop Hactive Hsummary. destruct (V.eq_dec owner popped) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. eapply summary_pop_other; eassumption.
Qed.
Lemma guard_clear tf st cleared next owner :
 B.control_active cleared next -> summary tf st owner ->
 guarded tf (P.clear_owner st cleared) next owner.
Proof.
 intros Hactive Hsummary. destruct (V.eq_dec owner cleared) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. apply summary_clear_other;assumption.
Qed.
Lemma guard_get tf st fr target next k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : summary tf (R.observe st target) owner)
 by (apply summary_observe,Hsummary).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. right;right;exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. right;right.
   eapply summary_get; [exact Hg |].
   subst current. destruct (R.is_materialized (R.observe st target) target);
   [exact Hobs |apply summary_enqueue,Hobs].
Qed.
Lemma guard_spawn tf st fr target next k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : summary tf (R.observe st target) owner)
 by (apply summary_observe,Hsummary).
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst. right;right;exact Hobs.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;right;right;[exact Hobs |].
   apply summary_materialize,summary_enqueue,Hobs.
Qed.
Lemma guard_drain tf st fr k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hq in Hstep; cbn in Hstep.
 - inversion Hstep;subst. right;right.
   apply summary_reset,Hsummary.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst. eapply guard_pop;
     [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. eapply guard_pop;
       [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
     * inversion Hstep;subst. right;right.
       apply summary_reset,Hsummary.
Qed.
Lemma guard_return tf st k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;right;right;exact Hsummary].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. right;right. eapply summary_get; eassumption.
Qed.
Lemma guard_base tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 summary tf (R.cfg_state before) owner ->
 R.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hsummary Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp; [|discriminate].
   inversion Hstep;subst. eapply guard_pop; [exact Hp |now left |exact Hsummary].
 - destruct l; cbn -[R.observe] in Hstep.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + destruct (R.is_materialized (R.observe st t) t);
     inversion Hstep;subst;right;right;apply summary_observe,Hsummary.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply guard_pop; [exact Hp |now left |exact Hsummary].
   + inversion Hstep;subst. right;right;exact Hsummary.
 - inversion Hstep;subst. right;right;apply summary_materialize,Hsummary.
 - destruct r.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + eapply guard_get; eassumption.
   + contradiction.
   + eapply guard_spawn; eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. right;right. apply summary_requeue.
   eapply summary_set; eassumption.
 - eapply guard_drain; eassumption.
 - eapply guard_return; eassumption.
Qed.

Lemma guard_precommit tf before after owner :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 summary tf (R.cfg_state before) owner ->
 P.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hsummary Hstep.
 destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply guard_base; eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply guard_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
   |now left |exact Hsummary].
 - eapply guard_base; eauto.
Qed.
Lemma guard_batched tf before after owner :
 nonpublication (R.cfg_control before) ->
 summary tf (R.cfg_state before) owner ->
 P.next_batched tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hsummary Hstep.
 destruct control; cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply guard_precommit; [ | |exact Hsummary |exact Hstep]; [exact I |exact Hdead]].
 - destruct r;
   try solve [eapply guard_precommit; [ | |exact Hsummary |exact Hstep]; [exact I |exact Hdead]].
   inversion Hstep;subst. right;right. apply summary_observe,Hsummary.
 - contradiction.
Qed.
Lemma guard_fresh tf before after owner :
 nonpublication (R.cfg_control before) ->
 summary tf (R.cfg_state before) owner ->
 P.next_fresh tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hsummary Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply guard_batched; eauto].
 - inversion Hstep;subst. destruct (V.eq_dec owner t) as [->|Hneq].
   + right;left;now left.
   + right;right. apply summary_materialize,summary_clear_other; assumption.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply guard_pop;
     [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
     |now left |exact Hsummary].
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply guard_clear; [now left |exact Hsummary].
     * eapply guard_batched; eauto.
 - destruct c; cbn -[P.next_batched] in Hstep;
   try solve [eapply guard_batched; eauto].
   inversion Hstep;subst. apply guard_clear; [now left |exact Hsummary].
Qed.
Lemma finish_summary tf before after fr target changed owner :
 summary tf after owner ->
 summary tf (C.finish_write before after fr target changed) owner.
Proof.
 unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;
 intro H; auto using summary_enqueue.
Qed.
Lemma publish_other_summary tf targets st fr owner :
 owner <> R.frame_owner fr -> summary tf st owner ->
 summary tf (C.publish targets st fr) owner.
Proof.
 intro Hneq. revert st. induction targets as [|target rest IH]; intros st Hsummary;
 cbn -[R.write_side_contribution C.finish_write]; [exact Hsummary |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH,finish_summary. eapply summary_write_other; eassumption.
Qed.
Lemma dead_pending_summary tf st fr direct target rest k owner after :
 summary tf st owner ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)).
 - inversion Hstep;subst. right;right;exact Hsummary.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hneq].
   + unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;left;cbn;auto.
   + assert (Hs : summary tf next owner)
     by (eapply summary_write_other; eassumption).
     assert (Hq : summary tf (C.requeue_source st next (R.frame_owner fr) target) owner).
     { unfold C.requeue_source. destruct C.cell_changed;
       [apply summary_enqueue,Hs |exact Hs]. }
     unfold R.continue_dead. destruct changed; [destruct (_ && _)%bool |];
     right;right;cbn;auto using summary_enqueue.
Qed.
Theorem next_preserves_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 summary tf (R.cfg_state before) owner ->
 N.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach Hsummary Hstep.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { eapply guard_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp)))
   |now left |exact Hsummary]. }
 clear Hstep. rename Hb into Hstep.
 destruct before as [st control]. destruct control;
 try solve [eapply guard_fresh; [ |exact Hsummary |exact Hstep]; exact I].
 destruct l as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq]; [right;left;now left |].
   right;right. apply summary_publish_other;[exact Hneq |].
   apply publish_other_summary; assumption.
 - eapply (@dead_pending_summary tf st f t target rest c owner after); eassumption.
Qed.

(** The repaired scheduler cannot lose pending owner work. *)


Theorem reachable_commit_summary tf roots st fr direct k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 summary tf st (R.frame_owner fr).
Proof.
 intro Hreach. exists direct. exact (proj1 (reachable_history Hreach)).
Qed.
Theorem actual_commit_summary tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 summary tf after (R.frame_owner fr).
Proof.
 intros Hreach Hstep.
 pose proof (reachable_commit_summary Hreach) as Hsummary.
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_frame] eqn:Hset.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 inversion Hstep;subst. apply summary_requeue.
 eapply summary_set;eassumption.
Qed.
Theorem next_guarded_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before ->
 guarded tf (R.cfg_state before) (R.cfg_control before) owner ->
 N.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach [Hq|[Ha|Hs]] Hstep.
 - destruct (@next_schedule tf before after Hstep owner (or_introl Hq))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_summary;eassumption.
 - destruct (@next_schedule tf before after Hstep owner (or_intror Ha))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_summary;eassumption.
 - eapply next_preserves_summary;eassumption.
Qed.
Definition summaries tf c := forall owner,Sem.solved (R.cfg_state c) owner ->
 guarded tf (R.cfg_state c) (R.cfg_control c) owner.
Lemma next_summaries tf roots before after :
 N.steps tf (R.initial_config roots) before -> summaries tf before ->
 N.next_config tf before = Some after -> summaries tf after.
Proof.
 intros Hreach Hsummaries Hstep owner Hsolved.
 destruct (@next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
 as [Hbefore|[Hq|Ha]];[|now left |now right;left].
 eapply next_guarded_summary;[exact Hreach |apply Hsummaries,Hbefore |exact Hstep].
Qed.
Lemma steps_summaries tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 summaries tf first -> summaries tf last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hsummaries;[exact Hsummaries |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_summaries;eassumption.
Qed.
Theorem reachable_summaries tf roots c :
 N.steps tf (R.initial_config roots) c -> summaries tf c.
Proof.
 intro Hreach. eapply steps_summaries;[exact Hreach |constructor |].
 intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
Qed.
Lemma observation_replay st body result :
 Sem.rhs_observes body result -> B.reads_agree st (O.observed_reads result) ->
 Sem.rhs_eval st body (O.observed_direct result) (O.observed_reads result) (O.observed_sides result).
Proof.
 intro Hobs. induction Hobs;intro Hreads;cbn in *.
 - constructor.
 - constructor;[apply Hreads;now left |]. apply IHHobs.
   intros target' value' Hin. apply Hreads. now right.
 - constructor. apply IHHobs,Hreads.
 - constructor. apply IHHobs,Hreads.
Qed.
Theorem reachable_clean_observation tf roots c owner :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 exists result,Sem.rhs_observes (tf owner) result /\
 Sem.rhs_eval (R.cfg_state c) (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 spawned (R.cfg_state c) (O.observed_spawns result).
Proof.
 intros Hreach Hsolved Hqueue Hactive.
 destruct (@reachable_summaries tf roots c Hreach owner Hsolved)
 as [Hq|[Ha|[direct [reads [effects [spawns [Hobs [Hguard Hspawn]]]]]]]];try contradiction.
 exists {|O.observed_direct:=direct;O.observed_reads:=reads;
 O.observed_sides:=effects;O.observed_spawns:=spawns|}.
 split;[exact Hobs |]. split;[|exact Hspawn].
 apply observation_replay;[exact Hobs |]. eapply H.guarded_reads_clean;eassumption.
Qed.
Theorem reachable_clean_paths tf roots c owner :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists result,Sem.rhs_eval (R.cfg_state c) (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 paths_below (R.sigma_value (R.cfg_state c)) result (tf owner) /\
 spawned (R.cfg_state c) (O.observed_spawns result).
Proof.
 intros Hreach Hsolved Hqueue Hactive Hdeps Heffects.
 destruct (@reachable_clean_observation tf roots c owner Hreach Hsolved Hqueue Hactive)
 as [result [Hobs [Heval Hspawn]]].
 exists result. split;[exact Heval |]. split;[|exact Hspawn].
 eapply monotone_paths_below;[exact Hdeps |exact Heffects |exact Hobs |].
 intros target value Hin. eapply replay_read_value;eassumption.
Qed.
Theorem committing_higher_paths tf roots st fr direct k after next_fr next_k owner :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Sem.solved st owner ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists result,Sem.rhs_eval st (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 paths_below (R.sigma_value st) result (tf owner) /\
 spawned st (O.observed_spawns result).
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved Hdeps Heffects.
 destruct (@committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 exact (@reachable_clean_paths tf roots _ owner Hreach Hsolved Hqueue Hactive Hdeps Heffects).
Qed.
Theorem successful_run_spawned fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall owner,Sem.solved final owner ->
 exists result,Sem.rhs_observes (tf owner) result /\
 Sem.rhs_eval final (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 spawned final (O.observed_spawns result).
Proof.
 intro Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
 as [Hshape Hquiet].
 assert (Hreach : N.steps tf (R.initial_config roots) (Sem.terminal_config final)).
 { rewrite <- Hshape. apply fuel_steps. }
 intros owner Hsolved. apply (@reachable_clean_observation tf roots (Sem.terminal_config final) owner Hreach Hsolved).
 - exact (@B.quiescent_not_queued final owner Hquiet).
 - cbn. tauto.
Qed.


Lemma path_get_solved st body result target next :
 Sem.rhs_eval st body (O.observed_direct result) (O.observed_reads result) (O.observed_sides result) ->
 paths_below (R.sigma_value st) result (R.ConstraintSystem.Get target next) ->
 Sem.solved st target.
Proof.
 intros Heval Hpaths.
 pose proof (@paths_get_target (R.sigma_value st) result target next Hpaths) as Hin.
 apply in_map_iff in Hin. destruct Hin as [[observed value] [Heq Hmem]]. cbn in Heq. subst observed.
 exists value. eapply replay_reads;[exact Heval |exact Hmem].
Qed.
Lemma path_spawn_solved cap st result target next :
 spawned st (O.observed_spawns result) ->
 paths_below cap result (R.ConstraintSystem.Spawn target next) ->
 Sem.solved st target.
Proof. intros Hspawn Hpaths. apply Hspawn. eapply paths_spawn_target;exact Hpaths. Qed.
End Demand.

(** Ordinary invalidation only queues materialized readers. *)
Module Readers.

Definition solved st := forall target reader,
 S.mem reader (R.lookup_set (R.readers st) target) = true -> Sem.solved st reader.
Lemma transport before after :
 R.readers after = R.readers before -> T.sigma_extends before after ->
 solved before -> solved after.
Proof.
 intros Hreaders Hsigma Hsolved target reader Hmem. rewrite Hreaders in Hmem.
 destruct (Hsolved target reader Hmem) as [value Hlookup]. exact (Hsigma reader value Hlookup).
Qed.
Lemma observe st target : solved st -> solved (R.observe st target).
Proof.
 apply transport;[|apply T.sigma_extends_observe].
 unfold R.observe. destruct (R.Ranking.observe (R.ranking st) target);reflexivity.
Qed.
Lemma materialize st target : solved st -> solved (R.materialize st target).
Proof.
 apply transport;[|apply T.sigma_extends_materialize].
 unfold R.materialize. destruct (M.lookup (R.sigma st) target);reflexivity.
Qed.
Lemma enqueue st target : solved st -> solved (R.enqueue st target).
Proof. apply transport;[reflexivity |apply T.sigma_extends_enqueue]. Qed.
Lemma queue st rest : solved st -> solved (R.with_queue st rest).
Proof. apply transport;[reflexivity |apply T.sigma_extends_with_queue]. Qed.
Lemma reset st scope : solved st -> solved (R.reset_registered_cells st scope).
Proof.
 apply transport;[|apply T.sigma_extends_reset_registered_cells].
 unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity.
Qed.
Lemma write st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) -> solved st -> solved next.
Proof.
 intro Hw. apply transport;[|eapply T.sigma_extends_write_side_contribution;exact Hw].
 exact (proj1 (proj2 (B.write_side_contribution_same_read_view Hw))).
Qed.
Lemma get_origin st fr target next next_fr value :
 R.complete_get st fr target = (next,next_fr,value) ->
 forall observed reader,S.mem reader (R.lookup_set (R.readers next) observed) = true ->
 reader = R.frame_owner fr \/ S.mem reader (R.lookup_set (R.readers st) observed) = true.
Proof.
 intros Hget observed reader Hmem. unfold R.complete_get in Hget.
 set (base:=if R.rank_lt st (R.frame_owner fr) target then st else R.promote_controlled st target) in *.
 inversion Hget;subst next. unfold R.materialize in Hmem.
 destruct (M.lookup _ target);cbn in Hmem.
 all: unfold R.lookup_set in Hmem.
 all: destruct (V.eq_dec observed target) as [->|Hneq].
 all: try rewrite ML.lookup_update_same in Hmem.
 all: try rewrite ML.lookup_update_other in Hmem by exact Hneq.
 all: try (apply SL.add_spec in Hmem;destruct Hmem as [->|Hmem];[now left |]).
 all: right;subst base;destruct (R.rank_lt st (R.frame_owner fr) target);exact Hmem.
Qed.
Lemma get st fr target next next_fr value :
 R.complete_get st fr target = (next,next_fr,value) ->
 Sem.solved st (R.frame_owner fr) -> solved st -> solved next.
Proof.
 intros Hget Howner Hreaders observed reader Hmem.
 assert (Hsolved : Sem.solved st reader).
 { destruct (@get_origin st fr target next next_fr value Hget observed reader Hmem) as [->|Hold];
   [exact Howner |apply Hreaders with observed,Hold]. }
 destruct Hsolved as [stored Hlookup].
 exact (@T.sigma_extends_complete_get st fr target next next_fr value Hget reader stored Hlookup).
Qed.
Lemma set_cases st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) ->
 next = st \/ exists value,next = B.commit_value st (R.frame_owner fr) value.
Proof.
 unfold R.set_value. intro Hset.
 destruct (R.equivalent (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr))).
 - inversion Hset;now left.
 - destruct (if S.mem (R.frame_owner fr) (R.controlled st)
   then U.update false (R.frame_owner fr) (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
     (D.join direct (R.aggregate st (R.frame_owner fr)))
   else (R.frame_phase fr,D.join direct (R.aggregate st (R.frame_owner fr)))) as [phase value].
   cbn in Hset. destruct (R.equivalent value (R.sigma_value st (R.frame_owner fr)));
   inversion Hset;subst;[now left |right;exists value;reflexivity].
Qed.
Lemma set_value st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) -> solved st -> solved next.
Proof.
 intros Hset Hreaders. destruct (@set_cases st fr direct next next_fr Hset) as [->|[value ->]];[exact Hreaders |].
 intros target reader Hmem.
 unfold B.commit_value,R.lookup_set in Hmem. cbn in Hmem.
 destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
 - rewrite ML.lookup_update_same,SL.empty_spec in Hmem. discriminate.
 - rewrite ML.lookup_update_other in Hmem by exact Hneq.
   eapply B.set_value_solved;[exact Hset |apply Hreaders with target,Hmem].
Qed.


Lemma solved_extends before after owner :
 T.sigma_extends before after -> Sem.solved before owner -> Sem.solved after owner.
Proof. intros Hsigma [value Hlookup]. exact (Hsigma owner value Hlookup). Qed.
Lemma base_get tf st fr target next k after :
 T.control_owners_materialized st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 solved st ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> solved (R.cfg_state after).
Proof.
 intros [Howner Htail] Hreaders Hstep.
 assert (Hsolved : Sem.solved (R.observe st target) (R.frame_owner fr)).
 { eapply solved_extends;[apply T.sigma_extends_observe |apply Demand.materialized_solved,Howner]. }
 assert (Hobs : solved (R.observe st target)) by (apply observe,Hreaders).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst;exact Hobs.
 - set (current:=if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. eapply get;[exact Hg | |].
   + subst current. destruct (R.is_materialized (R.observe st target) target);exact Hsolved.
   + subst current. destruct (R.is_materialized (R.observe st target) target);[exact Hobs |apply enqueue,Hobs].
Qed.
Lemma base_spawn tf st fr target next k after :
 solved st ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> solved (R.cfg_state after).
Proof.
 intros Hreaders Hstep. cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst;apply observe,Hreaders.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;[apply observe,Hreaders |].
   apply materialize,enqueue,observe,Hreaders.
Qed.
Lemma base_drain tf st fr k after :
 solved st ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> solved (R.cfg_state after).
Proof.
 intros Hreaders Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hq in Hstep;cbn in Hstep.
 - inversion Hstep;subst;apply reset,Hreaders.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst;apply queue,Hreaders.
   + destruct (R.rank_lt st (R.frame_owner fr) target);
     inversion Hstep;subst;[apply queue,Hreaders |apply reset,Hreaders].
Qed.
Lemma base_return tf st k after :
 T.control_owners_materialized st (R.Return k) -> solved st ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> solved (R.cfg_state after).
Proof.
 intros Hmat Hreaders Hstep. destruct k;cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;exact Hreaders].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. eapply get;[exact Hg | |exact Hreaders].
 apply Demand.materialized_solved. exact (proj1 Hmat).
Qed.
Lemma base_step tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 solved (R.cfg_state before) -> R.next_config tf before = Some after -> solved (R.cfg_state after).
Proof.
 destruct before as [st control]. intros Hside Hdead Hmat Hreaders Hstep. destruct control.
 - cbn -[R.queue_pop] in Hstep.
   destruct (R.queue_pop (R.queue st)) as [[target rest]|];[|discriminate].
   inversion Hstep;subst;apply queue,Hreaders.
 - destruct l as [|root rest];cbn -[R.observe] in Hstep.
   + inversion Hstep;subst;exact Hreaders.
   + destruct (R.is_materialized (R.observe st root) root);
     inversion Hstep;subst;apply observe,Hreaders.
 - cbn -[R.queue_pop] in Hstep.
   destruct (R.queue_pop (R.queue st)) as [[target rest]|];
   inversion Hstep;subst;[apply queue,Hreaders |exact Hreaders].
 - inversion Hstep;subst;apply materialize,Hreaders.
 - destruct r.
   + inversion Hstep;subst;exact Hreaders.
   + eapply base_get;eassumption.
   + contradiction.
   + eapply base_spawn;eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. apply queue. eapply set_value;eassumption.
 - eapply base_drain;eassumption.
 - eapply base_return;eassumption.
Qed.
Lemma precommit_step tf before after :
 not_side (R.cfg_control before) -> nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 solved (R.cfg_state before) -> P.next_config tf before = Some after -> solved (R.cfg_state after).
Proof.
 destruct before as [st control]. intros Hside Hdead Hmat Hreaders Hstep.
 destruct control;cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base_step;eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst;apply queue,Hreaders.
 - eapply base_step;eauto.
Qed.
Lemma batched_step tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 solved (R.cfg_state before) -> P.next_batched tf before = Some after -> solved (R.cfg_state after).
Proof.
 destruct before as [st control]. intros Hdead Hmat Hreaders Hstep.
 destruct control;cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply precommit_step;[ | | | |exact Hstep];[exact I |exact Hdead |exact Hmat |exact Hreaders]].
 - destruct r;
   try solve [eapply precommit_step;[ | | | |exact Hstep];[exact I |exact Hdead |exact Hmat |exact Hreaders]].
   inversion Hstep;subst;apply observe,Hreaders.
 - contradiction.
Qed.
Lemma fresh_step tf before after :
 nonpublication (R.cfg_control before) ->
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 solved (R.cfg_state before) -> P.next_fresh tf before = Some after -> solved (R.cfg_state after).
Proof.
 destruct before as [st control]. intros Hdead Hmat Hreaders Hstep.
 destruct control;cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched_step;eauto].
 - inversion Hstep;subst;apply materialize,queue,Hreaders.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst;apply queue,Hreaders.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst;apply queue,Hreaders.
     * eapply batched_step;eauto.
 - destruct c;cbn -[P.next_batched] in Hstep;
   try solve [eapply batched_step;[ | | |exact Hstep];[exact I |exact Hmat |exact Hreaders]].
   inversion Hstep;subst;apply queue,Hreaders.
Qed.


Lemma requeue before after source target :
 solved after -> solved (C.requeue_source before after source target).
Proof. unfold C.requeue_source. destruct C.cell_changed;[apply enqueue |trivial]. Qed.
Lemma finish before after fr target changed :
 solved after -> solved (C.finish_write before after fr target changed).
Proof. unfold C.finish_write. destruct changed;[intros H;apply enqueue,requeue,H |apply requeue]. Qed.
Lemma publish targets st fr : solved st -> solved (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hreaders;
 cbn -[R.write_side_contribution C.finish_write];[exact Hreaders |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end)) as [next changed] eqn:Hw.
 apply IH,finish. eapply write;eassumption.
Qed.
Lemma continue_dead st fr direct target pending k changed :
 solved st -> solved (R.cfg_state (R.continue_dead st fr direct target pending k changed)).
Proof.
 intro Hreaders. unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];
 cbn;auto using enqueue.
Qed.
Lemma dead_step tf st fr direct pending k after :
 solved st ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}
 = Some after -> solved (R.cfg_state after).
Proof.
 intros Hreaders Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   apply transport with (C.publish (S.elements (R.frame_current_targets fr)) st fr);
   [reflexivity |apply T.sigma_extends_same;reflexivity |apply publish,Hreaders].
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hreaders |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. apply continue_dead,requeue. eapply write;eassumption.
Qed.
Theorem next_solved tf before after :
 T.control_owners_materialized (R.cfg_state before) (R.cfg_control before) ->
 solved (R.cfg_state before) -> N.next_config tf before = Some after -> solved (R.cfg_state after).
Proof.
 intros Hmat Hreaders Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.Readers.next_solved tf before after Hmat Hreaders Hb).
 - apply queue,Hreaders.
Qed.
Lemma steps_solved tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 solved (R.cfg_state first) -> solved (R.cfg_state last).
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hreaders;[exact Hreaders |].
 apply IHHsteps.
 - eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_solved;[exact (reachable_owners_materialized Hreach) |exact Hreaders |exact H].
Qed.
Theorem reachable_solved tf roots c :
 N.steps tf (R.initial_config roots) c -> solved (R.cfg_state c).
Proof.
 intro Hreach. eapply steps_solved;[exact Hreach |constructor |].
 intros target reader Hmem. unfold R.lookup_set in Hmem. cbn in Hmem.
 rewrite ML.lookup_empty,SL.empty_spec in Hmem. discriminate.
Qed.
End Readers.

Module Support.
Definition system support (tf : R.ConstraintSystem.system) :=
 forall owner,B.supported support owner -> B.Sem.rhs_supported (B.supported support) (tf owner).
Lemma clear_state support st owner :
 B.state_supported support st -> B.state_supported support (P.clear_owner st owner).
Proof.
 intro Hstate. apply B.state_supported_with_queue;[exact Hstate |].
 intros target Hin. apply (B.state_queue_supported Hstate).
 exact (proj1 (proj1 (P.clear_owner_members st owner target) Hin)).
Qed.
Lemma clear_config support st ctrl owner :
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=ctrl|} ->
 B.config_supported support {|R.cfg_state:=P.clear_owner st owner;R.cfg_control:=ctrl|}.
Proof. intros [Hs Hc]. split;[apply clear_state,Hs |exact Hc]. Qed.
Lemma suspend support tf st fr direct k target rest :
 system support tf -> P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 B.config_supported support (P.suspend_commit tf st fr k target rest).
Proof.
 intros Htf Hpending [Hs [Hfr Hk]].
 destruct (@P.pending_above_spec st (R.frame_owner fr) target rest Hpending) as [_ [Hpop _]].
 destruct (@B.queue_supported_pop support (R.queue st) target rest (B.state_queue_supported Hs) Hpop) as [Ht Hrest].
 split;[apply B.state_supported_with_queue;assumption |]. split;[exact Ht |].
 split;[apply B.fresh_frame_supported;[exact (proj1 Hfr) |exact Hs] |].
 split;[exact (Htf (R.frame_owner fr) (proj1 Hfr)) |exact Hk].
Qed.
Lemma precommit support tf before after :
 system support tf -> B.config_supported support before ->
 P.next_config tf before = Some after -> B.config_supported support after.
Proof.
 destruct before as [st ctrl]. intros Htf Hsupport Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply B.next_config_supported;eassumption].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply suspend;eassumption.
 - eapply B.next_config_supported;eassumption.
Qed.
Lemma old_publish support targets st fr :
 B.supported support (R.frame_owner fr) -> Forall (B.supported support) targets ->
 B.state_supported support st -> B.state_supported support (P.publish_accumulated targets st fr).
Proof.
 intros Howner Htargets. revert st. induction Htargets;intros st Hstate;
 cbn -[R.write_side_contribution];[exact Hstate |].
 destruct (R.write_side_contribution st fr x
 (match M.lookup (R.frame_local_side fr) x with Some value=>value |None=>D.bottom end)) as [next changed] eqn:Hw.
 apply IHHtargets. assert (Hnext : B.state_supported support next)
 by (eapply B.state_supported_write_side_contribution;eassumption).
 destruct changed;[apply B.state_supported_enqueue;assumption |exact Hnext].
Qed.
Lemma batched support tf before after :
 system support tf -> B.config_supported support before ->
 P.next_batched tf before = Some after -> B.config_supported support after.
Proof.
 destruct before as [st ctrl]. intros Htf Hsupport Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit;eassumption].
 - destruct r;try solve [eapply precommit;eassumption].
   destruct Hsupport as [Hs [Hfr [Hbody Hk]]].
   destruct (B.rhs_supported_side_inv Hbody) as [Ht Hnext]. inversion Hstep;subst.
   split;[apply B.state_supported_observe;assumption |]. split.
   + apply B.frame_supported_with_side;assumption.
   + split;assumption.
 - destruct l;[|eapply precommit;eassumption].
   inversion Hstep;subst. destruct Hsupport as [Hs [Hfr [Hempty Hk]]]. split.
   + apply B.state_supported_publish_targets;[|exact Hfr].
     apply old_publish;[exact (proj1 Hfr) | |exact Hs].
     apply B.set_elements_supported. exact (proj1 (proj2 (proj2 (proj2 Hfr)))).
   + split;assumption.
Qed.
Lemma retry support tf st fr direct k :
 system support tf ->
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 B.config_supported support (P.retry_current tf st fr k).
Proof.
 intros Htf [Hs [Hfr Hk]].
 split;[apply clear_state,Hs |]. split.
 - apply B.fresh_frame_supported;[exact (proj1 Hfr) |apply clear_state,Hs].
 - split;[exact (Htf (R.frame_owner fr) (proj1 Hfr)) |exact Hk].
Qed.
Lemma fresh support tf before after :
 system support tf -> B.config_supported support before ->
 P.next_fresh tf before = Some after -> B.config_supported support after.
Proof.
 destruct before as [st ctrl]. intros Htf Hsupport Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched;eassumption].
 - eapply batched;[ | |exact Hstep];[exact Htf |apply clear_config,Hsupport].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply suspend;eassumption.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. eapply retry;eassumption.
     * eapply batched;eassumption.
 - destruct c;try solve [eapply batched;eassumption].
   eapply batched;[ | |exact Hstep];[exact Htf |apply clear_config,Hsupport].
Qed.
Lemma requeue support before after source target :
 B.supported support source -> B.state_supported support after ->
 B.state_supported support (C.requeue_source before after source target).
Proof.
 intros Hsource Hstate. unfold C.requeue_source. destruct C.cell_changed;
 [apply B.state_supported_enqueue;assumption |exact Hstate].
Qed.
Lemma finish support before after fr target changed :
 B.supported support (R.frame_owner fr) -> B.supported support target ->
 B.state_supported support after -> B.state_supported support (C.finish_write before after fr target changed).
Proof.
 intros Hsource Htarget Hstate. unfold C.finish_write. destruct changed.
 - apply B.state_supported_enqueue;[exact Htarget |apply requeue;assumption].
 - apply requeue;assumption.
Qed.
Lemma publish support targets st fr :
 B.supported support (R.frame_owner fr) -> Forall (B.supported support) targets ->
 B.state_supported support st -> B.state_supported support (C.publish targets st fr).
Proof.
 intros Howner Htargets. revert st. induction Htargets;intros st Hstate;
 cbn -[R.write_side_contribution C.finish_write];[exact Hstate |].
 destruct (R.write_side_contribution st fr x
 (match M.lookup (R.frame_local_side fr) x with Some value=>value |None=>D.bottom end)) as [next changed] eqn:Hw.
 apply IHHtargets,finish;[exact Howner |exact H |].
 eapply B.state_supported_write_side_contribution;eassumption.
Qed.
Lemma continue_dead support st fr direct target rest k changed :
 B.supported support target ->
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct rest k|} ->
 B.config_supported support (R.continue_dead st fr direct target rest k changed).
Proof.
 intros Htarget [Hs [Hfr [Hrest Hk]]]. unfold R.continue_dead.
 destruct changed;[destruct (_ && _)%bool |].
 - split;[exact Hs |]. split;[exact Htarget |]. split;[exact Hfr |]. split;assumption.
 - split;[apply B.state_supported_enqueue;assumption |]. split;[exact Hfr |]. split;assumption.
 - split;[exact Hs |]. split;[exact Hfr |]. split;assumption.
Qed.
Lemma dead support tf st fr direct pending k after :
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} = Some after ->
 B.config_supported support after.
Proof.
 intros [Hs [Hfr [Hpending Hk]]] Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst. split.
   + apply B.state_supported_publish_targets;[|exact Hfr].
     apply publish;[exact (proj1 Hfr) | |exact Hs].
     apply B.set_elements_supported. exact (proj1 (proj2 (proj2 (proj2 Hfr)))).
   + split;assumption.
 - inversion Hpending;subst.
   cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));
   [inversion Hstep;subst;split;[exact Hs |];split;[exact Hfr |];now split |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. apply continue_dead;[assumption |]. split.
   + apply requeue;[exact (proj1 Hfr) |]. eapply B.state_supported_write_side_contribution;eassumption.
   + split;[exact Hfr |]. split;assumption.
Qed.
Theorem next support tf before after :
 system support tf -> B.config_supported support before ->
 N.next_config tf before = Some after -> B.config_supported support after.
Proof.
 intros Htf Hsupport Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.Support.next support tf before after Htf Hsupport Hb).
 - eapply (@suspend support tf st fr D.bottom k target rest);[exact Htf |exact Hp |].
   destruct Hsupport as [Hs [Hfr [Hbody Hk]]]. split;[exact Hs |]. now split.
Qed.
Lemma steps support tf first last :
 N.steps tf first last -> system support tf ->
 B.config_supported support first -> B.config_supported support last.
Proof.
 intro Hsteps. induction Hsteps;intros Htf Hsupport;[exact Hsupport |].
 apply IHHsteps;[exact Htf |eapply next;eassumption].
Qed.
Theorem reachable tf roots (finite : B.Sem.finite_system tf roots) c :
 N.steps tf (R.initial_config roots) c -> B.config_supported (B.Sem.support finite) c.
Proof.
 intro Hreach. eapply steps;[exact Hreach | |apply B.initial_config_supported].
 intros owner Hin. apply B.Sem.system_supported,Hin.
Qed.

Lemma rhs_supported_bridge supported body :
 Sem.rhs_supported supported body -> B.Sem.rhs_supported supported body.
Proof. intro Hbody. induction Hbody;constructor;assumption. Qed.
Definition finite_bridge tf roots (finite : Sem.finite_system tf roots) :
 B.Sem.finite_system tf roots.
Proof.
 refine (@B.Sem.Build_finite_system tf roots (@Sem.support tf roots finite)
   (@Sem.support_nodup tf roots finite) (@Sem.initial_supported tf roots finite) _).
 intros owner Hin. apply rhs_supported_bridge. exact (@Sem.system_supported tf roots finite owner Hin).
Defined.
Theorem reachable_supported tf roots (finite : Sem.finite_system tf roots) c :
 N.steps tf (R.initial_config roots) c -> B.config_supported (@Sem.support tf roots finite) c.
Proof. intro Hreach. exact (@reachable tf roots (@finite_bridge tf roots finite) c Hreach). Qed.
End Support.

(** Credits are counted for a source while its episode remains on the stack.
    A higher episode may reset its own cells, but cannot refill this account. *)
Module SourceCredit.
Definition credit := B.Credits.source_side_credit.

Lemma clear support st owner source :
 credit support (P.clear_owner st owner) source = credit support st source.
Proof. apply T.source_credit_ext;reflexivity. Qed.
Lemma requeue support before after owner target source :
 credit support (C.requeue_source before after owner target) source = credit support after source.
Proof. unfold C.requeue_source. destruct C.cell_changed;
 [apply T.source_credit_enqueue |reflexivity]. Qed.
Lemma finish support before after fr target changed source :
 credit support (C.finish_write before after fr target changed) source = credit support after source.
Proof. apply C.finish_credit. Qed.
Lemma publish support targets st fr source :
 credit support (C.publish targets st fr) source <= credit support st source.
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[lia |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply Nat.le_trans;[apply IH |]. rewrite finish. eapply T.source_credit_write;exact Hw.
Qed.
Lemma continue_dead support st fr direct target pending k changed source :
 credit support (R.cfg_state (R.continue_dead st fr direct target pending k changed)) source =
 credit support st source.
Proof.
 unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];cbn;
 [reflexivity |apply T.source_credit_enqueue |reflexivity].
Qed.
Lemma continue_side support st fr target body k changed source :
 credit support (R.cfg_state (R.continue_side st fr target body k changed)) source =
 credit support st source.
Proof.
 unfold R.continue_side. destruct changed;[destruct (_ && _)%bool |];cbn;
 [reflexivity |apply T.source_credit_enqueue |reflexivity].
Qed.
Lemma base_get support tf st fr target body k after source :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}
 = Some after -> credit support (R.cfg_state after) source = credit support st source.
Proof.
 intro Hstep. cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 set (observed:=R.observe st target) in *.
 destruct (negb (R.is_materialized observed target) && R.rank_lt observed (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. apply T.source_credit_observe.
 - set (base:=if R.is_materialized observed target then observed else R.enqueue observed target) in *.
   destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hg.
   inversion Hstep;subst. cbn -[credit]. unfold credit.
   rewrite (@T.source_credit_complete_get support base fr target next next_fr value source Hg).
   subst base. destruct (R.is_materialized observed target);
   [apply T.source_credit_observe |].
   rewrite T.source_credit_enqueue. apply T.source_credit_observe.
Qed.
Lemma base_rhs support tf st fr body k after source :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=Some after ->
 credit support (R.cfg_state after) source <= credit support st source.
Proof.
 intro Hstep. destruct body as [direct|target body|target raw body|target body].
 - inversion Hstep;subst;apply Nat.le_refl.
 - rewrite (@base_get support tf st fr target body k after source Hstep). lia.
 - cbn -[R.observe R.record_side_input R.write_side_contribution R.continue_side] in Hstep.
   destruct (R.record_side_input fr target raw) as [next_fr input] eqn:Hr.
   destruct (R.write_side_contribution (R.observe st target) next_fr target input) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_side.
   pose proof (@T.source_credit_write support source _ _ _ _ _ _ Hw) as Hcredit.
   rewrite T.source_credit_observe in Hcredit. exact Hcredit.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st target) target);
   [inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_observe;lia |].
   destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;cbn -[credit];unfold credit;
   repeat rewrite T.source_credit_materialize;
   repeat rewrite T.source_credit_enqueue;rewrite T.source_credit_observe;lia.
Qed.
Lemma base_dead support tf st fr direct pending k after source :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 credit support (R.cfg_state after) source <= credit support st source.
Proof.
 intro Hstep. destruct pending as [|target rest].
 - inversion Hstep;subst;cbn -[credit];unfold credit.
   rewrite T.source_credit_publish_targets. lia.
 - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply Nat.le_refl |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_dead. eapply T.source_credit_write;exact Hw.
Qed.
Lemma reset support st owner k source :
 B.ScopeBounds.reset_sources_bounded st -> T.continuation_below st owner k ->
 T.continuation_contains source k ->
 credit support (R.reset_registered_cells st owner) source = credit support st source.
Proof.
 intros Hreset Hbelow Hcontains. apply B.reset_above_preserves_source_credit;[exact Hreset |].
 eapply T.continuation_contains_below;eassumption.
Qed.
Lemma base_drain support tf st fr k after source :
 B.ScopeBounds.reset_sources_bounded st -> T.control_ordered st (R.RunDrain fr k) ->
 T.control_contains source (R.cfg_control after) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=Some after ->
 credit support (R.cfg_state after) source = credit support st source.
Proof.
 intros Hreset Hordered Hcontains Hstep.
 destruct (R.queue st) as [|target rest] eqn:Hqueue;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hqueue in Hstep;cbn in Hstep.
 - inversion Hstep;subst. eapply reset;eassumption.
 - destruct (V.eq_dec target (R.frame_owner fr)).
   + inversion Hstep;subst. apply T.source_credit_with_queue.
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. apply T.source_credit_with_queue.
     * inversion Hstep;subst. eapply reset;eassumption.
Qed.

Lemma base_return support tf st k after source :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}=Some after ->
 credit support (R.cfg_state after) source = credit support st source.
Proof.
 intro Hstep. destruct k;cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;reflexivity].
 destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hg.
 inversion Hstep;subst. eapply T.source_credit_complete_get;exact Hg.
Qed.
Lemma base support tf before after source :
 B.ScopeBounds.reset_sources_bounded (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains source (R.cfg_control after) ->
 R.next_config tf before=Some after ->
 credit support (R.cfg_state after) source <= credit support (R.cfg_state before) source.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep. destruct ctrl.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];[|discriminate].
   inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_with_queue;lia.
 - destruct l;cbn -[R.observe] in Hstep;
   try destruct (R.is_materialized (R.observe st t) t);
   inversion Hstep;subst;cbn -[credit];unfold credit;
   try rewrite T.source_credit_observe;lia.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
   inversion Hstep;subst;cbn -[credit];unfold credit;
   try rewrite T.source_credit_with_queue;lia.
 - inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_materialize;lia.
 - eapply base_rhs;exact Hstep.
 - eapply base_dead;exact Hstep.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst;cbn -[credit R.requeue_changed_controlled_owner].
   unfold R.requeue_changed_controlled_owner,credit. rewrite T.source_credit_with_queue.
   rewrite (@T.source_credit_set_value support st f t next next_fr source Hs). lia.
 - rewrite (@base_drain support tf st f c after source Hr Ho Ha Hstep). apply Nat.le_refl.
 - rewrite (@base_return support tf st c after source Hstep). apply Nat.le_refl.
Qed.
Lemma precommit support tf before after source :
 B.ScopeBounds.reset_sources_bounded (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains source (R.cfg_control after) ->
 P.next_config tf before=Some after ->
 credit support (R.cfg_state after) source <= credit support (R.cfg_state before) source.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) source <= credit support st source). destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [exact (@base support tf _ after source Hr Ho Ha Hstep)].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_with_queue;lia.
 - exact (@base support tf _ after source Hr Ho Ha Hstep).
Qed.
Lemma old_publish support targets st fr source :
 credit support (P.publish_accumulated targets st fr) source <= credit support st source.
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution];[lia |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply Nat.le_trans;[apply IH |]. unfold credit.
 destruct changed;[rewrite T.source_credit_enqueue |];eapply T.source_credit_write;exact Hw.
Qed.
Lemma batched support tf before after source :
 B.ScopeBounds.reset_sources_bounded (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains source (R.cfg_control after) ->
 P.next_batched tf before=Some after ->
 credit support (R.cfg_state after) source <= credit support (R.cfg_state before) source.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) source <= credit support st source). destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [exact (@precommit support tf _ after source Hr Ho Ha Hstep)].
 - destruct r;try solve [exact (@precommit support tf _ after source Hr Ho Ha Hstep)].
   inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_observe;lia.
 - destruct l;[|exact (@precommit support tf _ after source Hr Ho Ha Hstep)].
   inversion Hstep;subst;cbn -[credit];unfold credit.
   rewrite T.source_credit_publish_targets. apply old_publish.
Qed.
Lemma fresh support tf before after source :
 B.ScopeBounds.reset_sources_bounded (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains source (R.cfg_control after) ->
 P.next_fresh tf before=Some after ->
 credit support (R.cfg_state after) source <= credit support (R.cfg_state before) source.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) source <= credit support st source). destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [exact (@batched support tf _ after source Hr Ho Ha Hstep)].
 - rewrite <- (@clear support st t source). eapply (@batched support tf {|R.cfg_state:=P.clear_owner st t;R.cfg_control:=R.StartEpisode t c|} after source);[ | |exact Ha |exact Hstep].
   + apply B.ScopeBounds.reset_sources_bounded_with_queue;exact Hr.
   + eapply ordered_extended;[apply B.rank_extends_with_queue |exact Ho].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.source_credit_with_queue;lia.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst;cbn -[credit P.clear_owner];rewrite clear;lia.
     * exact (@batched support tf _ after source Hr Ho Ha Hstep).
 - destruct c;try solve [exact (@batched support tf _ after source Hr Ho Ha Hstep)].
   rewrite <- (@clear support st (R.frame_owner f) source).
   eapply (@batched support tf {|R.cfg_state:=P.clear_owner st (R.frame_owner f);R.cfg_control:=R.Return (R.KAfterSide f r c)|} after source);[ | |exact Ha |exact Hstep].
   + apply B.ScopeBounds.reset_sources_bounded_with_queue;exact Hr.
   + eapply ordered_extended;[apply B.rank_extends_with_queue |exact Ho].
Qed.
Lemma dead support tf st fr direct pending k after source :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 credit support (R.cfg_state after) source <= credit support st source.
Proof.
 intro Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst;cbn -[credit].
   unfold credit. rewrite T.source_credit_publish_targets. apply publish.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply Nat.le_refl |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_dead,requeue. eapply T.source_credit_write;exact Hw.
Qed.
Theorem step_nonincreasing support tf roots before after source :
 N.steps tf (R.initial_config roots) before ->
 T.control_contains source (R.cfg_control after) ->
 N.next_config tf before=Some after ->
 credit support (R.cfg_state after) source <= credit support (R.cfg_state before) source.
Proof.
 intros Hreach Ha Hstep.
 pose proof (proj1 (N.reachable_scopes Hreach)) as Hr.
 pose proof (proj1 (reachable_history Hreach)) as Ho.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { change (credit support (R.with_queue st rest) source <= credit support st source). unfold credit. rewrite T.source_credit_with_queue. lia. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;try solve [exact (@fresh support tf _ after source Hr Ho Ha Hstep)].
 eapply dead;exact Hstep.
Qed.

Lemma publication_strict support tf roots st fr direct k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 B.config_supported support {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|}=Some after ->
 C.publication_changes (S.elements (R.frame_current_targets fr)) st fr ->
 credit support (R.cfg_state after) (R.frame_owner fr) < credit support st (R.frame_owner fr).
Proof.
 intros Hreach [_ [Hfr _]] Hstep Hchanged.
 cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst;cbn -[credit].
 unfold credit. rewrite T.source_credit_publish_targets.
 apply C.changed_publication_consumes_credit;[ |exact Hchanged].
 intros target Hin. pose proof (B.set_elements_supported
 (proj1 (proj2 (proj2 (proj2 Hfr))))) as Htargets.
 exact (proj1 (Forall_forall _ _) Htargets target Hin).
Qed.
Lemma dead_strict support tf st fr direct target rest k after next changed :
 List.In target support ->
 S.mem target (R.frame_current_targets fr)=false ->
 R.write_side_contribution st fr target D.bottom=(next,changed) ->
 C.cell_changed st next (R.frame_owner fr) target=true ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=Some after ->
 credit support (R.cfg_state after) (R.frame_owner fr) < credit support st (R.frame_owner fr).
Proof.
 intros Hin Hdead Hw Hchange Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 rewrite Hdead,Hw in Hstep. inversion Hstep;subst. rewrite continue_dead,requeue.
 eapply C.changed_source_consumes_credit;eassumption.
Qed.
Theorem reachable_publication_strict tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|}=Some after ->
 C.publication_changes (S.elements (R.frame_current_targets fr)) st fr ->
 credit (B.Sem.support finite) (R.cfg_state after) (R.frame_owner fr) <
 credit (B.Sem.support finite) st (R.frame_owner fr).
Proof.
 intros Hreach Hstep Hchange. eapply publication_strict;[exact Hreach | |exact Hstep |exact Hchange].
 exact (Support.reachable finite Hreach).
Qed.
Theorem reachable_dead_strict tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct target rest k after next changed :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 S.mem target (R.frame_current_targets fr)=false ->
 R.write_side_contribution st fr target D.bottom=(next,changed) ->
 C.cell_changed st next (R.frame_owner fr) target=true ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=Some after ->
 credit (B.Sem.support finite) (R.cfg_state after) (R.frame_owner fr) <
 credit (B.Sem.support finite) st (R.frame_owner fr).
Proof.
 intros Hreach Hdead Hw Hchange Hstep. eapply dead_strict;[ |exact Hdead |exact Hw |exact Hchange |exact Hstep].
 destruct (Support.reachable finite Hreach) as [_ [_ [Htargets _]]].
 inversion Htargets;assumption.
Qed.

(** The charge is executable and comes from the update account itself. *)
Definition charge support source before after : nat :=
 if Nat.ltb (credit support (R.cfg_state after) source)
   (credit support (R.cfg_state before) source) then 1 else 0.
Lemma charge_bound support tf roots source before after :
 N.steps tf (R.initial_config roots) before ->
 T.control_contains source (R.cfg_control after) ->
 N.next_config tf before=Some after ->
 charge support source before after + credit support (R.cfg_state after) source <=
 credit support (R.cfg_state before) source.
Proof.
 intros Hreach Hactive Hstep.
 pose proof (@step_nonincreasing support tf roots before after source Hreach Hactive Hstep) as Hle.
 unfold charge. destruct (Nat.ltb _ _) eqn:Hlt;[apply Nat.ltb_lt in Hlt |];lia.
Qed.
Lemma charge_strict support source before after :
 credit support (R.cfg_state after) source < credit support (R.cfg_state before) source ->
 charge support source before after=1.
Proof. intro Hlt. unfold charge. apply Nat.ltb_lt in Hlt. now rewrite Hlt. Qed.

Inductive active_steps support tf source : R.config -> R.config -> nat -> Prop :=
| active_refl : forall c, active_steps support tf source c c 0
| active_next : forall first next last count,
    N.next_config tf first=Some next ->
    T.control_contains source (R.cfg_control next) ->
    active_steps support tf source next last count ->
    active_steps support tf source first last (charge support source first next + count).
Lemma active_execution support tf source first last count :
 active_steps support tf source first last count -> N.steps tf first last.
Proof. intro Hsteps. induction Hsteps;[constructor |econstructor;eassumption]. Qed.
Theorem active_bound support tf roots source first last count :
 active_steps support tf source first last count ->
 N.steps tf (R.initial_config roots) first ->
 count + credit support (R.cfg_state last) source <= credit support (R.cfg_state first) source.
Proof.
 intro Hsteps. induction Hsteps;intro Hreach;[lia |].
 assert (Hnext : N.steps tf (R.initial_config roots) next).
 { eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor]. }
 specialize (IHHsteps Hnext).
 pose proof (@charge_bound support tf roots source first next Hreach H0 H) as Hpaid. lia.
Qed.
Corollary active_changes_bounded support tf roots source first last count :
 active_steps support tf source first last count ->
 N.steps tf (R.initial_config roots) first ->
 count <= credit support (R.cfg_state first) source.
Proof. intros Hsteps Hreach. pose proof (active_bound Hsteps Hreach). lia. Qed.

Fixpoint active_run fuel support tf source c : R.config * nat :=
 match fuel with
 | 0 => (c,0)
 | S rest =>
   match N.next_config tf c with
   | None => (c,0)
   | Some next =>
     if T.control_containsb source (R.cfg_control next) then
       let '(last,count) := active_run rest support tf source next in
       (last,charge support source c next + count)
     else (c,0)
   end
 end.
Lemma active_run_execution fuel support tf source c :
 active_steps support tf source c
   (fst (active_run fuel support tf source c))
   (snd (active_run fuel support tf source c)).
Proof.
 revert c. induction fuel as [|fuel IH];intro c;cbn;[constructor |].
 destruct (N.next_config tf c) as [next|] eqn:Hstep;[|constructor].
 destruct (T.control_containsb source (R.cfg_control next)) eqn:Hactive;[|constructor].
 specialize (IH next). destruct (active_run fuel support tf source next) as [last count];cbn in *.
 econstructor;[exact Hstep |apply T.control_containsb_spec,Hactive |exact IH].
Qed.
Theorem active_run_bound fuel support tf roots source c :
 N.steps tf (R.initial_config roots) c ->
 snd (active_run fuel support tf source c) <= credit support (R.cfg_state c) source.
Proof.
 intro Hreach. eapply active_changes_bounded;[apply active_run_execution |exact Hreach].
Qed.

End SourceCredit.

Module RankedResets.
Lemma queue st next_queue : B.state_resets_ranked st ->
 B.state_resets_ranked (R.with_queue st next_queue).
Proof. intro H. eapply B.state_resets_ranked_view;[apply B.rank_extends_with_queue |reflexivity |exact H]. Qed.
Lemma clear st owner : B.state_resets_ranked st -> B.state_resets_ranked (P.clear_owner st owner).
Proof. apply queue. Qed.
Lemma precommit tf before after :
 B.state_resets_ranked (R.cfg_state before) -> P.next_config tf before=Some after ->
 B.state_resets_ranked (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hr Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply B.next_config_resets_ranked;eassumption].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. apply queue,Hr.
 - eapply B.next_config_resets_ranked;eassumption.
Qed.
Lemma publish_targets st fr : B.state_resets_ranked st ->
 B.state_resets_ranked (R.publish_targets st fr).
Proof.
 intro Hr. eapply B.state_resets_ranked_view;[apply B.rank_extends_with_last_targets |reflexivity |exact Hr].
Qed.
Lemma old_publish targets st fr :
 B.state_resets_ranked st -> B.state_resets_ranked (P.publish_accumulated targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hr;
 cbn -[R.write_side_contribution];[exact Hr |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH. assert (Hnext : B.state_resets_ranked next)
 by (eapply B.state_resets_ranked_write_side_contribution;eassumption).
 destruct changed;[apply B.state_resets_ranked_enqueue,Hnext |exact Hnext].
Qed.
Lemma batched tf before after :
 B.state_resets_ranked (R.cfg_state before) -> P.next_batched tf before=Some after ->
 B.state_resets_ranked (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hr Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit;eassumption].
 - destruct r;try solve [eapply precommit;eassumption].
   inversion Hstep;subst. apply B.state_resets_ranked_observe,Hr.
 - destruct l;[|eapply precommit;eassumption].
   inversion Hstep;subst. apply publish_targets,old_publish,Hr.
Qed.
Lemma fresh tf before after :
 B.state_resets_ranked (R.cfg_state before) -> P.next_fresh tf before=Some after ->
 B.state_resets_ranked (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hr Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched;eassumption].
 - eapply batched;[ |exact Hstep]. apply clear,Hr.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. apply queue,Hr.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply clear,Hr.
     * eapply batched;eassumption.
 - destruct c;try solve [eapply batched;eassumption].
   eapply batched;[ |exact Hstep]. apply clear,Hr.
Qed.
Lemma requeue before after source target :
 B.state_resets_ranked after ->
 B.state_resets_ranked (C.requeue_source before after source target).
Proof.
 intro Hr. unfold C.requeue_source. destruct C.cell_changed;
 [apply B.state_resets_ranked_enqueue,Hr |exact Hr].
Qed.
Lemma finish before after fr target changed :
 B.state_resets_ranked after ->
 B.state_resets_ranked (C.finish_write before after fr target changed).
Proof.
 intro Hr. unfold C.finish_write. destruct changed;
 [apply B.state_resets_ranked_enqueue,requeue,Hr |apply requeue,Hr].
Qed.
Lemma publish targets st fr : B.state_resets_ranked st -> B.state_resets_ranked (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hr;
 cbn -[R.write_side_contribution C.finish_write];[exact Hr |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH,finish. eapply B.state_resets_ranked_write_side_contribution;eassumption.
Qed.
Lemma dead tf st fr direct pending k after :
 B.state_resets_ranked st ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 B.state_resets_ranked (R.cfg_state after).
Proof.
 intros Hr Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   apply publish_targets,publish,Hr.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hr |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. apply B.state_resets_ranked_continue_dead,requeue.
   eapply B.state_resets_ranked_write_side_contribution;eassumption.
Qed.
Theorem next tf before after :
 B.state_resets_ranked (R.cfg_state before) -> N.next_config tf before=Some after ->
 B.state_resets_ranked (R.cfg_state after).
Proof.
 intros Hr Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.RankedResets.next tf before after Hr Hb0).
 - exact Hr.
Qed.
Lemma steps tf first last : N.steps tf first last ->
 B.state_resets_ranked (R.cfg_state first) -> B.state_resets_ranked (R.cfg_state last).
Proof.
 intro Hsteps. induction Hsteps;intro Hr;[exact Hr |].
 apply IHHsteps. eapply next;eassumption.
Qed.
Theorem reachable tf roots c : N.steps tf (R.initial_config roots) c ->
 B.state_resets_ranked (R.cfg_state c).
Proof. intro Hreach. eapply steps;[exact Hreach |apply B.empty_state_resets_ranked]. Qed.
End RankedResets.

(** Incoming credit survives higher-episode resets and pays for aggregate
    changes that invalidate the suspended owner. *)
Module TargetCredit.
Definition credit := T.target_side_credit.
Lemma write support root st fr target input next changed :
 R.write_side_contribution st fr target input=(next,changed) ->
 credit support next root <= credit support st root.
Proof.
 intro Hw. destruct (V.eq_dec root target) as [->|Hneq].
 - eapply T.target_side_credit_write_nonincreasing;exact Hw.
 - unfold credit. rewrite (@T.target_side_credit_write_other_target support st fr target input next changed root Hw Hneq).
   lia.
Qed.

Lemma clear support st owner root :
 credit support (P.clear_owner st owner) root = credit support st root.
Proof. apply T.target_side_credit_ext;reflexivity. Qed.
Lemma requeue support before after owner target root :
 credit support (C.requeue_source before after owner target) root = credit support after root.
Proof. unfold C.requeue_source. destruct C.cell_changed;
 [apply T.target_credit_enqueue |reflexivity]. Qed.
Lemma finish support before after fr target changed root :
 credit support (C.finish_write before after fr target changed) root = credit support after root.
Proof.
 unfold C.finish_write. destruct changed;
 [unfold credit;rewrite T.target_credit_enqueue;apply requeue |apply requeue].
Qed.
Lemma publish support targets st fr root :
 credit support (C.publish targets st fr) root <= credit support st root.
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[lia |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply Nat.le_trans;[apply IH |]. rewrite finish. eapply write;exact Hw.
Qed.
Lemma continue_dead support st fr direct target pending k changed root :
 credit support (R.cfg_state (R.continue_dead st fr direct target pending k changed)) root =
 credit support st root.
Proof.
 unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];cbn;
 [reflexivity |apply T.target_credit_enqueue |reflexivity].
Qed.
Lemma continue_side support st fr target body k changed root :
 credit support (R.cfg_state (R.continue_side st fr target body k changed)) root =
 credit support st root.
Proof.
 unfold R.continue_side. destruct changed;[destruct (_ && _)%bool |];cbn;
 [reflexivity |apply T.target_credit_enqueue |reflexivity].
Qed.
Lemma base_get support tf st fr target body k after root :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}
 = Some after -> credit support (R.cfg_state after) root = credit support st root.
Proof.
 intro Hstep. cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 set (observed:=R.observe st target) in *.
 destruct (negb (R.is_materialized observed target) && R.rank_lt observed (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. apply T.target_credit_observe.
 - set (base:=if R.is_materialized observed target then observed else R.enqueue observed target) in *.
   destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hg.
   inversion Hstep;subst. cbn -[credit]. unfold credit.
   rewrite (@T.target_credit_complete_get support base fr target next next_fr value root Hg).
   subst base. destruct (R.is_materialized observed target);
   [apply T.target_credit_observe |].
   rewrite T.target_credit_enqueue. apply T.target_credit_observe.
Qed.
Lemma base_rhs support tf st fr body k after root :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=Some after ->
 credit support (R.cfg_state after) root <= credit support st root.
Proof.
 intro Hstep. destruct body as [direct|target body|target raw body|target body].
 - inversion Hstep;subst;apply Nat.le_refl.
 - rewrite (@base_get support tf st fr target body k after root Hstep). lia.
 - cbn -[R.observe R.record_side_input R.write_side_contribution R.continue_side] in Hstep.
   destruct (R.record_side_input fr target raw) as [next_fr input] eqn:Hr.
   destruct (R.write_side_contribution (R.observe st target) next_fr target input) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_side.
   pose proof (@write support root _ _ _ _ _ _ Hw) as Hcredit.
   rewrite T.target_credit_observe in Hcredit. exact Hcredit.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st target) target);
   [inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_observe;lia |].
   destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;cbn -[credit];unfold credit;
   repeat rewrite T.target_credit_materialize;
   repeat rewrite T.target_credit_enqueue;rewrite T.target_credit_observe;lia.
Qed.
Lemma base_dead support tf st fr direct pending k after root :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 credit support (R.cfg_state after) root <= credit support st root.
Proof.
 intro Hstep. destruct pending as [|target rest].
 - inversion Hstep;subst;cbn -[credit];unfold credit.
   rewrite T.target_credit_publish_targets. lia.
 - cbn -[R.write_side_contribution R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply Nat.le_refl |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_dead. eapply write;exact Hw.
Qed.
Lemma reset support st owner k root :
 B.state_resets_ranked st -> T.continuation_below st owner k ->
 T.continuation_contains root k ->
 credit support (R.reset_registered_cells st owner) root = credit support st root.
Proof.
 intros Hreset Hbelow Hcontains. apply T.reset_above_preserves_target_credit;[exact Hreset |].
 eapply T.continuation_contains_below;eassumption.
Qed.
Lemma base_drain support tf st fr k after root :
 B.state_resets_ranked st -> T.control_ordered st (R.RunDrain fr k) ->
 T.control_contains root (R.cfg_control after) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=Some after ->
 credit support (R.cfg_state after) root = credit support st root.
Proof.
 intros Hreset Hordered Hcontains Hstep.
 destruct (R.queue st) as [|target rest] eqn:Hqueue;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep;rewrite Hqueue in Hstep;cbn in Hstep.
 - inversion Hstep;subst. eapply reset;eassumption.
 - destruct (V.eq_dec target (R.frame_owner fr)).
   + inversion Hstep;subst. apply T.target_credit_with_queue.
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. apply T.target_credit_with_queue.
     * inversion Hstep;subst. eapply reset;eassumption.
Qed.

Lemma base_return support tf st k after root :
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}=Some after ->
 credit support (R.cfg_state after) root = credit support st root.
Proof.
 intro Hstep. destruct k;cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;reflexivity].
 destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hg.
 inversion Hstep;subst. eapply T.target_credit_complete_get;exact Hg.
Qed.
Lemma base support tf before after root :
 B.state_resets_ranked (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains root (R.cfg_control after) ->
 R.next_config tf before=Some after ->
 credit support (R.cfg_state after) root <= credit support (R.cfg_state before) root.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep. destruct ctrl.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];[|discriminate].
   inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_with_queue;lia.
 - destruct l;cbn -[R.observe] in Hstep;
   try destruct (R.is_materialized (R.observe st t) t);
   inversion Hstep;subst;cbn -[credit];unfold credit;
   try rewrite T.target_credit_observe;lia.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
   inversion Hstep;subst;cbn -[credit];unfold credit;
   try rewrite T.target_credit_with_queue;lia.
 - inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_materialize;lia.
 - eapply base_rhs;exact Hstep.
 - eapply base_dead;exact Hstep.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst;cbn -[credit R.requeue_changed_controlled_owner].
   unfold R.requeue_changed_controlled_owner,credit. rewrite T.target_credit_with_queue.
   rewrite (@T.target_credit_set_value support st f t next next_fr root Hs). lia.
 - rewrite (@base_drain support tf st f c after root Hr Ho Ha Hstep). apply Nat.le_refl.
 - rewrite (@base_return support tf st c after root Hstep). apply Nat.le_refl.
Qed.
Lemma precommit support tf before after root :
 B.state_resets_ranked (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains root (R.cfg_control after) ->
 P.next_config tf before=Some after ->
 credit support (R.cfg_state after) root <= credit support (R.cfg_state before) root.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) root <= credit support st root). destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [exact (@base support tf _ after root Hr Ho Ha Hstep)].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_with_queue;lia.
 - exact (@base support tf _ after root Hr Ho Ha Hstep).
Qed.
Lemma old_publish support targets st fr root :
 credit support (P.publish_accumulated targets st fr) root <= credit support st root.
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution];[lia |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply Nat.le_trans;[apply IH |]. unfold credit.
 destruct changed;[rewrite T.target_credit_enqueue |];eapply write;exact Hw.
Qed.
Lemma batched support tf before after root :
 B.state_resets_ranked (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains root (R.cfg_control after) ->
 P.next_batched tf before=Some after ->
 credit support (R.cfg_state after) root <= credit support (R.cfg_state before) root.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) root <= credit support st root). destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [exact (@precommit support tf _ after root Hr Ho Ha Hstep)].
 - destruct r;try solve [exact (@precommit support tf _ after root Hr Ho Ha Hstep)].
   inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_observe;lia.
 - destruct l;[|exact (@precommit support tf _ after root Hr Ho Ha Hstep)].
   inversion Hstep;subst;cbn -[credit];unfold credit.
   rewrite T.target_credit_publish_targets. apply old_publish.
Qed.
Lemma fresh support tf before after root :
 B.state_resets_ranked (R.cfg_state before) ->
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 T.control_contains root (R.cfg_control after) ->
 P.next_fresh tf before=Some after ->
 credit support (R.cfg_state after) root <= credit support (R.cfg_state before) root.
Proof.
 destruct before as [st ctrl]. intros Hr Ho Ha Hstep.
 change (credit support (R.cfg_state after) root <= credit support st root). destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [exact (@batched support tf _ after root Hr Ho Ha Hstep)].
 - rewrite <- (@clear support st t root). eapply (@batched support tf {|R.cfg_state:=P.clear_owner st t;R.cfg_control:=R.StartEpisode t c|} after root);[ | |exact Ha |exact Hstep].
   + apply RankedResets.queue;exact Hr.
   + eapply ordered_extended;[apply B.rank_extends_with_queue |exact Ho].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst;cbn -[credit];unfold credit;rewrite T.target_credit_with_queue;lia.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst;cbn -[credit P.clear_owner];rewrite clear;lia.
     * exact (@batched support tf _ after root Hr Ho Ha Hstep).
 - destruct c;try solve [exact (@batched support tf _ after root Hr Ho Ha Hstep)].
   rewrite <- (@clear support st (R.frame_owner f) root).
   eapply (@batched support tf {|R.cfg_state:=P.clear_owner st (R.frame_owner f);R.cfg_control:=R.Return (R.KAfterSide f r c)|} after root);[ | |exact Ha |exact Hstep].
   + apply RankedResets.queue;exact Hr.
   + eapply ordered_extended;[apply B.rank_extends_with_queue |exact Ho].
Qed.
Lemma dead support tf st fr direct pending k after root :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 credit support (R.cfg_state after) root <= credit support st root.
Proof.
 intro Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst;cbn -[credit].
   unfold credit. rewrite T.target_credit_publish_targets. apply publish.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply Nat.le_refl |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_dead,requeue. eapply write;exact Hw.
Qed.
Theorem step_nonincreasing support tf roots before after root :
 N.steps tf (R.initial_config roots) before ->
 T.control_contains root (R.cfg_control after) ->
 N.next_config tf before=Some after ->
 credit support (R.cfg_state after) root <= credit support (R.cfg_state before) root.
Proof.
 intros Hreach Ha Hstep.
 pose proof (RankedResets.reachable Hreach) as Hr.
 pose proof (proj1 (reachable_history Hreach)) as Ho.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { change (credit support (R.with_queue st rest) root <= credit support st root). unfold credit. rewrite T.target_credit_with_queue. lia. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;try solve [exact (@fresh support tf _ after root Hr Ho Ha Hstep)].
 eapply dead;exact Hstep.
Qed.

(** The charge is executable and comes from the update account itself. *)
Definition charge support root before after : nat :=
 if Nat.ltb (credit support (R.cfg_state after) root)
   (credit support (R.cfg_state before) root) then 1 else 0.
Lemma charge_bound support tf roots root before after :
 N.steps tf (R.initial_config roots) before ->
 T.control_contains root (R.cfg_control after) ->
 N.next_config tf before=Some after ->
 charge support root before after + credit support (R.cfg_state after) root <=
 credit support (R.cfg_state before) root.
Proof.
 intros Hreach Hactive Hstep.
 pose proof (@step_nonincreasing support tf roots before after root Hreach Hactive Hstep) as Hle.
 unfold charge. destruct (Nat.ltb _ _) eqn:Hlt;[apply Nat.ltb_lt in Hlt |];lia.
Qed.
Lemma charge_strict support root before after :
 credit support (R.cfg_state after) root < credit support (R.cfg_state before) root ->
 charge support root before after=1.
Proof. intro Hlt. unfold charge. apply Nat.ltb_lt in Hlt. now rewrite Hlt. Qed.

Inductive active_steps support tf root : R.config -> R.config -> nat -> Prop :=
| active_refl : forall c, active_steps support tf root c c 0
| active_next : forall first next last count,
    N.next_config tf first=Some next ->
    T.control_contains root (R.cfg_control next) ->
    active_steps support tf root next last count ->
    active_steps support tf root first last (charge support root first next + count).
Lemma active_execution support tf root first last count :
 active_steps support tf root first last count -> N.steps tf first last.
Proof. intro Hsteps. induction Hsteps;[constructor |econstructor;eassumption]. Qed.
Theorem active_bound support tf roots root first last count :
 active_steps support tf root first last count ->
 N.steps tf (R.initial_config roots) first ->
 count + credit support (R.cfg_state last) root <= credit support (R.cfg_state first) root.
Proof.
 intro Hsteps. induction Hsteps;intro Hreach;[lia |].
 assert (Hnext : N.steps tf (R.initial_config roots) next).
 { eapply steps_append;[exact Hreach |]. econstructor;[exact H |constructor]. }
 specialize (IHHsteps Hnext).
 pose proof (@charge_bound support tf roots root first next Hreach H0 H) as Hpaid. lia.
Qed.
Corollary active_changes_bounded support tf roots root first last count :
 active_steps support tf root first last count ->
 N.steps tf (R.initial_config roots) first ->
 count <= credit support (R.cfg_state first) root.
Proof. intros Hsteps Hreach. pose proof (active_bound Hsteps Hreach). lia. Qed.

Fixpoint active_run fuel support tf root c : R.config * nat :=
 match fuel with
 | 0 => (c,0)
 | S rest =>
   match N.next_config tf c with
   | None => (c,0)
   | Some next =>
     if T.control_containsb root (R.cfg_control next) then
       let '(last,count) := active_run rest support tf root next in
       (last,charge support root c next + count)
     else (c,0)
   end
 end.
Lemma active_run_execution fuel support tf root c :
 active_steps support tf root c
   (fst (active_run fuel support tf root c))
   (snd (active_run fuel support tf root c)).
Proof.
 revert c. induction fuel as [|fuel IH];intro c;cbn;[constructor |].
 destruct (N.next_config tf c) as [next|] eqn:Hstep;[|constructor].
 destruct (T.control_containsb root (R.cfg_control next)) eqn:Hactive;[|constructor].
 specialize (IH next). destruct (active_run fuel support tf root next) as [last count];cbn in *.
 econstructor;[exact Hstep |apply T.control_containsb_spec,Hactive |exact IH].
Qed.
Theorem active_run_bound fuel support tf roots root c :
 N.steps tf (R.initial_config roots) c ->
 snd (active_run fuel support tf root c) <= credit support (R.cfg_state c) root.
Proof.
 intro Hreach. eapply active_changes_bounded;[apply active_run_execution |exact Hreach].
Qed.



Lemma equivalent_refl value : R.equivalent value value=true.
Proof. unfold R.equivalent. rewrite DL.leq_refl. reflexivity. Qed.
Lemma equivalent_trans first middle last :
 R.equivalent first middle=true -> R.equivalent middle last=true -> R.equivalent first last=true.
Proof.
 unfold R.equivalent. rewrite !Bool.andb_true_iff.
 intros [Hfm Hmf] [Hml Hlm]. split;eapply DL.leq_trans;eassumption.
Qed.
Lemma write_stable support st fr target input next changed root :
 List.In (R.frame_owner fr) support ->
 R.write_side_contribution st fr target input=(next,changed) ->
 credit support next root=credit support st root ->
 R.equivalent (R.aggregate next root) (R.aggregate st root)=true.
Proof.
 intros Hin Hw Heq. destruct (V.eq_dec root target) as [->|Hneq].
 - destruct changed.
   + pose proof (@T.target_side_credit_write_decreases support st fr target input next Hin Hw).
     unfold credit in Heq. lia.
   + eapply B.write_side_unchanged_equivalent;exact Hw.
 - unfold R.aggregate. rewrite (@B.write_side_contribution_other st fr target input next changed root Hw Hneq).
   apply equivalent_refl.
Qed.
Lemma finish_aggregate before after fr target changed root :
 R.aggregate (C.finish_write before after fr target changed) root=R.aggregate after root.
Proof. unfold R.aggregate. now rewrite finish_contributions. Qed.
Lemma publish_stable support targets st fr root :
 List.In (R.frame_owner fr) support ->
 credit support (C.publish targets st fr) root=credit support st root ->
 R.equivalent (R.aggregate (C.publish targets st fr) root) (R.aggregate st root)=true.
Proof.
 intros Hin. revert st. induction targets as [|target rest IH];intros st Heq;
 cbn -[R.write_side_contribution C.finish_write] in Heq |- *;[apply equivalent_refl |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 pose proof (@publish support rest (C.finish_write st next fr target changed) fr root) as Htail.
 pose proof (@write support root st fr target _ next changed Hw) as Hhead.
 rewrite finish in Htail. assert (Hcredit : credit support next root=credit support st root) by lia.
 eapply equivalent_trans.
 - apply IH. rewrite finish. lia.
 - rewrite finish_aggregate. eapply write_stable;eassumption.
Qed.
Theorem publication_strict support targets st fr root :
 List.In (R.frame_owner fr) support ->
 R.equivalent (R.aggregate (C.publish targets st fr) root) (R.aggregate st root)=false ->
 credit support (C.publish targets st fr) root<credit support st root.
Proof.
 intros Hin Hchanged. pose proof (@publish support targets st fr root) as Hle.
 destruct (Nat.eq_dec (credit support (C.publish targets st fr) root) (credit support st root)) as [Heq|Hneq];[|lia].
 pose proof (@publish_stable support targets st fr root Hin Heq). congruence.
Qed.
Theorem reachable_publication_strict tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct k after root :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|}=Some after ->
 R.equivalent (R.aggregate (R.cfg_state after) root) (R.aggregate st root)=false ->
 credit (B.Sem.support finite) (R.cfg_state after) root<credit (B.Sem.support finite) st root.
Proof.
 intros Hreach Hstep Hchanged.
 destruct (Support.reachable finite Hreach) as [_ [Hfr _]].
 cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
 cbn -[credit] in Hchanged |- *. unfold credit. rewrite T.target_credit_publish_targets.
 apply publication_strict;[exact (proj1 Hfr) |exact Hchanged].
Qed.
Theorem reachable_dead_strict tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct target rest k after root :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=Some after ->
 R.equivalent (R.aggregate (R.cfg_state after) root) (R.aggregate st root)=false ->
 credit (B.Sem.support finite) (R.cfg_state after) root<credit (B.Sem.support finite) st root.
Proof.
 intros Hreach Hstep Hchanged.
 destruct (Support.reachable finite Hreach) as [_ [Hfr _]].
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)).
 - inversion Hstep;subst. rewrite equivalent_refl in Hchanged. discriminate.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. rewrite continue_dead,requeue.
   assert (Hagg : R.aggregate (R.cfg_state
    (R.continue_dead (C.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed)) root=
    R.aggregate next root).
   { unfold R.continue_dead,C.requeue_source. destruct changed,C.cell_changed;
     try destruct (_ && _)%bool;reflexivity. }
   rewrite Hagg in Hchanged. pose proof (@write (B.Sem.support finite) root st fr target D.bottom next changed Hw) as Hle.
   destruct (Nat.eq_dec (credit (B.Sem.support finite) next root) (credit (B.Sem.support finite) st root)) as [Heq|Hneq];[|lia].
   pose proof (@write_stable (B.Sem.support finite) st fr target D.bottom next changed root (proj1 Hfr) Hw Heq).
   congruence.
Qed.

End TargetCredit.

(** These are internal induction steps: higher-episode completion is an
    induction hypothesis to discharge in the ranked termination proof. *)
Module Episodes.
Definition complete tf owner k start :=
 exists st,N.steps tf start {|R.cfg_state:=st;R.cfg_control:=R.Return k|} /\
 T.queue_strictly_below owner st.
Definition children tf roots owner :=
 forall st target k,
 R.rank_lt st owner target=true ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode target k|} ->
 complete tf target k {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode target k|}.
Lemma one tf first next :
 N.next_config tf first=Some next -> N.steps tf first next.
Proof. intro Hstep. econstructor;[exact Hstep |constructor]. Qed.
Lemma reached tf roots before after :
 N.steps tf (R.initial_config roots) before -> N.next_config tf before=Some after ->
 N.steps tf (R.initial_config roots) after.
Proof. intros Hreach Hstep. eapply steps_append;[exact Hreach |apply one,Hstep]. Qed.
Lemma continue_dead_advances tf roots st fr direct target rest k changed :
 children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) (R.continue_dead st fr direct target rest k changed) ->
 exists next,N.steps tf (R.continue_dead st fr direct target rest k changed)
 {|R.cfg_state:=next;R.cfg_control:=R.RunDead fr direct rest k|}.
Proof.
 intros Hchildren Hreach. unfold R.continue_dead in *.
 destruct changed;[|exists st;constructor].
 destruct (R.rank_lt st (R.frame_owner fr) target && negb (R.is_materialized st target))%bool eqn:Hg;
 [|exists (R.enqueue st target);constructor].
 apply Bool.andb_true_iff in Hg.
 destruct (Hchildren st target (R.KDead fr direct rest k) (proj1 Hg) Hreach) as [next [Hsteps Hbelow]].
 exists next. eapply steps_append;[exact Hsteps |]. apply one. reflexivity.
Qed.
Lemma dead_advances tf roots st fr direct target rest k :
 children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 exists next,N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunDead fr direct rest k|}.
Proof.
 intros Hchildren Hreach. destruct (S.mem target (R.frame_current_targets fr)) eqn:Hmem.
 - exists st. apply one. cbn -[R.write_side_contribution C.requeue_source R.continue_dead]. now rewrite Hmem.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=
    Some (R.continue_dead (C.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed)).
   { cbn -[R.write_side_contribution C.requeue_source R.continue_dead]. now rewrite Hmem,Hw. }
   destruct (@continue_dead_advances tf roots _ fr direct target rest k changed Hchildren
     (reached Hreach Hstep)) as [done Hdone].
   exists done. econstructor;[exact Hstep |exact Hdone].
Qed.
Theorem dead_reaches_commit tf roots st fr direct pending k :
 children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 exists next,N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 revert st. induction pending as [|target rest IH];intros st Hchildren Hreach.
 - eexists. apply one. reflexivity.
 - destruct (@dead_advances tf roots st fr direct target rest k Hchildren Hreach) as [next Hnext].
   destruct (IH next Hchildren (steps_append Hreach Hnext)) as [done Hdone].
   exists done. eapply steps_append;eassumption.
Qed.

Definition reaches_commit tf owner k start :=
 exists st fr direct,R.frame_owner fr=owner /\
 N.steps tf start {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Definition body_complete tf roots owner body :=
 forall st fr k,R.frame_owner fr=owner -> children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 reaches_commit tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Lemma prepend tf owner k before after :
 N.steps tf before after -> reaches_commit tf owner k after -> reaches_commit tf owner k before.
Proof.
 intros Hsteps [st [fr [direct [Howner Hdone]]]].
 exists st,fr,direct. split;[exact Howner |eapply steps_append;eassumption].
Qed.
Lemma body_after tf roots owner body before st fr k :
 body_complete tf roots owner body -> R.frame_owner fr=owner -> children tf roots owner ->
 N.steps tf (R.initial_config roots) before ->
 N.steps tf before {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 reaches_commit tf owner k before.
Proof.
 intros Hbody Howner Hchildren Hreach Hsteps. eapply prepend;[exact Hsteps |].
 apply Hbody;[exact Howner |exact Hchildren |eapply steps_append;eassumption].
Qed.
Lemma return_get tf st fr target body k next next_fr value :
 R.complete_get st fr target=(next,next_fr,value) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KAfterGet fr target body k)|}=
 Some {|R.cfg_state:=next;R.cfg_control:=R.RunRhs next_fr (body value) k|}.
Proof. intro Hg. cbn -[R.complete_get]. now rewrite Hg. Qed.

Lemma get_nested tf roots owner target body st fr k :
 (forall value,body_complete tf roots owner (body value)) ->
 R.frame_owner fr=owner -> children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|} ->
 (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool=true ->
 reaches_commit tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}.
Proof.
 intros IH Howner Hchildren Hreach Hguard.
 assert (Hstep : N.next_config tf
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}=
 Some {|R.cfg_state:=R.observe st target;R.cfg_control:=R.StartEpisode target (R.KAfterGet fr target body k)|}).
 { cbn -[R.observe R.complete_get R.enqueue]. now rewrite Hguard. }
 apply Bool.andb_true_iff in Hguard. rewrite Howner in Hguard.
 destruct (Hchildren _ _ _ (proj2 Hguard) (reached Hreach Hstep)) as [child [Hchild Hbelow]].
 destruct (R.complete_get child fr target) as [[next next_fr] value] eqn:Hg.
 eapply (@body_after tf roots owner (body value) _ next next_fr k).
 - apply IH.
 - rewrite (@B.complete_get_owner child fr target next next_fr value Hg). exact Howner.
 - exact Hchildren.
 - exact Hreach.
 - econstructor;[exact Hstep |]. eapply steps_append;[exact Hchild |].
   apply one. eapply return_get;exact Hg.
Qed.
Lemma get_direct tf roots owner target body st fr k :
 (forall value,body_complete tf roots owner (body value)) ->
 R.frame_owner fr=owner -> children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|} ->
 (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool=false ->
 reaches_commit tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}.
Proof.
 intros IH Howner Hchildren Hreach Hguard.
 set (base:=if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target).
 destruct (R.complete_get base fr target) as [[next next_fr] value] eqn:Hg.
 eapply (@body_after tf roots owner (body value) _ next next_fr k).
 - apply IH.
 - rewrite (@B.complete_get_owner base fr target next next_fr value Hg). exact Howner.
 - exact Hchildren.
 - exact Hreach.
 - apply one. cbn -[R.observe R.complete_get R.enqueue]. rewrite Hguard. fold base. now rewrite Hg.
Qed.
Lemma get_complete tf roots owner target body :
 (forall value,body_complete tf roots owner (body value)) ->
 body_complete tf roots owner (R.ConstraintSystem.Get target body).
Proof.
 intros IH st fr k Howner Hchildren Hreach.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool eqn:Hguard.
 - eapply get_nested;eassumption.
 - eapply get_direct;eassumption.
Qed.
Lemma spawn_nested tf roots owner target body st fr k :
 body_complete tf roots owner body ->
 R.frame_owner fr=owner -> children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target body) k|} ->
 R.is_materialized (R.observe st target) target=false ->
 R.rank_lt (R.observe st target) (R.frame_owner fr) target=true ->
 reaches_commit tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target body) k|}.
Proof.
 intros IH Howner Hchildren Hreach Hfresh Hhigher.
 assert (Hstep : N.next_config tf
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target body) k|}=
 Some {|R.cfg_state:=R.observe st target;R.cfg_control:=R.StartEpisode target (R.KAfterSpawn fr body k)|}).
 { cbn -[R.observe R.materialize R.enqueue]. now rewrite Hfresh,Hhigher. }
 rewrite Howner in Hhigher.
 destruct (Hchildren _ _ _ Hhigher (reached Hreach Hstep)) as [child [Hchild Hbelow]].
 eapply (@body_after tf roots owner body _ child fr k);[exact IH |exact Howner |exact Hchildren |exact Hreach |].
 econstructor;[exact Hstep |]. eapply steps_append;[exact Hchild |]. apply one. reflexivity.
Qed.
Lemma spawn_complete tf roots owner target body :
 body_complete tf roots owner body ->
 body_complete tf roots owner (R.ConstraintSystem.Spawn target body).
Proof.
 intros IH st fr k Howner Hchildren Hreach.
 destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
 - eapply (@body_after tf roots owner body _ (R.observe st target) fr k);
   [exact IH |exact Howner |exact Hchildren |exact Hreach |].
   apply one. cbn -[R.observe R.materialize R.enqueue]. now rewrite Hmat.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target) eqn:Hhigher.
   + eapply spawn_nested;eassumption.
   + eapply (@body_after tf roots owner body _ (R.materialize (R.enqueue (R.observe st target) target) target) fr k);
     [exact IH |exact Howner |exact Hchildren |exact Hreach |].
     apply one. cbn -[R.observe R.materialize R.enqueue]. now rewrite Hmat,Hhigher.
Qed.
Lemma side_complete tf roots owner target raw body :
 body_complete tf roots owner body ->
 body_complete tf roots owner (R.ConstraintSystem.Side target raw body).
Proof.
 intros IH st fr k Howner Hchildren Hreach.
 destruct (R.record_side_input fr target raw) as [next_fr input] eqn:Hr.
 eapply (@body_after tf roots owner body _ (R.observe st target) next_fr k);
 [exact IH | |exact Hchildren |exact Hreach |].
 - rewrite (@B.record_side_input_owner fr target raw next_fr input Hr). exact Howner.
 - apply one. cbn -[R.record_side_input R.observe]. now rewrite Hr.
Qed.
Lemma ret_complete tf roots owner direct :
 body_complete tf roots owner (R.ConstraintSystem.Ret direct).
Proof.
 intros st fr k Howner Hchildren Hreach.
 set (pending:=if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []).
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Ret direct) k|}=
 Some {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}) by reflexivity.
 assert (Hchildren' : children tf roots (R.frame_owner fr)) by now rewrite Howner.
 destruct (@dead_reaches_commit tf roots st fr direct pending k Hchildren' (reached Hreach Hstep)) as [next Hnext].
 exists next,fr,direct. split;[exact Howner |]. econstructor;[exact Hstep |exact Hnext].
Qed.
Theorem rhs_reaches_commit tf roots owner body : body_complete tf roots owner body.
Proof.
 induction body.
 - apply ret_complete.
 - apply get_complete,H.
 - apply side_complete,IHbody.
 - apply spawn_complete,IHbody.
Qed.
Lemma precommit_extends tf before after :
 C.P.next_config tf before = Some after ->
 B.rank_extends (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[R.next_config C.P.pending_above C.P.suspend_commit] in Hstep;
 try solve [eapply B.next_config_rank_extends;exact Hstep].
 destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. apply B.rank_extends_with_queue.
 - eapply B.next_config_rank_extends;exact Hstep.
Qed.
Lemma batched_extends tf before after :
 C.P.next_batched tf before = Some after ->
 B.rank_extends (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[C.P.next_config R.observe R.record_side_input C.P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_extends;exact Hstep].
 - destruct r;try solve [eapply precommit_extends;exact Hstep].
   inversion Hstep;subst. eapply B.rank_extends_observe;reflexivity.
 - destruct l;[|eapply precommit_extends;exact Hstep].
   inversion Hstep;subst. apply C.H.publication_extends.
Qed.
Lemma fresh_extends tf before after :
 C.P.next_fresh tf before = Some after ->
 B.rank_extends (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st control]. intro Hstep. destruct control;
 cbn -[C.P.next_batched C.P.clear_owner C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep;
 try solve [eapply batched_extends;exact Hstep].
 - eapply B.rank_extends_trans;[apply B.rank_extends_with_queue |].
   exact (@batched_extends tf _ _ Hstep).
 - destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. apply B.rank_extends_with_queue.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply B.rank_extends_with_queue.
     * exact (@batched_extends tf _ _ Hstep).
 - destruct c;try solve [eapply batched_extends;exact Hstep].
   eapply B.rank_extends_trans;[apply B.rank_extends_with_queue |].
   exact (@batched_extends tf _ _ Hstep).
Qed.
Lemma next_extends tf before after :
 N.next_config tf before = Some after ->
 B.rank_extends (R.cfg_state before) (R.cfg_state after).
Proof.
 intro Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.Episodes.next_extends tf before after Hb0).
 - apply B.rank_extends_with_queue.
Qed.



Lemma steps_extends tf first last : N.steps tf first last ->
 B.rank_extends (R.cfg_state first) (R.cfg_state last).
Proof.
 intro Hsteps. induction Hsteps;[apply B.rank_extends_refl |].
 eapply B.rank_extends_trans;[eapply next_extends;exact H |exact IHHsteps].
Qed.
Theorem rank_bound tf roots (finite : B.Sem.finite_system tf roots) c owner rank :
 N.steps tf (R.initial_config roots) c ->
 R.Ranking.lookup (R.ranking (R.cfg_state c)) owner=Some rank ->
 rank<B.Finite.bound (B.Sem.support finite).
Proof.
 intros Hreach Hlookup. eapply B.Finite.generated_lookup_bound.
 - exact (B.configuration_rank_valid (reachable_ranked Hreach)).
 - exact (B.state_ranking_generated (proj1 (Support.reachable finite Hreach))).
 - exact Hlookup.
Qed.
Definition drains tf owner k start :=
 exists boundary,N.steps tf start boundary /\ T.drain_boundary tf owner k boundary.
Lemma drain_prepend tf owner k before after :
 N.steps tf before after -> drains tf owner k after -> drains tf owner k before.
Proof.
 intros Hsteps [last [Hlast Hb]]. exists last. split;[eapply steps_append;eassumption |exact Hb].
Qed.
Lemma drain_self tf st fr k :
 B.queue_ordered st -> R.queue_peek (R.queue st)=Some (R.frame_owner fr) ->
 drains tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hsort Hpeek. destruct (@T.queue_peek_some_pop _ _ Hpeek) as [tail Hpop].
 exists {|R.cfg_state:=R.with_queue st tail;
 R.cfg_control:=R.RunRhs (R.fresh_frame (R.with_queue st tail) (R.frame_owner fr) (R.frame_phase fr))
 (tf (R.frame_owner fr)) k|}. split.
 - apply one. cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame].
   rewrite Hpeek. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));[now rewrite Hpop |contradiction].
 - apply T.DrainBoundaryRerun;[reflexivity |]. eapply T.with_queue_strictly_below;eassumption.
Qed.
Lemma drain_none tf st fr k :
 R.queue_peek (R.queue st)=None ->
 drains tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intro Hpeek. exists {|R.cfg_state:=R.reset_registered_cells st (R.frame_owner fr);R.cfg_control:=R.Return k|}. split.
 - apply one. cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame]. now rewrite Hpeek.
 - apply T.DrainBoundaryReturn,T.reset_registered_cells_below. eapply T.queue_peek_none_below;exact Hpeek.
Qed.
Lemma drain_lower tf roots st fr k target :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 R.queue_peek (R.queue st)=Some target -> target<>R.frame_owner fr ->
 R.rank_lt st (R.frame_owner fr) target=false ->
 drains tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hreach Hpeek Hneq Hhigher.
 pose proof (reachable_ranked Hreach) as Hr.
 assert (Htarget : B.ranked st target).
 { apply (B.data_queue_ranked (B.configuration_state_data Hr)). apply T.queue_peek_member,Hpeek. }
 assert (Howner : B.ranked st (R.frame_owner fr)).
 { exact (proj1 (proj1 (B.configuration_control_ranked Hr))). }
 assert (Hlower : R.rank_lt st target (R.frame_owner fr)=true).
 { eapply T.rank_lt_reverse_if_false;[exact (B.configuration_rank_valid Hr) |exact Howner |exact Htarget |congruence |exact Hhigher]. }
 exists {|R.cfg_state:=R.reset_registered_cells st (R.frame_owner fr);R.cfg_control:=R.Return k|}. split.
 - apply one. cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame].
   rewrite Hpeek. destruct (V.eq_dec target (R.frame_owner fr));[contradiction |]. now rewrite Hhigher.
 - apply T.DrainBoundaryReturn,T.reset_registered_cells_below.
   eapply T.queue_peek_lower_below;[exact (B.configuration_queue_ordered Hr) |exact Hpeek |exact Hlower].
Qed.
Definition queue_bound st owner bound :=
 forall target rank,R.queue_peek (R.queue st)=Some target ->
 R.rank_lt st owner target=true -> R.Ranking.lookup (R.ranking st) target=Some rank -> rank<bound.
Lemma below_bound st target rank owner :
 T.queue_strictly_below target st -> R.Ranking.lookup (R.ranking st) target=Some rank ->
 queue_bound st owner rank.
Proof.
 intros Hbelow Hrank candidate candidate_rank Hpeek _ Hcandidate.
 pose proof (Hbelow candidate (@T.queue_peek_member _ _ Hpeek)) as Hlt.
 unfold R.rank_lt,R.ranking_lt in Hlt. rewrite Hcandidate,Hrank in Hlt.
 apply Nat.ltb_lt,Hlt.
Qed.
Lemma drain_child tf roots st fr k target :
 children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 R.queue_peek (R.queue st)=Some target -> target<>R.frame_owner fr ->
 R.rank_lt st (R.frame_owner fr) target=true ->
 exists done,
 N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 {|R.cfg_state:=done;R.cfg_control:=R.RunDrain fr k|} /\
 T.queue_strictly_below target done.
Proof.
 intros Hchildren Hreach Hpeek Hneq Hhigher.
 destruct (@T.queue_peek_some_pop _ _ Hpeek) as [tail Hpop].
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=R.with_queue st tail;R.cfg_control:=R.StartEpisode target (R.KDrain fr k)|}).
 { cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame].
   rewrite Hpeek. destruct (V.eq_dec target (R.frame_owner fr));[contradiction |]. now rewrite Hhigher,Hpop. }
 destruct (Hchildren (R.with_queue st tail) target (R.KDrain fr k) Hhigher (reached Hreach Hstep)) as [done [Hdone Hbelow]].
 exists done. split;[ |exact Hbelow].
 econstructor;[exact Hstep |]. eapply steps_append;[exact Hdone |]. apply one. reflexivity.
Qed.
Lemma drain_bounded tf roots owner fuel :
 children tf roots owner ->
 forall st fr k,R.frame_owner fr=owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 queue_bound st owner fuel ->
 drains tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intro Hchildren. induction fuel as [fuel IH] using Wf_nat.lt_wf_ind.
 intros st fr k Howner Hreach Hbound.
 destruct (R.queue_peek (R.queue st)) as [target|] eqn:Hpeek.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + rewrite <- Howner. apply drain_self;[exact (B.configuration_queue_ordered (reachable_ranked Hreach)) |now rewrite <- Heq].
   + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
     * assert (Htarget : B.ranked st target).
       { apply (B.data_queue_ranked (B.configuration_state_data (reachable_ranked Hreach))).
         apply T.queue_peek_member,Hpeek. }
       destruct Htarget as [rank Hrank].
       assert (Hlt : rank<fuel) by (eapply Hbound;[exact Hpeek |now rewrite <- Howner |exact Hrank]).
       assert (Hchildren' : children tf roots (R.frame_owner fr)) by now rewrite Howner.
       destruct (@drain_child tf roots st fr k target Hchildren' Hreach Hpeek Hneq Hhigher) as [done [Hdone Hbelow]].
       eapply drain_prepend;[exact Hdone |].
       apply (IH rank Hlt done fr k Howner).
       -- eapply steps_append;eassumption.
       -- eapply below_bound;[exact Hbelow |]. apply (steps_extends Hdone). exact Hrank.
     * rewrite <- Howner. eapply drain_lower;eassumption.
 - rewrite <- Howner. apply drain_none,Hpeek.
Qed.
Theorem drain_reaches_boundary tf roots (finite : B.Sem.finite_system tf roots) st fr k :
 children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 drains tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hchildren Hreach.
 eapply (@drain_bounded tf roots (R.frame_owner fr) (B.Finite.bound (B.Sem.support finite)));
 [exact Hchildren |reflexivity |exact Hreach |].
 intros target rank Hpeek Hhigher Hrank. eapply rank_bound;[exact Hreach |exact Hrank].
Qed.

End Episodes.

Module MaterializationBudget.
Definition credit := T.unmaterialized_count.
Lemma nonincreasing support before after :
 T.sigma_extends before after -> credit support after<=credit support before.
Proof.
 intro Hextends. induction support as [|owner rest IH];cbn;[lia |].
 destruct (R.is_materialized before owner) eqn:Hold.
 - rewrite (T.sigma_extends_materialized_mono Hextends owner Hold). lia.
 - destruct (R.is_materialized after owner);lia.
Qed.
Lemma strict support before after owner :
 T.sigma_extends before after -> List.In owner support ->
 R.is_materialized before owner=false -> R.is_materialized after owner=true ->
 credit support after<credit support before.
Proof.
 intros Hextends Hin Hbefore Hafter. induction support as [|head rest IH];[contradiction |].
 destruct Hin as [<-|Hin].
 - cbn. rewrite Hbefore,Hafter. pose proof (@nonincreasing rest before after Hextends). unfold credit in *. lia.
 - specialize (IH Hin). cbn.
   destruct (R.is_materialized before head) eqn:Hhead.
   + rewrite (T.sigma_extends_materialized_mono Hextends head Hhead). lia.
   + destruct (R.is_materialized after head);lia.
Qed.
Theorem steps_nonincreasing support tf before after :
 N.steps tf before after -> credit support (R.cfg_state after)<=credit support (R.cfg_state before).
Proof. intro Hsteps. apply nonincreasing. exact (proj1 (steps_materialized Hsteps)). Qed.
Lemma materialize_here st owner : R.is_materialized (R.materialize st owner) owner=true.
Proof.
 unfold R.materialize,R.is_materialized. destruct (M.lookup (R.sigma st) owner) eqn:Hlookup.
 - now rewrite Hlookup.
 - cbn. now rewrite ML.lookup_update_same.
Qed.
Lemma start_materializes tf st owner k after :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}=Some after ->
 R.is_materialized (R.cfg_state after) owner=true.
Proof. intro Hstep. inversion Hstep;subst. apply materialize_here. Qed.
Theorem completed_episode_materializes tf st owner k done :
 N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}
 {|R.cfg_state:=done;R.cfg_control:=R.Return k|} ->
 R.is_materialized done owner=true.
Proof.
 intro Hsteps. inversion Hsteps as [|first next last Hstep Htail];subst.
 eapply T.sigma_extends_materialized_mono.
 - exact (proj1 (steps_materialized Htail)).
 - eapply start_materializes;exact Hstep.
Qed.
Theorem fresh_episode_strict tf roots (finite : B.Sem.finite_system tf roots) st owner k done :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|} ->
 N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}
 {|R.cfg_state:=done;R.cfg_control:=R.Return k|} ->
 R.is_materialized st owner=false ->
 credit (B.Sem.support finite) done<credit (B.Sem.support finite) st.
Proof.
 intros Hreach Hsteps Hfresh.
 destruct (Support.reachable finite Hreach) as [_ [Howner Hk]].
 eapply strict;[exact (proj1 (steps_materialized Hsteps)) |exact Howner |exact Hfresh |].
 eapply completed_episode_materializes;exact Hsteps.
Qed.
End MaterializationBudget.


Module Promotion.
Definition persists before after := forall owner,
 S.mem owner (R.controlled before)=true -> S.mem owner (R.controlled after)=true.
Lemma same before after : R.controlled after=R.controlled before -> persists before after.
Proof. intros Heq owner Hmem. now rewrite Heq. Qed.
Lemma queue st next_queue : persists st (R.with_queue st next_queue).
Proof. apply same;reflexivity. Qed.
Lemma trans first middle last : persists first middle -> persists middle last -> persists first last.
Proof. intros Hfirst Hlast owner Hmem. apply Hlast,Hfirst,Hmem. Qed.
Lemma base tf before after : R.next_config tf before=Some after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof. intros Hstep owner Hmem. eapply T.controlled_step_monotone;[exact Hstep |exact Hmem]. Qed.
Lemma precommit tf before after : P.next_config tf before=Some after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intro Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base;exact Hstep].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. apply queue.
 - eapply base;exact Hstep.
Qed.
Lemma old_publish targets st fr : persists st (P.publish_accumulated targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution];[apply same;reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply trans;[ |apply IH]. destruct changed;intros owner Hmem;change (S.mem owner (R.controlled next)=true);
 (eapply B.ReaderOrder.controlled_mono_write_side;[exact Hw |exact Hmem]).
Qed.
Lemma batched tf before after : P.next_batched tf before=Some after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intro Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit;exact Hstep].
 - destruct r;try solve [eapply precommit;exact Hstep].
   inversion Hstep;subst. apply B.ReaderOrder.controlled_mono_observe.
 - destruct l;[|eapply precommit;exact Hstep].
   inversion Hstep;subst. apply old_publish.
Qed.
Lemma fresh tf before after : P.next_fresh tf before=Some after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intro Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched;exact Hstep].
 - eapply trans;[ |exact (@batched tf _ after Hstep)]. apply queue.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. apply queue.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply queue.
     * eapply batched;exact Hstep.
 - destruct c;try solve [eapply batched;exact Hstep].
   eapply trans;[ |exact (@batched tf _ after Hstep)]. apply queue.
Qed.
Lemma requeue before after source target : persists after (C.requeue_source before after source target).
Proof. unfold C.requeue_source. destruct C.cell_changed;apply same;reflexivity. Qed.
Lemma finish before after fr target changed : persists after (C.finish_write before after fr target changed).
Proof. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;apply same;reflexivity. Qed.
Lemma publish targets st fr : persists st (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[apply same;reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 eapply trans;[ |apply IH]. eapply trans;[ |apply finish].
 intros owner Hmem. eapply B.ReaderOrder.controlled_mono_write_side;[exact Hw |exact Hmem].
Qed.
Lemma dead tf st fr direct pending k after :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 persists st (R.cfg_state after).
Proof.
 intro Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst. apply publish.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply same;reflexivity |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. eapply trans.
   + intros owner Hmem. eapply B.ReaderOrder.controlled_mono_write_side;[exact Hw |exact Hmem].
   + unfold R.continue_dead,C.requeue_source. destruct changed,C.cell_changed;try destruct (_ && _)%bool;
     apply same;reflexivity.
Qed.
Theorem next tf before after : N.next_config tf before=Some after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof.
 intro Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.Promotion.next tf before after Hb0).
 - apply same;reflexivity.
Qed.
Theorem steps tf before after : N.steps tf before after ->
 persists (R.cfg_state before) (R.cfg_state after).
Proof.
 intro Hsteps. induction Hsteps;[apply same;reflexivity |].
 eapply trans;[eapply next;exact H |exact IHHsteps].
Qed.
Theorem reserve_nonincreasing tf before after owner : N.steps tf before after ->
 T.promotion_reserve (R.cfg_state after) owner<=T.promotion_reserve (R.cfg_state before) owner.
Proof.
 intro Hsteps. unfold T.promotion_reserve.
 destruct (S.mem owner (R.controlled (R.cfg_state before))) eqn:Hbefore.
 - rewrite (steps Hsteps Hbefore). lia.
 - destruct (S.mem owner (R.controlled (R.cfg_state after)));lia.
Qed.
End Promotion.


Module OrdinaryCredit.
Definition credit c owner := T.active_ordinary_credit (R.cfg_state c) (R.cfg_control c) owner.
Lemma same before after owner before_fr after_fr :
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 R.frame_phase after_fr=R.frame_phase before_fr ->
 R.sigma_value (R.cfg_state after) owner=R.sigma_value (R.cfg_state before) owner ->
 credit after owner<=credit before owner.
Proof. intros. eapply T.active_ordinary_credit_same_le;eassumption. Qed.
Lemma base tf before after owner before_fr after_fr :
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 B.Sem.solved (R.cfg_state before) owner ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 R.next_config tf before=Some after -> credit after owner<=credit before owner.
Proof.
 destruct before as [st ctrl]. intros Ho Hsolved Hb Ha Hbf Haf Hstep. destruct ctrl;
 try solve [discriminate Hbf].
 - eapply T.active_ordinary_start_episode_nonincreasing;eassumption.
 - eapply T.active_ordinary_runrhs_nonincreasing;eassumption.
 - eapply T.active_ordinary_rundead_nonincreasing;eassumption.
 - eapply T.active_ordinary_runcommit_nonincreasing;eassumption.
 - eapply T.active_ordinary_rundrain_nonincreasing;eassumption.
 - eapply T.active_ordinary_return_nonincreasing;eassumption.
Qed.
Lemma suspend_phase st fr k target rest tf owner before_fr after_fr direct :
 T.control_frame owner (R.RunCommit fr direct k)=Some before_fr ->
 T.control_frame owner (R.cfg_control (P.suspend_commit tf st fr k target rest))=Some after_fr ->
 R.frame_phase after_fr=R.frame_phase before_fr.
Proof.
 unfold P.suspend_commit. cbn [R.cfg_control T.control_frame T.continuation_frame R.fresh_frame R.frame_owner].
 destruct (V.eq_dec target owner);[discriminate |].
 destruct (V.eq_dec (R.frame_owner fr) owner);intros Hb Ha;inversion Hb;inversion Ha;subst;try reflexivity;congruence.
Qed.
Lemma suspend_credit st fr k target rest tf owner before_fr after_fr direct :
 S.mem owner (R.controlled st)=true ->
 T.control_frame owner (R.RunCommit fr direct k)=Some before_fr ->
 T.control_frame owner (R.cfg_control (P.suspend_commit tf st fr k target rest))=Some after_fr ->
 credit (P.suspend_commit tf st fr k target rest) owner <=
 credit {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} owner.
Proof.
 intros Hc Hb Ha. eapply same;[exact Hc |exact Hc |exact Hb |exact Ha | |reflexivity].
 eapply suspend_phase;eassumption.
Qed.
Lemma precommit tf before after owner before_fr after_fr :
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 B.Sem.solved (R.cfg_state before) owner ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 P.next_config tf before=Some after -> credit after owner<=credit before owner.
Proof.
 destruct before as [st ctrl]. intros Ho Hsolved Hb Ha Hbf Haf Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base;eassumption].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. eapply suspend_credit;eassumption.
 - eapply base;eassumption.
Qed.
Lemma side_phase fr target input body k owner before_fr after_fr :
 T.control_frame owner (R.RunRhs fr (R.ConstraintSystem.Side target input body) k)=Some before_fr ->
 T.control_frame owner (R.RunRhs (fst (R.record_side_input fr target input)) body k)=Some after_fr ->
 R.frame_phase after_fr=R.frame_phase before_fr.
Proof.
 unfold R.record_side_input. cbn -[R.accumulated_side_input T.continuation_frame].
 destruct (V.eq_dec (R.frame_owner fr) owner);intros Hb Ha;inversion Hb;inversion Ha;subst;try reflexivity;congruence.
Qed.
Lemma side_credit tf st fr target input body k after owner before_fr after_fr :
 S.mem owner (R.controlled st)=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.RunRhs fr (R.ConstraintSystem.Side target input body) k)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 P.next_batched tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Side target input body) k|}=Some after ->
 credit after owner<=credit {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Side target input body) k|} owner.
Proof.
 intros Hb Ha Hbf Haf Hstep. inversion Hstep;subst.
 eapply same;[exact Hb |exact Ha |exact Hbf |exact Haf | |].
 - eapply side_phase;eassumption.
 - unfold R.sigma_value,R.observe. destruct (R.Ranking.observe (R.ranking st) target);reflexivity.
Qed.
Lemma batched tf before after owner before_fr after_fr :
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 B.Sem.solved (R.cfg_state before) owner ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 P.next_batched tf before=Some after -> credit after owner<=credit before owner.
Proof.
 destruct before as [st ctrl]. intros Ho Hsolved Hb Ha Hbf Haf Hstep. destruct ctrl;
 try solve [exact (@precommit tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
 - destruct r;try solve [exact (@precommit tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
   eapply side_credit;eassumption.
 - destruct l;[|exact (@precommit tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
   inversion Hstep;subst. eapply same;[exact Hb |exact Ha |exact Hbf |exact Haf | |].
   + cbn [R.cfg_control T.control_frame] in Hbf,Haf. congruence.
   + unfold R.sigma_value. change (R.sigma_value (P.publish_accumulated (S.elements (R.frame_current_targets f)) st f) owner=R.sigma_value st owner).
     unfold R.sigma_value. rewrite old_publish_sigma. reflexivity.
Qed.


Lemma clear_batched tf st ctrl cleared after owner before_fr after_fr :
 T.control_ordered st ctrl -> B.Sem.solved st owner ->
 S.mem owner (R.controlled st)=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner ctrl=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 P.next_batched tf {|R.cfg_state:=P.clear_owner st cleared;R.cfg_control:=ctrl|}=Some after ->
 credit after owner<=credit {|R.cfg_state:=st;R.cfg_control:=ctrl|} owner.
Proof.
 intros Ho Hsolved Hb Ha Hbf Haf Hstep.
 change (credit after owner<=credit {|R.cfg_state:=P.clear_owner st cleared;R.cfg_control:=ctrl|} owner).
 eapply (@batched tf _ after owner before_fr after_fr);[ |exact Hsolved |exact Hb |exact Ha |exact Hbf |exact Haf |exact Hstep].
 eapply ordered_extended;[apply B.rank_extends_with_queue |exact Ho].
Qed.
Lemma retry_phase tf st fr k direct owner before_fr after_fr :
 T.control_frame owner (R.RunCommit fr direct k)=Some before_fr ->
 T.control_frame owner (R.cfg_control (P.retry_current tf st fr k))=Some after_fr ->
 R.frame_phase after_fr=R.frame_phase before_fr.
Proof.
 unfold P.retry_current. cbn -[T.continuation_frame P.clear_owner].
 destruct (V.eq_dec (R.frame_owner fr) owner);intros Hb Ha;inversion Hb;inversion Ha;subst;try reflexivity;congruence.
Qed.
Lemma retry_credit tf st fr k direct owner before_fr after_fr :
 S.mem owner (R.controlled st)=true ->
 T.control_frame owner (R.RunCommit fr direct k)=Some before_fr ->
 T.control_frame owner (R.cfg_control (P.retry_current tf st fr k))=Some after_fr ->
 credit (P.retry_current tf st fr k) owner<=
 credit {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} owner.
Proof.
 intros Hc Hb Ha. eapply same;[exact Hc |exact Hc |exact Hb |exact Ha | |reflexivity].
 eapply retry_phase;eassumption.
Qed.
Lemma fresh tf before after owner before_fr after_fr :
 T.control_ordered (R.cfg_state before) (R.cfg_control before) ->
 B.Sem.solved (R.cfg_state before) owner ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 P.next_fresh tf before=Some after -> credit after owner<=credit before owner.
Proof.
 destruct before as [st ctrl]. intros Ho Hsolved Hb Ha Hbf Haf Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [exact (@batched tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
 - eapply clear_batched;eassumption.
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. eapply suspend_credit;eassumption.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. eapply retry_credit;eassumption.
     * exact (@batched tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep).
 - destruct c;try solve [exact (@batched tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
   eapply clear_batched;eassumption.
Qed.
Lemma continue_dead_phase st fr direct target rest k changed owner before_fr after_fr :
 T.control_frame owner (R.RunDead fr direct rest k)=Some before_fr ->
 T.control_frame owner (R.cfg_control (R.continue_dead st fr direct target rest k changed))=Some after_fr ->
 R.frame_phase after_fr=R.frame_phase before_fr.
Proof.
 unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];
 cbn [R.cfg_control T.control_frame T.continuation_frame].
 all: repeat match goal with |- context [V.eq_dec ?x ?y] => destruct (V.eq_dec x y) end.
 all: intros Hb Ha;try discriminate;inversion Hb;inversion Ha;subst;try reflexivity;congruence.
Qed.
Lemma continue_dead_sigma st fr direct target rest k changed :
 R.sigma (R.cfg_state (R.continue_dead st fr direct target rest k changed))=R.sigma st.
Proof. unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];reflexivity. Qed.
Lemma dead tf st fr direct pending k after owner before_fr after_fr :
 S.mem owner (R.controlled st)=true ->
 S.mem owner (R.controlled (R.cfg_state after))=true ->
 T.control_frame owner (R.RunDead fr direct pending k)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 credit after owner<=credit {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} owner.
Proof.
 intros Hb Ha Hbf Haf Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   eapply same;[exact Hb |exact Ha |exact Hbf |exact Haf | |].
   + cbn [R.cfg_control T.control_frame] in Hbf,Haf. congruence.
   + unfold R.sigma_value. cbn -[C.publish]. now rewrite publish_sigma.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;apply Nat.le_refl |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. eapply same;[exact Hb |exact Ha |exact Hbf |exact Haf | |].
   + exact (@continue_dead_phase _ fr direct target rest k changed owner before_fr after_fr Hbf Haf).
   + unfold R.sigma_value. rewrite continue_dead_sigma,requeue_sigma.
     rewrite (@T.write_side_sigma st fr target D.bottom next changed Hw). reflexivity.
Qed.
Theorem step_nonincreasing tf roots before after owner before_fr after_fr :
 N.steps tf (R.initial_config roots) before -> N.next_config tf before=Some after ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_frame owner (R.cfg_control after)=Some after_fr ->
 credit after owner<=credit before owner.
Proof.
 intros Hreach Hstep Hb Hbf Haf.
 pose proof (proj1 (reachable_history Hreach)) as Ho.
 pose proof (@Promotion.next tf before after Hstep owner Hb) as Ha.
 assert (Hsolved : B.Sem.solved (R.cfg_state before) owner).
 { apply B.materialized_solved. eapply T.control_frame_materialized;
   [exact (reachable_owners_materialized Hreach) |exact Hbf]. }
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { eapply (@fresh tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr D.bottom k|}
 (P.suspend_commit tf st fr k target rest) owner before_fr after_fr);
 try eassumption.
 cbn -[P.pending_above P.suspend_commit P.next_batched]. now rewrite Hp. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;
 try solve [exact (@fresh tf _ after owner before_fr after_fr Ho Hsolved Hb Ha Hbf Haf Hstep)].
 eapply dead with (tf:=tf);eassumption.
Qed.


Lemma framed_not_higher st fr k owner before_fr :
 T.continuation_below st (R.frame_owner fr) k ->
 T.control_frame owner (R.RunCommit fr D.bottom k)=Some before_fr ->
 R.rank_lt st (R.frame_owner fr) owner=true -> False.
Proof.
 intros Ho Hframe Hhigher. cbn [T.control_frame] in Hframe.
 destruct (V.eq_dec (R.frame_owner fr) owner) as [Heq|Hneq].
 - rewrite Heq in Hhigher. exact (@B.rank_lt_true_neq_correctness st owner owner Hhigher eq_refl).
 - pose proof (@T.continuation_frame_contains owner k before_fr Hframe) as Hcontains.
   pose proof (@T.continuation_contains_below st (R.frame_owner fr) k owner Ho Hcontains) as Hlower.
   pose proof (@T.rank_lt_trans_true st owner (R.frame_owner fr) owner Hlower Hhigher) as Hself.
   exact (@B.rank_lt_true_neq_correctness st owner owner Hself eq_refl).
Qed.
Lemma rhs_start_unmaterialized tf st fr body k after owner after_k :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} ->
 R.is_materialized after owner=false.
Proof.
 intro Hstep. destruct body as [direct|target body|target raw body|target body].
 - discriminate Hstep.
 - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
   destruct (negb (R.is_materialized (R.observe st target) target) &&
    R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool eqn:Hg.
   + inversion Hstep;subst. apply Bool.andb_true_iff in Hg.
     apply Bool.negb_true_iff. exact (proj1 Hg).
   + destruct (R.complete_get
     (if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target) fr target)
     as [[next next_fr] value]. discriminate.
 - cbn -[R.record_side_input R.observe] in Hstep. destruct (R.record_side_input fr target raw);discriminate.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st target) target) eqn:Hg;[discriminate |].
   destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);[inversion Hstep;subst;exact Hg |discriminate].
Qed.
Lemma dead_start_unmaterialized tf st fr direct pending k after owner after_k :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} ->
 R.is_materialized after owner=false.
Proof.
 intro Hstep. destruct pending as [|target rest];[discriminate Hstep |].
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr));[discriminate |].
 destruct (R.write_side_contribution st fr target D.bottom) as [next changed].
 unfold R.continue_dead in Hstep. destruct changed;[|discriminate].
 destruct (R.rank_lt (C.requeue_source st next (R.frame_owner fr) target) (R.frame_owner fr) target &&
   negb (R.is_materialized (C.requeue_source st next (R.frame_owner fr) target) target))%bool eqn:Hg;[|discriminate].
 inversion Hstep;subst. apply Bool.andb_true_iff in Hg.
 apply Bool.negb_true_iff. exact (proj2 Hg).
Qed.
Lemma drain_cannot_start tf st fr k after owner after_k before_fr :
 T.continuation_below st (R.frame_owner fr) k ->
 T.control_frame owner (R.RunDrain fr k)=Some before_fr ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} -> False.
Proof.
 intros Ho Hframe Hstep. cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame] in Hstep.
 destruct (R.queue_peek (R.queue st)) as [target|];[|discriminate].
 destruct (V.eq_dec target (R.frame_owner fr)).
 - destruct (R.queue_pop (R.queue st)) as [[head tail]|];discriminate.
 - destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher;[|discriminate].
   destruct (R.queue_pop (R.queue st)) as [[head tail]|];[|discriminate].
   inversion Hstep;subst. eapply framed_not_higher;[exact Ho |exact Hframe |exact Hhigher].
Qed.
Lemma commit_cannot_start tf st fr direct k after owner after_k before_fr :
 T.continuation_below st (R.frame_owner fr) k ->
 T.control_frame owner (R.RunCommit fr direct k)=Some before_fr ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} -> False.
Proof.
 intros Ho Hframe Hstep. cbn -[P.pending_above P.suspend_commit P.retry_current P.next_batched] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst.
   pose proof (@P.pending_above_spec st (R.frame_owner fr) owner rest Hp) as [_ [_ Hhigher]].
   eapply framed_not_higher;[exact Ho |exact Hframe |exact Hhigher].
 - destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
   cbn -[R.set_value P.pending_above] in Hstep. rewrite Hp in Hstep.
   destruct (R.set_value st fr direct);discriminate.
Qed.
Theorem cannot_start_same tf roots before after owner after_k before_fr :
 N.steps tf (R.initial_config roots) before ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 N.next_config tf before=Some {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} -> False.
Proof.
 intros Hreach Hframe Hstep.
 pose proof (proj1 (reachable_history Hreach)) as Ho.
 assert (Hmat : R.is_materialized after owner=true).
 { eapply T.sigma_extends_materialized_mono.
   - exact (proj1 (@next_materialized tf before _ Hstep)).
   - eapply T.control_frame_materialized;[exact (reachable_owners_materialized Hreach) |exact Hframe]. }
 destruct (@Front.step_cases tf before
 {|R.cfg_state:=after;R.cfg_control:=R.StartEpisode owner after_k|} Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp Heq]]]]]]]]].
 2: { inversion Heq;subst.
   eapply (@framed_not_higher st fr k target before_fr);[exact Ho |exact Hframe |].
   exact (proj2 (proj2 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp))). }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;try discriminate Hframe.
 - discriminate Hstep.
 - pose proof (@rhs_start_unmaterialized tf st f r c after owner after_k Hstep). congruence.
 - pose proof (@dead_start_unmaterialized tf st f t l c after owner after_k Hstep). congruence.
 - eapply commit_cannot_start;[exact Ho |exact Hframe |exact Hstep].
 - eapply drain_cannot_start;[exact Ho |exact Hframe |exact Hstep].
 - destruct c;cbn -[R.complete_get] in Hstep;try discriminate.
Qed.
Theorem frame_persists tf roots before after owner before_fr :
 N.steps tf (R.initial_config roots) before -> N.next_config tf before=Some after ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_contains owner (R.cfg_control after) ->
 exists after_fr,T.control_frame owner (R.cfg_control after)=Some after_fr.
Proof.
 intros Hreach Hstep Hframe Hactive.
 destruct (@T.control_contains_frame_or_start owner (R.cfg_control after) Hactive) as [Hfound|[k Hstart]];[exact Hfound |].
 destruct after as [st ctrl]. cbn in Hstart. subst ctrl.
 exfalso. eapply cannot_start_same;[exact Hreach |exact Hframe |exact Hstep].
Qed.


Theorem committing_strict tf st fr direct k after next_fr next_k :
 S.mem (R.frame_owner fr) (R.controlled st)=true ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 R.equivalent (R.sigma_value after (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))=false ->
 credit {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} (R.frame_owner fr)<
 credit {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} (R.frame_owner fr).
Proof.
 intros Hcontrolled Hstep Hchanged.
 cbn -[P.pending_above P.retry_current R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp;[discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 destruct (R.set_value st fr direct) as [next nf] eqn:Hs. inversion Hstep;subst.
 change (T.active_ordinary_credit next (R.RunRhs next_fr (tf (R.frame_owner fr)) next_k) (R.frame_owner fr)<
 T.active_ordinary_credit st (R.RunRhs fr (tf (R.frame_owner fr)) next_k) (R.frame_owner fr)).
 eapply T.active_ordinary_credit_set_value_decreases;[exact Hcontrolled |exact Hs |exact Hchanged].
Qed.
Definition charge before after owner :=
 if Nat.ltb (credit after owner) (credit before owner) then 1 else 0.
Lemma charge_bound tf roots before after owner before_fr :
 N.steps tf (R.initial_config roots) before -> N.next_config tf before=Some after ->
 S.mem owner (R.controlled (R.cfg_state before))=true ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_contains owner (R.cfg_control after) ->
 charge before after owner+credit after owner<=credit before owner.
Proof.
 intros Hreach Hstep Hb Hframe Hactive.
 destruct (frame_persists owner Hreach Hstep Hframe Hactive) as [after_fr Haf].
 pose proof (@step_nonincreasing tf roots before after owner before_fr after_fr Hreach Hstep Hb Hframe Haf) as Hle.
 unfold charge. destruct (Nat.ltb _ _) eqn:Hlt;[apply Nat.ltb_lt in Hlt |];lia.
Qed.
Inductive active_steps tf owner : R.config -> R.config -> nat -> Prop :=
| active_refl : forall c,active_steps tf owner c c 0
| active_next : forall first next last count,N.next_config tf first=Some next ->
 T.control_contains owner (R.cfg_control next) -> active_steps tf owner next last count ->
 active_steps tf owner first last (charge first next owner+count).
Lemma active_execution tf owner first last count :
 active_steps tf owner first last count -> N.steps tf first last.
Proof. intro Hsteps. induction Hsteps;[constructor |econstructor;eassumption]. Qed.
Theorem active_bound tf roots owner first last count :
 active_steps tf owner first last count ->
 forall first_fr,N.steps tf (R.initial_config roots) first ->
 S.mem owner (R.controlled (R.cfg_state first))=true ->
 T.control_frame owner (R.cfg_control first)=Some first_fr ->
 count+credit last owner<=credit first owner.
Proof.
 intro Hsteps. induction Hsteps;intros first_fr Hreach Hb Hframe;[lia |].
 destruct (frame_persists owner Hreach H Hframe H0) as [next_fr Hnextframe].
 pose proof (@charge_bound tf roots first next owner first_fr Hreach H Hb Hframe H0) as Hpaid.
 assert (Hnextreach : N.steps tf (R.initial_config roots) next) by (eapply Episodes.reached;eassumption).
 pose proof (@Promotion.next tf first next H owner Hb) as Hnextcontrolled.
 specialize (IHHsteps next_fr Hnextreach Hnextcontrolled Hnextframe). lia.
Qed.
Corollary active_changes_bounded tf roots owner first last count first_fr :
 active_steps tf owner first last count -> N.steps tf (R.initial_config roots) first ->
 S.mem owner (R.controlled (R.cfg_state first))=true ->
 T.control_frame owner (R.cfg_control first)=Some first_fr ->
 count<=credit first owner.
Proof.
 intros Hsteps Hreach Hb Hframe. pose proof (active_bound Hsteps Hreach Hb Hframe). lia.
Qed.
Fixpoint active_run fuel tf owner c : R.config * nat :=
 match fuel with
 | 0 => (c,0)
 | S rest => match N.next_config tf c with
   | None => (c,0)
   | Some next => if T.control_containsb owner (R.cfg_control next) then
     let '(last,count):=active_run rest tf owner next in (last,charge c next owner+count)
     else (c,0)
   end
 end.
Lemma active_run_execution fuel tf owner c :
 active_steps tf owner c (fst (active_run fuel tf owner c)) (snd (active_run fuel tf owner c)).
Proof.
 revert c. induction fuel as [|fuel IH];intro c;cbn;[constructor |].
 destruct (N.next_config tf c) as [next|] eqn:Hstep;[|constructor].
 destruct (T.control_containsb owner (R.cfg_control next)) eqn:Hactive;[|constructor].
 specialize (IH next). destruct (active_run fuel tf owner next) as [last count];cbn in *.
 econstructor;[exact Hstep |apply T.control_containsb_spec,Hactive |exact IH].
Qed.
Theorem active_run_bound fuel tf roots owner c before_fr :
 N.steps tf (R.initial_config roots) c ->
 S.mem owner (R.controlled (R.cfg_state c))=true ->
 T.control_frame owner (R.cfg_control c)=Some before_fr ->
 snd (active_run fuel tf owner c)<=credit c owner.
Proof.
 intros Hreach Hb Hframe. eapply active_changes_bounded;[apply active_run_execution |exact Hreach |exact Hb |exact Hframe].
Qed.
Theorem no_promotion_step tf roots before after owner before_fr :
 N.steps tf (R.initial_config roots) before -> N.next_config tf before=Some after ->
 T.promotion_reserve (R.cfg_state after) owner=T.promotion_reserve (R.cfg_state before) owner ->
 T.control_frame owner (R.cfg_control before)=Some before_fr ->
 T.control_contains owner (R.cfg_control after) -> credit after owner<=credit before owner.
Proof.
 intros Hreach Hstep Hreserve Hframe Hactive.
 pose proof (T.promotion_reserve_equal_membership _ _ _ Hreserve) as Hsame.
 destruct (S.mem owner (R.controlled (R.cfg_state before))) eqn:Hcontrolled.
 - destruct (frame_persists owner Hreach Hstep Hframe Hactive) as [after_fr Haf].
   eapply step_nonincreasing;[exact Hreach |exact Hstep |exact Hcontrolled |exact Hframe |exact Haf].
 - unfold credit,T.active_ordinary_credit. rewrite Hsame,Hcontrolled. lia.
Qed.
End OrdinaryCredit.

(** The extra queue component pays pre-commit retries which merely finish
    already pending higher work. No domain update is required in this case. *)
Module PendingBudget.
Definition entry st owner target :=
 if R.rank_lt st owner target then
 match R.Ranking.lookup (R.ranking st) target with
 | Some rank => S rank | None => 0
 end else 0.
Definition total st owner pending := fold_right (fun target n => Nat.max (entry st owner target) n) 0 pending.
Definition credit st owner := total st owner (R.queue st).
Lemma member st owner pending target :
 List.In target pending -> entry st owner target<=total st owner pending.
Proof.
 induction pending as [|head rest IH];cbn;[contradiction |].
 intros [Heq|Hin];[subst;apply Nat.le_max_l |].
 eapply Nat.le_trans;[apply IH,Hin |apply Nat.le_max_r].
Qed.
Lemma bounded st owner pending bound :
 (forall target,List.In target pending -> entry st owner target<=bound) ->
 total st owner pending<=bound.
Proof.
 induction pending as [|head rest IH];cbn;intro Hbound;[lia |].
 apply Nat.max_lub;[apply Hbound;left;reflexivity |].
 apply IH. intros target Hin. apply Hbound;right;exact Hin.
Qed.
Lemma below st owner target rank :
 T.queue_strictly_below target st -> R.Ranking.lookup (R.ranking st) target=Some rank ->
 credit st owner<=rank.
Proof.
 intros Hbelow Hrank. apply bounded. intros candidate Hin.
 pose proof (Hbelow candidate Hin) as Hlt.
 unfold R.rank_lt,R.ranking_lt in Hlt. rewrite Hrank in Hlt.
 destruct (R.Ranking.lookup (R.ranking st) candidate) as [nr|] eqn:Hcandidate;[|discriminate].
 apply Nat.ltb_lt in Hlt. unfold entry. destruct R.rank_lt;[rewrite Hcandidate |];lia.
Qed.
Lemma clear st owner :
 credit (P.clear_owner st owner) owner<=credit st owner.
Proof.
 apply bounded. intros target Hin. apply List.filter_In in Hin.
 change (entry st owner target<=credit st owner).
 apply member. exact (proj1 Hin).
Qed.
Lemma pending_strict st owner target rest rank :
 P.pending_above st owner=Some (target,rest) ->
 R.Ranking.lookup (R.ranking st) target=Some rank ->
 rank<credit st owner.
Proof.
 intros Hp Hrank. destruct (@P.pending_above_spec st owner target rest Hp) as [_ [Hpop Hhigher]].
 pose proof (@member st owner (R.queue st) target (@T.queue_pop_member _ _ _ Hpop)) as Hle.
 unfold entry in Hle. rewrite Hhigher,Hrank in Hle. exact Hle.
Qed.
Theorem completed_child_strict tf st fr k target rest done :
 P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 N.steps tf (P.suspend_commit tf st fr k target rest)
 {|R.cfg_state:=done;R.cfg_control:=R.Return
 (R.KAfterSide (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)|} ->
 T.queue_strictly_below target done ->
 credit (P.clear_owner done (R.frame_owner fr)) (R.frame_owner fr)<
 credit st (R.frame_owner fr).
Proof.
 intros Hp Hsteps Hbelow.
 pose proof (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [_ Hhigher]].
 unfold R.rank_lt,R.ranking_lt in Hhigher.
 destruct (R.Ranking.lookup (R.ranking st) (R.frame_owner fr));[|discriminate].
 destruct (R.Ranking.lookup (R.ranking st) target) as [rank|] eqn:Hrank;[|discriminate].
 pose proof (Episodes.steps_extends Hsteps) as Hextends.
 assert (Hrank' : R.Ranking.lookup (R.ranking done) target=Some rank).
 { exact (Hextends target rank Hrank). }
 pose proof (@below done (R.frame_owner fr) target rank Hbelow Hrank').
 pose proof (clear done (R.frame_owner fr)).
 pose proof (@pending_strict st (R.frame_owner fr) target rest rank Hp Hrank). lia.
Qed.
End PendingBudget.

(** Equality of the source account excludes both kinds of enqueue:
    changed aggregates and changed individual cells hidden by an aggregate. *)
Module EvaluationQueue.
Lemma write_unchanged support st fr target input next changed :
 List.In target support -> R.write_side_contribution st fr target input=(next,changed) ->
 SourceCredit.credit support next (R.frame_owner fr)=SourceCredit.credit support st (R.frame_owner fr) ->
 changed=false /\ C.cell_changed st next (R.frame_owner fr) target=false.
Proof.
 intros Hin Hw Heq. split.
 - destruct changed;[|reflexivity].
   pose proof (@B.Credits.source_side_credit_write_decreases support st fr target input next Hin Hw).
   unfold SourceCredit.credit in Heq. lia.
 - destruct (C.cell_changed st next (R.frame_owner fr) target) eqn:Hcell;[|reflexivity].
   pose proof (@C.changed_source_consumes_credit support st fr target input next changed Hin Hw Hcell).
   unfold SourceCredit.credit in Heq. lia.
Qed.
Lemma finish_queue support st fr target input next changed :
 List.In target support -> R.write_side_contribution st fr target input=(next,changed) ->
 SourceCredit.credit support next (R.frame_owner fr)=SourceCredit.credit support st (R.frame_owner fr) ->
 R.queue (C.finish_write st next fr target changed)=R.queue st.
Proof.
 intros Hin Hw Heq. destruct (@write_unchanged support st fr target input next changed Hin Hw Heq) as [Hchanged Hcell].
 unfold C.finish_write,C.requeue_source. rewrite Hchanged,Hcell.
 eapply T.write_side_queue;exact Hw.
Qed.
Lemma publication_queue support targets st fr :
 List.incl targets support ->
 SourceCredit.credit support (C.publish targets st fr) (R.frame_owner fr)=SourceCredit.credit support st (R.frame_owner fr) ->
 R.queue (C.publish targets st fr)=R.queue st.
Proof.
 revert st. induction targets as [|target rest IH];intros st Hin Heq;[reflexivity |].
 cbn -[R.write_side_contribution C.finish_write] in Heq |- *.
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw.
 pose proof (@SourceCredit.publish support rest (C.finish_write st next fr target changed) fr (R.frame_owner fr)) as Htail.
 rewrite SourceCredit.finish in Htail.
 pose proof (@T.source_credit_write support (R.frame_owner fr) st fr target _ next changed Hw) as Hhead.
 change (SourceCredit.credit support next (R.frame_owner fr)<=SourceCredit.credit support st (R.frame_owner fr)) in Hhead.
 assert (Hcredit : SourceCredit.credit support next (R.frame_owner fr)=SourceCredit.credit support st (R.frame_owner fr)) by lia.
 rewrite IH.
 - eapply finish_queue;[apply Hin;left;reflexivity |exact Hw |exact Hcredit].
 - intros x Hx. apply Hin;right;exact Hx.
 - rewrite SourceCredit.finish. lia.
Qed.
Lemma dead_queue support tf st fr direct target rest k after :
 List.In target support ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=Some after ->
 SourceCredit.credit support (R.cfg_state after) (R.frame_owner fr)=SourceCredit.credit support st (R.frame_owner fr) ->
 R.queue (R.cfg_state after)=R.queue st /\
 R.cfg_control after=R.RunDead fr direct rest k.
Proof.
 intros Hin Hstep Heq.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;split;reflexivity |].
 destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
 inversion Hstep;subst;clear Hstep.
 rewrite SourceCredit.continue_dead,SourceCredit.requeue in Heq.
 destruct (@write_unchanged support st fr target D.bottom next changed Hin Hw Heq) as [Hchanged Hcell].
 unfold R.continue_dead,C.requeue_source. rewrite Hchanged,Hcell. cbn.
 split;[eapply T.write_side_queue;exact Hw |reflexivity].
Qed.
Theorem reachable_dead_queue tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct target rest k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}=Some after ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state after) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) st (R.frame_owner fr) ->
 R.queue (R.cfg_state after)=R.queue st /\ R.cfg_control after=R.RunDead fr direct rest k.
Proof.
 intros Hreach Hstep Heq. eapply dead_queue;[ |exact Hstep |exact Heq].
 destruct (Support.reachable finite Hreach) as [_ [_ [Htargets _]]].
 inversion Htargets;assumption.
Qed.
Theorem reachable_publication_queue tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|}=Some after ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state after) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) st (R.frame_owner fr) ->
 R.queue (R.cfg_state after)=R.queue st.
Proof.
 intros Hreach Hstep Heq.
 cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
 cbn -[SourceCredit.credit] in Heq. unfold SourceCredit.credit in Heq.
 rewrite T.source_credit_publish_targets in Heq.
 change (R.queue (C.publish (S.elements (R.frame_current_targets fr)) st fr)=R.queue st).
 eapply publication_queue;[ |exact Heq].
 destruct (Support.reachable finite Hreach) as [_ [Hfr _]].
 pose proof (B.set_elements_supported (proj1 (proj2 (proj2 (proj2 Hfr))))) as Htargets.
 exact (proj1 (Forall_forall _ _) Htargets).
Qed.
End EvaluationQueue.

Module EvaluationReads.
Lemma materialized_before support tf before after target :
 List.In target support -> N.next_config tf before=Some after ->
 MaterializationBudget.credit support (R.cfg_state after)=MaterializationBudget.credit support (R.cfg_state before) ->
 R.is_materialized (R.cfg_state after) target=true ->
 R.is_materialized (R.cfg_state before) target=true.
Proof.
 intros Hin Hstep Heq Hafter.
 destruct (R.is_materialized (R.cfg_state before) target) eqn:Hbefore;[reflexivity |].
 pose proof (@MaterializationBudget.strict support (R.cfg_state before) (R.cfg_state after) target
 (proj1 (@next_materialized tf before after Hstep)) Hin Hbefore Hafter). lia.
Qed.
Lemma get_materializes st fr target next next_fr value :
 R.complete_get st fr target=(next,next_fr,value) -> R.is_materialized next target=true.
Proof.
 unfold R.complete_get. intro Hget. inversion Hget;subst.
 apply MaterializationBudget.materialize_here.
Qed.
Lemma observed_materialized st target :
 R.is_materialized (R.observe st target) target=R.is_materialized st target.
Proof. unfold R.observe. destruct R.Ranking.observe. reflexivity. Qed.
Lemma get_queue support tf st fr target body k after :
 List.In target support ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target body) k|}=Some after ->
 MaterializationBudget.credit support (R.cfg_state after)=MaterializationBudget.credit support st ->
 R.queue (R.cfg_state after)=R.queue st.
Proof.
 intros Hin Hstep Heq. pose proof Hstep as Hactual.
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. unfold R.observe. destruct R.Ranking.observe. reflexivity.
 - destruct (R.complete_get
 (if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target)
 fr target) as [[next next_fr] value] eqn:Hg.
 inversion Hstep;subst;clear Hstep.
 assert (Hmat : R.is_materialized st target=true).
 { exact (@materialized_before support tf _ _ target Hin Hactual Heq (get_materializes Hg)). }
 assert (Hobs : R.is_materialized (R.observe st target) target=true) by (rewrite observed_materialized;exact Hmat).
 rewrite Hobs in Hg. cbn.
 rewrite (@T.complete_get_queue _ fr target next next_fr value Hg).
 unfold R.observe. destruct R.Ranking.observe. reflexivity.
Qed.
Lemma spawn_queue support tf st fr target body k after :
 List.In target support ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target body) k|}=Some after ->
 MaterializationBudget.credit support (R.cfg_state after)=MaterializationBudget.credit support st ->
 R.queue (R.cfg_state after)=R.queue st.
Proof.
 intros Hin Hstep Heq. pose proof Hstep as Hactual.
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
 - inversion Hstep;subst. unfold R.observe. destruct R.Ranking.observe. reflexivity.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target).
   + inversion Hstep;subst. unfold R.observe. destruct R.Ranking.observe. reflexivity.
   + inversion Hstep;subst.
     pose proof (@materialized_before support tf _ _ target Hin Hactual Heq
     (MaterializationBudget.materialize_here _ target)) as Hbefore.
     rewrite observed_materialized in Hmat. cbn in Hbefore. congruence.
Qed.
Theorem rhs_queue tf roots (finite : B.Sem.finite_system tf roots) st fr body k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=Some after ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state after)=
 MaterializationBudget.credit (B.Sem.support finite) st ->
 R.queue (R.cfg_state after)=R.queue st.
Proof.
 intros Hreach Hstep Heq.
 destruct (Support.reachable finite Hreach) as [_ [_ [Hbody _]]].
 destruct body as [direct|target body|target raw body|target body].
 - inversion Hstep;subst;reflexivity.
 - eapply (@get_queue (B.Sem.support finite) tf st fr target body k after);[inversion Hbody;assumption |exact Hstep |exact Heq].
 - inversion Hstep;subst. unfold R.observe. destruct R.Ranking.observe. reflexivity.
 - eapply (@spawn_queue (B.Sem.support finite) tf st fr target body k after);[inversion Hbody;assumption |exact Hstep |exact Heq].
Qed.
End EvaluationReads.

Module EvaluationPrefix.
Inductive frontier owner : R.config -> Prop :=
| rhs : forall st fr body k,R.frame_owner fr=owner ->
 frontier owner {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
| dead : forall st fr direct pending k,R.frame_owner fr=owner ->
 frontier owner {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}
| commit : forall st fr direct k,R.frame_owner fr=owner ->
 frontier owner {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
| fresh : forall st target k,R.is_materialized st target=false ->
 frontier owner {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode target k|}.
Lemma rhs_frontier tf st fr body k after :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=Some after ->
 frontier (R.frame_owner fr) after.
Proof.
 intro Hstep. destruct body as [direct|target body|target raw body|target body].
 - inversion Hstep;subst. apply dead;reflexivity.
 - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
   destruct (negb (R.is_materialized (R.observe st target) target) &&
   R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool eqn:Hg.
   + inversion Hstep;subst. apply fresh. apply Bool.andb_true_iff in Hg.
     apply Bool.negb_true_iff, (proj1 Hg).
   + destruct (R.complete_get
     (if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target)
     fr target) as [[next next_fr] value] eqn:Hget.
     inversion Hstep;subst. apply rhs. eapply B.complete_get_owner;exact Hget.
 - cbn -[R.observe R.record_side_input] in Hstep.
   destruct (R.record_side_input fr target raw) as [next_fr input] eqn:Hr.
   inversion Hstep;subst. apply rhs. eapply B.record_side_input_owner;exact Hr.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st target) target) eqn:Hmat.
   + inversion Hstep;subst. apply rhs;reflexivity.
   + destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
     inversion Hstep;subst;[apply fresh;exact Hmat |apply rhs;reflexivity].
Qed.
Lemma fresh_cannot_stutter tf roots (finite : B.Sem.finite_system tf roots) st target k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode target k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode target k|}=Some after ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state after)=MaterializationBudget.credit (B.Sem.support finite) st ->
 R.is_materialized st target=false -> False.
Proof.
 intros Hreach Hstep Heq Hfresh.
 destruct (Support.reachable finite Hreach) as [_ [Hin _]].
 pose proof (@EvaluationReads.materialized_before (B.Sem.support finite) tf _ _ target Hin Hstep Heq
 (MaterializationBudget.start_materializes Hstep)) as Hmat.
 cbn in Hmat. congruence.
Qed.
Theorem stable_step tf roots (finite : B.Sem.finite_system tf roots) owner before after :
 N.steps tf (R.initial_config roots) before ->
 frontier owner before -> T.owner_commitb owner before=false ->
 N.next_config tf before=Some after ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state after)=
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state before) ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state after) owner=
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state before) owner ->
 frontier owner after /\ R.queue (R.cfg_state after)=R.queue (R.cfg_state before).
Proof.
 intros Hreach Hfront Hnot Hstep Hmat Hsource. destruct Hfront.
 - subst owner. split;[eapply rhs_frontier;exact Hstep |].
   eapply EvaluationReads.rhs_queue;[exact Hreach |exact Hstep |exact Hmat].
 - subst owner. destruct pending as [|target rest].
   + split.
     * inversion Hstep;subst. apply commit;reflexivity.
     * eapply EvaluationQueue.reachable_publication_queue;[exact Hreach |exact Hstep |exact Hsource].
   + destruct (@EvaluationQueue.reachable_dead_queue tf roots finite st fr direct target rest k after Hreach Hstep Hsource)
     as [Hqueue Hcontrol]. split;[ |exact Hqueue].
     destruct after as [next ctrl]. cbn in Hcontrol. subst ctrl. apply dead;reflexivity.
 - unfold T.owner_commitb in Hnot. cbn in Hnot. rewrite H in Hnot.
   destruct (V.eq_dec owner owner);[discriminate |contradiction].
 - exfalso. eapply fresh_cannot_stutter;[exact Hreach |exact Hstep |exact Hmat |exact H].
Qed.
Inductive until_commit tf owner : R.config -> R.config -> Prop :=
| until_here : forall c,T.owner_commitb owner c=true -> until_commit tf owner c c
| until_next : forall first next last,T.owner_commitb owner first=false ->
 N.next_config tf first=Some next -> until_commit tf owner next last ->
 until_commit tf owner first last.
Lemma execution tf owner first last :
 until_commit tf owner first last -> N.steps tf first last.
Proof. intro Hsteps. induction Hsteps;[constructor |econstructor;eassumption]. Qed.
Lemma final_commit tf owner first last :
 until_commit tf owner first last -> T.owner_commitb owner last=true.
Proof. intro Hsteps. induction Hsteps;assumption. Qed.
Theorem stable_queue tf roots (finite : B.Sem.finite_system tf roots) owner first last count :
 until_commit tf owner first last ->
 SourceCredit.active_steps (B.Sem.support finite) tf owner first last count ->
 N.steps tf (R.initial_config roots) first -> frontier owner first ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state first) ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) owner=
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state first) owner ->
 R.queue (R.cfg_state last)=R.queue (R.cfg_state first).
Proof.
 intro Huntil. revert count. induction Huntil;intros count Hactive Hreach Hfront Hmat Hsource;[reflexivity |].
 inversion Hactive as [|first' next' last' count' Hnext Hcontains Htail];subst;[reflexivity |].
 assert (Heq : next'=next) by (rewrite H0 in Hnext;inversion Hnext;reflexivity). subst next'.
 assert (Hr : N.steps tf (R.initial_config roots) next) by (eapply Episodes.reached;eassumption).
 pose proof (@SourceCredit.step_nonincreasing (B.Sem.support finite) tf roots first next owner Hreach Hcontains H0) as Hshead.
 pose proof (@SourceCredit.active_bound (B.Sem.support finite) tf roots owner next last count' Htail Hr) as Hstail.
 pose proof (@MaterializationBudget.steps_nonincreasing (B.Sem.support finite) tf first next (@Episodes.one tf first next H0)) as Hmhead.
 pose proof (@MaterializationBudget.steps_nonincreasing (B.Sem.support finite) tf next last (SourceCredit.active_execution Htail)) as Hmtail.
 assert (Hm : MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state next)=
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state first)) by lia.
 assert (Hs : SourceCredit.credit (B.Sem.support finite) (R.cfg_state next) owner=
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state first) owner) by lia.
 destruct (@stable_step tf roots finite owner first next Hreach Hfront H H0 Hm Hs) as [Hfront' Hqueue].
 rewrite <- Hqueue. eapply IHHuntil;[exact Htail |exact Hr |exact Hfront' |lia |lia].
Qed.
Corollary clean_commit tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k last count :
 until_commit tf (R.frame_owner fr) {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);
 R.cfg_control:=R.RunRhs fr body k|} last ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);R.cfg_control:=R.RunRhs fr body k|} last count ->
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);R.cfg_control:=R.RunRhs fr body k|} ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=
 MaterializationBudget.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) (R.frame_owner fr) ->
 R.queue_contains (R.frame_owner fr) (R.queue (R.cfg_state last))=false.
Proof.
 intros Huntil Hactive Hreach Hmat Hsource.
 pose proof (@stable_queue tf roots finite (R.frame_owner fr) _ last count Huntil Hactive Hreach
 (rhs _ fr body k eq_refl) Hmat Hsource) as Hqueue.
 rewrite Hqueue. apply B.queue_contains_false. apply P.clear_owner_not_queued.
Qed.
Theorem queued_commit_paid tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k last count :
 until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);R.cfg_control:=R.RunRhs fr body k|} last ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);R.cfg_control:=R.RunRhs fr body k|} last count ->
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=P.clear_owner st (R.frame_owner fr);R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue (R.cfg_state last))=true ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)<
 MaterializationBudget.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) \/
 (MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=
 MaterializationBudget.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) /\
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr)<
 SourceCredit.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) (R.frame_owner fr)).
Proof.
 intros Huntil Hactive Hreach Hqueued.
 pose proof (@MaterializationBudget.steps_nonincreasing (B.Sem.support finite) tf _ last (execution Huntil)) as Hmle.
 pose proof (@SourceCredit.active_bound (B.Sem.support finite) tf roots (R.frame_owner fr) _ last count Hactive Hreach) as Hsle.
 cbn -[MaterializationBudget.credit SourceCredit.credit] in Hmle,Hsle.
 destruct (Nat.lt_ge_cases
 (MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last))
 (MaterializationBudget.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)))) as [Hm|Hm];[now left |].
 assert (Hmeq : MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=
 MaterializationBudget.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr))) by lia.
 right. split;[exact Hmeq |].
 destruct (Nat.lt_ge_cases
 (SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr))
 (SourceCredit.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) (R.frame_owner fr))) as [Hs|Hs];[exact Hs |].
 assert (Hseq : SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) (P.clear_owner st (R.frame_owner fr)) (R.frame_owner fr)) by lia.
 pose proof (@clean_commit tf roots finite st fr body k last count Huntil Hactive Hreach Hmeq Hseq).
 congruence.
Qed.
End EvaluationPrefix.

(** Before the first owner commit, its continuation can contain pending
    reads, spawns, or dead-side work, but no drain of that owner. *)
Module FirstCommit.
Fixpoint stack owner base k : Prop :=
 match k with
 | R.KLoop | R.KSeedLoop _ => False
 | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest
 | R.KAfterSpawn fr _ rest | R.KDead fr _ _ rest =>
   (R.frame_owner fr=owner /\ rest=base) \/ stack owner base rest
 | R.KDrain _ rest => stack owner base rest
 end.
Definition context owner base control : Prop :=
 match control with
 | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k =>
   (R.frame_owner fr=owner /\ k=base) \/ stack owner base k
 | R.StartEpisode _ k | R.RunDrain _ k | R.Return k => stack owner base k
 | _ => False
 end.
Lemma stack_contains owner base k :
 stack owner base k -> T.continuation_contains owner k.
Proof.
 induction k;cbn;intro H;try contradiction.
 all: try (destruct H as [[Howner Hbase]|H];[left;congruence |right;apply IHk,H]).
 right. apply IHk,H.
Qed.
Lemma contains owner base ctrl : context owner base ctrl -> T.control_contains owner ctrl.
Proof.
 destruct ctrl;cbn;intro H;try contradiction.
 all: try (destruct H as [[Howner Hbase]|H];[left;congruence |right;eapply stack_contains;exact H]).
 - right. eapply stack_contains;exact H.
 - right. eapply stack_contains;exact H.
 - eapply stack_contains;exact H.
Qed.
Lemma rhs_step tf st fr body k after owner base :
 context owner base (R.RunRhs fr body k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=Some after ->
 context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hstep. destruct body as [direct|target body|target raw body|target body].
 - inversion Hstep;subst;exact Hcontext.
 - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
   destruct (negb (R.is_materialized (R.observe st target) target) &&
   R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
   + inversion Hstep;subst;exact Hcontext.
   + destruct (R.complete_get
     (if R.is_materialized (R.observe st target) target then R.observe st target else R.enqueue (R.observe st target) target)
     fr target) as [[next next_fr] value] eqn:Hg.
     inversion Hstep;subst. cbn [R.cfg_control context].
     rewrite (@B.complete_get_owner _ fr target next next_fr value Hg). exact Hcontext.
 - cbn -[R.observe R.record_side_input] in Hstep.
   destruct (R.record_side_input fr target raw) as [next_fr input] eqn:Hr.
   inversion Hstep;subst. cbn [R.cfg_control context].
   rewrite (@B.record_side_input_owner fr target raw next_fr input Hr). exact Hcontext.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st target) target);
   [inversion Hstep;subst;exact Hcontext |].
   destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;exact Hcontext.
Qed.
Lemma dead_step tf st fr direct pending k after owner base :
 context owner base (R.RunDead fr direct pending k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hstep. destruct pending as [|target rest].
 - inversion Hstep;subst;exact Hcontext.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hcontext |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed].
   unfold R.continue_dead in Hstep.
   destruct changed;[destruct (_ && _)%bool |];inversion Hstep;subst;exact Hcontext.
Qed.
Lemma commit_step tf st fr direct k after owner base :
 context owner base (R.RunCommit fr direct k) ->
 T.owner_commitb owner {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=false ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=Some after ->
 context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hnot Hstep.
 assert (Hstack : stack owner base k).
 { destruct Hcontext as [[Howner Hk]|Hstack];[ |exact Hstack].
   unfold T.owner_commitb in Hnot. cbn in Hnot. rewrite Howner in Hnot.
   destruct (V.eq_dec owner owner);[discriminate |contradiction]. }
 cbn -[P.pending_above P.suspend_commit P.retry_current R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|].
 - inversion Hstep;subst. right;exact Hstack.
 - destruct (R.queue_contains (R.frame_owner fr) (R.queue st)).
   + inversion Hstep;subst. right;exact Hstack.
   + destruct (R.set_value st fr direct) as [next next_fr]. inversion Hstep;subst;exact Hstack.
Qed.
Lemma drain_step tf st fr k after owner base :
 context owner base (R.RunDrain fr k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=Some after ->
 context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hstep.
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame] in Hstep.
 destruct (R.queue_peek (R.queue st)) as [target|];[ |inversion Hstep;subst;exact Hcontext].
 destruct (V.eq_dec target (R.frame_owner fr)).
 - destruct (R.queue_pop (R.queue st)) as [[head tail]|];[ |discriminate].
   inversion Hstep;subst. right;exact Hcontext.
 - destruct (R.rank_lt st (R.frame_owner fr) target).
   + destruct (R.queue_pop (R.queue st)) as [[head tail]|];[ |discriminate].
     inversion Hstep;subst;exact Hcontext.
   + inversion Hstep;subst;exact Hcontext.
Qed.
Lemma return_step tf st k after owner base :
 context owner base (R.Return k) ->
 C.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}=Some after ->
 context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hstep. destruct k;try contradiction.
 - cbn -[R.complete_get] in Hstep.
   destruct (R.complete_get st f t) as [[next next_fr] value] eqn:Hg.
   inversion Hstep;subst. cbn [R.cfg_control context].
   rewrite (@B.complete_get_owner st f t next next_fr value Hg). exact Hcontext.
 - inversion Hstep;subst;exact Hcontext.
 - inversion Hstep;subst;exact Hcontext.
 - inversion Hstep;subst;exact Hcontext.
 - inversion Hstep;subst;exact Hcontext.
Qed.
Theorem next_context tf before after owner base :
 context owner base (R.cfg_control before) -> T.owner_commitb owner before=false ->
 N.next_config tf before=Some after -> context owner base (R.cfg_control after).
Proof.
 intros Hcontext Hnot Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [cont [target [rest [-> [Hp ->]]]]]]]]].
 2: { exact Hcontext. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;try contradiction.

 - inversion Hstep;subst. right;exact Hcontext.
 - eapply rhs_step;[exact Hcontext |exact Hstep].
 - eapply dead_step;[exact Hcontext |exact Hstep].
 - eapply commit_step;[exact Hcontext |exact Hnot |exact Hstep].
 - eapply drain_step;[exact Hcontext |exact Hstep].
 - eapply return_step;[exact Hcontext |exact Hstep].
Qed.
Lemma extract tf owner first last :
 N.steps tf first last -> T.owner_commitb owner last=true ->
 exists found,EvaluationPrefix.until_commit tf owner first found /\ N.steps tf found last.
Proof.
 intro Hsteps. induction Hsteps;intro Hlast.
 - exists c. split;[constructor;exact Hlast |constructor].
 - destruct (T.owner_commitb owner first) eqn:Hfirst.
   + exists first. split;[constructor;exact Hfirst |econstructor;eassumption].
   + destruct (IHHsteps Hlast) as [found [Huntil Htail]].
     exists found. split;[econstructor;eassumption |exact Htail].
Qed.
Theorem active support tf owner base first last :
 EvaluationPrefix.until_commit tf owner first last ->
 context owner base (R.cfg_control first) ->
 exists count,SourceCredit.active_steps support tf owner first last count /\
 context owner base (R.cfg_control last).
Proof.
 intro Huntil. induction Huntil;intro Hcontext.
 - exists 0. split;[constructor |exact Hcontext].
 - pose proof (@next_context tf first next owner base Hcontext H H0) as Hnext.
   destruct (IHHuntil Hnext) as [count [Hactive Hlast]].
   exists (SourceCredit.charge support owner first next+count). split;[ |exact Hlast].
   econstructor;[exact H0 |eapply contains;exact Hnext |exact Hactive].
Qed.
Lemma commit_base st fr direct k owner base :
 context owner base (R.RunCommit fr direct k) -> R.frame_owner fr=owner ->
 T.control_ordered st (R.RunCommit fr direct k) -> k=base.
Proof.
 intros [[Hlocal Hbase]|Hstack] Howner Ho;[exact Hbase |].
 pose proof (@T.continuation_contains_below st (R.frame_owner fr) k owner Ho
 (@stack_contains owner base k Hstack)) as Hlt.
 rewrite Howner in Hlt. exact (False_ind _ ((@B.rank_lt_true_neq_correctness st owner owner Hlt) eq_refl)).
Qed.
Theorem rhs_first_commit support tf roots st fr body k :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 exists next next_fr direct count,R.frame_owner next_fr=R.frame_owner fr /\
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} /\
 SourceCredit.active_steps support tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} count.
Proof.
 intros Hchildren Hreach.
 destruct (@Episodes.rhs_reaches_commit tf roots (R.frame_owner fr) body st fr k eq_refl Hchildren Hreach)
 as [done [done_fr [value [Howner Hsteps]]]].
 assert (Hlast : T.owner_commitb (R.frame_owner fr)
 {|R.cfg_state:=done;R.cfg_control:=R.RunCommit done_fr value k|}=true).
 { unfold T.owner_commitb;cbn. rewrite Howner. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));congruence. }
 destruct (extract (R.frame_owner fr) Hsteps Hlast) as [found [Huntil Htail]].
 destruct (@active support tf (R.frame_owner fr) k _ found Huntil (or_introl (conj eq_refl eq_refl)))
 as [count [Hactive Hcontext]].
 pose proof (EvaluationPrefix.final_commit Huntil) as Hcommit.
 assert (Hfound : N.steps tf (R.initial_config roots) found).
 { eapply steps_append;[exact Hreach |eapply EvaluationPrefix.execution;exact Huntil]. }
 pose proof (proj1 (reachable_history Hfound)) as Ho.
 destruct found as [next ctrl]. destruct ctrl;try discriminate Hcommit.
 unfold T.owner_commitb;cbn in Hcommit.
 destruct (V.eq_dec (R.frame_owner f) (R.frame_owner fr)) as [Heq|Hneq];[ |discriminate].
 assert (Hbase : c=k) by (eapply commit_base;[exact Hcontext |exact Heq |exact Ho]). subst c.
 exists next,f,t,count. repeat split;assumption.
Qed.
End FirstCommit.

Module RoundAccounts.
Definition evaluation_payment support owner before after :=
 MaterializationBudget.credit support after<MaterializationBudget.credit support before \/
 (MaterializationBudget.credit support after=MaterializationBudget.credit support before /\
 SourceCredit.credit support after owner<SourceCredit.credit support before owner).
Lemma queued_paid tf roots (finite : B.Sem.finite_system tf roots) st fr body k last count :
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 R.queue_contains (R.frame_owner fr) (R.queue (R.cfg_state last))=true ->
 evaluation_payment (B.Sem.support finite) (R.frame_owner fr) st (R.cfg_state last).
Proof.
 intros Huntil Hactive Hreach Hclean Hqueued.
 pose proof (@MaterializationBudget.steps_nonincreasing (B.Sem.support finite) tf _ last
 (EvaluationPrefix.execution Huntil)) as Hmle.
 pose proof (@SourceCredit.active_bound (B.Sem.support finite) tf roots (R.frame_owner fr) _ last count Hactive Hreach) as Hsle.
 cbn -[MaterializationBudget.credit SourceCredit.credit] in Hmle,Hsle.
 unfold evaluation_payment.
 destruct (Nat.lt_ge_cases
 (MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last))
 (MaterializationBudget.credit (B.Sem.support finite) st)) as [Hm|Hm];[now left |].
 assert (Hmeq : MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=
 MaterializationBudget.credit (B.Sem.support finite) st) by lia.
 right. split;[exact Hmeq |].
 destruct (Nat.lt_ge_cases
 (SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr))
 (SourceCredit.credit (B.Sem.support finite) st (R.frame_owner fr))) as [Hs|Hs];[exact Hs |].
 assert (Hseq : SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) st (R.frame_owner fr)) by lia.
 pose proof (@EvaluationPrefix.stable_queue tf roots finite (R.frame_owner fr) _ last count Huntil Hactive Hreach
 (EvaluationPrefix.rhs st fr body k eq_refl) Hmeq Hseq) as Hqueue.
 cbn -[R.queue] in Hqueue. rewrite Hqueue,Hclean in Hqueued. discriminate.
Qed.
Theorem first_commit_accounted tf roots (finite : B.Sem.finite_system tf roots) st fr body k :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 exists next next_fr direct count,R.frame_owner next_fr=R.frame_owner fr /\
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} /\
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} count /\
 (R.queue_contains (R.frame_owner fr) (R.queue next)=false \/
 evaluation_payment (B.Sem.support finite) (R.frame_owner fr) st next).
Proof.
 intros Hchildren Hreach Hclean.
 destruct (@FirstCommit.rhs_first_commit (B.Sem.support finite) tf roots st fr body k Hchildren Hreach)
 as [next [next_fr [direct [count [Howner [Huntil Hactive]]]]]].
 exists next,next_fr,direct,count. split;[exact Howner |]. split;[exact Huntil |].
 split;[exact Hactive |]. destruct (R.queue_contains (R.frame_owner fr) (R.queue next)) eqn:Hqueued;[ |now left].
 right. exact (@queued_paid tf roots finite st fr body k
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} count Huntil Hactive Hreach Hclean Hqueued).
Qed.
Lemma pending_entry_extends before after owner target :
 B.rank_extends before after -> B.ranked before owner -> B.ranked before target ->
 PendingBudget.entry after owner target=PendingBudget.entry before owner target.
Proof.
 intros Hextends Howner Htarget. unfold PendingBudget.entry.
 rewrite <- (@B.rank_lt_stable before after owner target Hextends Howner Htarget).
 destruct Htarget as [rank Hrank]. rewrite Hrank,(Hextends target rank Hrank). reflexivity.
Qed.
Lemma pending_total_extends before after owner pending :
 B.rank_extends before after -> B.ranked before owner ->
 (forall target,List.In target pending -> B.ranked before target) ->
 PendingBudget.total after owner pending=PendingBudget.total before owner pending.
Proof.
 intros Hextends Howner. induction pending as [|target rest IH];intro Hqueue;[reflexivity |].
 cbn. rewrite (@pending_entry_extends before after owner target Hextends Howner (Hqueue target (or_introl eq_refl))).
 f_equal. apply IH. intros x Hx;apply Hqueue;right;exact Hx.
Qed.
Lemma pending_queue_extends before after owner :
 B.rank_extends before after -> B.ranked before owner -> B.queue_ranked before ->
 R.queue after=R.queue before -> PendingBudget.credit after owner=PendingBudget.credit before owner.
Proof.
 intros Hextends Howner Hqueue Heq. unfold PendingBudget.credit. rewrite Heq.
 apply pending_total_extends;assumption.
Qed.
Theorem stable_pending tf roots (finite : B.Sem.finite_system tf roots) st fr body k last count :
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 MaterializationBudget.credit (B.Sem.support finite) (R.cfg_state last)=MaterializationBudget.credit (B.Sem.support finite) st ->
 SourceCredit.credit (B.Sem.support finite) (R.cfg_state last) (R.frame_owner fr)=
 SourceCredit.credit (B.Sem.support finite) st (R.frame_owner fr) ->
 PendingBudget.credit (R.cfg_state last) (R.frame_owner fr)=PendingBudget.credit st (R.frame_owner fr).
Proof.
 intros Huntil Hactive Hreach Hmat Hsource.
 pose proof (reachable_ranked Hreach) as Hr.
 eapply pending_queue_extends.
 - exact (Episodes.steps_extends (EvaluationPrefix.execution Huntil)).
 - exact (proj1 (proj1 (B.configuration_control_ranked Hr))).
 - exact (B.data_queue_ranked (B.configuration_state_data Hr)).
 - exact (@EvaluationPrefix.stable_queue tf roots finite (R.frame_owner fr) _ last count
 Huntil Hactive Hreach (EvaluationPrefix.rhs st fr body k eq_refl) Hmat Hsource).
Qed.
End RoundAccounts.

Module EpisodePath.
Definition context := T.episode_active_control.
Definition progress owner base after :=
 context owner base (R.cfg_control after) \/ R.cfg_control after=R.Return base.
Lemma base tf before after owner k :
 context owner k (R.cfg_control before) -> R.next_config tf before=Some after ->
 progress owner k after.
Proof. intros Hcontext Hstep. eapply T.episode_active_control_step;[exact Hstep |exact Hcontext]. Qed.
Lemma precommit tf before after owner k :
 context owner k (R.cfg_control before) -> P.next_config tf before=Some after ->
 progress owner k after.
Proof.
 destruct before as [st ctrl]. intros Hcontext Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base;[exact Hcontext |exact Hstep]].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. left. right. exact Hcontext.
 - eapply base;[exact Hcontext |exact Hstep].
Qed.
Lemma batched tf before after owner k :
 context owner k (R.cfg_control before) -> P.next_batched tf before=Some after ->
 progress owner k after.
Proof.
 destruct before as [st ctrl]. intros Hcontext Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit;[exact Hcontext |exact Hstep]].
 - destruct r;try solve [eapply precommit;[exact Hcontext |exact Hstep]].
   destruct (R.record_side_input f t t0) as [next_fr input] eqn:Hr.
   inversion Hstep;subst. left. cbn [R.cfg_control context T.episode_active_control].
   rewrite (@B.record_side_input_owner f t t0 next_fr input Hr). exact Hcontext.
 - destruct l;[ |eapply precommit;[exact Hcontext |exact Hstep]].
   inversion Hstep;subst. left;exact Hcontext.
Qed.
Lemma fresh tf before after owner k :
 context owner k (R.cfg_control before) -> P.next_fresh tf before=Some after ->
 progress owner k after.
Proof.
 destruct before as [st ctrl]. intros Hcontext Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched;[exact Hcontext |exact Hstep]].
 - eapply (@batched tf {|R.cfg_state:=P.clear_owner st t;R.cfg_control:=R.StartEpisode t c|} after owner k);
   [exact Hcontext |exact Hstep].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. left;right;exact Hcontext.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. left;exact Hcontext.
     * eapply batched;[exact Hcontext |exact Hstep].
 - destruct c;try solve [eapply batched;[exact Hcontext |exact Hstep]].
   eapply (@batched tf {|R.cfg_state:=P.clear_owner st (R.frame_owner f);R.cfg_control:=R.Return (R.KAfterSide f r c)|} after owner k);
   [exact Hcontext |exact Hstep].
Qed.
Lemma dead tf st fr direct pending k after owner basek :
 context owner basek (R.RunDead fr direct pending k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 progress owner basek after.
Proof.
 intros Hcontext Hstep. destruct pending as [|target rest].
 - inversion Hstep;subst;left;exact Hcontext.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;left;exact Hcontext |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed].
   unfold R.continue_dead in Hstep.
   destruct changed;[destruct (_ && _)%bool |];inversion Hstep;subst;left;try exact Hcontext.
   right;exact Hcontext.
Qed.
Theorem next tf before after owner k :
 context owner k (R.cfg_control before) -> N.next_config tf before=Some after ->
 progress owner k after.
Proof.
 intros Hcontext Hstep. destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [cont [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.EpisodePath.next tf before after owner k Hcontext Hb0).
 - left. right. exact Hcontext.
Qed.
Lemma base_absent st owner k :
 T.continuation_below st owner k -> ~T.continuation_contains owner k.
Proof.
 intros Ho Hcontains.
 pose proof (@T.continuation_contains_below st owner k owner Ho Hcontains) as Hlt.
 exact ((@B.rank_lt_true_neq_correctness st owner owner Hlt) eq_refl).
Qed.
Lemma return_inactive owner k :
 ~T.continuation_contains owner k -> ~context owner k (R.Return k).
Proof.
 intros Habsent Hcontext. apply Habsent. eapply T.continuation_above_contains;exact Hcontext.
Qed.
Lemma rhs_not_return tf st fr body k after basek :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} -> False.
Proof.
 intro Hstep. destruct body.
 - discriminate Hstep.
 - cbn -[R.observe R.complete_get R.enqueue] in Hstep.
   destruct (negb (R.is_materialized (R.observe st t) t) &&
   R.rank_lt (R.observe st t) (R.frame_owner fr) t)%bool;[discriminate |].
   destruct (R.complete_get
   (if R.is_materialized (R.observe st t) t then R.observe st t else R.enqueue (R.observe st t) t)
   fr t) as [[next next_fr] value];discriminate.
 - discriminate Hstep.
 - cbn -[R.observe R.materialize R.enqueue] in Hstep.
   destruct (R.is_materialized (R.observe st t) t);[discriminate |].
   destruct (R.rank_lt (R.observe st t) (R.frame_owner fr) t);discriminate.
Qed.
Lemma dead_not_return tf st fr direct pending k after basek :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} -> False.
Proof.
 intro Hstep. destruct pending as [|target rest];[discriminate |].
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr));[discriminate |].
 destruct (R.write_side_contribution st fr target D.bottom) as [next changed].
 unfold R.continue_dead in Hstep. destruct changed;[destruct (_ && _)%bool |];discriminate.
Qed.
Lemma commit_not_return tf st fr direct k after basek :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} -> False.
Proof.
 intro Hstep.
 cbn -[P.pending_above P.suspend_commit P.retry_current R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 destruct (R.set_value st fr direct);discriminate.
Qed.
Lemma return_not_return tf st k after basek :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} -> False.
Proof.
 intro Hstep.
 destruct (@Front.step_cases tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} Hstep)
 as [Hb0|[state [fr [body [cont [target [rest [Hbefore [Hp Hafter]]]]]]]]].
 - exact (@N.O.EpisodePath.return_not_return tf st k after basek Hb0).
 - discriminate Hafter.
Qed.
Lemma drain_return tf roots st fr k after basek :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} ->
 k=basek /\ T.queue_strictly_below (R.frame_owner fr) after.
Proof.
 intros Hreach Hstep. pose proof (reachable_ranked Hreach) as Hr.
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame] in Hstep.
 destruct (R.queue_peek (R.queue st)) as [target|] eqn:Hpeek.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + destruct (R.queue_pop (R.queue st)) as [[head tail]|];discriminate.
   + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
     * destruct (R.queue_pop (R.queue st)) as [[head tail]|];discriminate.
     * inversion Hstep;subst. split;[reflexivity |]. apply T.reset_registered_cells_below.
       eapply T.queue_peek_lower_below;[exact (B.configuration_queue_ordered Hr) |exact Hpeek |].
       eapply T.rank_lt_reverse_if_false;[exact (B.configuration_rank_valid Hr) | | |congruence |exact Hhigher].
       -- exact (proj1 (proj1 (B.configuration_control_ranked Hr))).
       -- apply (B.data_queue_ranked (B.configuration_state_data Hr)). apply T.queue_peek_member,Hpeek.
 - inversion Hstep;subst. split;[reflexivity |]. apply T.reset_registered_cells_below.
   eapply T.queue_peek_none_below;exact Hpeek.
Qed.
Theorem exit_below tf roots before after owner k :
 N.steps tf (R.initial_config roots) before ->
 context owner k (R.cfg_control before) -> ~T.continuation_contains owner k ->
 N.next_config tf before=Some {|R.cfg_state:=after;R.cfg_control:=R.Return k|} ->
 T.queue_strictly_below owner after.
Proof.
 destruct before as [st ctrl]. intros Hreach Hcontext Habsent Hstep. destruct ctrl;try contradiction.
 - discriminate Hstep.
 - exfalso. eapply rhs_not_return;exact Hstep.
 - exfalso. eapply dead_not_return;exact Hstep.
 - exfalso. eapply commit_not_return;exact Hstep.
 - destruct (@drain_return tf roots st f c after k Hreach Hstep) as [Hbase Hbelow]. subst c.
   destruct Hcontext as [[Howner Hbase]|Habove];[now rewrite <- Howner |].
   exfalso. apply Habsent. eapply T.continuation_above_contains;exact Habove.
 - exfalso. eapply return_not_return;exact Hstep.
Qed.
Inductive prefix owner basek tf : R.config -> R.config -> Prop :=
| prefix_refl : forall c,prefix owner basek tf c c
| prefix_next : forall first next last,context owner basek (R.cfg_control first) ->
 N.next_config tf first=Some next -> prefix owner basek tf next last ->
 prefix owner basek tf first last.
Lemma execution owner basek tf first last :
 prefix owner basek tf first last -> N.steps tf first last.
Proof. intro Hprefix. induction Hprefix;[constructor |econstructor;eassumption]. Qed.
Theorem first_return tf roots owner basek first done :
 N.steps tf first {|R.cfg_state:=done;R.cfg_control:=R.Return basek|} ->
 N.steps tf (R.initial_config roots) first ->
 context owner basek (R.cfg_control first) -> ~T.continuation_contains owner basek ->
 exists after,prefix owner basek tf first {|R.cfg_state:=after;R.cfg_control:=R.Return basek|} /\
 T.queue_strictly_below owner after.
Proof.
 intros Hsteps. remember {|R.cfg_state:=done;R.cfg_control:=R.Return basek|} as final eqn:Hfinal.
 revert done Hfinal. induction Hsteps;intros done Hfinal Hreach Hcontext Habsent.
 - subst c. exfalso. eapply return_inactive;[exact Habsent |exact Hcontext].
 - destruct (@next tf first next0 owner basek Hcontext H) as [Hnext|Hexit].
   + destruct (IHHsteps done Hfinal (Episodes.reached Hreach H) Hnext Habsent) as [after [Hprefix Hbelow]].
     exists after. split;[econstructor;eassumption |exact Hbelow].
   + destruct next0 as [after ctrl]. cbn in Hexit. subst ctrl.
     exists after. split.
     * econstructor;[exact Hcontext |exact H |constructor].
     * eapply exit_below;[exact Hreach |exact Hcontext |exact Habsent |exact H].
Qed.
Lemma above_ancestor owner basek k source :
 T.continuation_above owner basek k -> T.continuation_contains source basek ->
 T.continuation_contains source k.
Proof.
 induction k;cbn;intros Habove Hsource;try contradiction.
 all: destruct Habove as [[Howner Hbase]|Habove].
 all: try (subst k;right;exact Hsource).
 all: right;apply IHk;assumption.
Qed.
Lemma context_ancestor owner basek ctrl source :
 context owner basek ctrl -> T.continuation_contains source basek ->
 T.control_contains source ctrl.
Proof.
 destruct ctrl;cbn;intros Hcontext Hsource;try contradiction.
 all: try (destruct Hcontext as [[Howner Hbase]|Habove];
 [subst c;right;exact Hsource |right;eapply above_ancestor;[exact Habove |exact Hsource]]).
 eapply above_ancestor;[exact Hcontext |exact Hsource].
Qed.
Lemma active_ancestor support tf owner basek first last source :
 prefix owner basek tf first last -> T.continuation_contains source basek ->
 T.control_contains source (R.cfg_control last) ->
 exists count,SourceCredit.active_steps support tf source first last count.
Proof.
 intro Hprefix. induction Hprefix as [c|first middle last Hcontext Hstep Htail IH];intros Hsource Hend.
 - exists 0;constructor.
 - destruct (IH Hsource Hend) as [count Hactive].
   assert (Hmiddle : T.control_contains source (R.cfg_control middle)).
   { destruct Htail;[exact Hend |eapply context_ancestor;[exact H |exact Hsource]]. }
   exists (SourceCredit.charge support source first middle+count).
   econstructor;[exact Hstep |exact Hmiddle |exact Hactive].
Qed.
Theorem child_segment support tf roots st owner k done source :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|} ->
 N.steps tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}
 {|R.cfg_state:=done;R.cfg_control:=R.Return k|} ->
 T.continuation_contains source k ->
 exists after count,
 prefix owner k tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}
 {|R.cfg_state:=after;R.cfg_control:=R.Return k|} /\
 SourceCredit.active_steps support tf source
 {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}
 {|R.cfg_state:=after;R.cfg_control:=R.Return k|} count /\
 T.queue_strictly_below owner after.
Proof.
 intros Hreach Hsteps Hsource.
 pose proof (proj1 (reachable_history Hreach)) as Ho.
 destruct (@first_return tf roots owner k _ done Hsteps Hreach
 (or_introl (conj eq_refl eq_refl)) (@base_absent st owner k Ho)) as [after [Hprefix Hbelow]].
 destruct (@active_ancestor support tf owner k _ _ source Hprefix Hsource Hsource) as [count Hactive].
 exists after,count. split;[exact Hprefix |]. split;assumption.
Qed.
End EpisodePath.

Module ActiveAccounts.
Lemma one support tf owner before after :
 N.next_config tf before=Some after -> T.control_contains owner (R.cfg_control after) ->
 SourceCredit.active_steps support tf owner before after (SourceCredit.charge support owner before after).
Proof.
 intros Hstep Hcontains. rewrite <- (Nat.add_0_r (SourceCredit.charge support owner before after)).
 econstructor;[exact Hstep |exact Hcontains |constructor].
Qed.
Lemma append support tf owner first middle last count1 count2 :
 SourceCredit.active_steps support tf owner first middle count1 ->
 SourceCredit.active_steps support tf owner middle last count2 ->
 SourceCredit.active_steps support tf owner first last (count1+count2).
Proof.
 intro Hfirst. induction Hfirst;intro Hlast;[exact Hlast |].
 rewrite <- Nat.add_assoc. econstructor;[exact H |exact H0 |apply IHHfirst,Hlast].
Qed.
Lemma incoming trace_support support tf owner first last count :
 SourceCredit.active_steps trace_support tf owner first last count ->
 exists incoming_count,TargetCredit.active_steps support tf owner first last incoming_count.
Proof.
 intro Hactive. induction Hactive.
 - exists 0;constructor.
 - destruct IHHactive as [n Htail].
   exists (TargetCredit.charge support owner first next+n).
   econstructor;[exact H |exact H0 |exact Htail].
Qed.
Lemma ordinary support tf owner first last count :
 SourceCredit.active_steps support tf owner first last count ->
 exists ordinary_count,OrdinaryCredit.active_steps tf owner first last ordinary_count.
Proof.
 intro Hactive. induction Hactive.
 - exists 0;constructor.
 - destruct IHHactive as [n Htail].
   exists (OrdinaryCredit.charge first next owner+n).
   econstructor;[exact H |exact H0 |exact Htail].
Qed.
Lemma incoming_nonincreasing trace_support support tf roots owner first last count :
 SourceCredit.active_steps trace_support tf owner first last count ->
 N.steps tf (R.initial_config roots) first ->
 TargetCredit.credit support (R.cfg_state last) owner<=TargetCredit.credit support (R.cfg_state first) owner.
Proof.
 intros Hactive Hreach. destruct (@incoming trace_support support tf owner first last count Hactive) as [n Hincoming].
 pose proof (@TargetCredit.active_bound support tf roots owner first last n Hincoming Hreach). lia.
Qed.
Lemma ordinary_nonincreasing support tf roots owner first last count fr :
 SourceCredit.active_steps support tf owner first last count ->
 N.steps tf (R.initial_config roots) first ->
 S.mem owner (R.controlled (R.cfg_state first))=true ->
 T.control_frame owner (R.cfg_control first)=Some fr ->
 OrdinaryCredit.credit last owner<=OrdinaryCredit.credit first owner.
Proof.
 intros Hactive Hreach Hcontrolled Hframe.
 destruct (ordinary Hactive) as [n Hordinary].
 pose proof (@OrdinaryCredit.active_bound tf roots owner first last n Hordinary fr Hreach Hcontrolled Hframe). lia.
Qed.
End ActiveAccounts.
Module HigherRetry.
Definition resumed tf saved current fr k :=
 {|R.cfg_state:=P.clear_owner current (R.frame_owner fr);
 R.cfg_control:=R.RunRhs (R.fresh_frame saved (R.frame_owner fr) (R.frame_phase fr))
 (tf (R.frame_owner fr)) k|}.
Definition returned tf saved current owner phase k :=
 {|R.cfg_state:=current;R.cfg_control:=R.Return
 (R.KAfterSide (R.fresh_frame saved owner phase) (tf owner) k)|}.

Lemma child_decreases tf st owner target rest k done :
 P.pending_above st owner=Some (target,rest) ->
 N.steps tf {|R.cfg_state:=R.with_queue st rest;R.cfg_control:=R.StartEpisode target k|}
 {|R.cfg_state:=done;R.cfg_control:=R.Return k|} ->
 T.queue_strictly_below target done ->
 PendingBudget.credit done owner<PendingBudget.credit st owner.
Proof.
 intros Hp Hsteps Hbelow.
 pose proof (@P.pending_above_spec st owner target rest Hp) as [_ [_ Hhigher]].
 unfold R.rank_lt,R.ranking_lt in Hhigher.
 destruct (R.Ranking.lookup (R.ranking st) owner);[|discriminate].
 destruct (R.Ranking.lookup (R.ranking st) target) as [rank|] eqn:Hrank;[|discriminate].
 pose proof (Episodes.steps_extends Hsteps) as Hextends.
 assert (Hrank' : R.Ranking.lookup (R.ranking done) target=Some rank)
 by (exact (Hextends target rank Hrank)).
 pose proof (@PendingBudget.below done owner target rank Hbelow Hrank').
 pose proof (@PendingBudget.pending_strict st owner target rest rank Hp Hrank). lia.
Qed.

Lemma ready support tf saved st owner phase k :
 P.pending_above st owner=None ->
 SourceCredit.active_steps support tf owner
 (returned tf saved st owner phase k)
 (resumed tf saved st (R.fresh_frame saved owner phase) k)
 (SourceCredit.charge support owner (returned tf saved st owner phase k)
 (resumed tf saved st (R.fresh_frame saved owner phase) k)).
Proof.
 intro Hp. apply ActiveAccounts.one;[ |left;reflexivity].
 unfold returned. rewrite N.resume_ready;[reflexivity |exact Hp].
Qed.

Lemma drain support tf roots owner phase k :
 Episodes.children tf roots owner ->
 forall budget saved st,PendingBudget.credit st owner=budget ->
 N.steps tf (R.initial_config roots) (returned tf saved st owner phase k) ->
 exists final_saved done count,
 SourceCredit.active_steps support tf owner (returned tf saved st owner phase k)
 (resumed tf final_saved done (R.fresh_frame saved owner phase) k) count /\
 PendingBudget.credit done owner<=PendingBudget.credit st owner.
Proof.
 intros Hchildren budget. induction budget as [budget IH] using (well_founded_induction Nat.lt_wf_0).
 intros saved st Hbudget Hreach.
 destruct (P.pending_above st owner) as [[target rest]|] eqn:Hp.
 - assert (Hstep : N.next_config tf (returned tf saved st owner phase k)=
   Some (P.suspend_commit tf st (R.fresh_frame saved owner phase) k target rest)).
   { apply N.resume_higher. exact Hp. }
   pose proof (@P.pending_above_spec st owner target rest Hp) as [_ [_ Hhigher]].
   pose proof (Episodes.reached Hreach Hstep) as Hchild.
   destruct (Hchildren (R.with_queue st rest) target
   (R.KAfterSide (R.fresh_frame st owner phase) (tf owner) k) Hhigher Hchild)
   as [candidate [Hcomplete Hbelow]].
   destruct (@EpisodePath.child_segment support tf roots (R.with_queue st rest) target
   (R.KAfterSide (R.fresh_frame st owner phase) (tf owner) k) candidate owner
   Hchild Hcomplete (or_introl eq_refl))
   as [middle [n [Hprefix [Hactive Hmiddle]]]].
   pose proof (@child_decreases tf st owner target rest _ middle Hp
   (EpisodePath.execution Hprefix) Hmiddle) as Hlt.
   assert (Hmiddle_reach : N.steps tf (R.initial_config roots)
     (returned tf st middle owner phase k)).
   { eapply steps_append;[exact Hchild |exact (SourceCredit.active_execution Hactive)]. }
   destruct (IH (PendingBudget.credit middle owner) (eq_ind _ (fun b => PendingBudget.credit middle owner < b) Hlt _ Hbudget)
   st middle eq_refl Hmiddle_reach) as [final_saved [done [m [Htail Hbound]]]].
   exists final_saved,done,(SourceCredit.charge support owner
   (returned tf saved st owner phase k)
   (P.suspend_commit tf st (R.fresh_frame saved owner phase) k target rest)+(n+m)).
   split;[ |lia]. econstructor;[exact Hstep |right;left;reflexivity |].
   eapply ActiveAccounts.append;[exact Hactive |exact Htail].
 - exists saved,st,(SourceCredit.charge support owner (returned tf saved st owner phase k)
   (resumed tf saved st (R.fresh_frame saved owner phase) k)).
   split;[apply ready,Hp |lia].
Qed.

Theorem segment support tf roots st fr direct k target rest :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 exists saved done count,
 SourceCredit.active_steps support tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} (resumed tf saved done fr k) count /\
 PendingBudget.credit (P.clear_owner done (R.frame_owner fr)) (R.frame_owner fr)<
 PendingBudget.credit st (R.frame_owner fr).
Proof.
 intros Hchildren Hreach Hp.
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some (P.suspend_commit tf st fr k target rest)).
 { cbn -[P.pending_above P.suspend_commit P.next_batched P.retry_current]. now rewrite Hp. }
 pose proof (@P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [_ Hhigher]].
 pose proof (Episodes.reached Hreach Hstep) as Hchild.
 destruct (Hchildren (R.with_queue st rest) target
 (R.KAfterSide (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)
 Hhigher Hchild) as [candidate [Hcomplete Hbelow]].
 destruct (@EpisodePath.child_segment support tf roots (R.with_queue st rest) target
 (R.KAfterSide (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k)
 candidate (R.frame_owner fr) Hchild Hcomplete (or_introl eq_refl))
 as [middle [n [Hprefix [Hactive Hmiddle]]]].
 pose proof (@child_decreases tf st (R.frame_owner fr) target rest _ middle Hp
 (EpisodePath.execution Hprefix) Hmiddle) as Hlt.
 assert (Hmiddle_reach : N.steps tf (R.initial_config roots)
 (returned tf st middle (R.frame_owner fr) (R.frame_phase fr) k)).
 { eapply steps_append;[exact Hchild |exact (SourceCredit.active_execution Hactive)]. }
 destruct (@drain support tf roots (R.frame_owner fr) (R.frame_phase fr) k Hchildren
 _ st middle eq_refl Hmiddle_reach) as [saved [done [m [Htail Hbound]]]].
 exists saved,done,(SourceCredit.charge support (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
 (P.suspend_commit tf st fr k target rest)+(n+m)).
 split.
 - econstructor;[exact Hstep |right;left;reflexivity |].
   eapply ActiveAccounts.append;[exact Hactive |exact Htail].
 - pose proof (PendingBudget.clear done (R.frame_owner fr)). lia.
Qed.
End HigherRetry.

Module RetryMeasure.
Definition vector support owner c :=
 (MaterializationBudget.credit support (R.cfg_state c),
 (T.promotion_reserve (R.cfg_state c) owner,
 (SourceCredit.credit support (R.cfg_state c) owner,
 (TargetCredit.credit support (R.cfg_state c) owner,
 (OrdinaryCredit.credit c owner,PendingBudget.credit (R.cfg_state c) owner))))).
Definition relation :=
 Relation_Operators.slexprod nat (nat*(nat*(nat*(nat*nat)))) lt
 (Relation_Operators.slexprod nat (nat*(nat*(nat*nat))) lt
 (Relation_Operators.slexprod nat (nat*(nat*nat)) lt
 (Relation_Operators.slexprod nat (nat*nat) lt
 (Relation_Operators.slexprod nat nat lt lt)))).
Definition decreases support owner after before :=
 relation (vector support owner after) (vector support owner before).
Theorem well_founded support owner : well_founded (decreases support owner).
Proof.
 unfold decreases. apply wf_inverse_image.
 unfold relation. repeat apply wf_slexprod;apply Nat.lt_wf_0.
Qed.
Lemma pair_decreases (A : Type) (rel : A -> A -> Prop) a a' b b' :
 a'<=a -> (a'=a -> rel b' b) ->
 Relation_Operators.slexprod nat A lt rel (a',b') (a,b).
Proof.
 intros Hle Htail. destruct (Nat.lt_ge_cases a' a) as [Hlt|Hge].
 - apply Relation_Operators.left_slex,Hlt.
 - assert (Heq : a'=a) by lia. subst a'. apply Relation_Operators.right_slex,Htail,eq_refl.
Qed.
Lemma all_nonincreasing support owner before after :
 MaterializationBudget.credit support (R.cfg_state after)<=MaterializationBudget.credit support (R.cfg_state before) ->
 T.promotion_reserve (R.cfg_state after) owner<=T.promotion_reserve (R.cfg_state before) owner ->
 SourceCredit.credit support (R.cfg_state after) owner<=SourceCredit.credit support (R.cfg_state before) owner ->
 TargetCredit.credit support (R.cfg_state after) owner<=TargetCredit.credit support (R.cfg_state before) owner ->
 OrdinaryCredit.credit after owner<=OrdinaryCredit.credit before owner ->
 PendingBudget.credit (R.cfg_state after) owner<PendingBudget.credit (R.cfg_state before) owner ->
 decreases support owner after before.
Proof.
 intros Hmat Hpromotion Hsource Htarget Hordinary Hpending.
 unfold decreases,relation,vector. apply pair_decreases;[exact Hmat |intro].
 apply pair_decreases;[exact Hpromotion |intro].
 apply pair_decreases;[exact Hsource |intro].
 apply pair_decreases;[exact Htarget |intro].
 apply pair_decreases;[exact Hordinary |intro]. exact Hpending.
Qed.
Theorem higher support tf roots st fr direct k target rest :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 exists saved done count,
 SourceCredit.active_steps support tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} (HigherRetry.resumed tf saved done fr k) count /\
 decreases support (R.frame_owner fr) (HigherRetry.resumed tf saved done fr k)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intros Hchildren Hreach Hp.
 destruct (@HigherRetry.segment support tf roots st fr direct k target rest Hchildren Hreach Hp)
 as [saved [done [count [Hactive Hpending]]]].
 exists saved,done,count. split;[exact Hactive |].
 pose proof (SourceCredit.active_execution Hactive) as Hsteps.
 apply all_nonincreasing.
 - exact (MaterializationBudget.steps_nonincreasing support Hsteps).
 - exact (Promotion.reserve_nonincreasing (R.frame_owner fr) Hsteps).
 - pose proof (@SourceCredit.active_bound support tf roots (R.frame_owner fr) _ _ count Hactive Hreach). lia.
 - eapply ActiveAccounts.incoming_nonincreasing;[exact Hactive |exact Hreach].
 - eapply ActiveAccounts.ordinary_nonincreasing;[exact Hactive |exact Hreach | |].
   + exact (proj1 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp)).
   + unfold T.control_frame;cbn. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));[reflexivity |contradiction].
 - exact Hpending.
Qed.
Lemma evaluation_paid_decreases support owner before after :
 RoundAccounts.evaluation_payment support owner (R.cfg_state before) (R.cfg_state after) ->
 T.promotion_reserve (R.cfg_state after) owner<=T.promotion_reserve (R.cfg_state before) owner ->
 decreases support owner after before.
Proof.
 intros [Hmat|[Hmat Hsource]] Hpromotion;unfold decreases,relation,vector.
 - apply Relation_Operators.left_slex,Hmat.
 - rewrite Hmat. apply Relation_Operators.right_slex.
   apply pair_decreases;[exact Hpromotion |intro].
   apply Relation_Operators.left_slex,Hsource.
Qed.
Lemma clear_materialization support st owner :
 MaterializationBudget.credit support (P.clear_owner st owner)=MaterializationBudget.credit support st.
Proof. apply T.unmaterialized_count_sigma_ext;reflexivity. Qed.
Theorem queued tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k next next_fr direct count :
 R.frame_owner next_fr=R.frame_owner fr ->
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 P.pending_above next (R.frame_owner next_fr)=None ->
 R.queue_contains (R.frame_owner next_fr) (R.queue next)=true ->
 N.next_config tf {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|}=
 Some (P.retry_current tf next next_fr k) /\
 decreases (B.Sem.support finite) (R.frame_owner fr) (P.retry_current tf next next_fr k)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Proof.
 intros Howner Huntil Hactive Hreach Hclean Hpending Hqueued. split.
 - cbn -[P.pending_above P.retry_current P.next_batched]. now rewrite Hpending,Hqueued.
 - assert (Hqueued' : R.queue_contains (R.frame_owner fr) (R.queue next)=true) by (now rewrite <- Howner).
   pose proof (@RoundAccounts.queued_paid tf roots finite st fr body k
   {|R.cfg_state:=next;R.cfg_control:=R.RunCommit next_fr direct k|} count
   Huntil Hactive Hreach Hclean Hqueued') as Hpaid.
   apply evaluation_paid_decreases.
   + unfold RoundAccounts.evaluation_payment in Hpaid |- *.
     cbn -[MaterializationBudget.credit SourceCredit.credit P.clear_owner].
     rewrite clear_materialization,SourceCredit.clear. exact Hpaid.
   + change (T.promotion_reserve next (R.frame_owner fr)<=T.promotion_reserve st (R.frame_owner fr)).
     exact (Promotion.reserve_nonincreasing (R.frame_owner fr) (SourceCredit.active_execution Hactive)).
Qed.
End RetryMeasure.

Module RoundComposition.
Definition weak support owner after before :=
 RetryMeasure.decreases support owner after before \/
 RetryMeasure.vector support owner after=RetryMeasure.vector support owner before.
Lemma pair_transitive (A B : Type) (ra : A -> A -> Prop) (rb : B -> B -> Prop) :
 (forall x y z,ra x y -> ra y z -> ra x z) ->
 (forall x y z,rb x y -> rb y z -> rb x z) ->
 forall x y z,Relation_Operators.slexprod A B ra rb x y ->
 Relation_Operators.slexprod A B ra rb y z ->
 Relation_Operators.slexprod A B ra rb x z.
Proof.
 intros Ha Hb [a b] [c d] [e f] Hxy Hyz.
 inversion Hxy;subst;inversion Hyz;subst;
 [apply Relation_Operators.left_slex;eapply Ha;eassumption |
 apply Relation_Operators.left_slex;assumption |
 apply Relation_Operators.left_slex;assumption |
 apply Relation_Operators.right_slex;eapply Hb;eassumption].
Qed.
Lemma transitive support owner first middle last :
 RetryMeasure.decreases support owner first middle ->
 RetryMeasure.decreases support owner middle last ->
 RetryMeasure.decreases support owner first last.
Proof.
 unfold RetryMeasure.decreases,RetryMeasure.relation.
 apply pair_transitive;[intros;lia |].
 apply pair_transitive;[intros;lia |].
 apply pair_transitive;[intros;lia |].
 apply pair_transitive;[intros;lia |].
 apply pair_transitive;intros;lia.
Qed.
Lemma after_weak support owner first middle last :
 RetryMeasure.decreases support owner last middle -> weak support owner middle first ->
 RetryMeasure.decreases support owner last first.
Proof.
 intros Hlast [Hmiddle|Heq];[eapply transitive;eassumption |].
 unfold RetryMeasure.decreases in *. now rewrite <- Heq.
Qed.
Lemma pair_weak (A : Type) (rel : A -> A -> Prop) a a' b b' :
 a'<=a -> (a'=a -> rel b' b \/ b'=b) ->
 Relation_Operators.slexprod nat A lt rel (a',b') (a,b) \/ (a',b')=(a,b).
Proof.
 intros Hle Htail. destruct (Nat.lt_ge_cases a' a) as [Hlt|Hge].
 - left;apply Relation_Operators.left_slex,Hlt.
 - assert (Heq : a'=a) by lia. subst a'.
   destruct (Htail eq_refl) as [Hrel|Heq].
   + left;apply Relation_Operators.right_slex,Hrel.
   + right;now subst b'.
Qed.
Lemma ordinary_when_unpromoted support tf roots owner first last count fr :
 SourceCredit.active_steps support tf owner first last count ->
 N.steps tf (R.initial_config roots) first ->
 T.control_frame owner (R.cfg_control first)=Some fr ->
 T.promotion_reserve (R.cfg_state last) owner=T.promotion_reserve (R.cfg_state first) owner ->
 OrdinaryCredit.credit last owner<=OrdinaryCredit.credit first owner.
Proof.
 intros Hactive Hreach Hframe Hpromotion.
 destruct (S.mem owner (R.controlled (R.cfg_state first))) eqn:Hcontrolled.
 - eapply ActiveAccounts.ordinary_nonincreasing;[exact Hactive |exact Hreach |exact Hcontrolled |exact Hframe].
 - pose proof (T.promotion_reserve_equal_membership _ _ _ Hpromotion) as Heq.
   unfold OrdinaryCredit.credit,T.active_ordinary_credit. rewrite Heq,Hcontrolled. lia.
Qed.
Theorem evaluation_weak tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k last count :
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} last count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 weak (B.Sem.support finite) (R.frame_owner fr) last
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Proof.
 intros Huntil Hactive Hreach. pose proof (SourceCredit.active_execution Hactive) as Hsteps.
 pose proof (MaterializationBudget.steps_nonincreasing (B.Sem.support finite) Hsteps) as Hmat.
 pose proof (Promotion.reserve_nonincreasing (R.frame_owner fr) Hsteps) as Hpromotion.
 pose proof (@SourceCredit.active_bound (B.Sem.support finite) tf roots (R.frame_owner fr) _ last count Hactive Hreach) as Hsource.
 pose proof (@ActiveAccounts.incoming_nonincreasing (B.Sem.support finite) (B.Sem.support finite)
 tf roots (R.frame_owner fr) _ last count Hactive Hreach) as Hincoming.
 unfold weak,RetryMeasure.decreases,RetryMeasure.vector,RetryMeasure.relation.
 apply pair_weak;[exact Hmat |intro Hmeq].
 apply pair_weak;[exact Hpromotion |intro Hpeq].
 apply pair_weak;[lia |intro Hseq].
 apply pair_weak;[exact Hincoming |intro Heq].
 apply pair_weak.
 - eapply ordinary_when_unpromoted;[exact Hactive |exact Hreach | |exact Hpeq].
   unfold T.control_frame;cbn. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));[reflexivity |contradiction].
 - intro Hordinary. right.
   exact (@RoundAccounts.stable_pending tf roots finite st fr body k last count Huntil Hactive Hreach Hmeq Hseq).
Qed.
Lemma evaluation_then_higher tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k middle middle_fr direct count target rest :
 R.frame_owner middle_fr=R.frame_owner fr ->
 Episodes.children tf roots (R.frame_owner fr) ->
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|} ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|} count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 P.pending_above middle (R.frame_owner middle_fr)=Some (target,rest) ->
 exists saved done total,
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 (HigherRetry.resumed tf saved done middle_fr k) total /\
 RetryMeasure.decreases (B.Sem.support finite) (R.frame_owner fr)
 (HigherRetry.resumed tf saved done middle_fr k)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Proof.
 intros Howner Hchildren Huntil Hactive Hreach Hp.
 assert (Hmiddle : N.steps tf (R.initial_config roots)
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|}).
 { eapply steps_append;[exact Hreach |exact (SourceCredit.active_execution Hactive)]. }
 assert (Hchildren' : Episodes.children tf roots (R.frame_owner middle_fr)) by (now rewrite Howner).
 destruct (@RetryMeasure.higher (B.Sem.support finite) tf roots middle middle_fr direct k target rest
 Hchildren' Hmiddle Hp) as [saved [done [n [Hhigher Hdecrease]]]].
 rewrite Howner in Hhigher,Hdecrease.
 exists saved,done,(count+n). split;[eapply ActiveAccounts.append;eassumption |].
 eapply after_weak;[exact Hdecrease |].
 exact (@evaluation_weak tf roots finite st fr body k _ count Huntil Hactive Hreach).
Qed.
End RoundComposition.
Module ReaderRanks.
Definition valid := B.ReaderOrder.reader_edges_ordered.
Lemma queue st q : valid st -> valid (R.with_queue st q).
Proof. apply B.ReaderOrder.reader_edges_ordered_with_queue. Qed.
Lemma enqueue st target : valid st -> valid (R.enqueue st target).
Proof. apply B.ReaderOrder.reader_edges_ordered_enqueue. Qed.
Lemma base tf before after :
 valid (R.cfg_state before) -> R.next_config tf before=Some after -> valid (R.cfg_state after).
Proof. apply B.ReaderOrder.next_config_reader_edges_ordered. Qed.
Lemma precommit tf before after :
 valid (R.cfg_state before) -> P.next_config tf before=Some after -> valid (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hv Hstep. destruct ctrl;
 cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply base;[exact Hv |exact Hstep]].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. apply queue,Hv.
 - eapply base;[exact Hv |exact Hstep].
Qed.
Lemma old_publish targets st fr : valid st -> valid (P.publish_accumulated targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hv;
 cbn -[R.write_side_contribution];[exact Hv |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw. apply IH. destruct changed;[apply enqueue |].
 all: eapply B.ReaderOrder.reader_edges_ordered_write_side;[exact Hv |exact Hw].
Qed.
Lemma batched tf before after :
 valid (R.cfg_state before) -> P.next_batched tf before=Some after -> valid (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hv Hstep. destruct ctrl;
 cbn -[P.next_config R.observe R.record_side_input P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit;[exact Hv |exact Hstep]].
 - destruct r;try solve [eapply precommit;[exact Hv |exact Hstep]].
   inversion Hstep;subst. apply B.ReaderOrder.reader_edges_ordered_observe,Hv.
 - destruct l;[ |eapply precommit;[exact Hv |exact Hstep]].
   inversion Hstep;subst. apply B.ReaderOrder.reader_edges_ordered_publish_targets,old_publish,Hv.
Qed.
Lemma fresh tf before after :
 valid (R.cfg_state before) -> P.next_fresh tf before=Some after -> valid (R.cfg_state after).
Proof.
 destruct before as [st ctrl]. intros Hv Hstep. destruct ctrl;
 cbn -[P.next_batched P.clear_owner P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply batched;[exact Hv |exact Hstep]].
 - eapply (@batched tf {|R.cfg_state:=P.clear_owner st t;R.cfg_control:=R.StartEpisode t c|} after);
   [apply queue,Hv |exact Hstep].
 - destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. apply queue,Hv.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. apply queue,Hv.
     * eapply batched;[exact Hv |exact Hstep].
 - destruct c;try solve [eapply batched;[exact Hv |exact Hstep]].
   eapply (@batched tf {|R.cfg_state:=P.clear_owner st (R.frame_owner f);R.cfg_control:=R.Return (R.KAfterSide f r c)|} after);
   [apply queue,Hv |exact Hstep].
Qed.
Lemma requeue before after source target :
 valid after -> valid (C.requeue_source before after source target).
Proof. unfold C.requeue_source. destruct C.cell_changed;[apply enqueue |trivial]. Qed.
Lemma finish before after fr target changed :
 valid after -> valid (C.finish_write before after fr target changed).
Proof. intro Hv. unfold C.finish_write. destruct changed;[apply enqueue |];apply requeue,Hv. Qed.
Lemma publish targets st fr : valid st -> valid (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hv;
 cbn -[R.write_side_contribution C.finish_write];[exact Hv |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end))
 as [next changed] eqn:Hw. apply IH,finish.
 eapply B.ReaderOrder.reader_edges_ordered_write_side;[exact Hv |exact Hw].
Qed.
Lemma dead tf st fr direct pending k after :
 valid st -> N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|}=Some after ->
 valid (R.cfg_state after).
Proof.
 intros Hv Hstep. destruct pending as [|target rest].
 - inversion Hstep;subst. apply B.ReaderOrder.reader_edges_ordered_publish_targets,publish,Hv.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;exact Hv |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   assert (Hnext : valid (C.requeue_source st next (R.frame_owner fr) target)).
   { apply requeue. eapply B.ReaderOrder.reader_edges_ordered_write_side;[exact Hv |exact Hw]. }
   inversion Hstep;subst. unfold R.continue_dead.
   destruct changed;[destruct (_ && _)%bool |];cbn;try exact Hnext;apply enqueue,Hnext.
Qed.
Theorem next tf before after :
 valid (R.cfg_state before) -> N.next_config tf before=Some after -> valid (R.cfg_state after).
Proof.
 intros Hv Hstep.
 destruct (@Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 - exact (@N.O.ReaderRanks.next tf before after Hv Hb0).
 - apply queue,Hv.
Qed.
Theorem steps tf before after :
 N.steps tf before after -> valid (R.cfg_state before) -> valid (R.cfg_state after).
Proof.
 intro Hsteps. induction Hsteps;intro Hv;[exact Hv |].
 apply IHHsteps. eapply next;[exact Hv |exact H].
Qed.
Theorem reachable tf roots c :
 N.steps tf (R.initial_config roots) c -> valid (R.cfg_state c).
Proof.
 intro Hsteps. eapply steps;[exact Hsteps |].
 intros target source Hmem. unfold R.lookup_set in Hmem. cbn in Hmem.
 rewrite ML.lookup_empty,SL.empty_spec in Hmem. discriminate.
Qed.
End ReaderRanks.

Module Draining.
Definition finishes support tf owner k start :=
 (exists st,N.steps tf start {|R.cfg_state:=st;R.cfg_control:=R.Return k|} /\ T.queue_strictly_below owner st) \/
 (exists st fr count,R.frame_owner fr=owner /\
 SourceCredit.active_steps support tf owner start
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (tf owner) k|} count /\ T.queue_strictly_below owner st).
Lemma prepend support tf owner k first middle count :
 SourceCredit.active_steps support tf owner first middle count ->
 finishes support tf owner k middle -> finishes support tf owner k first.
Proof.
 intros Hprefix [[st [Hsteps Hbelow]]|[st [fr [n [Howner [Hactive Hbelow]]]]]].
 - left. exists st. split;[eapply steps_append;[exact (SourceCredit.active_execution Hprefix) |exact Hsteps] |exact Hbelow].
 - right. exists st,fr,(count+n). split;[exact Howner |]. split;[eapply ActiveAccounts.append;eassumption |exact Hbelow].
Qed.
Lemma return_now support tf roots st fr k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return k|} ->
 finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hreach Hstep. left. exists after. split;[apply Episodes.one,Hstep |].
 exact (proj2 (@EpisodePath.drain_return tf roots st fr k after k Hreach Hstep)).
Qed.
Lemma self support tf st fr k :
 B.queue_ordered st -> R.queue_peek (R.queue st)=Some (R.frame_owner fr) ->
 finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hsort Hpeek. destruct (@T.queue_peek_some_pop _ _ Hpeek) as [tail Hpop].
 set (after := {|R.cfg_state:=R.with_queue st tail;
 R.cfg_control:=R.RunRhs (R.fresh_frame (R.with_queue st tail) (R.frame_owner fr) (R.frame_phase fr))
 (tf (R.frame_owner fr)) k|}).
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=Some after).
 { cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame].
   rewrite Hpeek. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));[now rewrite Hpop |contradiction]. }
 right. exists (R.with_queue st tail),
 (R.fresh_frame (R.with_queue st tail) (R.frame_owner fr) (R.frame_phase fr)),
 (SourceCredit.charge support (R.frame_owner fr) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} after).
 split;[reflexivity |]. split.
 - apply ActiveAccounts.one;[exact Hstep |left;reflexivity].
 - eapply T.with_queue_strictly_below;[exact Hsort |exact Hpop].
Qed.
Lemma none support tf roots st fr k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 R.queue_peek (R.queue st)=None ->
 finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hreach Hpeek. eapply return_now;[exact Hreach |].
 cbn -[R.queue_peek R.reset_registered_cells]. now rewrite Hpeek.
Qed.
Lemma lower support tf roots st fr k target :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 R.queue_peek (R.queue st)=Some target -> target<>R.frame_owner fr ->
 R.rank_lt st (R.frame_owner fr) target=false ->
 finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hreach Hpeek Hneq Hhigher. eapply return_now;[exact Hreach |].
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame]. rewrite Hpeek.
 destruct (V.eq_dec target (R.frame_owner fr));[contradiction |]. now rewrite Hhigher.
Qed.
Lemma child support tf roots st fr k target :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 R.queue_peek (R.queue st)=Some target -> target<>R.frame_owner fr ->
 R.rank_lt st (R.frame_owner fr) target=true ->
 exists done count,
 SourceCredit.active_steps support tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 {|R.cfg_state:=done;R.cfg_control:=R.RunDrain fr k|} count /\ T.queue_strictly_below target done.
Proof.
 intros Hchildren Hreach Hpeek Hneq Hhigher.
 destruct (@T.queue_peek_some_pop _ _ Hpeek) as [tail Hpop].
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=R.with_queue st tail;R.cfg_control:=R.StartEpisode target (R.KDrain fr k)|}).
 { cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame]. rewrite Hpeek.
   destruct (V.eq_dec target (R.frame_owner fr));[contradiction |]. now rewrite Hhigher,Hpop. }
 destruct (Hchildren (R.with_queue st tail) target (R.KDrain fr k) Hhigher (Episodes.reached Hreach Hstep))
 as [candidate [Hdone Hbelow]].
 destruct (@EpisodePath.child_segment support tf roots (R.with_queue st tail) target (R.KDrain fr k)
 candidate (R.frame_owner fr) (Episodes.reached Hreach Hstep) Hdone (or_introl eq_refl))
 as [done [n [Hprefix [Hactive Hdone_below]]]].
 exists done,(SourceCredit.charge support (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 {|R.cfg_state:=R.with_queue st tail;R.cfg_control:=R.StartEpisode target (R.KDrain fr k)|}+
 (n+SourceCredit.charge support (R.frame_owner fr)
 {|R.cfg_state:=done;R.cfg_control:=R.Return (R.KDrain fr k)|}
 {|R.cfg_state:=done;R.cfg_control:=R.RunDrain fr k|})).
 split;[ |exact Hdone_below].
 econstructor;[exact Hstep |right;left;reflexivity |].
 eapply ActiveAccounts.append;[exact Hactive |]. apply ActiveAccounts.one;[reflexivity |left;reflexivity].
Qed.
Lemma bounded support tf roots (finite : B.Sem.finite_system tf roots) owner k bound :
 forall st fr,R.frame_owner fr=owner -> Episodes.children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 Episodes.queue_bound st owner bound ->
 finishes support tf owner k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 induction bound as [bound IH] using Wf_nat.lt_wf_ind.
 intros st fr Howner Hchildren Hreach Hbound.
 destruct (R.queue_peek (R.queue st)) as [target|] eqn:Hpeek.
 - destruct (V.eq_dec target owner) as [Heq|Hneq].
   + rewrite <- Howner. apply self;[exact (B.configuration_queue_ordered (reachable_ranked Hreach)) |rewrite Howner;now rewrite <- Heq].
   + destruct (R.rank_lt st owner target) eqn:Hhigher.
     * assert (Htarget : B.ranked st target).
       { apply (B.data_queue_ranked (B.configuration_state_data (reachable_ranked Hreach))). apply T.queue_peek_member,Hpeek. }
       destruct Htarget as [rank Hrank].
       destruct (@child support tf roots st fr k target)
       as [done [count [Hactive Hbelow]]];[now rewrite Howner |exact Hreach |exact Hpeek |congruence |now rewrite Howner |].
       pose proof (SourceCredit.active_execution Hactive) as Hsteps.
       assert (Hrank' : R.Ranking.lookup (R.ranking done) target=Some rank)
       by (exact (@Episodes.steps_extends tf _ _ Hsteps target rank Hrank)).
       eapply prepend;[rewrite <- Howner;exact Hactive |].
       eapply (IH rank);[eapply Hbound;[exact Hpeek |exact Hhigher |exact Hrank] |exact Howner |exact Hchildren | |].
       -- eapply steps_append;[exact Hreach |exact Hsteps].
       -- eapply Episodes.below_bound;[exact Hbelow |exact Hrank'].
     * rewrite <- Howner. eapply lower;[exact Hreach |exact Hpeek |congruence |now rewrite Howner].
 - rewrite <- Howner. eapply none;[exact Hreach |exact Hpeek].
Qed.
Theorem completes support tf roots (finite : B.Sem.finite_system tf roots) st fr k :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}.
Proof.
 intros Hchildren Hreach.
 eapply (@bounded support tf roots finite (R.frame_owner fr) k (B.Finite.bound (B.Sem.support finite)) st fr);
 [reflexivity |exact Hchildren |exact Hreach |].
 intros target rank Hpeek Hhigher Hrank. exact (@Episodes.rank_bound tf roots finite _ target rank Hreach Hrank).
Qed.
End Draining.

Module CommitQueues.
Lemma below_zero st owner :
 T.queue_strictly_below owner st -> PendingBudget.credit st owner=0.
Proof.
 intro Hbelow. apply Nat.le_antisymm;[ |lia]. apply PendingBudget.bounded.
 intros target Hin. pose proof (Hbelow target Hin) as Hlt.
 destruct (@B.rank_lt_true_ranked st target owner Hlt) as [Ht Ho].
 unfold PendingBudget.entry. rewrite (@B.rank_lt_asymmetric st target owner Ht Ho Hlt). lia.
Qed.
Lemma zero_below tf roots st fr direct k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 PendingBudget.credit st (R.frame_owner fr)=0 ->
 T.queue_strictly_below (R.frame_owner fr) st.
Proof.
 intros Hreach Hclean Hzero target Hin. pose proof (reachable_ranked Hreach) as Hr.
 assert (Ht : B.ranked st target) by (apply (B.data_queue_ranked (B.configuration_state_data Hr)),Hin).
 assert (Ho : B.ranked st (R.frame_owner fr)) by (exact (proj1 (proj1 (B.configuration_control_ranked Hr)))).
 assert (Hneq : R.frame_owner fr<>target).
 { intro Heq. subst target. apply B.queue_contains_false in Hclean. contradiction. }
 destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher.
 - pose proof (@PendingBudget.member st (R.frame_owner fr) (R.queue st) target Hin) as Hbound.
   destruct Ht as [rank Hrank]. unfold PendingBudget.entry in Hbound. rewrite Hhigher,Hrank in Hbound.
   change (S rank<=PendingBudget.credit st (R.frame_owner fr)) in Hbound. rewrite Hzero in Hbound. lia.
 - eapply T.rank_lt_reverse_if_false;[exact (B.configuration_rank_valid Hr) |exact Ho |exact Ht |exact Hneq |exact Hhigher].
Qed.
Lemma controlled_ready_below tf roots st fr direct k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 S.mem (R.frame_owner fr) (R.controlled st)=true ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 P.pending_above st (R.frame_owner fr)=None ->
 T.queue_strictly_below (R.frame_owner fr) st.
Proof.
 intros Hreach Hcontrolled Hclean Hp. pose proof (reachable_ranked Hreach) as Hr.
 destruct (R.queue_peek (R.queue st)) as [target|] eqn:Hpeek;[ |eapply T.queue_peek_none_below;exact Hpeek].
 destruct (@T.queue_peek_some_pop _ _ Hpeek) as [rest Hpop].
 unfold P.pending_above in Hp. rewrite Hcontrolled,Hpop in Hp.
 destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hhigher;[discriminate |].
 assert (Hin : List.In target (R.queue st)) by (apply T.queue_peek_member,Hpeek).
 assert (Ht : B.ranked st target) by (apply (B.data_queue_ranked (B.configuration_state_data Hr)),Hin).
 assert (Ho : B.ranked st (R.frame_owner fr)) by (exact (proj1 (proj1 (B.configuration_control_ranked Hr)))).
 assert (Hneq : R.frame_owner fr<>target).
 { intro Heq. subst target. apply B.queue_contains_false in Hclean. contradiction. }
 eapply T.queue_peek_lower_below;[exact (B.configuration_queue_ordered Hr) |exact Hpeek |].
 eapply T.rank_lt_reverse_if_false;[exact (B.configuration_rank_valid Hr) |exact Ho |exact Ht |exact Hneq |exact Hhigher].
Qed.
Lemma uncontrolled_set_below tf roots st fr direct k next next_fr :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 S.mem (R.frame_owner fr) (R.controlled st)=false ->
 T.queue_strictly_below (R.frame_owner fr) st ->
 R.set_value st fr direct=(next,next_fr) ->
 T.queue_strictly_below (R.frame_owner fr) next.
Proof.
 intros Hreach Hcontrolled Hbelow Hset target Hin.
 destruct (in_dec V.eq_dec target (R.queue st)) as [Hold|Hnew].
 - pose proof (Hbelow target Hold) as Hlt.
   destruct (@B.rank_lt_true_ranked st target (R.frame_owner fr) Hlt) as [Ht Ho].
   rewrite <- (@B.rank_lt_stable st next target (R.frame_owner fr)
   (@B.rank_extends_set_value st fr direct next next_fr Hset) Ht Ho). exact Hlt.
 - destruct (@B.set_value_new_queue_cause st fr direct next next_fr target Hset Hnew Hin) as [_ Hreader].
   destruct (@ReaderRanks.reachable tf roots _ Hreach (R.frame_owner fr) target Hreader) as [Hlt|Hknown].
   + destruct (@B.rank_lt_true_ranked st target (R.frame_owner fr) Hlt) as [Ht Ho].
     rewrite <- (@B.rank_lt_stable st next target (R.frame_owner fr)
     (@B.rank_extends_set_value st fr direct next next_fr Hset) Ht Ho). exact Hlt.
   + cbn in Hknown. congruence.
Qed.
Lemma drain_below_returns tf roots st fr k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 T.queue_strictly_below (R.frame_owner fr) st ->
 exists after,N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.Return k|} /\ T.queue_strictly_below (R.frame_owner fr) after.
Proof.
 intros Hreach Hbelow. exists (R.reset_registered_cells st (R.frame_owner fr)).
 split;[ |apply T.reset_registered_cells_below,Hbelow].
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame].
 destruct (R.queue_peek (R.queue st)) as [target|] eqn:Hpeek;[ |reflexivity].
 pose proof (Hbelow target (@T.queue_peek_member _ _ Hpeek)) as Hlt.
 destruct (@B.rank_lt_true_ranked st target (R.frame_owner fr) Hlt) as [Ht Ho].
 destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
 - subst target. exfalso. exact ((@B.rank_lt_true_neq_correctness st (R.frame_owner fr) (R.frame_owner fr) Hlt) eq_refl).
 - rewrite (@B.rank_lt_asymmetric st target (R.frame_owner fr) Ht Ho Hlt). reflexivity.
Qed.
End CommitQueues.

Module DrainMeasure.
Lemma pending support tf roots owner first last count fr :
 SourceCredit.active_steps support tf owner first last count ->
 N.steps tf (R.initial_config roots) first ->
 T.control_frame owner (R.cfg_control first)=Some fr ->
 PendingBudget.credit (R.cfg_state last) owner<PendingBudget.credit (R.cfg_state first) owner ->
 RetryMeasure.decreases support owner last first.
Proof.
 intros Hactive Hreach Hframe Hpending. pose proof (SourceCredit.active_execution Hactive) as Hsteps.
 unfold RetryMeasure.decreases,RetryMeasure.relation,RetryMeasure.vector.
 apply RetryMeasure.pair_decreases;[exact (MaterializationBudget.steps_nonincreasing support Hsteps) |intro].
 apply RetryMeasure.pair_decreases;[exact (Promotion.reserve_nonincreasing owner Hsteps) |intro Hpromotion].
 apply RetryMeasure.pair_decreases.
 - pose proof (@SourceCredit.active_bound support tf roots owner first last count Hactive Hreach). lia.
 - intro. apply RetryMeasure.pair_decreases;[eapply ActiveAccounts.incoming_nonincreasing;eassumption |intro].
   apply RetryMeasure.pair_decreases;[eapply RoundComposition.ordinary_when_unpromoted;eassumption |intro].
   exact Hpending.
Qed.
Lemma ordinary support tf roots owner first last count :
 SourceCredit.active_steps support tf owner first last count ->
 N.steps tf (R.initial_config roots) first ->
 OrdinaryCredit.credit last owner<OrdinaryCredit.credit first owner ->
 RetryMeasure.decreases support owner last first.
Proof.
 intros Hactive Hreach Hordinary. pose proof (SourceCredit.active_execution Hactive) as Hsteps.
 unfold RetryMeasure.decreases,RetryMeasure.relation,RetryMeasure.vector.
 apply RetryMeasure.pair_decreases;[exact (MaterializationBudget.steps_nonincreasing support Hsteps) |intro].
 apply RetryMeasure.pair_decreases;[exact (Promotion.reserve_nonincreasing owner Hsteps) |intro].
 apply RetryMeasure.pair_decreases.
 - pose proof (@SourceCredit.active_bound support tf roots owner first last count Hactive Hreach). lia.
 - intro. apply RetryMeasure.pair_decreases;[eapply ActiveAccounts.incoming_nonincreasing;eassumption |intro].
   apply Relation_Operators.left_slex,Hordinary.
Qed.
Lemma controlled_commit support tf roots st fr direct k after after_fr after_k last count :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr after_k|} ->
 R.frame_owner after_fr=R.frame_owner fr ->
 S.mem (R.frame_owner fr) (R.controlled st)=true ->
 R.equivalent (R.sigma_value after (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))=false ->
 SourceCredit.active_steps support tf (R.frame_owner fr)
 {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr after_k|} last count ->
 OrdinaryCredit.credit last (R.frame_owner fr)<
 OrdinaryCredit.credit {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} (R.frame_owner fr).
Proof.
 intros Hreach Hstep Howner Hcontrolled Hchanged Htail.
 pose proof (@OrdinaryCredit.committing_strict tf st fr direct k after after_fr after_k Hcontrolled Hstep Hchanged) as Hstrict.
 assert (Hnext : N.steps tf (R.initial_config roots) {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr after_k|})
 by (eapply Episodes.reached;eassumption).
 assert (Hafter : S.mem (R.frame_owner fr) (R.controlled after)=true)
 by (exact (@Promotion.next tf _ _ Hstep (R.frame_owner fr) Hcontrolled)).
 assert (Hframe : T.control_frame (R.frame_owner fr) (R.RunDrain after_fr after_k)=Some after_fr).
 { cbn [T.control_frame]. rewrite Howner. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));congruence. }
 pose proof (@ActiveAccounts.ordinary_nonincreasing support tf roots (R.frame_owner fr) _ last count after_fr
 Htail Hnext Hafter Hframe). lia.
Qed.
End DrainMeasure.
Module RoundResult.
Definition finishes support tf owner k start :=
 (exists st,N.steps tf start {|R.cfg_state:=st;R.cfg_control:=R.Return k|} /\ T.queue_strictly_below owner st) \/
 (exists st fr count,R.frame_owner fr=owner /\
 SourceCredit.active_steps support tf owner start
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (tf owner) k|} count /\
 R.queue_contains owner (R.queue st)=false /\
 RetryMeasure.decreases support owner {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (tf owner) k|} start).
Lemma below_clean st owner :
 T.queue_strictly_below owner st -> R.queue_contains owner (R.queue st)=false.
Proof.
 intro Hbelow. apply B.queue_contains_false. intro Hin.
 exact ((@B.rank_lt_true_neq_correctness st owner owner (Hbelow owner Hin)) eq_refl).
Qed.
Lemma prepend support tf owner k first middle count :
 SourceCredit.active_steps support tf owner first middle count ->
 RoundComposition.weak support owner middle first ->
 finishes support tf owner k middle -> finishes support tf owner k first.
Proof.
 intros Hprefix Hweak [[st [Hsteps Hbelow]]|[st [fr [n [Howner [Hactive [Hclean Hdecrease]]]]]]].
 - left. exists st. split;[eapply steps_append;[exact (SourceCredit.active_execution Hprefix) |exact Hsteps] |exact Hbelow].
 - right. exists st,fr,(count+n). split;[exact Howner |]. split;[eapply ActiveAccounts.append;eassumption |].
   split;[exact Hclean |eapply RoundComposition.after_weak;eassumption].
Qed.
End RoundResult.
Module OrdinaryRound.
Lemma below support tf roots st fr direct k after after_fr :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr k|} ->
 R.frame_owner after_fr=R.frame_owner fr ->
 T.queue_strictly_below (R.frame_owner fr) after ->
 RoundResult.finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intros Hreach Hstep Howner Hbelow.
 destruct (@CommitQueues.drain_below_returns tf roots after after_fr k (Episodes.reached Hreach Hstep))
 as [done [Hreturn Hdone]];[now rewrite Howner |].
 left. exists done. split.
 - econstructor;[exact Hstep |apply Episodes.one,Hreturn].
 - now rewrite <- Howner.
Qed.
Lemma paid_drain support tf roots (finite : B.Sem.finite_system tf roots)
 st fr direct k after after_fr :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr k|} ->
 R.frame_owner after_fr=R.frame_owner fr ->
 ((S.mem (R.frame_owner fr) (R.controlled st)=true /\
 R.equivalent (R.sigma_value after (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))=false) \/
 0<PendingBudget.credit st (R.frame_owner fr)) ->
 RoundResult.finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intros Hchildren Hreach Hstep Howner Hpaid.
 assert (Hr : N.steps tf (R.initial_config roots) {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr k|})
 by (eapply Episodes.reached;eassumption).
 destruct (@Draining.completes support tf roots finite after after_fr k) as
 [[done [Hreturn Hbelow]]|[done [done_fr [count [Hdoneowner [Htail Hbelow]]]]]];
 [now rewrite Howner |exact Hr | |].
 - left. exists done. split;[econstructor;[exact Hstep |exact Hreturn] |now rewrite <- Howner].
 - rewrite Howner in Htail,Hbelow. rewrite Howner in Hdoneowner.
   assert (Hactive : SourceCredit.active_steps support tf (R.frame_owner fr)
   {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
   {|R.cfg_state:=done;R.cfg_control:=R.RunRhs done_fr (tf (R.frame_owner fr)) k|}
   (SourceCredit.charge support (R.frame_owner fr)
   {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}
   {|R.cfg_state:=after;R.cfg_control:=R.RunDrain after_fr k|}+count)).
   { econstructor;[exact Hstep |left;congruence |exact Htail]. }
   right. do 3 eexists. split;[exact Hdoneowner |]. split;[exact Hactive |].
   split;[apply RoundResult.below_clean,Hbelow |].
   destruct Hpaid as [[Hcontrolled Hchanged]|Hpending].
   + eapply DrainMeasure.ordinary;[exact Hactive |exact Hreach |].
     eapply DrainMeasure.controlled_commit;[exact Hreach |exact Hstep |exact Howner |exact Hcontrolled |exact Hchanged |exact Htail].
   + eapply DrainMeasure.pending;[exact Hactive |exact Hreach | |].
     * unfold T.control_frame;cbn. destruct (V.eq_dec (R.frame_owner fr) (R.frame_owner fr));[reflexivity |contradiction].
     * cbn -[PendingBudget.credit]. rewrite (CommitQueues.below_zero Hbelow). exact Hpending.
Qed.
Theorem ready support tf roots (finite : B.Sem.finite_system tf roots) st fr direct k :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr)=None ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 RoundResult.finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intros Hchildren Hreach Hp Hclean.
 destruct (R.set_value st fr direct) as [next next_fr] eqn:Hs.
 set (after := R.requeue_changed_controlled_owner st next (R.frame_owner fr)).
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}=
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr k|}).
 { cbn -[P.pending_above R.queue_contains R.set_value R.requeue_changed_controlled_owner].
   now rewrite Hp,Hclean,Hs. }
 assert (Howner : R.frame_owner next_fr=R.frame_owner fr) by (eapply B.set_value_owner;exact Hs).
 destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
 - destruct (R.equivalent (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr))) eqn:Hchanged.
   + eapply below;[exact Hreach |exact Hstep |exact Howner |].
     unfold after. rewrite (@B.requeue_unchanged st next (R.frame_owner fr) Hchanged).
     eapply T.queue_below_extended;[exact (@B.rank_extends_set_value st fr direct next next_fr Hs) | | |].
     * exact (proj1 (proj1 (B.configuration_control_ranked (reachable_ranked Hreach)))).
     * eapply T.set_value_equivalent_queue;[exact Hs |exact Hchanged].
     * eapply CommitQueues.controlled_ready_below;[exact Hreach |exact Hcontrolled |exact Hclean |exact Hp].
   + eapply (@paid_drain support tf roots finite);[exact Hchildren |exact Hreach |exact Hstep |exact Howner |].
     left. split;[exact Hcontrolled |exact Hchanged].
 - destruct (Nat.eq_dec (PendingBudget.credit st (R.frame_owner fr)) 0) as [Hzero|Hpositive].
   + eapply below;[exact Hreach |exact Hstep |exact Howner |].
     unfold after. rewrite (@B.requeue_uncontrolled st next (R.frame_owner fr) Hcontrolled).
     eapply CommitQueues.uncontrolled_set_below;[exact Hreach |exact Hcontrolled | |exact Hs].
     eapply CommitQueues.zero_below;[exact Hreach |exact Hclean |exact Hzero].
   + eapply (@paid_drain support tf roots finite);[exact Hchildren |exact Hreach |exact Hstep |exact Howner |].
     right;lia.
Qed.
End OrdinaryRound.

Module CompleteRound.
Lemma higher support tf roots st fr direct k target rest :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 RoundResult.finishes support tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|}.
Proof.
 intros Hchildren Hreach Hp.
 destruct (@RetryMeasure.higher support tf roots st fr direct k target rest Hchildren Hreach Hp)
 as [saved [done [count [Hactive Hdecrease]]]].
 right. exists (P.clear_owner done (R.frame_owner fr)),
 (R.fresh_frame saved (R.frame_owner fr) (R.frame_phase fr)),count.
 split;[reflexivity |]. split;[exact Hactive |]. split;[ |exact Hdecrease].
 apply B.queue_contains_false,P.clear_owner_not_queued.
Qed.
Lemma queued tf roots (finite : B.Sem.finite_system tf roots)
 st fr body k middle middle_fr direct count :
 R.frame_owner middle_fr=R.frame_owner fr ->
 EvaluationPrefix.until_commit tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|} ->
 SourceCredit.active_steps (B.Sem.support finite) tf (R.frame_owner fr)
 {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|} count ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 P.pending_above middle (R.frame_owner middle_fr)=None ->
 R.queue_contains (R.frame_owner middle_fr) (R.queue middle)=true ->
 RoundResult.finishes (B.Sem.support finite) tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Proof.
 intros Howner Huntil Hactive Hreach Hclean Hp Hqueued.
 destruct (@RetryMeasure.queued tf roots finite st fr body k middle middle_fr direct count
 Howner Huntil Hactive Hreach Hclean Hp Hqueued) as [Hstep Hdecrease].
 set (after:=P.retry_current tf middle middle_fr k) in *.
 assert (Hview : after={|R.cfg_state:=P.clear_owner middle (R.frame_owner middle_fr);
 R.cfg_control:=R.RunRhs (R.fresh_frame (P.clear_owner middle (R.frame_owner middle_fr))
 (R.frame_owner middle_fr) (R.frame_phase middle_fr)) (tf (R.frame_owner fr)) k|}).
 { unfold after,P.retry_current. now rewrite Howner. }
 assert (Hlast : T.control_contains (R.frame_owner fr) (R.cfg_control after)).
 { rewrite Hview. left;cbn;congruence. }
 pose proof (@ActiveAccounts.one (B.Sem.support finite) tf (R.frame_owner fr) _ after Hstep Hlast) as Hone.
 pose proof (@ActiveAccounts.append (B.Sem.support finite) tf (R.frame_owner fr) _ _ after count
 (SourceCredit.charge (B.Sem.support finite) (R.frame_owner fr) _ after) Hactive Hone) as Hall.
 rewrite Hview in Hall,Hdecrease.
 right. exists (P.clear_owner middle (R.frame_owner middle_fr)),
 (R.fresh_frame (P.clear_owner middle (R.frame_owner middle_fr)) (R.frame_owner middle_fr) (R.frame_phase middle_fr)).
 eexists. split;[exact Howner |]. split;[exact Hall |].
 split;[ |exact Hdecrease]. rewrite <- Howner. apply B.queue_contains_false,P.clear_owner_not_queued.
Qed.
Theorem completes tf roots (finite : B.Sem.finite_system tf roots) st fr body k :
 Episodes.children tf roots (R.frame_owner fr) ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.queue_contains (R.frame_owner fr) (R.queue st)=false ->
 RoundResult.finishes (B.Sem.support finite) tf (R.frame_owner fr) k {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|}.
Proof.
 intros Hchildren Hreach Hclean.
 destruct (@FirstCommit.rhs_first_commit (B.Sem.support finite) tf roots st fr body k Hchildren Hreach)
 as [middle [middle_fr [direct [count [Howner [Huntil Hactive]]]]]].
 assert (Hr : N.steps tf (R.initial_config roots)
 {|R.cfg_state:=middle;R.cfg_control:=R.RunCommit middle_fr direct k|}).
 { eapply steps_append;[exact Hreach |exact (SourceCredit.active_execution Hactive)]. }
 pose proof (@RoundComposition.evaluation_weak tf roots finite st fr body k _ count Huntil Hactive Hreach) as Hweak.
 destruct (P.pending_above middle (R.frame_owner middle_fr)) as [[target rest]|] eqn:Hp.
 - eapply RoundResult.prepend;[exact Hactive |exact Hweak |]. rewrite <- Howner.
   eapply (@higher (B.Sem.support finite) tf roots middle middle_fr direct k target rest);
   [now rewrite Howner |exact Hr |exact Hp].
 - destruct (R.queue_contains (R.frame_owner middle_fr) (R.queue middle)) eqn:Hqueued.
   + eapply queued;[exact Howner |exact Huntil |exact Hactive |exact Hreach |exact Hclean |exact Hp |exact Hqueued].
   + eapply RoundResult.prepend;[exact Hactive |exact Hweak |]. rewrite <- Howner.
     eapply (@OrdinaryRound.ready (B.Sem.support finite) tf roots finite);
     [now rewrite Howner |exact Hr |exact Hp |exact Hqueued].
Qed.
End CompleteRound.

Module EpisodeTermination.
Theorem rounds tf roots (finite : B.Sem.finite_system tf roots) owner k :
 Episodes.children tf roots owner ->
 forall first st fr body,first={|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.frame_owner fr=owner ->
 N.steps tf (R.initial_config roots) first ->
 R.queue_contains owner (R.queue st)=false ->
 Episodes.complete tf owner k first.
Proof.
 intro Hchildren.
 refine (well_founded_induction (RetryMeasure.well_founded (B.Sem.support finite) owner)
 (fun first => forall st fr body,first={|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 R.frame_owner fr=owner -> N.steps tf (R.initial_config roots) first ->
 R.queue_contains owner (R.queue st)=false -> Episodes.complete tf owner k first) _).
 intros first IH st fr body Hfirst Howner Hreach Hclean. subst first.
 assert (Hchildren' : Episodes.children tf roots (R.frame_owner fr)) by (now rewrite Howner).
 assert (Hclean' : R.queue_contains (R.frame_owner fr) (R.queue st)=false) by (now rewrite Howner).
 pose proof (@CompleteRound.completes tf roots finite st fr body k Hchildren' Hreach Hclean') as Hround.
 rewrite Howner in Hround. destruct Hround as [[done [Hsteps Hbelow]]|[done [next_fr [count [Hnextowner [Hactive [Hnextclean Hdecrease]]]]]]].
 - exists done;split;assumption.
 - pose proof (SourceCredit.active_execution Hactive) as Hsteps.
   destruct (IH _ Hdecrease done next_fr (tf owner) eq_refl Hnextowner
   (steps_append Hreach Hsteps) Hnextclean) as [final [Hfinal Hbelow]].
   exists final. split;[eapply steps_append;eassumption |exact Hbelow].
Qed.
Theorem start tf roots (finite : B.Sem.finite_system tf roots) st owner k :
 Episodes.children tf roots owner ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|} ->
 Episodes.complete tf owner k {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}.
Proof.
 intros Hchildren Hreach.
 set (next := R.materialize (P.clear_owner st owner) owner).
 set (fr := R.fresh_frame next owner (U.initial_phase false owner)).
 assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}=
 Some {|R.cfg_state:=next;R.cfg_control:=R.RunRhs fr (tf owner) k|}) by reflexivity.
 assert (Hclean : R.queue_contains owner (R.queue next)=false).
 { unfold next,R.materialize. destruct (M.lookup (R.sigma (P.clear_owner st owner)) owner);
   apply B.queue_contains_false,P.clear_owner_not_queued. }
 destruct (@rounds tf roots finite owner k Hchildren _ next fr (tf owner) eq_refl eq_refl
 (Episodes.reached Hreach Hstep) Hclean) as [done [Hdone Hbelow]].
 exists done. split;[econstructor;[exact Hstep |exact Hdone] |exact Hbelow].
Qed.
Lemma comparable tf first left right :
 N.steps tf first left -> N.steps tf first right ->
 N.steps tf left right \/ N.steps tf right left.
Proof.
 intro Hleft. revert right. induction Hleft;intros right Hright.
 - left;exact Hright.
 - inversion Hright as [|first' next' last' Hnext Htail];subst.
   + right;econstructor;eassumption.
   + assert (Heq : next'=next) by (rewrite H in Hnext;inversion Hnext;reflexivity). subst next'.
     apply IHHleft,Htail.
Qed.
Lemma ranks_agree tf roots left right owner a b :
 N.steps tf (R.initial_config roots) left -> N.steps tf (R.initial_config roots) right ->
 R.Ranking.lookup (R.ranking (R.cfg_state left)) owner=Some a ->
 R.Ranking.lookup (R.ranking (R.cfg_state right)) owner=Some b -> a=b.
Proof.
 intros Hleft Hright Ha Hb. destruct (comparable Hleft Hright) as [Hsteps|Hsteps].
 - pose proof (@Episodes.steps_extends tf _ _ Hsteps owner a Ha). congruence.
 - pose proof (@Episodes.steps_extends tf _ _ Hsteps owner b Hb). congruence.
Qed.
Theorem ranked tf roots (finite : B.Sem.finite_system tf roots) :
 forall bound st owner k rank,
 rank+bound=B.Finite.bound (B.Sem.support finite) ->
 R.Ranking.lookup (R.ranking st) owner=Some rank ->
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|} ->
 Episodes.complete tf owner k {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}.
Proof.
 intro bound. induction bound as [bound IH] using Wf_nat.lt_wf_ind.
 intros st owner k rank Hbound Hrank Hreach.
 apply (@start tf roots finite st owner k);[ |exact Hreach].
 intros child_st target child_k Hhigher Hchild.
 unfold R.rank_lt,R.ranking_lt in Hhigher.
 destruct (R.Ranking.lookup (R.ranking child_st) owner) as [owner_rank|] eqn:Howner;[ |discriminate].
 destruct (R.Ranking.lookup (R.ranking child_st) target) as [target_rank|] eqn:Htarget;[ |discriminate].
 assert (Hsame : rank=owner_rank) by (eapply ranks_agree;[exact Hreach |exact Hchild |exact Hrank |exact Howner]).
 subst owner_rank. apply Nat.ltb_lt in Hhigher.
 pose proof (@Episodes.rank_bound tf roots finite _ target target_rank Hchild Htarget) as Hcap.
 eapply (IH (B.Finite.bound (B.Sem.support finite)-target_rank));[lia | |exact Htarget |exact Hchild]. lia.
Qed.
Theorem all_episodes tf roots (finite : B.Sem.finite_system tf roots) st owner k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|} ->
 Episodes.complete tf owner k {|R.cfg_state:=st;R.cfg_control:=R.StartEpisode owner k|}.
Proof.
 intro Hreach.
 pose proof (proj1 (B.configuration_control_ranked (reachable_ranked Hreach))) as Howner.
 destruct Howner as [rank Hrank].
 pose proof (@Episodes.rank_bound tf roots finite _ owner rank Hreach Hrank) as Hcap.
 eapply (@ranked tf roots finite (B.Finite.bound (B.Sem.support finite)-rank) st owner k rank);
 [lia |exact Hrank |exact Hreach].
Qed.
End EpisodeTermination.

Module Termination.
Definition loop_control (mode : option (list V.t)) :=
 match mode with None=>R.RunLoop |Some pending=>R.RunSeedLoop pending end.
Definition loop_continuation (mode : option (list V.t)) :=
 match mode with None=>R.KLoop |Some pending=>R.KSeedLoop pending end.
Definition loop_done (mode : option (list V.t)) :=
 match mode with None=>R.RunLoop |Some pending=>R.RunSeeds pending end.
Definition loop_finishes tf mode start :=
 exists st,N.steps tf start {|R.cfg_state:=st;R.cfg_control:=loop_done mode|} /\ Sem.quiescent st.
Definition queue_bound st bound :=
 forall target rest rank,R.queue_pop (R.queue st)=Some (target,rest) ->
 R.Ranking.lookup (R.ranking st) target=Some rank -> rank<bound.
Lemma pop_none queue : R.queue_pop queue=None -> R.queue_peek queue=None.
Proof. destruct queue;[reflexivity |discriminate]. Qed.
Lemma loop_empty tf mode st :
 R.queue_pop (R.queue st)=None ->
 loop_finishes tf mode {|R.cfg_state:=st;R.cfg_control:=loop_control mode|}.
Proof.
 intro Hpop. exists st. split;[ |apply pop_none,Hpop].
 destruct mode;[apply Episodes.one;cbn -[R.queue_pop];now rewrite Hpop |constructor].
Qed.
Lemma pop_step tf mode st target rest :
 R.queue_pop (R.queue st)=Some (target,rest) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=loop_control mode|}=
 Some {|R.cfg_state:=R.with_queue st rest;R.cfg_control:=R.StartEpisode target (loop_continuation mode)|}.
Proof. intro Hpop. destruct mode;cbn -[R.queue_pop];now rewrite Hpop. Qed.
Lemma return_step tf mode st :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return (loop_continuation mode)|}=
 Some {|R.cfg_state:=st;R.cfg_control:=loop_control mode|}.
Proof. destruct mode;reflexivity. Qed.
Lemma below_bound st target rank :
 T.queue_strictly_below target st -> R.Ranking.lookup (R.ranking st) target=Some rank ->
 queue_bound st rank.
Proof.
 intros Hbelow Hrank candidate rest nr Hpop Hlookup.
 pose proof (Hbelow candidate (@T.queue_pop_member _ _ _ Hpop)) as Hlt.
 unfold R.rank_lt,R.ranking_lt in Hlt. rewrite Hlookup,Hrank in Hlt. apply Nat.ltb_lt,Hlt.
Qed.
Lemma loop_bounded tf roots (finite : B.Sem.finite_system tf roots) mode bound :
 forall st,N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=loop_control mode|} ->
 queue_bound st bound ->
 loop_finishes tf mode {|R.cfg_state:=st;R.cfg_control:=loop_control mode|}.
Proof.
 induction bound as [bound IH] using Wf_nat.lt_wf_ind. intros st Hreach Hbound.
 destruct (R.queue_pop (R.queue st)) as [[target rest]|] eqn:Hpop;[ |apply loop_empty,Hpop].
 pose proof (@pop_step tf mode st target rest Hpop) as Hstep.
 assert (Htarget : B.ranked st target).
 { apply (B.data_queue_ranked (B.configuration_state_data (reachable_ranked Hreach))).
   exact (@T.queue_pop_member _ _ _ Hpop). }
 destruct Htarget as [rank Hrank].
 destruct (@EpisodeTermination.all_episodes tf roots finite (R.with_queue st rest) target (loop_continuation mode)
 (Episodes.reached Hreach Hstep)) as [done [Hepisode Hbelow]].
 assert (Hdone : N.steps tf (R.initial_config roots)
 {|R.cfg_state:=done;R.cfg_control:=loop_control mode|}).
 { eapply steps_append;[exact (Episodes.reached Hreach Hstep) |].
   eapply steps_append;[exact Hepisode |apply Episodes.one,return_step]. }
 assert (Hrank' : R.Ranking.lookup (R.ranking done) target=Some rank)
 by (exact (@Episodes.steps_extends tf _ _ Hepisode target rank Hrank)).
 destruct (IH rank (Hbound target rest rank Hpop Hrank) done Hdone (below_bound Hbelow Hrank'))
 as [final [Hfinal Hquiet]].
 exists final. split;[ |exact Hquiet].
 econstructor;[exact Hstep |]. eapply steps_append;[exact Hepisode |].
 econstructor;[apply return_step |exact Hfinal].
Qed.
Theorem loop_completes tf roots (finite : B.Sem.finite_system tf roots) mode st :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=loop_control mode|} ->
 loop_finishes tf mode {|R.cfg_state:=st;R.cfg_control:=loop_control mode|}.
Proof.
 intro Hreach. eapply (@loop_bounded tf roots finite mode (B.Finite.bound (B.Sem.support finite)) st);[exact Hreach |].
 intros target rest rank Hpop Hrank. exact (@Episodes.rank_bound tf roots finite _ target rank Hreach Hrank).
Qed.
Definition finishes tf start :=
 exists final,N.steps tf start (Sem.terminal_config final) /\ Sem.quiescent final.
Lemma prepend tf before after :
 N.steps tf before after -> finishes tf after -> finishes tf before.
Proof.
 intros Hsteps [final [Hfinal Hquiet]]. exists final. split;[eapply steps_append;eassumption |exact Hquiet].
Qed.
Lemma seed_done tf roots (finite : B.Sem.finite_system tf roots) pending :
 (forall st,N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds pending|} ->
 finishes tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds pending|}) ->
 forall st,N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KSeedLoop pending)|} ->
 finishes tf {|R.cfg_state:=st;R.cfg_control:=R.Return (R.KSeedLoop pending)|}.
Proof.
 intros IH st Hreach.
 pose proof (@return_step tf (Some pending) st) as Hstep.
 destruct (@loop_completes tf roots finite (Some pending) st (Episodes.reached Hreach Hstep))
 as [done [Hloop Hquiet]].
 eapply prepend;[apply Episodes.one,Hstep |]. eapply prepend;[exact Hloop |].
 apply IH. eapply steps_append;[exact (Episodes.reached Hreach Hstep) |exact Hloop].
Qed.
Theorem seeds tf roots (finite : B.Sem.finite_system tf roots) pending :
 forall st,N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds pending|} ->
 finishes tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds pending|}.
Proof.
 induction pending as [|owner pending IH];intros st Hreach.
 - assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds []|}=
   Some {|R.cfg_state:=st;R.cfg_control:=R.RunLoop|}) by reflexivity.
   eapply prepend;[apply Episodes.one,Hstep |].
   exact (@loop_completes tf roots finite None st (Episodes.reached Hreach Hstep)).
 - destruct (R.is_materialized (R.observe st owner) owner) eqn:Hmat.
   + assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds (owner::pending)|}=
     Some {|R.cfg_state:=R.observe st owner;R.cfg_control:=R.RunSeeds pending|}).
     { cbn -[R.observe]. now rewrite Hmat. }
     eapply prepend;[apply Episodes.one,Hstep |]. apply IH, (Episodes.reached Hreach Hstep).
   + assert (Hstep : N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunSeeds (owner::pending)|}=
     Some {|R.cfg_state:=R.observe st owner;R.cfg_control:=R.StartEpisode owner (R.KSeedLoop pending)|}).
     { cbn -[R.observe]. now rewrite Hmat. }
     destruct (@EpisodeTermination.all_episodes tf roots finite (R.observe st owner) owner (R.KSeedLoop pending)
     (Episodes.reached Hreach Hstep)) as [done [Hepisode Hbelow]].
     eapply prepend;[apply Episodes.one,Hstep |]. eapply prepend;[exact Hepisode |].
     eapply (@seed_done tf roots finite pending IH).
     eapply steps_append;[exact (Episodes.reached Hreach Hstep) |exact Hepisode].
Qed.
Theorem terminates tf roots (finite : B.Sem.finite_system tf roots) :
 finishes tf (R.initial_config roots).
Proof. exact (@seeds tf roots finite roots _ (N.steps_refl tf _)). Qed.
Lemma steps_fuel tf first last :
 N.steps tf first last -> exists fuel,N.run_fuel fuel tf first=last.
Proof.
 intro Hsteps. induction Hsteps.
 - exists 0;reflexivity.
 - destruct IHHsteps as [fuel Hfuel]. exists (S fuel). cbn. now rewrite H,Hfuel.
Qed.
Theorem sufficient_fuel_base tf roots (finite : B.Sem.finite_system tf roots) :
 exists fuel final,N.solve_fuel fuel tf roots=Some final.
Proof.
 destruct (terminates finite) as [final [Hsteps Hquiet]].
 destruct (steps_fuel Hsteps) as [fuel Hfuel]. exists fuel,final.
 unfold N.solve_fuel. rewrite Hfuel. unfold R.terminal_state,Sem.terminal_config. cbn.
 unfold Sem.quiescent in Hquiet. now rewrite Hquiet.
Qed.
Theorem sufficient_fuel tf roots (finite : Sem.finite_system tf roots) :
 exists fuel final,N.solve_fuel fuel tf roots=Some final.
Proof. exact (@sufficient_fuel_base tf roots (@Support.finite_bridge tf roots finite)). Qed.
(** Final-state termination for the public theorem interface. *)
Definition terminates_to tf roots final : Prop :=
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) /\ Sem.quiescent final.

Theorem solver_terminates : forall tf roots,
 Sem.finite_system tf roots -> exists final, terminates_to tf roots final.
Proof.
 intros tf roots finite.
 exact (@terminates tf roots (@Support.finite_bridge tf roots finite)).
Qed.
End Termination.
(** Shared public specifications are bound here, outside extraction dependencies. *)
  Module Store.
    Definition state := R.state.
    Definition sigma := R.sigma.
    Definition sigma_value := R.sigma_value.
  End Store.
  Module TransferView.
    Definition rhs := Sem.ConstraintSyntax.rhs.
    Definition observation := Sem.observation.
    Definition observed_sides := Sem.observed_sides.
    Definition observed_spawns := Sem.observed_spawns.
    Definition observes_at := Sem.observes_at.
    Definition rhs_observes := Sem.rhs_observes.
    Definition rhs_eval_with := Sem.rhs_eval_with.
    Definition rhs_dependencies_monotone := Sem.rhs_dependencies_monotone.
    Definition rhs_effects_monotone := Sem.rhs_effects_monotone.
  End TransferView.
  Module Spec := SolverSpecifications.Make V D M TransferView Store.

  Theorem successful_run_spawn_correct : forall fuel tf roots final,
    N.solve_fuel fuel tf roots = Some final -> Spec.correct_final_state tf roots final.
  Proof.
    intros fuel tf roots final Hrun. split.
    - intros owner Hin.
      exact (proj1 (@successful_run_correct fuel tf roots final Hrun owner Hin)).
    - intros owner Hsolved.
      destruct (@successful_run_replay_post_solution fuel tf roots final Hrun owner Hsolved)
        as [Hexists Hpost]. split; [exact Hexists |]. split; [exact Hpost |].
      intros result Hobs target Hin.
      destruct (@Demand.successful_run_spawned fuel tf roots final Hrun owner Hsolved)
        as [canonical [Hcanonical [Hreplay Hspawned]]].
      assert (Hcanonical_at : Sem.observes_at (R.sigma_value final) (tf owner) canonical).
      { split; [exact Hcanonical |]. intros read value Hread.
        eapply replay_read_value; eassumption. }
      pose proof (Sem.observes_at_deterministic Hcanonical_at Hobs) as Hequal.
      subst result. exact (Hspawned target Hin).
  Qed.

End Make.
