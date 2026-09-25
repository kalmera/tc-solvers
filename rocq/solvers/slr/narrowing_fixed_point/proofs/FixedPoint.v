From Stdlib Require Import Bool List Lia Arith.PeanoNat.
From TcSolvers Require Import common.Assumptions common.BoxUpdate
  solvers.slr.narrowing_fixed_point.proofs.Replay.
Import ListNotations.
Set Implicit Arguments.

(** Descending side publications and complete episode preservation.
    The executable commit barrier establishes settled cells and covered inputs.
    The reachable episode invariant derives ordinary narrowing admissibility
    from operational monotonicity; it is not a public solver assumption. *)

Module Make (V : VAR) (D : DOMAIN) (WN : WIDEN_NARROW D).
Module Descent.
  Module U := OneBoxUpdate V D WN.
    Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
      (WS : WIDEN_STABILITY D WN).

      Definition equivalent (x y : D.t) := D.leq x y = true /\ D.leq y x = true.

      Lemma update_sound is_side variable phase old input :
        D.leq input (snd (U.update is_side variable phase old input)) = true.
      Proof.
        destruct phase; cbn -[D.leq]; [| |apply WNL.widen_upper_input].
        all: destruct (D.leq input old) eqn:Hle; cbn;
          [apply WNL.narrow_lower, Hle |apply WNL.widen_upper_input].
      Qed.

      Lemma stable_smaller_input_bounded
        is_side variable phase old input smaller :
        equivalent (snd (U.update is_side variable phase old input)) old ->
        D.leq smaller input = true ->
        D.leq (snd (U.update is_side variable phase old smaller)) old = true.
      Proof.
        intros Hstable Hsmaller.
        assert (Hinput : D.leq input old = true).
        { eapply DL.leq_trans; [apply update_sound |exact (proj1 Hstable)]. }
        assert (Hbelow : D.leq smaller old = true).
        { eapply DL.leq_trans; eassumption. }
        destruct phase; cbn -[D.leq] in *.
        - rewrite Hbelow. apply WNL.narrow_upper, Hbelow.
        - rewrite Hbelow. apply WNL.narrow_upper, Hbelow.
        - exact (proj1 (WS.widen_stable Hbelow)).
      Qed.
    End WithLaws.
End Descent.
Module U := Descent.U.
Module WithLaws (DL : DOMAIN_LAWS D) (WNL : WIDEN_NARROW_LAWS D WN)
 (WS : WIDEN_STABILITY D WN) (UL : UPDATE_LAWS V D U).
Module A := Descent.WithLaws DL WNL WS.
Definition settled is_side variable phase value :=
 phase = U.Widen ->
 UL.equivalent (snd (U.update is_side variable U.Widen value value)) value.
Lemma stable_settled is_side variable phase value input :
 UL.equivalent (snd (U.update is_side variable phase value input)) value ->
 settled is_side variable phase value.
Proof.
 intros _ Hphase. subst phase.
 apply WS.widen_stable, DL.leq_refl.
Qed.
Lemma settled_widen_stutters is_side variable value input :
 settled is_side variable U.Widen value -> D.leq input value = true ->
 UL.equivalent (snd (U.update is_side variable U.Widen value input)) value.
Proof.
 intros _ Hinput. apply WS.widen_stable, Hinput.
Qed.
Lemma settled_update_descends is_side variable phase value input :
 settled is_side variable phase value -> D.leq input value = true ->
 D.leq (snd (U.update is_side variable phase value input)) value = true.
Proof.
 intros Hsettled Hinput. destruct phase.
 - cbn -[D.leq]. rewrite Hinput. apply WNL.narrow_upper, Hinput.
 - cbn -[D.leq]. rewrite Hinput. apply WNL.narrow_upper, Hinput.
 - apply settled_widen_stutters; assumption.
Qed.
Lemma settled_update_preserved is_side variable phase value input :
 settled is_side variable phase value -> D.leq input value = true ->
 settled is_side variable (fst (U.update is_side variable phase value input))
 (snd (U.update is_side variable phase value input)).
Proof.
 intros Hsettled Hinput. destruct phase.
 - cbn -[D.leq]. rewrite Hinput. unfold settled. discriminate.
 - cbn -[D.leq]. rewrite Hinput. unfold settled. discriminate.
 - pose proof (settled_widen_stutters Hsettled Hinput) as Hstable.
   apply stable_settled with input.
   apply UL.update_stutter_closed; [exact Hstable |exact Hstable |split; apply DL.leq_refl].
Qed.
Lemma reset_settled is_side variable value :
 settled is_side variable (U.initial_phase is_side variable) value.
Proof. unfold settled, U.initial_phase. discriminate. Qed.

Module WithCollections (S : SET V) (M : MAP V)
 (Features : Base.FEATURES) (SL : SET_LAWS V S) (ML : MAP_LAWS V M).
Module Replay := Replay.Make V D U S M Features DL UL SL ML.
Import Replay.Front.
Module PS := Replay.PS.
Module C := PS.C.
Module B := C.H.B.
Module R := C.R.
Definition cell_settled st source target :=
 settled true target (R.side_phase (R.stored_side_cell st source target))
 (R.stored_contribution st source target).
Lemma stable_cell_settled st source target input :
 PS.cell_stable st source target input -> cell_settled st source target.
Proof. unfold cell_settled. apply stable_settled. Qed.
Lemma write_settled_descends st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
 D.leq (R.stored_contribution next (R.frame_owner fr) target)
 (R.stored_contribution st (R.frame_owner fr) target) = true /\
 cell_settled next (R.frame_owner fr) target.
Proof.
 intros Hw Hsettled Hinput. unfold R.write_side_contribution in Hw.
 set (base := R.promote_side_target st fr target) in *.
 assert (Hvalue : R.stored_contribution base (R.frame_owner fr) target =
   R.stored_contribution st (R.frame_owner fr) target).
 { subst base. unfold R.promote_side_target.
   destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
 assert (Hcell : R.stored_side_cell base (R.frame_owner fr) target =
   R.stored_side_cell st (R.frame_owner fr) target).
 { subst base. unfold R.promote_side_target.
   destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
 rewrite Hvalue, Hcell in Hw.
 destruct (U.update true target (R.side_phase (R.stored_side_cell st (R.frame_owner fr) target))
 (R.stored_contribution st (R.frame_owner fr) target) input) as [phase value] eqn:Hu.
 cbn in Hw. inversion Hw; subst next changed.
 unfold cell_settled. rewrite PS.phase_after_update, C.stored_after_update.
 pose proof (settled_update_descends Hsettled Hinput) as Hdown.
 pose proof (settled_update_preserved Hsettled Hinput) as Hnext.
 rewrite Hu in Hdown,Hnext. now split.
Qed.
Theorem committing_publication_settled tf st fr direct k after next_fr next_k target :
 N.next_config tf {| R.cfg_state := R.publish_targets
 (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr;
 R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 S.mem target (R.frame_current_targets fr) = true ->
 cell_settled (R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr)
 (R.frame_owner fr) target.
Proof.
 intros Hstep Hmem. eapply stable_cell_settled.
 eapply PS.committing_publication_stable; [exact Hstep |exact Hmem].
Qed.

Lemma reset_cells_lookup ids cells source target :
 M.lookup (R.lookup_map (R.reset_cells ids cells) source) target =
 M.lookup (R.lookup_map cells source) target \/
 M.lookup (R.lookup_map (R.reset_cells ids cells) source) target =
 Some (R.default_side_cell target).
Proof.
 revert cells. induction ids as [|[s t] rest IH]; intro cells; cbn; [now left |].
 destruct (IH (R.update_map cells s t (R.default_side_cell t))) as [Hsame|Hfresh];
 [|now right]. rewrite Hsame.
 destruct (V.eq_dec source s) as [->|Hsource], (V.eq_dec target t) as [->|Htarget].
 - right. apply B.lookup_update_map_same.
 - left. apply B.Credits.lookup_cell_update_other. congruence.
 - left. apply B.Credits.lookup_cell_update_other. congruence.
 - left. apply B.Credits.lookup_cell_update_other. congruence.
Qed.
Lemma reset_preserves_settled st scope source target :
 cell_settled st source target ->
 cell_settled (R.reset_registered_cells st scope) source target.
Proof.
 intro Hsettled. unfold R.reset_registered_cells.
 destruct Features.restart_side_phases; [|exact Hsettled].
 unfold cell_settled, R.stored_side_cell. cbn.
 destruct (reset_cells_lookup (R.lookup_reset_ids (R.reset_at_close st) scope)
 (R.side_cells st) source target) as [Hsame|Hfresh].
 - rewrite Hsame. exact Hsettled.
 - rewrite Hfresh. apply reset_settled.
Qed.
Lemma row_update_descends st source target value :
 D.leq value (R.stored_contribution st source target) = true ->
 D.leq (R.aggregate (R.with_contributions st
 (R.update_map (R.contributions st) target source value)) target)
 (R.aggregate st target) = true.
Proof.
 intro Hvalue. unfold R.aggregate. cbn. unfold R.update_map, R.lookup_map.
 rewrite ML.lookup_update_same.
 set (row := R.lookup_map (R.contributions st) target) in *.
 destruct (ML.values_update row source value) as [rest [Hnew Hold]].
 pose proof (B.Credits.join_values_permutation Hnew) as Hnewle.
 eapply DL.leq_trans; [exact (proj1 Hnewle) |].
 destruct (M.lookup row source) as [previous|] eqn:Hlookup.
 - pose proof (B.Credits.join_values_permutation Hold) as Holdle.
   eapply DL.leq_trans; [|exact (proj2 Holdle)]. cbn.
   unfold R.stored_contribution in Hvalue. fold row in Hvalue. rewrite Hlookup in Hvalue.
   apply DL.join_least; [|apply DL.join_upper_right].
   eapply DL.leq_trans; [exact Hvalue |apply DL.join_upper_left].
 - pose proof (B.Credits.join_values_permutation Hold) as Holdle.
   eapply DL.leq_trans; [|exact (proj2 Holdle)]. cbn.
   unfold R.stored_contribution in Hvalue. fold row in Hvalue. rewrite Hlookup in Hvalue.
   apply DL.join_least; [|apply DL.leq_refl].
   eapply DL.leq_trans; [exact Hvalue |apply DL.bottom_least].
Qed.

Definition contributions_descend before after :=
 forall source target, D.leq (R.stored_contribution after source target)
 (R.stored_contribution before source target) = true.
Definition aggregates_descend before after :=
 forall target, D.leq (R.aggregate after target) (R.aggregate before target) = true.
Lemma write_contributions_descend st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 D.leq (R.stored_contribution next (R.frame_owner fr) target)
 (R.stored_contribution st (R.frame_owner fr) target) = true ->
 contributions_descend st next.
Proof.
 intros Hw Hdown source observed.
 destruct (V.eq_dec source (R.frame_owner fr)) as [->|Hs],
 (V.eq_dec observed target) as [->|Ht]; [exact Hdown | | |].
 all: rewrite (B.Credits.stored_contribution_write_other Hw) by congruence;
 apply DL.leq_refl.
Qed.
Lemma write_aggregates_descend st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 D.leq (R.stored_contribution next (R.frame_owner fr) target)
 (R.stored_contribution st (R.frame_owner fr) target) = true ->
 aggregates_descend st next.
Proof.
 intros Hw Hdown observed. destruct (V.eq_dec observed target) as [->|Hother].
 - unfold R.write_side_contribution in Hw.
   destruct (U.update true target
   (R.side_phase (R.stored_side_cell (R.promote_side_target st fr target) (R.frame_owner fr) target))
   (R.stored_contribution (R.promote_side_target st fr target) (R.frame_owner fr) target)
   input) as [phase value] eqn:Hu.
   cbn in Hw. inversion Hw; subst next changed.
   rewrite C.stored_after_update in Hdown.
   rewrite B.aggregate_register_reset.
   rewrite <- (B.Credits.aggregate_promote_side_target st fr target).
   apply row_update_descends.
   unfold R.promote_side_target.
   destruct (R.rank_lt st target (R.frame_owner fr)); exact Hdown.
 - unfold R.aggregate. rewrite (B.write_side_contribution_other Hw Hother).
   apply DL.leq_refl.
Qed.
Definition local_input fr target :=
 match M.lookup (R.frame_local_side fr) target with
 Some value => value | None => D.bottom end.
Definition publication_ready targets st fr :=
 forall target, List.In target targets ->
 cell_settled st (R.frame_owner fr) target /\
 D.leq (local_input fr target) (R.stored_contribution st (R.frame_owner fr) target) = true.
Lemma finish_ready targets before after fr target changed :
 publication_ready targets after fr ->
 publication_ready targets (C.finish_write before after fr target changed) fr.
Proof.
 unfold publication_ready, cell_settled, C.finish_write, C.requeue_source.
 destruct changed, C.cell_changed; trivial.
Qed.
Lemma write_ready targets st fr target next changed :
 publication_ready targets st fr -> List.In target targets ->
 R.write_side_contribution st fr target (local_input fr target) = (next,changed) ->
 publication_ready targets next fr.
Proof.
 intros Hready Hin Hw observed Hobs.
 destruct (V.eq_dec observed target) as [->|Hother].
 - destruct (Hready target Hin) as [Hsettled Hinput]. split.
   + exact (proj2 (write_settled_descends Hw Hsettled Hinput)).
   + destruct (B.write_side_contribution_records_input Hw) as [value [Hlookup Hle]].
     unfold R.stored_contribution. rewrite Hlookup. exact Hle.
 - destruct (Hready observed Hobs) as [Hsettled Hinput].
   unfold cell_settled in *.
   rewrite (B.Credits.stored_side_cell_write_other Hw) by congruence.
   rewrite (B.Credits.stored_contribution_write_other Hw) by congruence.
   now split.
Qed.
Lemma finish_contributions before after fr target changed :
 contributions_descend after (C.finish_write before after fr target changed).
Proof.
 unfold contributions_descend, C.finish_write, C.requeue_source.
 destruct changed, C.cell_changed; intros; apply DL.leq_refl.
Qed.
Lemma finish_aggregates before after fr target changed :
 aggregates_descend after (C.finish_write before after fr target changed).
Proof.
 unfold aggregates_descend, C.finish_write, C.requeue_source.
 destruct changed, C.cell_changed; intros; apply DL.leq_refl.
Qed.

Theorem publish_descends targets support st fr :
 List.incl targets support -> publication_ready support st fr ->
 contributions_descend st (C.publish targets st fr) /\
 aggregates_descend st (C.publish targets st fr) /\
 publication_ready support (C.publish targets st fr) fr.
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hin Hready;
 cbn -[R.write_side_contribution C.finish_write].
 - split; [intros source observed; apply DL.leq_refl |].
   split; [intro observed; apply DL.leq_refl |exact Hready].
 - fold (local_input fr target).
   destruct (R.write_side_contribution st fr target (local_input fr target))
   as [next changed] eqn:Hw.
   assert (Hmember : List.In target support) by (apply Hin; now left).
   assert (Hnext : publication_ready support (C.finish_write st next fr target changed) fr).
   { apply finish_ready. eapply write_ready; eassumption. }
   destruct (IH (C.finish_write st next fr target changed)
     (fun x Hx => Hin x (or_intror Hx)) Hnext) as [Hcells [Haggregates Hready']].
   destruct (Hready target Hmember) as [Hsettled Hinput].
   pose proof (proj1 (write_settled_descends Hw Hsettled Hinput)) as Hdown.
   split.
   + intros source observed. eapply DL.leq_trans; [apply Hcells |].
     eapply DL.leq_trans; [apply finish_contributions |].
     eapply write_contributions_descend; eassumption.
   + split; [|exact Hready']. intro observed.
     eapply DL.leq_trans; [apply Haggregates |].
     eapply DL.leq_trans; [apply finish_aggregates |].
     eapply write_aggregates_descend; eassumption.
Qed.
Theorem committing_publication_ready tf st fr direct k after next_fr next_k :
 N.next_config tf {| R.cfg_state := R.publish_targets
 (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr;
 R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 publication_ready (S.elements (R.frame_current_targets fr))
 (R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr) fr.
Proof.
 intros Hstep target Hin. apply SL.mem_spec in Hin.
 pose proof (@PS.committing_publication_stable tf st fr direct k after next_fr next_k target Hstep Hin) as Hstable.
 split; [eapply stable_cell_settled; exact Hstable |].
 eapply PS.stable_covers_input; exact Hstable.
Qed.
Lemma smaller_publication_ready targets support st previous fr :
 R.frame_owner fr = R.frame_owner previous ->
 List.incl targets support -> publication_ready support st previous ->
 (forall target, List.In target targets ->
 D.leq (local_input fr target) (local_input previous target) = true) ->
 publication_ready targets st fr.
Proof.
 intros Howner Hin Hready Hsmaller target Htarget.
 destruct (Hready target (Hin target Htarget)) as [Hsettled Hinput].
 rewrite Howner. split; [exact Hsettled |].
 eapply DL.leq_trans; [apply Hsmaller, Htarget |exact Hinput].
Qed.
Corollary smaller_publication_descends targets support st previous fr :
 R.frame_owner fr = R.frame_owner previous ->
 List.incl targets support -> publication_ready support st previous ->
 (forall target, List.In target targets ->
 D.leq (local_input fr target) (local_input previous target) = true) ->
 contributions_descend st (C.publish targets st fr) /\
 aggregates_descend st (C.publish targets st fr) /\
 publication_ready targets (C.publish targets st fr) fr.
Proof.
 intros Howner Hin Hready Hsmaller. apply publish_descends.
 - intros target Htarget. exact Htarget.
 - eapply smaller_publication_ready; eassumption.
Qed.

Lemma settled_narrow_credit_nonincreasing is_side variable phase value input :
 settled is_side variable phase value -> D.leq input value = true ->
 UL.remaining_changes U.BoxN (snd (U.update is_side variable phase value input)) <=
 UL.remaining_changes U.BoxN value.
Proof.
 intros Hsettled Hinput.
 pose proof (UL.remaining_changes_nonincreasing is_side variable U.BoxN value input) as Hcredit.
 cbn -[D.leq] in Hcredit. rewrite Hinput in Hcredit. cbn in Hcredit.
 destruct phase; cbn -[D.leq]; try (rewrite Hinput; exact Hcredit).
 pose proof (@UL.remaining_changes_extensional U.BoxN _ _
 (settled_widen_stutters Hsettled Hinput)) as Heq. cbn in Heq. now rewrite Heq.
Qed.
Lemma settled_change_narrow_credit is_side variable phase value input :
 settled is_side variable phase value -> D.leq input value = true ->
 ~ UL.equivalent (snd (U.update is_side variable phase value input)) value ->
 UL.remaining_changes U.BoxN (snd (U.update is_side variable phase value input)) <
 UL.remaining_changes U.BoxN value.
Proof.
 intros Hsettled Hinput Hchange.
 pose proof (@UL.update_change_consumes is_side variable U.BoxN value input) as Hcredit.
 cbn -[D.leq] in Hcredit. rewrite Hinput in Hcredit. cbn in Hcredit.
 destruct phase; cbn -[D.leq] in *; try (rewrite Hinput in *; now apply Hcredit).
 exfalso. apply Hchange. exact (settled_widen_stutters Hsettled Hinput).
Qed.

Lemma write_update st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 U.update true target (R.side_phase (R.stored_side_cell st (R.frame_owner fr) target))
 (R.stored_contribution st (R.frame_owner fr) target) input =
 (R.side_phase (R.stored_side_cell next (R.frame_owner fr) target),
 R.stored_contribution next (R.frame_owner fr) target).
Proof.
 intro Hw. unfold R.write_side_contribution in Hw.
 assert (Hcell : R.stored_side_cell (R.promote_side_target st fr target) (R.frame_owner fr) target =
 R.stored_side_cell st (R.frame_owner fr) target).
 { unfold R.promote_side_target. destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
 assert (Hvalue : R.stored_contribution (R.promote_side_target st fr target) (R.frame_owner fr) target =
 R.stored_contribution st (R.frame_owner fr) target).
 { unfold R.promote_side_target. destruct (R.rank_lt st target (R.frame_owner fr)); reflexivity. }
 rewrite Hcell,Hvalue in Hw.
 destruct (U.update true target (R.side_phase (R.stored_side_cell st (R.frame_owner fr) target))
 (R.stored_contribution st (R.frame_owner fr) target) input) as [phase value] eqn:Hu.
 cbn in Hw. inversion Hw; subst next changed.
 rewrite PS.phase_after_update, C.stored_after_update. reflexivity.
Qed.
Lemma write_narrow_credit st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
 UL.remaining_changes U.BoxN (R.stored_contribution next (R.frame_owner fr) target) <=
 UL.remaining_changes U.BoxN (R.stored_contribution st (R.frame_owner fr) target).
Proof.
 intros Hw Hsettled Hinput.
 pose proof (settled_narrow_credit_nonincreasing Hsettled Hinput) as Hcredit.
 rewrite (write_update Hw) in Hcredit. exact Hcredit.
Qed.
Lemma changed_write_narrow_credit st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
 C.cell_changed st next (R.frame_owner fr) target = true ->
 UL.remaining_changes U.BoxN (R.stored_contribution next (R.frame_owner fr) target) <
 UL.remaining_changes U.BoxN (R.stored_contribution st (R.frame_owner fr) target).
Proof.
 intros Hw Hsettled Hinput Hchange.
 pose proof (settled_change_narrow_credit Hsettled Hinput) as Hcredit.
 rewrite (write_update Hw) in Hcredit. cbn in Hcredit. apply Hcredit.
 intros [Hnewold Holdnew]. unfold C.cell_changed,R.equivalent in Hchange.
 rewrite Hnewold,Holdnew in Hchange. discriminate.
Qed.
Fixpoint source_narrow_credit targets st source :=
 match targets with
 | nil => 0
 | target::rest => UL.remaining_changes U.BoxN (R.stored_contribution st source target) +
 source_narrow_credit rest st source
 end.
Lemma finish_narrow_credit support before after fr target changed source :
 source_narrow_credit support (C.finish_write before after fr target changed) source =
 source_narrow_credit support after source.
Proof.
 unfold C.finish_write,C.requeue_source.
 destruct changed,C.cell_changed; induction support; cbn -[R.stored_contribution]; try reflexivity.
 all: rewrite IHsupport; reflexivity.
Qed.
Lemma reset_narrow_credit support st scope source :
 source_narrow_credit support (R.reset_registered_cells st scope) source =
 source_narrow_credit support st source.
Proof.
 unfold R.reset_registered_cells. destruct Features.restart_side_phases;
 induction support; cbn -[R.stored_contribution]; try reflexivity.
 all: rewrite IHsupport; reflexivity.
Qed.
Lemma write_source_narrow_credit support st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
 source_narrow_credit support next (R.frame_owner fr) <=
 source_narrow_credit support st (R.frame_owner fr).
Proof.
 intros Hw Hsettled Hinput. induction support as [|head rest IH]; cbn; [reflexivity |].
 destruct (V.eq_dec head target) as [->|Hother].
 - pose proof (write_narrow_credit Hw Hsettled Hinput). lia.
 - rewrite (B.Credits.stored_contribution_write_other Hw) by congruence. lia.
Qed.
Lemma changed_source_narrow_credit support st fr target input next changed :
 List.In target support -> R.write_side_contribution st fr target input = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 D.leq input (R.stored_contribution st (R.frame_owner fr) target) = true ->
 C.cell_changed st next (R.frame_owner fr) target = true ->
 source_narrow_credit support next (R.frame_owner fr) <
 source_narrow_credit support st (R.frame_owner fr).
Proof.
 intros Hin Hw Hsettled Hinput Hchange.
 induction support as [|head rest IH]; [contradiction |]. cbn.
 destruct Hin as [->|Hin].
 - pose proof (changed_write_narrow_credit Hw Hsettled Hinput Hchange).
   pose proof (write_source_narrow_credit rest Hw Hsettled Hinput). lia.
 - destruct (V.eq_dec head target) as [->|Hother].
   + pose proof (changed_write_narrow_credit Hw Hsettled Hinput Hchange).
     pose proof (write_source_narrow_credit rest Hw Hsettled Hinput). lia.
   + rewrite (B.Credits.stored_contribution_write_other Hw) by congruence.
     specialize (IH Hin). lia.
Qed.

Lemma publish_narrow_credit targets support st fr :
 List.incl targets support -> publication_ready support st fr ->
 source_narrow_credit support (C.publish targets st fr) (R.frame_owner fr) <=
 source_narrow_credit support st (R.frame_owner fr).
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hin Hready;
 cbn -[R.write_side_contribution C.finish_write]; [reflexivity |].
 fold (local_input fr target).
 destruct (R.write_side_contribution st fr target (local_input fr target))
 as [next changed] eqn:Hw.
 assert (Hmember : List.In target support) by (apply Hin; now left).
 destruct (Hready target Hmember) as [Hsettled Hinput].
 eapply Nat.le_trans; [apply IH |].
 - intros x Hx. apply Hin. now right.
 - apply finish_ready. eapply write_ready; eassumption.
 - rewrite finish_narrow_credit. eapply write_source_narrow_credit; eassumption.
Qed.
Theorem changed_publication_narrow_credit targets support st fr :
 List.incl targets support -> publication_ready support st fr ->
 C.publication_changes targets st fr ->
 source_narrow_credit support (C.publish targets st fr) (R.frame_owner fr) <
 source_narrow_credit support st (R.frame_owner fr).
Proof.
 revert st. induction targets as [|target rest IH]; intros st Hin Hready Hchange;
 cbn -[R.write_side_contribution C.finish_write] in Hchange |- *; [contradiction |].
 fold (local_input fr target) in Hchange |- *.
 destruct (R.write_side_contribution st fr target (local_input fr target))
 as [next changed] eqn:Hw.
 assert (Hmember : List.In target support) by (apply Hin; now left).
 assert (Htail : List.incl rest support) by (intros x Hx; apply Hin; now right).
 assert (Hnext : publication_ready support (C.finish_write st next fr target changed) fr).
 { apply finish_ready. eapply write_ready; eassumption. }
 destruct (Hready target Hmember) as [Hsettled Hinput].
 destruct Hchange as [Hhead|Hrest].
 - eapply Nat.le_lt_trans; [apply publish_narrow_credit; eassumption |].
   rewrite finish_narrow_credit. eapply changed_source_narrow_credit; eassumption.
 - eapply Nat.lt_le_trans; [apply IH; eassumption |].
   rewrite finish_narrow_credit. eapply write_source_narrow_credit; eassumption.
Qed.
Lemma reset_publication_ready targets st fr scope :
 publication_ready targets st fr ->
 publication_ready targets (R.reset_registered_cells st scope) fr.
Proof.
 intros Hready target Hin. destruct (Hready target Hin) as [Hsettled Hinput].
 split; [apply reset_preserves_settled, Hsettled |].
 unfold R.reset_registered_cells. destruct Features.restart_side_phases; exact Hinput.
Qed.
Corollary dead_write_descends st fr target next changed :
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 cell_settled st (R.frame_owner fr) target ->
 contributions_descend st next /\ aggregates_descend st next /\
 cell_settled next (R.frame_owner fr) target.
Proof.
 intros Hw Hsettled.
 destruct (write_settled_descends Hw Hsettled (DL.bottom_least _)) as [Hdown Hnext].
 split; [eapply write_contributions_descend; eassumption |].
 split; [eapply write_aggregates_descend; eassumption |exact Hnext].
Qed.

Theorem reachable_commit_ready tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} ->
 N.next_config tf {| R.cfg_state := st; R.cfg_control := R.RunCommit fr direct k |} =
 Some {| R.cfg_state := after; R.cfg_control := R.RunDrain next_fr next_k |} ->
 publication_ready (S.elements (R.frame_current_targets fr)) st fr.
Proof.
 intros Hreach Hstep.
 destruct (Replay.reachable_commit_origin Hreach) as [before ->].
 eapply committing_publication_ready; exact Hstep.
Qed.
Definition live_settled st source :=
 forall target, S.mem target (R.lookup_set (R.last_targets st) source) = true ->
 cell_settled st source target.
Lemma live_settled_view before after source :
 R.last_targets after = R.last_targets before ->
 R.side_cells after = R.side_cells before ->
 R.contributions after = R.contributions before ->
 live_settled before source -> live_settled after source.
Proof.
 intros Htargets Hcells Hcontrib.
 unfold live_settled,cell_settled,R.stored_side_cell,R.stored_contribution.
 now rewrite Htargets,Hcells,Hcontrib.
Qed.
Lemma set_value_side_view st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) ->
 R.last_targets next = R.last_targets st /\
 R.side_cells next = R.side_cells st /\
 R.contributions next = R.contributions st.
Proof.
 intro Hset. unfold R.set_value in Hset.
 repeat match type of Hset with
 | context [if ?condition then _ else _] => destruct condition
 end;inversion Hset;repeat split;reflexivity.
Qed.
Theorem reachable_commit_live_settled tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 live_settled st (R.frame_owner fr).
Proof.
 intros Hreach Hstep target Hmem.
 destruct (Replay.reachable_commit_origin Hreach) as [before ->].
 unfold R.lookup_set in Hmem. cbn in Hmem. rewrite ML.lookup_update_same in Hmem.
 eapply committing_publication_settled;[exact Hstep |exact Hmem].
Qed.
Theorem actual_commit_live_settled tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 live_settled after (R.frame_owner fr).
Proof.
 intros Hreach Hstep.
 pose proof (@reachable_commit_live_settled tf roots st fr direct k after next_fr next_k Hreach Hstep) as Hlive.
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep.
 destruct (C.P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_frame] eqn:Hs.
 destruct (C.P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 inversion Hstep;subst.
 change (live_settled next (R.frame_owner fr)).
 destruct (@set_value_side_view st fr direct next next_fr Hs) as [Ht [Hc Hv]].
 eapply live_settled_view;eassumption.
Qed.
Lemma reset_live_settled st source scope :
 live_settled st source -> live_settled (R.reset_registered_cells st scope) source.
Proof.
 intros Hlive target Hmem. apply reset_preserves_settled,Hlive.
 unfold R.reset_registered_cells in Hmem.
 destruct Features.restart_side_phases;exact Hmem.
Qed.


Lemma live_observe st source target :
 live_settled st source -> live_settled (R.observe st target) source.
Proof.
 unfold R.observe. destruct (R.Ranking.observe (R.ranking st) target).
 eapply live_settled_view; reflexivity.
Qed.
Lemma live_materialize st source target :
 live_settled st source -> live_settled (R.materialize st target) source.
Proof.
 unfold R.materialize. destruct (M.lookup (R.sigma st) target).
 - trivial.
 - eapply live_settled_view; reflexivity.
Qed.
Lemma live_enqueue st source target :
 live_settled st source -> live_settled (R.enqueue st target) source.
Proof. eapply live_settled_view; reflexivity. Qed.
Lemma live_queue st source queue :
 live_settled st source -> live_settled (R.with_queue st queue) source.
Proof. eapply live_settled_view; reflexivity. Qed.
Lemma live_get st fr target next next_fr value source :
 R.complete_get st fr target = (next,next_fr,value) ->
 live_settled st source -> live_settled next source.
Proof.
 unfold R.complete_get. intro Hget. inversion Hget;subst next.
 intro Hlive. apply live_materialize.
 destruct (R.rank_lt st (R.frame_owner fr) target);
 eapply live_settled_view; try reflexivity; exact Hlive.
Qed.
Lemma live_set_value st fr direct next next_fr source :
 R.set_value st fr direct = (next,next_fr) ->
 live_settled st source -> live_settled next source.
Proof.
 intro Hset. destruct (@set_value_side_view st fr direct next next_fr Hset)
 as [Ht [Hc Hv]]. eapply live_settled_view;eassumption.
Qed.


Lemma live_read_step tf st fr target next k source after :
 live_settled st source ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> live_settled (R.cfg_state after) source.
Proof.
 intros Hlive Hstep.
 assert (Hobs : live_settled (R.observe st target) source)
 by (apply live_observe,Hlive).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst;exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. eapply live_get;[exact Hg |].
   subst current. destruct (R.is_materialized (R.observe st target) target);
   [exact Hobs |apply live_enqueue,Hobs].
Qed.
Lemma live_spawn_step tf st fr target next k source after :
 live_settled st source ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> live_settled (R.cfg_state after) source.
Proof.
 intros Hlive Hstep.
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst;apply live_observe,Hlive.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;[apply live_observe,Hlive |].
   apply live_materialize,live_enqueue,live_observe,Hlive.
Qed.
Lemma live_drain_step tf st fr k source after :
 live_settled st source ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> live_settled (R.cfg_state after) source.
Proof.
 intros Hlive Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hq in Hstep; cbn in Hstep.
 - inversion Hstep;subst;apply reset_live_settled,Hlive.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst;apply live_queue,Hlive.
   + destruct (R.rank_lt st (R.frame_owner fr) target);
     inversion Hstep;subst;[apply live_queue,Hlive |apply reset_live_settled,Hlive].
Qed.
Lemma live_return_step tf st k source after :
 live_settled st source ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> live_settled (R.cfg_state after) source.
Proof.
 intros Hlive Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;exact Hlive].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. eapply live_get;eassumption.
Qed.
Lemma live_base tf before after source :
 Replay.not_side (R.cfg_control before) -> Replay.nonpublication (R.cfg_control before) ->
 live_settled (R.cfg_state before) source ->
 R.next_config tf before = Some after -> live_settled (R.cfg_state after) source.
Proof.
 destruct before as [st control]. intros Hside Hdead Hlive Hstep.
 destruct control.
 - cbn -[R.queue_pop] in Hstep.
   destruct (R.queue_pop (R.queue st)) as [[target rest]|];[|discriminate].
   inversion Hstep;subst;apply live_queue,Hlive.
 - destruct l as [|root rest];cbn -[R.observe] in Hstep.
   + inversion Hstep;subst;exact Hlive.
   + destruct (R.is_materialized (R.observe st root) root);
     inversion Hstep;subst;apply live_observe,Hlive.
 - cbn -[R.queue_pop] in Hstep.
   destruct (R.queue_pop (R.queue st)) as [[target rest]|];
   inversion Hstep;subst;[apply live_queue,Hlive |exact Hlive].
 - inversion Hstep;subst;apply live_materialize,Hlive.
 - destruct r.
   + inversion Hstep;subst;exact Hlive.
   + eapply live_read_step;eassumption.
   + contradiction.
   + eapply live_spawn_step;eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst. apply live_queue.
   eapply live_set_value;eassumption.
 - eapply live_drain_step;eassumption.
 - eapply live_return_step;eassumption.
Qed.


Lemma live_precommit tf before after source :
 Replay.not_side (R.cfg_control before) -> Replay.nonpublication (R.cfg_control before) ->
 live_settled (R.cfg_state before) source ->
 C.P.next_config tf before = Some after -> live_settled (R.cfg_state after) source.
Proof.
 destruct before as [st control]. intros Hside Hdead Hlive Hstep.
 destruct control;cbn -[R.next_config C.P.pending_above C.P.suspend_commit] in Hstep;
 try solve [eapply live_base;eauto].
 destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst;apply live_queue,Hlive.
 - eapply live_base;eauto.
Qed.
Lemma live_batched tf before after source :
 Replay.nonpublication (R.cfg_control before) ->
 live_settled (R.cfg_state before) source ->
 C.P.next_batched tf before = Some after -> live_settled (R.cfg_state after) source.
Proof.
 destruct before as [st control]. intros Hdead Hlive Hstep.
 destruct control;cbn -[C.P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply live_precommit;[ | |exact Hlive |exact Hstep];[exact I |exact Hdead]].
 - destruct r;
   try solve [eapply live_precommit;[ | |exact Hlive |exact Hstep];[exact I |exact Hdead]].
   inversion Hstep;subst;apply live_observe,Hlive.
 - contradiction.
Qed.
Lemma live_fresh tf before after source :
 Replay.nonpublication (R.cfg_control before) ->
 live_settled (R.cfg_state before) source ->
 C.P.next_fresh tf before = Some after -> live_settled (R.cfg_state after) source.
Proof.
 destruct before as [st control]. intros Hdead Hlive Hstep.
 destruct control;
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep;
 try solve [eapply live_batched;eauto].
 - inversion Hstep;subst;apply live_materialize,live_queue,Hlive.
 - destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst;apply live_queue,Hlive.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst;apply live_queue,Hlive.
     * eapply live_batched;eauto.
 - destruct c;cbn -[C.P.next_batched] in Hstep;
   try solve [eapply live_batched;eauto].
   inversion Hstep;subst;apply live_queue,Hlive.
Qed.
Lemma write_last_targets st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 R.last_targets next = R.last_targets st.
Proof.
 unfold R.write_side_contribution,R.register_reset,R.promote_side_target.
 destruct (R.rank_lt st target (R.frame_owner fr));intro Hwrite;
 inversion Hwrite;reflexivity.
Qed.
Lemma live_write_other st fr target input next changed source :
 R.write_side_contribution st fr target input = (next,changed) ->
 source <> R.frame_owner fr -> live_settled st source -> live_settled next source.
Proof.
 intros Hwrite Hneq Hlive observed Hmem.
 pose proof (@write_last_targets st fr target input next changed Hwrite) as Htargets.
 unfold cell_settled.
 rewrite (@B.Credits.stored_side_cell_write_other st fr target input next changed source observed Hwrite),
 (@B.Credits.stored_contribution_write_other st fr target input next changed source observed Hwrite);
 try solve [intro Heq;inversion Heq;contradiction].
 apply Hlive. now rewrite Htargets in Hmem.
Qed.
Lemma live_requeue before after source target owner :
 live_settled after owner -> live_settled (C.requeue_source before after source target) owner.
Proof.
 unfold C.requeue_source. destruct C.cell_changed;[apply live_enqueue |trivial].
Qed.
Lemma live_finish before after fr target changed source :
 live_settled after source -> live_settled (C.finish_write before after fr target changed) source.
Proof.
 unfold C.finish_write. destruct changed;[intro H;apply live_enqueue,live_requeue,H |apply live_requeue].
Qed.
Lemma live_publish_other targets st fr source :
 source <> R.frame_owner fr -> live_settled st source ->
 live_settled (C.publish targets st fr) source.
Proof.
 intro Hneq. revert st. induction targets as [|target rest IH];intros st Hlive;
 cbn -[R.write_side_contribution C.finish_write];[exact Hlive |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some v=>v |None=>D.bottom end))
 as [next changed] eqn:Hw.
 apply IH,live_finish. eapply live_write_other;eassumption.
Qed.
Lemma live_publish_targets_other st fr source :
 source <> R.frame_owner fr -> live_settled st source ->
 live_settled (R.publish_targets st fr) source.
Proof.
 intros Hneq Hlive target Hmem.
 unfold R.lookup_set in Hmem. cbn in Hmem.
 rewrite ML.lookup_update_other in Hmem;[apply Hlive;exact Hmem |congruence].
Qed.


Definition live_guarded st control source :=
 B.queued st source \/ B.control_active source control \/ live_settled st source.
Lemma live_dead_step tf st fr direct target rest k source after :
 live_settled st source ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|}
 = Some after -> live_guarded (R.cfg_state after) (R.cfg_control after) source.
Proof.
 intros Hlive Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr)).
 - inversion Hstep;subst;right;right;exact Hlive.
 - destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
   inversion Hstep;subst. destruct (V.eq_dec source (R.frame_owner fr)) as [->|Hneq].
   + unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];
     right;left;cbn;auto.
   + assert (Hnext : live_settled (C.requeue_source st next (R.frame_owner fr) target) source).
     { apply live_requeue. eapply live_write_other;eassumption. }
     unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];
     right;right;cbn;auto using live_enqueue.
Qed.
Lemma next_preserves_live tf before after source :
 live_settled (R.cfg_state before) source ->
 N.next_config tf before = Some after ->
 live_guarded (R.cfg_state after) (R.cfg_control after) source.
Proof.
 intros Hlive Hstep. destruct (@Replay.Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp0 ->]]]]]]]]].
 2: { right;right. apply live_queue,Hlive. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st control]. destruct control;
 try solve [right;right;eapply live_fresh;[ |exact Hlive |exact Hstep];exact I].
 destruct l as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   destruct (V.eq_dec source (R.frame_owner f)) as [->|Hneq];[right;left;now left |].
   right;right. apply live_publish_targets_other;[exact Hneq |].
   apply live_publish_other;assumption.
 - eapply (@live_dead_step tf st f t target rest c source after);eassumption.
Qed.
Lemma next_guarded_live tf roots before after source :
 N.steps tf (R.initial_config roots) before ->
 live_guarded (R.cfg_state before) (R.cfg_control before) source ->
 N.next_config tf before = Some after ->
 live_guarded (R.cfg_state after) (R.cfg_control after) source.
Proof.
 intros Hreach [Hq|[Ha|Hl]] Hstep.
 - destruct (@Replay.next_schedule tf before after Hstep source (or_introl Hq))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_live_settled;eassumption.
 - destruct (@Replay.next_schedule tf before after Hstep source (or_intror Ha))
   as [[Hq'|Ha']|Hcommit];[now left |now right;left |].
   destruct Hcommit as [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
   right;right. eapply actual_commit_live_settled;eassumption.
 - eapply next_preserves_live;eassumption.
Qed.
Lemma steps_guarded_live tf roots before after :
 N.steps tf before after ->
 N.steps tf (R.initial_config roots) before ->
 (forall source,live_guarded (R.cfg_state before) (R.cfg_control before) source) ->
 forall source,live_guarded (R.cfg_state after) (R.cfg_control after) source.
Proof.
 intros Hsteps. induction Hsteps;intros Hreach Hlive;[exact Hlive |].
 apply IHHsteps.
 - eapply Replay.steps_append;[exact Hreach |].
   eapply N.steps_next;[exact H |constructor].
 - intro source. eapply next_guarded_live;[exact Hreach |apply Hlive |exact H].
Qed.
Theorem reachable_live_settled tf roots c :
 N.steps tf (R.initial_config roots) c ->
 forall source,live_guarded (R.cfg_state c) (R.cfg_control c) source.
Proof.
 intro Hreach. eapply steps_guarded_live;[exact Hreach |constructor |].
 intro source. right;right. intros target Hmem.
 unfold R.lookup_set in Hmem. cbn in Hmem.
 rewrite ML.lookup_empty in Hmem. rewrite SL.empty_spec in Hmem. discriminate.
Qed.


Theorem reachable_clean_live_settled tf roots c source :
 N.steps tf (R.initial_config roots) c ->
 ~ B.queued (R.cfg_state c) source ->
 ~ B.control_active source (R.cfg_control c) ->
 live_settled (R.cfg_state c) source.
Proof.
 intros Hreach Hqueue Hactive.
 destruct (@reachable_live_settled tf roots c Hreach source)
 as [Hq|[Ha|Hl]];[contradiction |contradiction |exact Hl].
Qed.
Theorem committing_higher_live_settled tf roots st fr direct k after next_fr next_k source :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) source = true ->
 live_settled st source.
Proof.
 intros Hreach Hstep Hcontrolled Hhigher.
 destruct (@Replay.committing_higher_clean tf roots st fr direct k after next_fr next_k source
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 exact (@reachable_clean_live_settled tf roots _ source Hreach Hqueue Hactive).
Qed.
Theorem successful_run_live_settled fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall source,live_settled final source.
Proof.
 intro Hsolve. unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve)
 as [Hshape Hquiet].
 assert (Hreach : N.steps tf (R.initial_config roots) (Replay.Sem.terminal_config final)).
 { rewrite <- Hshape. apply Replay.fuel_steps. }
 intro source. apply (@reachable_clean_live_settled tf roots (Replay.Sem.terminal_config final) source Hreach).
 - exact (@B.quiescent_not_queued final source Hquiet).
 - cbn. tauto.
Qed.


Lemma live_effects_settled st owner effects :
 live_settled st owner -> Replay.targets_live st owner effects ->
 forall target value,In (target,value) effects -> cell_settled st owner target.
Proof. intros Hlive Htargets target value Hin. apply Hlive,Htargets with value,Hin. Qed.
Theorem reachable_clean_replay_settled tf roots c owner direct reads effects :
 N.steps tf (R.initial_config roots) c -> Replay.Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 Replay.Sem.rhs_eval (R.cfg_state c) (tf owner) direct reads effects ->
 forall target value,In (target,value) effects -> cell_settled (R.cfg_state c) owner target.
Proof.
 intros Hreach Hsolved Hqueue Hactive Heval.
 apply live_effects_settled.
 - exact (@reachable_clean_live_settled tf roots c owner Hreach Hqueue Hactive).
 - exact (@Replay.reachable_clean_replay_targets tf roots c owner direct reads effects
   Hreach Hsolved Hqueue Hactive Heval).
Qed.
Theorem committing_higher_replay_settled tf roots st fr direct k after next_fr next_k owner result reads effects :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Replay.Sem.solved st owner ->
 Replay.Sem.rhs_eval st (tf owner) result reads effects ->
 forall target value,In (target,value) effects -> cell_settled st owner target.
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved Heval.
 destruct (@Replay.committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 exact (@reachable_clean_replay_settled tf roots _ owner result reads effects
 Hreach Hsolved Hqueue Hactive Heval).
Qed.
Lemma effects_ready_publication st fr lower upper :
 Replay.accumulation fr lower -> Replay.O.valued_events_le lower upper ->
 live_settled st (R.frame_owner fr) ->
 Replay.targets_live st (R.frame_owner fr) upper ->
 Replay.effects_bounded upper (R.stored_contribution st (R.frame_owner fr)) ->
 publication_ready (S.elements (R.frame_current_targets fr)) st fr.
Proof.
 intros [_ [Hacc Htargets]] Hle Hlive Hupper Hbounded.
 assert (Hbound : Replay.frame_bounded fr (R.stored_contribution st (R.frame_owner fr))).
 { apply Hacc. intros target value Hin.
   destruct (Hle target value Hin) as [upper_value [Hmem Hvalue]].
   eapply DL.leq_trans;[exact Hvalue |exact (Hbounded target upper_value Hmem)]. }
 intros target Hin. split;[|apply Hbound].
 apply SL.mem_spec in Hin.
 destruct (proj1 (Htargets target) Hin) as [value Hmem].
 destruct (Hle target value Hmem) as [upper_value [Hu Hv]].
 apply Hlive,Hupper with upper_value,Hu.
Qed.
Theorem reachable_clean_smaller_publication_ready tf roots c lower fr direct reads effects :
 N.steps tf (R.initial_config roots) c -> Replay.Sem.solved (R.cfg_state c) (R.frame_owner fr) ->
 ~ B.queued (R.cfg_state c) (R.frame_owner fr) ->
 ~ B.control_active (R.frame_owner fr) (R.cfg_control c) ->
 Replay.Sem.rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
 Replay.Sem.rhs_effects_monotone (tf (R.frame_owner fr)) ->
 (forall target,D.leq (R.sigma_value lower target) (R.sigma_value (R.cfg_state c) target) = true) ->
 Replay.Sem.rhs_eval lower (tf (R.frame_owner fr)) direct reads effects ->
 Replay.accumulation fr effects ->
 publication_ready (S.elements (R.frame_current_targets fr)) (R.cfg_state c) fr.
Proof.
 intros Hreach Hsolved Hqueue Hactive Hdeps Heffects Hdown Heval Hacc.
 destruct (@Replay.reachable_clean_replay tf roots c (R.frame_owner fr)
 Hreach Hsolved Hqueue Hactive) as [du [ru [eu [Hupper [Hdirect Hside]]]]].
 eapply effects_ready_publication;[exact Hacc | | | |exact Hside].
 - exact (proj2 (@Replay.replay_effects_monotone (tf (R.frame_owner fr))
   lower (R.cfg_state c) direct reads effects du ru eu Hdeps Heffects Heval Hupper Hdown)).
 - exact (@reachable_clean_live_settled tf roots c (R.frame_owner fr) Hreach Hqueue Hactive).
 - exact (@Replay.reachable_clean_replay_targets tf roots c (R.frame_owner fr) du ru eu
   Hreach Hsolved Hqueue Hactive Hupper).
Qed.
Theorem successful_run_replay_cells_settled fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final ->
 forall owner,Replay.Sem.solved final owner ->
 exists direct reads effects,Replay.Sem.rhs_eval final (tf owner) direct reads effects /\
 (forall target value,In (target,value) effects -> cell_settled final owner target).
Proof.
 intros Hsolve owner Hsolved.
 destruct (@Replay.successful_run_target_replay fuel tf roots final Hsolve owner Hsolved)
 as [direct [reads [effects [Heval Hlive]]]].
 exists direct,reads,effects. split;[exact Heval |].
 apply live_effects_settled;[eapply successful_run_live_settled;exact Hsolve |exact Hlive].
Qed.


Module O := Replay.O.
Module Sem := Replay.Sem.
Module Demand := Replay.Demand.
Definition source_frontier tf st owner (result : O.observation) :=
 Sem.solved st owner /\
 Sem.rhs_observes (tf owner) result /\
 Sem.rhs_eval st (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 Replay.paths_below (R.sigma_value st) result (tf owner) /\
 D.leq (D.join (O.observed_direct result) (R.aggregate st owner)) (R.sigma_value st owner) = true /\
 Replay.effects_bounded (O.observed_sides result) (R.stored_contribution st owner) /\
 Replay.targets_live st owner (O.observed_sides result) /\
 live_settled st owner /\ Demand.spawned st (O.observed_spawns result).
Lemma clean_replay_bounds tf roots c owner result :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 Sem.rhs_eval (R.cfg_state c) (tf owner) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) ->
 D.leq (D.join (O.observed_direct result) (R.aggregate (R.cfg_state c) owner))
 (R.sigma_value (R.cfg_state c) owner) = true /\
 Replay.effects_bounded (O.observed_sides result) (R.stored_contribution (R.cfg_state c) owner).
Proof.
 intros Hreach Hsolved Hqueue Hactive Heval.
 destruct (@Replay.reachable_clean_replay tf roots c owner Hreach Hsolved Hqueue Hactive)
 as [direct [reads [effects [Hreplay [Hdirect Hside]]]]].
 destruct (B.rhs_eval_deterministic Hreplay Heval) as [-> [-> ->]].
 split;[|exact Hside]. apply DL.join_least;[exact Hdirect |].
 destruct (Replay.reachable_aggregate Hreach owner) as [Hq|[Ha|Hagg]];try contradiction;exact Hagg.
Qed.
Theorem reachable_clean_frontier tf roots c owner :
 N.steps tf (R.initial_config roots) c -> Sem.solved (R.cfg_state c) owner ->
 ~ B.queued (R.cfg_state c) owner -> ~ B.control_active owner (R.cfg_control c) ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists result,source_frontier tf (R.cfg_state c) owner result.
Proof.
 intros Hreach Hsolved Hqueue Hactive Hdeps Heffects.
 destruct (@Demand.reachable_clean_observation tf roots c owner Hreach Hsolved Hqueue Hactive)
 as [result [Hobs [Heval Hspawns]]].
 assert (Hpaths : Replay.paths_below (R.sigma_value (R.cfg_state c)) result (tf owner)).
 { eapply Replay.monotone_paths_below;[exact Hdeps |exact Heffects |exact Hobs |].
   intros target value Hin. eapply Replay.replay_read_value;eassumption. }
 destruct (@clean_replay_bounds tf roots c owner result Hreach Hsolved Hqueue Hactive Heval)
 as [Hdirect Hside].
 exists result. split;[exact Hsolved |]. split;[exact Hobs |]. split;[exact Heval |]. split;[exact Hpaths |].
 split;[exact Hdirect |]. split;[exact Hside |]. split.
 - exact (@Replay.reachable_clean_replay_targets tf roots c owner _ _ _ Hreach Hsolved Hqueue Hactive Heval).
 - split;[|exact Hspawns].
   exact (@reachable_clean_live_settled tf roots c owner Hreach Hqueue Hactive).
Qed.
Theorem committing_higher_frontier tf roots st fr direct k after next_fr next_k owner :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 R.rank_lt st (R.frame_owner fr) owner = true -> Sem.solved st owner ->
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 exists result,source_frontier tf st owner result.
Proof.
 intros Hreach Hstep Hcontrolled Hhigher Hsolved Hdeps Heffects.
 destruct (@Replay.committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) as [Hqueue Hactive].
 exact (@reachable_clean_frontier tf roots _ owner Hreach Hsolved Hqueue Hactive Hdeps Heffects).
Qed.
Lemma frontier_get_solved tf st owner result target next :
 source_frontier tf st owner result ->
 Replay.paths_below (R.sigma_value st) result (R.ConstraintSystem.Get target next) ->
 Sem.solved st target.
Proof.
 intros [_ [_ [Heval _]]] Hpaths. eapply Demand.path_get_solved;[exact Heval |exact Hpaths].
Qed.
Lemma frontier_spawn_solved tf st owner result cap target next :
 source_frontier tf st owner result ->
 Replay.paths_below cap result (R.ConstraintSystem.Spawn target next) ->
 Sem.solved st target.
Proof.
 intros [_ [_ [_ [_ [_ [_ [_ [_ Hspawns]]]]]]]] Hpaths.
 eapply Demand.path_spawn_solved;[exact Hspawns |exact Hpaths].
Qed.

(** Historical observations account for completed publications even when the
    ordinary commit is delayed. These proof-side snapshots are not runtime
    state and are not public solver premises. *)
Module Episode.
Import ListNotations.

Definition values_descend before after :=
 forall target,D.leq (R.sigma_value after target) (R.sigma_value before target) = true.
Definition reads_floor st reads :=
 forall target value,In (target,value) reads ->
 D.leq (R.sigma_value st target) value = true.
Definition reads_solved st (reads : list (V.t * D.t)) :=
 forall target value,In (target,value) reads -> Sem.solved st target.
Definition snapshot tf st owner (result : O.observation) :=
 Sem.rhs_observes (tf owner) result /\
 reads_floor st (O.observed_reads result) /\
 reads_solved st (O.observed_reads result) /\
 Demand.spawned st (O.observed_spawns result) /\
 D.leq (D.join (O.observed_direct result) (R.aggregate st owner)) (R.sigma_value st owner) = true /\
 Replay.effects_bounded (O.observed_sides result) (R.stored_contribution st owner) /\
 Replay.targets_live st owner (O.observed_sides result) /\ live_settled st owner.
Lemma reads_floor_descend before after reads :
 values_descend before after -> reads_floor before reads -> reads_floor after reads.
Proof.
 intros Hdown Hreads target value Hin. eapply DL.leq_trans;[apply Hdown |apply Hreads,Hin].
Qed.
Lemma reads_solved_extends before after reads :
 Replay.T.sigma_extends before after -> reads_solved before reads -> reads_solved after reads.
Proof.
 intros Hextends Hreads target value Hin. destruct (Hreads target value Hin) as [stored Hlookup].
 exact (Hextends target stored Hlookup).
Qed.
Lemma replay_floor st body direct reads effects :
 Sem.rhs_eval st body direct reads effects -> reads_floor st reads /\ reads_solved st reads.
Proof.
 intro Heval. split;intros target value Hin.
 - rewrite (@Replay.replay_read_value st body direct reads effects target value Heval Hin). apply DL.leq_refl.
 - exists value. eapply Replay.replay_reads;[exact Heval |exact Hin].
Qed.
Lemma frontier_snapshot tf st owner result :
 source_frontier tf st owner result -> snapshot tf st owner result.
Proof.
 intros [_ [Hobs [Heval [Hpaths [Hbound [Hside [Hlive [Hsettled Hspawn]]]]]]]].
 destruct (replay_floor Heval) as [Hfloor Hreads].
 split;[exact Hobs |]. split;[exact Hfloor |]. split;[exact Hreads |].
 split;[exact Hspawn |]. split;[exact Hbound |]. split;[exact Hside |]. split;assumption.
Qed.
Lemma historical_paths body st upper :
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_observes body upper -> reads_floor st (O.observed_reads upper) ->
 Replay.paths_below (R.sigma_value st) upper body.
Proof.
 intros Hdeps Heffects Hupper Hfloor lower Hlower Hreads.
 assert (Hcommon : O.common_read_values_le lower upper).
 { intros target vl vu Hl Hu. eapply DL.leq_trans;[apply Hreads,Hl |apply Hfloor,Hu]. }
 pose proof (Replay.dependency_order_gives_read_order Hdeps Hlower Hupper Hcommon) as Horder.
 split;[apply Heffects;assumption |].
 intros target Hin. apply in_map_iff in Hin.
 destruct Hin as [[observed value] [Heq Hmem]]. cbn in Heq. subst observed.
 destruct (Horder target value Hmem) as [upper_value [Hu Hle]].
 apply in_map_iff. exists (target,upper_value). now split.
Qed.
Lemma snapshot_paths tf st owner result :
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 snapshot tf st owner result -> Replay.paths_below (R.sigma_value st) result (tf owner).
Proof.
 intros Hdeps Heffects [Hobs [Hfloor _]]. eapply historical_paths;eassumption.
Qed.
Definition prefix_order upper reads :=
 forall target lower_value upper_value,In (target,lower_value) reads ->
 In (target,upper_value) (O.observed_reads upper) ->
 D.leq lower_value upper_value = true.
Lemma prefix_order_read upper st reads target value :
 prefix_order upper reads -> reads_floor st (O.observed_reads upper) ->
 value = R.sigma_value st target ->
 prefix_order upper (reads ++ [(target,value)]).
Proof.
 intros Hprefix Hfloor -> observed vl vu Hl Hu. apply in_app_or in Hl.
 destruct Hl as [Hl|[Heq|Hin]].
 - eapply Hprefix;eassumption.
 - inversion Heq;subst. apply Hfloor,Hu.
 - contradiction.
Qed.
Lemma reads_floor_read st reads target value :
 reads_floor st reads -> value = R.sigma_value st target ->
 reads_floor st (reads ++ [(target,value)]).
Proof.
 intros Hreads -> observed v Hin. apply in_app_or in Hin.
 destruct Hin as [Hin|[Heq|Hin]].
 - apply Hreads,Hin.
 - inversion Heq;subst. apply DL.leq_refl.
 - contradiction.
Qed.
Lemma context_common upper prefix_reads prefix_effects prefix_spawns suffix :
 prefix_order upper prefix_reads ->
 (forall target vl vu,In (target,vl) (O.observed_reads suffix) ->
 In (target,vu) (O.observed_reads upper) -> D.leq vl vu = true) ->
 O.common_read_values_le (Demand.prepend prefix_reads prefix_effects prefix_spawns suffix) upper.
Proof.
 intros Hprefix Hsuffix target vl vu Hl Hu. cbn in Hl. apply in_app_or in Hl.
 destruct Hl as [Hp|Hs];[eapply Hprefix |eapply Hsuffix];eassumption.
Qed.
Lemma context_paths body current st upper reads effects spawns :
 Demand.context body current reads effects spawns ->
 prefix_order upper reads -> reads_floor st (O.observed_reads upper) ->
 Sem.rhs_dependencies_monotone body -> Sem.rhs_effects_monotone body ->
 Sem.rhs_observes body upper ->
 Replay.paths_below (R.sigma_value st) upper current.
Proof.
 intros Hcontext Hprefix Hfloor Hdeps Heffects Hupper suffix Hsuffix Hreads.
 pose proof (Hcontext _ Hsuffix) as Hwhole.
 assert (Hcommon : O.common_read_values_le (Demand.prepend reads effects spawns suffix) upper).
 { apply context_common;[exact Hprefix |]. intros target vl vu Hl Hu.
   eapply DL.leq_trans;[apply Hreads,Hl |apply Hfloor,Hu]. }
 pose proof (Replay.dependency_order_gives_read_order Hdeps Hwhole Hupper Hcommon) as Horder.
 pose proof (Heffects _ _ Hwhole Hupper Horder) as Hbound. split.
 - constructor;[exact (O.direct_effect_le Hbound) | |].
   + intros target value Hin. apply (O.side_effects_le Hbound). apply in_or_app;now right.
   + intros target Hin. apply (O.spawn_effects_le Hbound). apply in_or_app;now right.
 - intros target Hin. apply in_map_iff in Hin.
   destruct Hin as [[observed value] [Heq Hmem]]. cbn in Heq. subst observed.
   assert (Hwhole_read : In (target,value) (O.observed_reads (Demand.prepend reads effects spawns suffix))).
   { cbn. apply in_or_app;now right. }
   destruct (Horder target value Hwhole_read) as [upper_value [Hu Hle]].
   apply in_map_iff. exists (target,upper_value). now split.
Qed.


Definition evaluation tf st fr current upper :=
 exists reads effects spawns,Demand.context (tf (R.frame_owner fr)) current reads effects spawns /\
 Replay.accumulation fr effects /\ reads_floor st reads /\ reads_solved st reads /\
 Demand.spawned st spawns /\ prefix_order upper reads.
Lemma evaluation_initial tf st owner phase upper :
 evaluation tf st (R.fresh_frame st owner phase) (tf owner) upper.
Proof.
 exists [],[],[]. split;[apply Demand.context_initial |].
 split;[apply Replay.accumulation_fresh |].
 split;[intros t v Hin;contradiction |].
 split;[intros t v Hin;contradiction |].
 split;[intros t Hin;contradiction |intros t vl vu Hin;contradiction].
Qed.
Lemma evaluation_carries tf before after fr current upper :
 values_descend before after -> Replay.T.sigma_extends before after ->
 evaluation tf before fr current upper -> evaluation tf after fr current upper.
Proof.
 intros Hdown Hextends [reads [effects [spawns [Hcontext [Hacc [Hfloor [Hreads [Hspawns Hprefix]]]]]]]].
 exists reads,effects,spawns. split;[exact Hcontext |]. split;[exact Hacc |].
 split;[eapply reads_floor_descend;eassumption |].
 split;[eapply reads_solved_extends;eassumption |].
 split;[eapply Demand.spawned_carries;eassumption |exact Hprefix].
Qed.
Lemma evaluation_side tf st fr target value next upper :
 evaluation tf st fr (R.ConstraintSystem.Side target value next) upper ->
 evaluation tf st (fst (R.record_side_input fr target value)) next upper.
Proof.
 intros [reads [effects [spawns [Hcontext [Hacc [Hfloor [Hreads [Hspawns Hprefix]]]]]]]].
 exists reads,(effects ++ [(target,value)]),spawns.
 split;[apply Demand.context_side,Hcontext |].
 split;[apply Replay.accumulation_record,Hacc |].
 split;[exact Hfloor |]. split;[exact Hreads |]. split;assumption.
Qed.
Lemma evaluation_spawn tf st fr target next upper :
 evaluation tf st fr (R.ConstraintSystem.Spawn target next) upper ->
 Sem.solved st target -> evaluation tf st fr next upper.
Proof.
 intros [reads [effects [spawns [Hcontext [Hacc [Hfloor [Hreads [Hspawns Hprefix]]]]]]]] Hsolved.
 exists reads,effects,(spawns ++ [target]). split;[apply Demand.context_spawn,Hcontext |].
 split;[exact Hacc |]. split;[exact Hfloor |]. split;[exact Hreads |]. split;[|exact Hprefix].
 intros observed Hin. apply in_app_or in Hin.
 destruct Hin as [Hin|[->|Hin]];[apply Hspawns,Hin |exact Hsolved |contradiction].
Qed.
Lemma evaluation_paths tf st fr current upper :
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fr)) ->
 snapshot tf st (R.frame_owner fr) upper ->
 evaluation tf st fr current upper ->
 Replay.paths_below (R.sigma_value st) upper current.
Proof.
 intros Hdeps Heffects [Hobs [Hfloor _]]
 [reads [effects [spawns [Hcontext [Hacc [Hreadfloor [Hreadsolved [Hspawn Hprefix]]]]]]]].
 eapply context_paths;eassumption.
Qed.
Lemma evaluation_ret tf st fr direct upper :
 evaluation tf st fr (R.ConstraintSystem.Ret direct) upper ->
 exists reads effects spawns,
 Sem.rhs_observes (tf (R.frame_owner fr))
 {|O.observed_direct:=direct;O.observed_reads:=reads;O.observed_sides:=effects;O.observed_spawns:=spawns|} /\
 Replay.accumulation fr effects /\ reads_floor st reads /\ reads_solved st reads /\
 Demand.spawned st spawns /\ prefix_order upper reads.
Proof.
 intros [reads [effects [spawns [Hcontext Hrest]]]].
 exists reads,effects,spawns. split;[|exact Hrest].
 specialize (Hcontext _ (Sem.ObserveRet direct)).
 unfold Demand.prepend in Hcontext. cbn in Hcontext.
 repeat rewrite app_nil_r in Hcontext. exact Hcontext.
Qed.
Lemma snapshot_smaller_observation tf st owner upper lower :
 Sem.rhs_dependencies_monotone (tf owner) -> Sem.rhs_effects_monotone (tf owner) ->
 snapshot tf st owner upper -> Sem.rhs_observes (tf owner) lower ->
 O.common_read_values_le lower upper ->
 reads_floor st (O.observed_reads lower) -> reads_solved st (O.observed_reads lower) ->
 Demand.spawned st (O.observed_spawns lower) -> snapshot tf st owner lower.
Proof.
 intros Hdeps Heffects [Hupper [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive Hsettled]]]]]]]
 Hlower Hcommon Hfloor' Hreads' Hspawns'.
 pose proof (Replay.dependency_order_gives_read_order Hdeps Hlower Hupper Hcommon) as Horder.
 pose proof (Heffects _ _ Hlower Hupper Horder) as Hle.
 split;[exact Hlower |]. split;[exact Hfloor' |]. split;[exact Hreads' |].
 split;[exact Hspawns' |]. split.
 - eapply DL.leq_trans;[|exact Hbound].
   apply DL.join_least.
   + eapply DL.leq_trans;[exact (O.direct_effect_le Hle) |apply DL.join_upper_left].
   + apply DL.join_upper_right.
 - split.
   + intros target value Hin.
     destruct (O.side_effects_le Hle target value Hin) as [upper_value [Hu Hv]].
     eapply DL.leq_trans;[exact Hv |exact (Hside target upper_value Hu)].
   + split;[|exact Hsettled]. intros target value Hin.
     destruct (O.side_effects_le Hle target value Hin) as [upper_value [Hu Hv]].
     exact (Hlive target upper_value Hu).
Qed.
Theorem completed_evaluation_refreshes_snapshot tf st fr direct upper :
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fr)) ->
 snapshot tf st (R.frame_owner fr) upper ->
 evaluation tf st fr (R.ConstraintSystem.Ret direct) upper ->
 exists reads effects spawns,
 snapshot tf st (R.frame_owner fr)
 {|O.observed_direct:=direct;O.observed_reads:=reads;O.observed_sides:=effects;O.observed_spawns:=spawns|} /\
 Replay.accumulation fr effects.
Proof.
 intros Hdeps Heffects Hsnapshot Heval.
 destruct (evaluation_ret Heval) as [reads [effects [spawns [Hobs [Hacc [Hfloor [Hreads [Hspawns Hprefix]]]]]]]].
 exists reads,effects,spawns. split;[|exact Hacc].
 eapply snapshot_smaller_observation;[exact Hdeps |exact Heffects |exact Hsnapshot
 |exact Hobs |exact Hprefix |exact Hfloor |exact Hreads |exact Hspawns].
Qed.
Lemma snapshot_publication_ready tf st fr result :
 snapshot tf st (R.frame_owner fr) result ->
 Replay.accumulation fr (O.observed_sides result) ->
 publication_ready (S.elements (R.frame_current_targets fr)) st fr.
Proof.
 intros [Hobs [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive Hsettled]]]]]]] Hacc.
 eapply effects_ready_publication;[exact Hacc | |exact Hsettled |exact Hlive |exact Hside].
 intros target value Hin. exists value. split;[exact Hin |apply DL.leq_refl].
Qed.


Lemma snapshot_get_solved tf st owner upper target next :
 snapshot tf st owner upper ->
 Replay.paths_below (R.sigma_value st) upper (R.ConstraintSystem.Get target next) ->
 Sem.solved st target.
Proof.
 intros [_ [_ [Hreads _]]] Hpaths.
 pose proof (@Replay.paths_get_target (R.sigma_value st) upper target next Hpaths) as Hin.
 apply in_map_iff in Hin. destruct Hin as [[observed value] [Heq Hmem]]. cbn in Heq. subst observed.
 exact (Hreads target value Hmem).
Qed.
Lemma snapshot_spawn_solved tf st owner upper target next :
 snapshot tf st owner upper ->
 Replay.paths_below (R.sigma_value st) upper (R.ConstraintSystem.Spawn target next) ->
 Sem.solved st target.
Proof.
 intros [_ [_ [_ [Hspawns _]]]] Hpaths.
 apply Hspawns. eapply Replay.paths_spawn_target;exact Hpaths.
Qed.
Lemma get_view st fr target after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) -> Sem.solved st target ->
 R.sigma after = R.sigma st /\ value = R.sigma_value st target /\
 R.frame_owner next_fr = R.frame_owner fr /\
 R.frame_local_side next_fr = R.frame_local_side fr /\
 R.frame_current_targets next_fr = R.frame_current_targets fr.
Proof.
 intros Hget [stored Hstored]. unfold R.complete_get in Hget.
 destruct (R.rank_lt st (R.frame_owner fr) target);
 inversion Hget;subst;unfold R.materialize;cbn;rewrite Hstored;
 repeat split;reflexivity.
Qed.
Lemma evaluation_frame_view tf st fr next_fr current upper :
 R.frame_owner next_fr = R.frame_owner fr ->
 R.frame_local_side next_fr = R.frame_local_side fr ->
 R.frame_current_targets next_fr = R.frame_current_targets fr ->
 evaluation tf st fr current upper -> evaluation tf st next_fr current upper.
Proof.
 intros Howner Hlocal Htargets [reads [effects [spawns [Hcontext [Hacc Hrest]]]]].
 exists reads,effects,spawns. split;[rewrite Howner;exact Hcontext |].
 split;[eapply Replay.accumulation_view;eassumption |exact Hrest].
Qed.
Lemma evaluation_get tf st fr target next upper after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) ->
 Sem.solved st target -> reads_floor st (O.observed_reads upper) ->
 evaluation tf st fr (R.ConstraintSystem.Get target next) upper ->
 evaluation tf after next_fr (next value) upper.
Proof.
 intros Hget Hsolved Hupper Heval.
 destruct (@get_view st fr target after next_fr value Hget Hsolved)
 as [Hsigma [Hvalue [Howner [Hlocal Htargets]]]].
 apply evaluation_frame_view with fr;[exact Howner |exact Hlocal |exact Htargets |].
 destruct Heval as [reads [effects [spawns [Hcontext [Hacc [Hfloor [Hreads [Hspawns Hprefix]]]]]]]].
 exists (reads ++ [(target,value)]),effects,spawns. split;[apply Demand.context_get,Hcontext |].
 split;[exact Hacc |]. split.
 - unfold reads_floor,R.sigma_value in *. rewrite Hsigma.
   apply reads_floor_read;assumption.
 - split.
   + intros observed v Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
     * destruct (Hreads observed v Hin) as [stored Hlookup].
       exists stored. now rewrite Hsigma.
     * inversion Heq;subst. destruct Hsolved as [stored Hlookup].
       exists stored. now rewrite Hsigma.
     * contradiction.
   + split.
     * eapply Demand.spawned_carries;[apply Replay.T.sigma_extends_same;exact Hsigma |exact Hspawns].
     * eapply prefix_order_read;eassumption.
Qed.
Theorem bounded_get_step tf st fr target next upper after next_fr value :
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fr)) ->
 snapshot tf st (R.frame_owner fr) upper ->
 evaluation tf st fr (R.ConstraintSystem.Get target next) upper ->
 R.complete_get st fr target = (after,next_fr,value) ->
 R.sigma after = R.sigma st /\ evaluation tf after next_fr (next value) upper.
Proof.
 intros Hdeps Heffects Hsnapshot Heval Hget.
 assert (Hsolved : Sem.solved st target).
 { eapply snapshot_get_solved;[exact Hsnapshot |].
   eapply evaluation_paths;eassumption. }
 split;[exact (proj1 (@get_view st fr target after next_fr value Hget Hsolved)) |].
 eapply evaluation_get;[exact Hget |exact Hsolved |exact (proj1 (proj2 Hsnapshot)) |exact Heval].
Qed.
Theorem bounded_spawn_step tf st fr target next upper :
 Sem.rhs_dependencies_monotone (tf (R.frame_owner fr)) ->
 Sem.rhs_effects_monotone (tf (R.frame_owner fr)) ->
 snapshot tf st (R.frame_owner fr) upper ->
 evaluation tf st fr (R.ConstraintSystem.Spawn target next) upper ->
 Sem.solved st target /\ evaluation tf st fr next upper.
Proof.
 intros Hdeps Heffects Hsnapshot Heval.
 assert (Hsolved : Sem.solved st target).
 { eapply snapshot_spawn_solved;[exact Hsnapshot |].
   eapply evaluation_paths;eassumption. }
 split;[exact Hsolved |eapply evaluation_spawn;eassumption].
Qed.


Definition publication_state st fr :=
 R.publish_targets (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr.
Lemma publication_sigma st fr : R.sigma (publication_state st fr) = R.sigma st.
Proof. unfold publication_state. cbn. apply Replay.publish_sigma. Qed.
Lemma publication_targets st fr effects :
 Replay.accumulation fr effects ->
 Replay.targets_live (publication_state st fr) (R.frame_owner fr) effects.
Proof.
 intros [Hframe _] target value Hin.
 destruct (Hframe target value Hin) as [input [Hlookup [Hle Hmem]]].
 unfold publication_state,R.lookup_set. cbn. rewrite ML.lookup_update_same. exact Hmem.
Qed.
Lemma publication_settled st fr :
 publication_ready (S.elements (R.frame_current_targets fr))
 (C.publish (S.elements (R.frame_current_targets fr)) st fr) fr ->
 live_settled (publication_state st fr) (R.frame_owner fr).
Proof.
 intros Hready target Hmem.
 unfold publication_state,R.lookup_set in Hmem. cbn in Hmem. rewrite ML.lookup_update_same in Hmem.
 apply SL.mem_spec in Hmem.
 exact (proj1 (Hready target Hmem)).
Qed.
Theorem publication_snapshot tf st fr result :
 snapshot tf st (R.frame_owner fr) result -> Replay.accumulation fr (O.observed_sides result) ->
 contributions_descend st (publication_state st fr) /\
 aggregates_descend st (publication_state st fr) /\
 snapshot tf (publication_state st fr) (R.frame_owner fr) result.
Proof.
 intros Hsnapshot Hacc.
 pose proof (snapshot_publication_ready Hsnapshot Hacc) as Hready.
 destruct (@publish_descends (S.elements (R.frame_current_targets fr))
 (S.elements (R.frame_current_targets fr)) st fr (fun _ Hin=>Hin) Hready) as [Hcells [Hagg Hready']].
 split;[exact Hcells |]. split;[exact Hagg |].
 destruct Hsnapshot as [Hobs [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive Hsettled]]]]]]].
 split;[exact Hobs |]. split.
 - eapply reads_floor_descend;[|exact Hfloor].
   intros target. unfold R.sigma_value. rewrite publication_sigma. apply DL.leq_refl.
 - split.
   + eapply reads_solved_extends;[apply Replay.T.sigma_extends_same;apply publication_sigma |exact Hreads].
   + split.
     * eapply Demand.spawned_carries;[apply Replay.T.sigma_extends_same;apply publication_sigma |exact Hspawns].
     * split.
       -- change (D.leq (D.join (O.observed_direct result)
          (R.aggregate (C.publish (S.elements (R.frame_current_targets fr)) st fr) (R.frame_owner fr)))
          (R.sigma_value (publication_state st fr) (R.frame_owner fr)) = true).
          unfold R.sigma_value. rewrite publication_sigma.
          eapply DL.leq_trans;[|exact Hbound].
          apply DL.join_least;[apply DL.join_upper_left |].
          eapply DL.leq_trans;[apply Hagg |apply DL.join_upper_right].
       -- split.
          ++ apply Replay.recorded_effects_bounded.
             change (B.recorded_effects (C.publish (S.elements (R.frame_current_targets fr)) st fr)
               (R.frame_owner fr) (O.observed_sides result)).
             apply Replay.publish_records_frame, (proj1 Hacc).
          ++ split;[apply publication_targets,Hacc |apply publication_settled,Hready'].
Qed.


Lemma update_safe phase owner old input :
 phase <> U.Widen -> D.leq input old = true ->
 D.leq (snd (U.update false owner phase old input)) old = true /\
 fst (U.update false owner phase old input) <> U.Widen.
Proof.
 intros Hphase Hinput. destruct phase;try contradiction.
 all: cbn -[D.leq];rewrite Hinput;split;[apply WNL.narrow_upper,Hinput |discriminate].
Qed.
Lemma set_value_owner_descends st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) ->
 R.frame_phase fr <> U.Widen ->
 D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
 D.leq (R.sigma_value next (R.frame_owner fr)) (R.sigma_value st (R.frame_owner fr)) = true /\
 R.frame_phase next_fr <> U.Widen.
Proof.
 intros Hset Hphase Hbound. unfold R.set_value in Hset.
 set (owner:=R.frame_owner fr) in *.
 set (candidate:=D.join direct (R.aggregate st owner)) in *.
 set (old:=R.sigma_value st owner) in *.
 destruct (R.equivalent candidate old) eqn:Hcandidate.
 - inversion Hset;subst. split;[apply DL.leq_refl |exact Hphase].
 - destruct (S.mem owner (R.controlled st)).
   + pose proof (@update_safe (R.frame_phase fr) owner old candidate Hphase Hbound) as Hu.
     destruct (U.update false owner (R.frame_phase fr) old candidate) as [phase value] eqn:Hupdate.
     cbn in Hu,Hset. destruct Hu as [Hvalue Hsafe].
     destruct (R.equivalent value old).
     * inversion Hset;subst. split;[apply DL.leq_refl |exact Hsafe].
     * inversion Hset;subst. split;[|exact Hsafe].
       rewrite B.sigma_value_with_readers,B.sigma_value_enqueue_all,B.sigma_value_update_same.
       exact Hvalue.
   + cbn in Hset. rewrite Hcandidate in Hset. inversion Hset;subst.
     split;[|exact Hphase].
     rewrite B.sigma_value_with_readers,B.sigma_value_enqueue_all,B.sigma_value_update_same.
     exact Hbound.
Qed.
Theorem set_value_descends st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) ->
 R.frame_phase fr <> U.Widen ->
 D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
 values_descend st next /\ R.frame_phase next_fr <> U.Widen.
Proof.
 intros Hset Hphase Hbound.
 destruct (@set_value_owner_descends st fr direct next next_fr Hset Hphase Hbound) as [Howner Hsafe].
 split;[|exact Hsafe]. intro target.
 destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq];[exact Howner |].
 rewrite (@B.set_value_sigma_value_other_correctness st fr direct next next_fr target Hset Hneq). apply DL.leq_refl.
Qed.
Theorem commit_snapshot tf st fr result next next_fr :
 R.set_value st fr (O.observed_direct result) = (next,next_fr) ->
 R.frame_phase fr <> U.Widen ->
 snapshot tf st (R.frame_owner fr) result ->
 values_descend st next /\ R.frame_phase next_fr <> U.Widen /\
 snapshot tf next (R.frame_owner fr) result.
Proof.
 intros Hset Hphase [Hobs [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive Hsettled]]]]]]].
 destruct (@set_value_descends st fr (O.observed_direct result) next next_fr Hset Hphase Hbound) as [Hdown Hsafe].
 pose proof (@Replay.T.sigma_extends_set_value st fr (O.observed_direct result) next next_fr Hset) as Hextends.
 destruct (@set_value_side_view st fr (O.observed_direct result) next next_fr Hset) as [Ht [Hc Hv]].
 split;[exact Hdown |]. split;[exact Hsafe |].
 split;[exact Hobs |]. split;[eapply reads_floor_descend;eassumption |].
 split;[eapply reads_solved_extends;eassumption |].
 split;[eapply Demand.spawned_carries;eassumption |]. split.
 - unfold R.aggregate. rewrite Hv. eapply B.set_value_candidate_sound;exact Hset.
 - split.
   + unfold Replay.effects_bounded,R.stored_contribution. rewrite Hv. exact Hside.
   + split.
     * unfold Replay.targets_live,R.lookup_set. rewrite Ht. exact Hlive.
     * eapply live_settled_view;eassumption.
Qed.


Lemma snapshot_view tf before after owner result :
 R.sigma after = R.sigma before ->
 R.contributions after = R.contributions before ->
 R.last_targets after = R.last_targets before ->
 R.side_cells after = R.side_cells before ->
 snapshot tf before owner result -> snapshot tf after owner result.
Proof.
 intros Hsigma Hcontrib Htargets Hcells.
 unfold snapshot,reads_floor,reads_solved,Demand.spawned,Sem.solved,R.sigma_value,
 R.aggregate,Replay.effects_bounded,Replay.targets_live,live_settled,cell_settled,
 R.stored_contribution,R.stored_side_cell.
 now rewrite Hsigma,Hcontrib,Htargets,Hcells.
Qed.
Lemma snapshot_enqueue tf st target owner result :
 snapshot tf st owner result -> snapshot tf (R.enqueue st target) owner result.
Proof. eapply snapshot_view;reflexivity. Qed.
Lemma snapshot_requeue tf before after owner result target :
 snapshot tf after owner result ->
 snapshot tf (C.requeue_source before after owner target) owner result.
Proof.
 unfold C.requeue_source. destruct C.cell_changed;[apply snapshot_enqueue |trivial].
Qed.
Lemma write_live_settled st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 live_settled st (R.frame_owner fr) -> cell_settled next (R.frame_owner fr) target ->
 live_settled next (R.frame_owner fr).
Proof.
 intros Hwrite Hlive Hsettled observed Hmem.
 destruct (V.eq_dec observed target) as [->|Hneq];[exact Hsettled |].
 unfold cell_settled.
 rewrite (B.Credits.stored_side_cell_write_other Hwrite) by congruence.
 rewrite (B.Credits.stored_contribution_write_other Hwrite) by congruence.
 apply Hlive. now rewrite (@write_last_targets st fr target input next changed Hwrite) in Hmem.
Qed.
Lemma dead_effects_preserved st fr target next changed effects :
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 (forall value,~ In (target,value) effects) ->
 Replay.effects_bounded effects (R.stored_contribution st (R.frame_owner fr)) ->
 Replay.effects_bounded effects (R.stored_contribution next (R.frame_owner fr)).
Proof.
 intros Hw Habsent Hbound observed value Hin.
 assert (Hneq : (R.frame_owner fr,observed) <> (R.frame_owner fr,target)).
 { intro Heq. inversion Heq;subst observed. exact (Habsent value Hin). }
 rewrite (B.Credits.stored_contribution_write_other Hw) by exact Hneq.
 exact (Hbound observed value Hin).
Qed.
Theorem dead_snapshot tf st fr result target next changed :
 snapshot tf st (R.frame_owner fr) result ->
 S.mem target (R.lookup_set (R.last_targets st) (R.frame_owner fr)) = true ->
 (forall value,~ In (target,value) (O.observed_sides result)) ->
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 contributions_descend st next /\ aggregates_descend st next /\
 snapshot tf next (R.frame_owner fr) result.
Proof.
 intros [Hobs [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive Hsettled]]]]]]] Htarget Habsent Hw.
 destruct (@dead_write_descends st fr target next changed Hw (Hsettled target Htarget))
 as [Hcontrib [Hagg Hcell]].
 pose proof (@Replay.T.write_side_contribution_sigma st fr target D.bottom next changed Hw) as Hsigma.
 pose proof (@write_last_targets st fr target D.bottom next changed Hw) as Htargets.
 split;[exact Hcontrib |]. split;[exact Hagg |].
 split;[exact Hobs |]. split.
 - unfold reads_floor,R.sigma_value in *. now rewrite Hsigma.
 - split.
   + eapply reads_solved_extends;[apply Replay.T.sigma_extends_same;exact Hsigma |exact Hreads].
   + split.
     * eapply Demand.spawned_carries;[apply Replay.T.sigma_extends_same;exact Hsigma |exact Hspawns].
     * split.
       -- unfold R.sigma_value. rewrite Hsigma.
          eapply DL.leq_trans;[|exact Hbound]. apply DL.join_least;[apply DL.join_upper_left |].
          eapply DL.leq_trans;[apply Hagg |apply DL.join_upper_right].
       -- split;[eapply dead_effects_preserved;eassumption |].
          split.
          ++ unfold Replay.targets_live. rewrite Htargets. exact Hlive.
          ++ eapply write_live_settled;eassumption.
Qed.
Corollary dead_frame_snapshot tf st fr result target next changed :
 snapshot tf st (R.frame_owner fr) result ->
 Replay.accumulation fr (O.observed_sides result) ->
 S.mem target (R.lookup_set (R.last_targets st) (R.frame_owner fr)) = true ->
 S.mem target (R.frame_current_targets fr) = false ->
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 contributions_descend st next /\ aggregates_descend st next /\
 snapshot tf next (R.frame_owner fr) result.
Proof.
 intros Hsnapshot [Hframe _] Htarget Hmissing Hw.
 eapply dead_snapshot;[exact Hsnapshot |exact Htarget | |exact Hw].
 intros value Hin. destruct (Hframe target value Hin) as [input [Hlookup [Hle Hmem]]].
 rewrite Hmissing in Hmem. discriminate.
Qed.


Lemma snapshot_transport tf before after owner result :
 values_descend before after -> Replay.T.sigma_extends before after ->
 R.sigma_value after owner = R.sigma_value before owner ->
 aggregates_descend before after ->
 (forall target,R.stored_contribution after owner target = R.stored_contribution before owner target) ->
 R.lookup_set (R.last_targets after) owner = R.lookup_set (R.last_targets before) owner ->
 live_settled after owner ->
 snapshot tf before owner result -> snapshot tf after owner result.
Proof.
 intros Hdown Hextends Howner Hagg Hcells Htargets Hsettled
 [Hobs [Hfloor [Hreads [Hspawns [Hbound [Hside [Hlive _]]]]]]].
 split;[exact Hobs |]. split;[eapply reads_floor_descend;eassumption |].
 split;[eapply reads_solved_extends;eassumption |].
 split;[eapply Demand.spawned_carries;eassumption |]. split.
 - rewrite Howner. eapply DL.leq_trans;[|exact Hbound].
   apply DL.join_least;[apply DL.join_upper_left |].
   eapply DL.leq_trans;[apply Hagg |apply DL.join_upper_right].
 - split.
   + intros target value Hin. rewrite Hcells. exact (Hside target value Hin).
   + split;[|exact Hsettled]. intros target value Hin. rewrite Htargets. exact (Hlive target value Hin).
Qed.
Lemma reset_snapshot tf st owner result scope :
 snapshot tf st owner result -> snapshot tf (R.reset_registered_cells st scope) owner result.
Proof.
 intro Hsnapshot. eapply snapshot_transport;[ | | | | | | |exact Hsnapshot].
 - intro target. unfold R.reset_registered_cells. destruct Features.restart_side_phases;apply DL.leq_refl.
 - apply Replay.T.sigma_extends_reset_registered_cells.
 - unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity.
 - intro target. unfold R.reset_registered_cells. destruct Features.restart_side_phases;apply DL.leq_refl.
 - intro target. unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity.
 - unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity.
 - apply reset_live_settled. destruct Hsnapshot as [_ [_ [_ [_ [_ [_ [_ Hl]]]]]]]. exact Hl.
Qed.
Theorem other_commit_snapshot tf st fr direct next next_fr owner result :
 R.set_value st fr direct = (next,next_fr) -> values_descend st next ->
 owner <> R.frame_owner fr -> snapshot tf st owner result -> snapshot tf next owner result.
Proof.
 intros Hset Hdown Hneq Hsnapshot.
 destruct (@set_value_side_view st fr direct next next_fr Hset) as [Ht [Hc Hv]].
 eapply snapshot_transport;[exact Hdown | | | | | | |exact Hsnapshot].
 - eapply Replay.T.sigma_extends_set_value;exact Hset.
 - eapply B.set_value_sigma_value_other_correctness;eassumption.
 - intro target. unfold R.aggregate. rewrite Hv. apply DL.leq_refl.
 - intro target. unfold R.stored_contribution. now rewrite Hv.
 - now rewrite Ht.
 - destruct Hsnapshot as [_ [_ [_ [_ [_ [_ [_ Hl]]]]]]].
   eapply live_settled_view;eassumption.
Qed.
Theorem other_write_snapshot tf st fr target input next changed owner result :
 R.write_side_contribution st fr target input = (next,changed) ->
 aggregates_descend st next -> owner <> R.frame_owner fr ->
 snapshot tf st owner result -> snapshot tf next owner result.
Proof.
 intros Hw Hagg Hneq Hsnapshot.
 pose proof (@Replay.T.write_side_contribution_sigma st fr target input next changed Hw) as Hsigma.
 eapply snapshot_transport;[ | | |exact Hagg | | | |exact Hsnapshot].
 - intro observed. unfold R.sigma_value. rewrite Hsigma. apply DL.leq_refl.
 - apply Replay.T.sigma_extends_same,Hsigma.
 - unfold R.sigma_value. now rewrite Hsigma.
 - intro observed. eapply B.Credits.stored_contribution_write_other;[exact Hw |congruence].
 - now rewrite (@write_last_targets st fr target input next changed Hw).
 - destruct Hsnapshot as [_ [_ [_ [_ [_ [_ [_ Hl]]]]]]].
   eapply live_write_other;eassumption.
Qed.


Definition higher_queue_solved root st :=
 forall owner,R.rank_lt st root owner = true -> B.queued st owner -> Sem.solved st owner.
Definition higher_unsolved_bottom root st :=
 forall owner,R.rank_lt st root owner = true -> ~ Sem.solved st owner ->
 D.leq (R.aggregate st owner) D.bottom = true.
Lemma unsolved_value_bottom st owner :
 ~ Sem.solved st owner -> R.sigma_value st owner = D.bottom.
Proof.
 intro Hunsolved. unfold R.sigma_value.
 destruct (M.lookup (R.sigma st) owner) as [value|] eqn:Hlookup;[|reflexivity].
 exfalso. apply Hunsolved. now exists value.
Qed.
Lemma continuation_active_solved st k owner :
 Replay.T.continuation_owners_materialized st k ->
 B.continuation_active_correctness owner k -> Sem.solved st owner.
Proof.
 induction k;cbn;intros Hmat Hactive;try contradiction.
 all: destruct Hmat as [Hhead Htail].
 all: try destruct Hactive as [->|Hactive].
 all: try solve [apply Demand.materialized_solved,Hhead].
 all: apply IHk;assumption.
Qed.
Lemma dead_active_solved st fr direct pending k owner :
 Replay.T.control_owners_materialized st (R.RunDead fr direct pending k) ->
 B.control_active owner (R.RunDead fr direct pending k) -> Sem.solved st owner.
Proof.
 intros [Howner Htail] [->|Hactive];[apply Demand.materialized_solved,Howner |].
 eapply continuation_active_solved;eassumption.
Qed.
Theorem dead_higher_unsolved_bottom tf roots st fr direct pending k root :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 higher_queue_solved root st -> higher_unsolved_bottom root st.
Proof.
 intros Hreach Hqueue owner Hhigher Hunsolved.
 destruct (Replay.reachable_aggregate Hreach owner) as [Hq|[Ha|Hagg]].
 - exfalso. apply Hunsolved,Hqueue;assumption.
 - exfalso. apply Hunsolved.
   eapply dead_active_solved;[exact (Replay.reachable_owners_materialized Hreach) |exact Ha].
 - unfold B.aggregate_bounded in Hagg. cbn in Hagg.
   rewrite (unsolved_value_bottom Hunsolved) in Hagg. exact Hagg.
Qed.
Lemma write_changed_flag st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 changed = negb (R.equivalent (R.aggregate next target) (R.aggregate st target)).
Proof.
 unfold R.write_side_contribution. intro Hw. inversion Hw;subst.
 unfold R.promote_side_target. destruct (R.rank_lt st target (R.frame_owner fr));reflexivity.
Qed.
Lemma write_ranking st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 R.ranking next = R.ranking st.
Proof.
 unfold R.write_side_contribution. intro Hw. inversion Hw;subst.
 unfold R.promote_side_target. destruct (R.rank_lt st target (R.frame_owner fr));reflexivity.
Qed.
Lemma equivalent_bottom lower upper :
 D.leq lower D.bottom = true -> D.leq upper D.bottom = true ->
 R.equivalent lower upper = true.
Proof.
 intros Hl Hu. unfold R.equivalent. apply andb_true_iff. split; eapply DL.leq_trans; eauto using DL.bottom_least.
Qed.
Theorem descending_write_changed_higher_solved root st fr target input next changed :
 higher_unsolved_bottom root st ->
 R.write_side_contribution st fr target input = (next,changed) ->
 aggregates_descend st next -> R.rank_lt st root target = true ->
 changed = true -> Sem.solved st target.
Proof.
 intros Hbottom Hw Hdown Hhigher Hchanged.
 destruct (M.lookup (R.sigma st) target) as [value|] eqn:Hlookup;[now exists value |].
 assert (Hunsolved : ~ Sem.solved st target).
 { intros [value Hv]. rewrite Hlookup in Hv. discriminate. }
 pose proof (Hbottom target Hhigher Hunsolved) as Hold.
 assert (Hnext : D.leq (R.aggregate next target) D.bottom = true)
 by (eapply DL.leq_trans;[apply Hdown |exact Hold]).
 pose proof (write_changed_flag Hw) as Hflag.
 rewrite Hchanged,(equivalent_bottom Hnext Hold) in Hflag. discriminate.
Qed.


Lemma higher_queue_view root before after :
 R.ranking after = R.ranking before -> R.sigma after = R.sigma before ->
 (forall owner,B.queued after owner -> B.queued before owner) ->
 higher_queue_solved root before -> higher_queue_solved root after.
Proof.
 intros Hrank Hsigma Hqueues Hqueue owner Hhigher Hqueued.
 unfold R.rank_lt,R.ranking_lt in Hhigher. rewrite Hrank in Hhigher.
 destruct (Hqueue owner Hhigher (Hqueues owner Hqueued)) as [value Hlookup].
 exists value. now rewrite Hsigma.
Qed.
Lemma higher_bottom_view root before after :
 R.ranking after = R.ranking before -> R.sigma after = R.sigma before ->
 aggregates_descend before after -> higher_unsolved_bottom root before ->
 higher_unsolved_bottom root after.
Proof.
 intros Hrank Hsigma Hdown Hbottom owner Hhigher Hunsolved.
 unfold R.rank_lt,R.ranking_lt in Hhigher. rewrite Hrank in Hhigher.
 assert (Hbefore : ~ Sem.solved before owner).
 { intros [value Hlookup]. apply Hunsolved. exists value. now rewrite Hsigma. }
 eapply DL.leq_trans;[apply Hdown |apply Hbottom;assumption].
Qed.
Lemma higher_queue_enqueue root st inserted :
 (R.rank_lt st root inserted = true -> Sem.solved st inserted) ->
 higher_queue_solved root st -> higher_queue_solved root (R.enqueue st inserted).
Proof.
 intros Hinsert Hqueue owner Hhigher Hqueued.
 unfold B.queued in Hqueued. cbn in Hqueued.
 apply (proj1 (@B.queue_insert_members (R.ranking st) inserted (R.queue st) owner)) in Hqueued.
 destruct Hqueued as [->|Hqueued];[apply Hinsert,Hhigher |apply Hqueue;assumption].
Qed.
Lemma write_queue st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) -> R.queue next = R.queue st.
Proof.
 unfold R.write_side_contribution. intro Hw. inversion Hw;subst.
 unfold R.promote_side_target. destruct (R.rank_lt st target (R.frame_owner fr));reflexivity.
Qed.
Lemma write_higher_queue root st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 higher_queue_solved root st -> higher_queue_solved root next.
Proof.
 intros Hw Hqueue. eapply higher_queue_view;[eapply write_ranking;exact Hw
 |eapply Replay.T.write_side_contribution_sigma;exact Hw | |exact Hqueue].
 intros owner Hq. unfold B.queued in *. now rewrite (write_queue Hw) in Hq.
Qed.
Lemma finish_higher_queue root st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 Sem.solved st (R.frame_owner fr) -> higher_queue_solved root st ->
 higher_unsolved_bottom root st -> aggregates_descend st next ->
 higher_queue_solved root (C.finish_write st next fr target changed).
Proof.
 intros Hw Hsource Hqueue Hbottom Hdown.
 pose proof (@Replay.T.write_side_contribution_sigma st fr target input next changed Hw) as Hsigma.
 pose proof (write_ranking Hw) as Hrank.
 assert (Hsource' : Sem.solved next (R.frame_owner fr)).
 { destruct Hsource as [value Hlookup]. exists value. now rewrite Hsigma. }
 assert (Hqueue' : higher_queue_solved root next) by (eapply write_higher_queue;eassumption).
 assert (Htarget : changed = true -> R.rank_lt next root target = true -> Sem.solved next target).
 { intros Hchanged Hhigher. unfold R.rank_lt,R.ranking_lt in Hhigher. rewrite Hrank in Hhigher.
   destruct (@descending_write_changed_higher_solved root st fr target input next changed
     Hbottom Hw Hdown Hhigher Hchanged) as [value Hlookup].
   exists value. now rewrite Hsigma. }
 unfold C.finish_write,C.requeue_source.
 destruct changed,C.cell_changed.
 - apply higher_queue_enqueue;[intros Hhigher;apply Htarget;[reflexivity |exact Hhigher] |].
   apply higher_queue_enqueue;[intros _;exact Hsource' |exact Hqueue'].
 - apply higher_queue_enqueue;[intros Hhigher;apply Htarget;[reflexivity |exact Hhigher] |exact Hqueue'].
 - apply higher_queue_enqueue;[intros _;exact Hsource' |exact Hqueue'].
 - exact Hqueue'.
Qed.
Lemma finish_ranking before after fr target changed :
 R.ranking (C.finish_write before after fr target changed) = R.ranking after.
Proof. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;reflexivity. Qed.
Lemma finish_higher_bottom root st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 aggregates_descend st next -> higher_unsolved_bottom root st ->
 higher_unsolved_bottom root (C.finish_write st next fr target changed).
Proof.
 intros Hw Hdown Hbottom.
 eapply higher_bottom_view;[rewrite finish_ranking;eapply write_ranking;exact Hw
 |rewrite Replay.finish_sigma;eapply Replay.T.write_side_contribution_sigma;exact Hw | |exact Hbottom].
 intros observed. eapply DL.leq_trans;[apply finish_aggregates |apply Hdown].
Qed.
Theorem publish_higher_queue root targets support st fr :
 List.incl targets support -> publication_ready support st fr ->
 Sem.solved st (R.frame_owner fr) ->
 higher_queue_solved root st -> higher_unsolved_bottom root st ->
 higher_queue_solved root (C.publish targets st fr) /\
 higher_unsolved_bottom root (C.publish targets st fr).
Proof.
 revert st. induction targets as [|target rest IH];intros st Hin Hready Hsource Hqueue Hbottom;
 cbn -[R.write_side_contribution C.finish_write];[now split |].
 fold (local_input fr target).
 destruct (R.write_side_contribution st fr target (local_input fr target)) as [next changed] eqn:Hw.
 assert (Hmember : In target support) by (apply Hin;now left).
 destruct (Hready target Hmember) as [Hsettled Hinput].
 assert (Hdown : aggregates_descend st next).
 { eapply write_aggregates_descend;[exact Hw |].
   exact (proj1 (write_settled_descends Hw Hsettled Hinput)). }
 apply IH.
 - intros observed Hmem. apply Hin;now right.
 - apply finish_ready. eapply write_ready;eassumption.
 - destruct Hsource as [value Hlookup]. exists value.
   rewrite Replay.finish_sigma,(@Replay.T.write_side_contribution_sigma st fr target (local_input fr target) next changed Hw).
   exact Hlookup.
 - eapply finish_higher_queue;eassumption.
 - eapply finish_higher_bottom;eassumption.
Qed.


Theorem actual_publication_higher_queue tf roots root st fr direct k result :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 higher_queue_solved root st ->
 snapshot tf st (R.frame_owner fr) result ->
 Replay.accumulation fr (O.observed_sides result) ->
 higher_queue_solved root (publication_state st fr) /\
 higher_unsolved_bottom root (publication_state st fr).
Proof.
 intros Hreach Hqueue Hsnapshot Hacc.
 assert (Hsource : Sem.solved st (R.frame_owner fr)).
 { apply Demand.materialized_solved.
   exact (proj1 (Replay.reachable_owners_materialized Hreach)). }
 assert (Hbottom : higher_unsolved_bottom root st)
 by (eapply dead_higher_unsolved_bottom;eassumption).
 destruct (@publish_higher_queue root (S.elements (R.frame_current_targets fr))
 (S.elements (R.frame_current_targets fr)) st fr (fun _ Hin=>Hin)
 (snapshot_publication_ready Hsnapshot Hacc) Hsource Hqueue Hbottom) as [Hq Hb].
 split.
 - eapply higher_queue_view;[reflexivity |reflexivity | |exact Hq].
   intros owner Hqueued. exact Hqueued.
 - eapply higher_bottom_view;[reflexivity |reflexivity | |exact Hb].
   intros target. apply DL.leq_refl.
Qed.
Lemma solved_materialized st owner : Sem.solved st owner -> R.is_materialized st owner = true.
Proof. intros [value Hlookup]. unfold R.is_materialized. now rewrite Hlookup. Qed.
Lemma requeue_ranking before after source target :
 R.ranking (C.requeue_source before after source target) = R.ranking after.
Proof. unfold C.requeue_source. destruct C.cell_changed;reflexivity. Qed.
Lemma requeue_materialized before after source target owner :
 R.is_materialized (C.requeue_source before after source target) owner = R.is_materialized after owner.
Proof. unfold R.is_materialized. now rewrite Replay.requeue_sigma. Qed.
Theorem descending_dead_continuation root st fr direct target rest k next changed :
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 higher_unsolved_bottom root st -> aggregates_descend st next ->
 (R.frame_owner fr = root \/ R.rank_lt st root (R.frame_owner fr) = true) ->
 R.continue_dead (C.requeue_source st next (R.frame_owner fr) target)
 fr direct target rest k changed =
 {|R.cfg_state:=C.finish_write st next fr target changed;
 R.cfg_control:=R.RunDead fr direct rest k|}.
Proof.
 intros Hw Hbottom Hdown Howner.
 unfold R.continue_dead,C.finish_write. destruct changed;[|reflexivity].
 assert (Hguard : (R.rank_lt (C.requeue_source st next (R.frame_owner fr) target)
 (R.frame_owner fr) target &&
 negb (R.is_materialized (C.requeue_source st next (R.frame_owner fr) target) target))%bool = false).
 { destruct (R.rank_lt (C.requeue_source st next (R.frame_owner fr) target) (R.frame_owner fr) target)
   eqn:Hlt;[|reflexivity].
   assert (Hhigher : R.rank_lt st root target = true).
   { unfold R.rank_lt,R.ranking_lt in Hlt.
     rewrite requeue_ranking,(write_ranking Hw) in Hlt.
     destruct Howner as [<-|Hroot];[exact Hlt |].
     eapply Replay.T.rank_lt_trans_true;[exact Hroot |exact Hlt]. }
   pose proof (@descending_write_changed_higher_solved root st fr target D.bottom next true
     Hbottom Hw Hdown Hhigher eq_refl) as Hsolved.
   assert (Hnext : Sem.solved next target).
   { destruct Hsolved as [value Hlookup]. exists value.
     now rewrite (@Replay.T.write_side_contribution_sigma st fr target D.bottom next true Hw). }
   rewrite requeue_materialized,(solved_materialized Hnext). reflexivity. }
 rewrite Hguard. reflexivity.
Qed.


Lemma set_higher_queue root st fr direct next next_fr :
 higher_queue_solved root st -> Replay.Readers.solved st ->
 R.set_value st fr direct = (next,next_fr) -> higher_queue_solved root next.
Proof.
 intros Hqueue Hreaders Hset owner Hhigher Hqueued.
 destruct (@Replay.Readers.set_cases st fr direct next next_fr Hset) as [->|[value ->]];
 [apply Hqueue;assumption |].
 unfold B.commit_value,B.queued in Hqueued. cbn in Hqueued.
 apply (proj1 (@B.queue_insert_all_members (R.ranking st)
 (S.elements (R.lookup_set (R.readers st) (R.frame_owner fr))) (R.queue st) owner)) in Hqueued.
 destruct Hqueued as [Hinvalidated|Hqueued].
 - eapply B.set_value_solved;[exact Hset |].
   apply Hreaders with (R.frame_owner fr). apply SL.mem_spec,Hinvalidated.
 - eapply B.set_value_solved;[exact Hset |]. apply Hqueue;assumption.
Qed.
Lemma ordinary_requeue_higher_queue root before after owner :
 Sem.solved after owner -> higher_queue_solved root after ->
 higher_queue_solved root (R.requeue_changed_controlled_owner before after owner).
Proof.
 intros Hsolved Hqueue. unfold R.requeue_changed_controlled_owner.
 destruct (_ && _)%bool;[|exact Hqueue].
 apply higher_queue_enqueue;[intros _;exact Hsolved |exact Hqueue].
Qed.
Theorem actual_commit_higher_queue tf roots root st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 higher_queue_solved root st -> higher_queue_solved root after.
Proof.
 intros Hreach Hstep Hqueue.
 pose proof (Replay.Readers.reachable_solved Hreach) as Hreaders.
 pose proof (Replay.reachable_commit_owner_solved Hreach) as Hsource.
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep.
 destruct (C.P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_frame] eqn:Hset.
 destruct (C.P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 inversion Hstep;subst. apply ordinary_requeue_higher_queue.
 - eapply B.set_value_solved;[exact Hset |exact Hsource].
 - eapply set_higher_queue;eassumption.
Qed.
Lemma snapshot_finish tf before after fr target changed owner result :
 snapshot tf after owner result ->
 snapshot tf (C.finish_write before after fr target changed) owner result.
Proof.
 unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;intro Hsnapshot;
 auto using snapshot_enqueue.
Qed.
Theorem publish_other_snapshot tf targets support st fr owner result :
 List.incl targets support -> publication_ready support st fr ->
 owner <> R.frame_owner fr -> snapshot tf st owner result ->
 snapshot tf (C.publish targets st fr) owner result.
Proof.
 intros Hin. revert st. induction targets as [|target rest IH];intros st Hready Hneq Hsnapshot;
 cbn -[R.write_side_contribution C.finish_write];[exact Hsnapshot |].
 fold (local_input fr target).
 destruct (R.write_side_contribution st fr target (local_input fr target)) as [next changed] eqn:Hw.
 assert (Hmem : In target support) by (apply Hin;now left).
 destruct (Hready target Hmem) as [Hsettled Hinput].
 apply IH;[intros observed Hm;apply Hin;now right | |exact Hneq |].
 - apply finish_ready. eapply write_ready;eassumption.
 - apply snapshot_finish. eapply other_write_snapshot;[exact Hw | |exact Hneq |exact Hsnapshot].
   eapply write_aggregates_descend;[exact Hw |].
   exact (proj1 (write_settled_descends Hw Hsettled Hinput)).
Qed.
Lemma targets_other_snapshot tf st fr owner result :
 owner <> R.frame_owner fr -> snapshot tf st owner result ->
 snapshot tf (R.publish_targets st fr) owner result.
Proof.
 intros Hneq Hsnapshot.
 eapply snapshot_transport;[ | | | | | | |exact Hsnapshot].
 - intro target. apply DL.leq_refl.
 - apply Replay.T.sigma_extends_same;reflexivity.
 - reflexivity.
 - intro target. apply DL.leq_refl.
 - intro target. reflexivity.
 - unfold R.lookup_set. cbn. rewrite ML.lookup_update_other;[reflexivity |congruence].
 - apply live_publish_targets_other;[exact Hneq |].
   destruct Hsnapshot as [_ [_ [_ [_ [_ [_ [_ Hl]]]]]]]. exact Hl.
Qed.
Theorem publication_other_snapshot tf st fr current owner result :
 snapshot tf st (R.frame_owner fr) current -> Replay.accumulation fr (O.observed_sides current) ->
 owner <> R.frame_owner fr -> snapshot tf st owner result ->
 snapshot tf (publication_state st fr) owner result.
Proof.
 intros Hcurrent Hacc Hneq Hsnapshot. apply targets_other_snapshot;[exact Hneq |].
 eapply publish_other_snapshot;[intros target Hmem;exact Hmem
 |exact (snapshot_publication_ready Hcurrent Hacc) |exact Hneq |exact Hsnapshot].
Qed.

Theorem commit_observation tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 exists result,O.observed_direct result = direct /\
 Sem.rhs_observes (tf (R.frame_owner fr)) result /\
 Sem.rhs_eval st (tf (R.frame_owner fr)) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) /\
 Demand.spawned st (O.observed_spawns result).
Proof.
 intros Hreach Hstep.
 destruct (Demand.reachable_history Hreach) as [[reads [effects [spawns [Hobs [Hguard Hspawns]]]]] Hk].
 destruct (@C.P.fresh_commit_ready tf st fr direct k after next_fr next_k Hstep) as [Hpending Hclean].
 exists {|O.observed_direct:=direct;O.observed_reads:=reads;O.observed_sides:=effects;O.observed_spawns:=spawns|}.
 split;[reflexivity |]. split;[exact Hobs |]. split;[|exact Hspawns].
 apply Demand.observation_replay;[exact Hobs |].
 eapply C.H.guarded_reads_clean;eassumption.
Qed.
Lemma commit_replay_accumulation tf roots st fr direct k after next_fr next_k result :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 Sem.rhs_eval st (tf (R.frame_owner fr)) (O.observed_direct result)
 (O.observed_reads result) (O.observed_sides result) ->
 Replay.accumulation fr (O.observed_sides result) /\
 Replay.effects_bounded (O.observed_sides result) (R.stored_contribution st (R.frame_owner fr)).
Proof.
 intros Hreach Hstep Heval.
 destruct (@Replay.actual_commit_accumulation tf roots st fr direct k after next_fr next_k Hreach Hstep)
 as [reads [effects [Hreplay Hacc]]].
 destruct (B.rhs_eval_deterministic Hreplay Heval) as [Hd [Hr He]].
 rewrite He in Hacc. split;[exact Hacc |].
 destruct (@Replay.actual_commit_side_coverage tf roots st fr direct k after next_fr next_k Hreach Hstep)
 as [rs [es [Hreplay' Hside]]].
 destruct (B.rhs_eval_deterministic Hreplay' Heval) as [_ [_ ->]]. exact Hside.
Qed.
Theorem commit_input_snapshot tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true ->
 exists result,O.observed_direct result = direct /\ snapshot tf st (R.frame_owner fr) result /\
 Replay.accumulation fr (O.observed_sides result).
Proof.
 intros Hreach Hstep Hbound.
 destruct (@commit_observation tf roots st fr direct k after next_fr next_k Hreach Hstep)
 as [result [Hdirect [Hobs [Heval Hspawn]]]].
 destruct (@commit_replay_accumulation tf roots st fr direct k after next_fr next_k result Hreach Hstep Heval)
 as [Hacc Hside].
 destruct (replay_floor Heval) as [Hfloor Hreads].
 exists result. split;[exact Hdirect |]. split;[|exact Hacc].
 split;[exact Hobs |]. split;[exact Hfloor |]. split;[exact Hreads |].
 split;[exact Hspawn |]. split;[now rewrite Hdirect |]. split;[exact Hside |]. split.
 - destruct (Replay.reachable_commit_origin Hreach) as [before ->].
   apply publication_targets,Hacc.
 - eapply reachable_commit_live_settled;[exact Hreach |exact Hstep].
Qed.
Lemma boxn_entry_input st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) ->
 R.frame_phase fr = U.BoxW -> R.frame_phase next_fr = U.BoxN ->
 S.mem (R.frame_owner fr) (R.controlled st) = true /\
 D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
 intros Hset Hphase Hnext. unfold R.set_value in Hset.
 set (candidate:=D.join direct (R.aggregate st (R.frame_owner fr))) in *.
 set (old:=R.sigma_value st (R.frame_owner fr)) in *.
 destruct (R.equivalent candidate old).
 - inversion Hset;subst. rewrite Hphase in Hnext. discriminate.
 - destruct (S.mem (R.frame_owner fr) (R.controlled st)) eqn:Hcontrolled.
   + rewrite Hphase in Hset. cbn -[D.leq R.sigma_value] in Hset.
     destruct (D.leq candidate old) eqn:Hinput;[now split |].
     cbn -[R.equivalent WN.widen] in Hset.
     destruct (R.equivalent (WN.widen old candidate) old);
     inversion Hset;subst;discriminate.
   + cbn in Hset. destruct (R.equivalent candidate old);
     inversion Hset;subst;cbn in Hnext;rewrite Hphase in Hnext;discriminate.
Qed.

Lemma commit_step_shape tf st fr direct k after next_fr next_k :
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 exists next,R.set_value st fr direct = (next,next_fr) /\
 after = R.requeue_changed_controlled_owner st next (R.frame_owner fr) /\ next_k = k.
Proof.
 intro Hstep.
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep.
 destruct (C.P.pending_above st (R.frame_owner fr));[destruct p;discriminate |].
 destruct (R.queue_contains (R.frame_owner fr) (R.queue st));[discriminate |].
 cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
 destruct (R.set_value st fr direct) as [next next_frame] eqn:Hset.
 destruct (C.P.pending_above st (R.frame_owner fr)) as [[target rest]|];[discriminate |].
 inversion Hstep;subst. exists next. now repeat split.
Qed.
Lemma set_ranking st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) -> R.ranking next = R.ranking st.
Proof.
 intro Hset. destruct (@Replay.Readers.set_cases st fr direct next next_fr Hset) as [->|[value ->]];reflexivity.
Qed.
Lemma ordinary_requeue_snapshot tf before after source owner result :
 snapshot tf after owner result ->
 snapshot tf (R.requeue_changed_controlled_owner before after source) owner result.
Proof. eapply snapshot_view;reflexivity. Qed.
Definition higher_snapshots tf root st :=
 forall owner,R.rank_lt st root owner = true -> Sem.solved st owner ->
 exists result,snapshot tf st owner result.
Definition monotone (tf : R.ConstraintSystem.system) := forall owner,
 Sem.rhs_dependencies_monotone (tf owner) /\ Sem.rhs_effects_monotone (tf owner).
Theorem commit_higher_snapshots tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true -> monotone tf ->
 higher_snapshots tf (R.frame_owner fr) st.
Proof.
 intros Hreach Hstep Hcontrolled Hmono owner Hhigher Hsolved.
 destruct (@committing_higher_frontier tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher Hsolved (proj1 (Hmono owner)) (proj2 (Hmono owner)))
 as [result Hfrontier].
 exists result. apply frontier_snapshot,Hfrontier.
Qed.
Lemma higher_snapshots_set tf root st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) -> R.frame_owner fr = root ->
 values_descend st next -> higher_snapshots tf root st -> higher_snapshots tf root next.
Proof.
 intros Hset Howner Hdown Hhistory owner Hhigher Hsolved.
 assert (Hhigher' : R.rank_lt st root owner = true).
 { unfold R.rank_lt,R.ranking_lt in *. now rewrite (@set_ranking st fr direct next next_fr Hset) in Hhigher. }
 assert (Hneq : owner <> R.frame_owner fr).
 { rewrite Howner. intro Heq. subst owner.
   exact (@B.rank_lt_true_neq_correctness st root root Hhigher' eq_refl). }
 assert (Hbefore : Sem.solved st owner).
 { destruct (@B.set_value_solved_origin st fr direct next next_fr owner Hset Hsolved) as [Hsolved'|Heq];
   [exact Hsolved' |contradiction]. }
 destruct (Hhistory owner Hhigher' Hbefore) as [result Hsnapshot].
 exists result. eapply other_commit_snapshot;eassumption.
Qed.
Lemma higher_snapshots_requeue tf root before after source :
 higher_snapshots tf root after ->
 higher_snapshots tf root (R.requeue_changed_controlled_owner before after source).
Proof.
 intros Hhistory owner Hhigher Hsolved.
 destruct (Hhistory owner Hhigher Hsolved) as [result Hsnapshot].
 exists result. apply ordinary_requeue_snapshot,Hsnapshot.
Qed.
Lemma controlled_commit_higher_queue tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 S.mem (R.frame_owner fr) (R.controlled st) = true ->
 higher_queue_solved (R.frame_owner fr) st.
Proof.
 intros Hreach Hstep Hcontrolled owner Hhigher Hqueued. exfalso.
 exact (proj1 (@Replay.committing_higher_clean tf roots st fr direct k after next_fr next_k owner
 Hreach Hstep Hcontrolled Hhigher) Hqueued).
Qed.
Theorem boxn_entry_state tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots)
 {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 R.frame_phase fr = U.BoxW -> R.frame_phase next_fr = U.BoxN -> monotone tf ->
 values_descend st after /\ Sem.solved after (R.frame_owner fr) /\
 (exists result,snapshot tf after (R.frame_owner fr) result) /\
 higher_snapshots tf (R.frame_owner fr) after /\ higher_queue_solved (R.frame_owner fr) after.
Proof.
 intros Hreach Hstep Hphase Hnextphase Hmono.
 destruct (@commit_step_shape tf st fr direct k after next_fr next_k Hstep) as [next [Hset [Hafter Hk]]].
 destruct (@boxn_entry_input st fr direct next next_fr Hset Hphase Hnextphase) as [Hcontrolled Hbound].
 destruct (@commit_input_snapshot tf roots st fr direct k after next_fr next_k Hreach Hstep Hbound)
 as [result [Hdirect [Hsnapshot Hacc]]].
 assert (Hset' : R.set_value st fr (O.observed_direct result) = (next,next_fr)) by now rewrite Hdirect.
 assert (Hsafe : R.frame_phase fr <> U.Widen) by (rewrite Hphase;discriminate).
 destruct (@commit_snapshot tf st fr result next next_fr Hset' Hsafe Hsnapshot) as [Hdown [_ Hsnapshot']].
 assert (Hhigher : higher_snapshots tf (R.frame_owner fr) st)
 by (eapply commit_higher_snapshots;eassumption).
 assert (Hqueue : higher_queue_solved (R.frame_owner fr) st)
 by (eapply controlled_commit_higher_queue;eassumption).
 split;[rewrite Hafter;exact Hdown |]. split.
 - rewrite Hafter. change (Sem.solved next (R.frame_owner fr)).
   eapply B.set_value_solved;[exact Hset |].
   eapply Replay.reachable_commit_owner_solved;exact Hreach.
 - split.
   + exists result. rewrite Hafter. apply ordinary_requeue_snapshot,Hsnapshot'.
   + split.
     * rewrite Hafter. apply higher_snapshots_requeue.
       eapply higher_snapshots_set;[exact Hset |reflexivity |exact Hdown |exact Hhigher].
     * eapply actual_commit_higher_queue;[exact Hreach |exact Hstep |exact Hqueue].
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
 exact (@Replay.Episodes.next_extends tf before after).
Qed.


Lemma continuation_active_ranked st k owner :
 B.continuation_ranked st k -> B.continuation_active_correctness owner k -> B.ranked st owner.
Proof.
 revert owner. induction k;intros owner Hranked Hactive;cbn in Hranked,Hactive;try contradiction.
 - destruct Hranked as [[Howner _] [_ Hrest]]. destruct Hactive as [->|Ha];[exact Howner |eapply IHk;eassumption].
 - destruct Hranked as [[Howner _] Hrest]. destruct Hactive as [->|Ha];[exact Howner |eapply IHk;eassumption].
 - destruct Hranked as [[Howner _] Hrest]. destruct Hactive as [->|Ha];[exact Howner |eapply IHk;eassumption].
 - destruct Hranked as [[Howner _] [_ Hrest]]. destruct Hactive as [->|Ha];[exact Howner |eapply IHk;eassumption].
 - destruct Hranked as [_ Hrest]. eapply IHk;eassumption.
Qed.
Lemma control_active_ranked st control owner :
 B.control_ranked st control -> B.control_active owner control -> B.ranked st owner.
Proof.
 intros Hranked Hactive. destruct control;cbn in Hranked,Hactive;try contradiction.
 - destruct Hranked as [Howner Hrest]. destruct Hactive as [->|Ha];[exact Howner |eapply continuation_active_ranked;eassumption].
 - destruct Hranked as [[Howner _] Hrest]. destruct Hactive as [->|Ha];[exact Howner |eapply continuation_active_ranked;eassumption].
 - destruct Hranked as [[Howner _] [_ Hrest]]. destruct Hactive as [->|Ha];[exact Howner |eapply continuation_active_ranked;eassumption].
 - destruct Hranked as [[Howner _] Hrest]. destruct Hactive as [->|Ha];[exact Howner |eapply continuation_active_ranked;eassumption].
 - destruct Hranked as [_ Hrest]. eapply continuation_active_ranked;eassumption.
 - eapply continuation_active_ranked;eassumption.
Qed.
Definition solved_ranked st := forall owner,Sem.solved st owner -> B.ranked st owner.
Lemma next_solved_ranked tf roots before after :
 N.steps tf (R.initial_config roots) before -> solved_ranked (R.cfg_state before) ->
 N.next_config tf before = Some after -> solved_ranked (R.cfg_state after).
Proof.
 intros Hreach Hranked Hstep owner Hsolved.
 pose proof (@Replay.next_ranked tf before after (Replay.reachable_ranked Hreach) Hstep) as Hafter.
 destruct (@Replay.next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
 as [Hbefore|[Hqueue|Hactive]].
 - eapply B.ranked_extended;[exact (@next_extends tf before after Hstep) |apply Hranked,Hbefore].
 - apply (B.data_queue_ranked (B.configuration_state_data Hafter)),Hqueue.
 - eapply control_active_ranked;[exact (B.configuration_control_ranked Hafter) |exact Hactive].
Qed.
Lemma steps_solved_ranked tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 solved_ranked (R.cfg_state first) -> solved_ranked (R.cfg_state last).
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hranked;[exact Hranked |].
 apply IHHsteps.
 - eapply Replay.steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - eapply next_solved_ranked;eassumption.
Qed.
Theorem reachable_solved_ranked tf roots c :
 N.steps tf (R.initial_config roots) c -> solved_ranked (R.cfg_state c).
Proof.
 intro Hreach. eapply steps_solved_ranked;[exact Hreach |constructor |].
 intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
Qed.
Lemma observe_ranked st target :
 B.ranked st target -> R.observe st target = st.
Proof.
 intros [rank Hrank]. unfold R.observe.
 change ((let '(next,_) := C.P.Base.Laws.R.observe (R.ranking st) target in R.with_ranking st next) = st).
 rewrite (C.P.Base.Laws.observe_existing (R.ranking st) target Hrank).
 now destruct st.
Qed.
Lemma live_target_ranked st owner target :
 B.state_data_ranked st ->
 S.mem target (R.lookup_set (R.last_targets st) owner) = true -> B.ranked st target.
Proof.
 intros Hdata Hmem. unfold R.lookup_set in Hmem.
 destruct (M.lookup (R.last_targets st) owner) as [targets|] eqn:Htargets.
 - apply (B.data_targets_ranked Hdata Htargets). exact Hmem.
 - rewrite SL.empty_spec in Hmem. discriminate.
Qed.


Definition region root st owner := owner = root \/ R.rank_lt st root owner = true.
Definition histories tf root st :=
 forall owner,region root st owner -> Sem.solved st owner -> exists result,snapshot tf st owner result.
Definition previous_live st fr :=
 forall target,S.mem target (R.frame_previous_targets fr) = true ->
 S.mem target (R.lookup_set (R.last_targets st) (R.frame_owner fr)) = true.
Definition eligible root st fr := region root st (R.frame_owner fr) /\ R.frame_phase fr <> U.Widen.
Definition restart_frame st fr := Replay.accumulation fr [] /\ previous_live st fr.
Inductive stack tf root st (base : R.continuation) : R.continuation -> Prop :=
| StackBase : stack tf root st base base
| StackDrain : forall fr rest,eligible root st fr -> stack tf root st base rest ->
 stack tf root st base (R.KDrain fr rest)
| StackRestart : forall fr rest,eligible root st fr -> restart_frame st fr ->
 stack tf root st base rest -> stack tf root st base (R.KAfterSide fr (tf (R.frame_owner fr)) rest).
Definition running tf st fr current :=
 exists upper,snapshot tf st (R.frame_owner fr) upper /\ evaluation tf st fr current upper.
Definition completed tf st fr direct :=
 exists result,O.observed_direct result = direct /\ snapshot tf st (R.frame_owner fr) result /\
 Replay.accumulation fr (O.observed_sides result).
Definition pending_live st fr pending :=
 forall target,In target pending -> S.mem target (R.lookup_set (R.last_targets st) (R.frame_owner fr)) = true.
Definition control tf root base st ctrl :=
 match ctrl with
 | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => False
 | R.StartEpisode owner k => R.rank_lt st root owner = true /\ Sem.solved st owner /\ stack tf root st base k
 | R.RunRhs fr body k => eligible root st fr /\ running tf st fr body /\ previous_live st fr /\ stack tf root st base k
 | R.RunDead fr direct pending k => eligible root st fr /\ completed tf st fr direct /\ pending_live st fr pending /\ stack tf root st base k
 | R.RunCommit fr direct k => eligible root st fr /\ completed tf st fr direct /\ stack tf root st base k
 | R.RunDrain fr k => eligible root st fr /\ stack tf root st base k
 | R.Return k => stack tf root st base k
 end.
Definition wave tf root base st ctrl :=
 histories tf root st /\ higher_queue_solved root st /\ control tf root base st ctrl.
Lemma previous_fresh st owner phase : previous_live st (R.fresh_frame st owner phase).
Proof. intros target Hmem. exact Hmem. Qed.
Lemma running_fresh tf st owner phase :
 (exists upper,snapshot tf st owner upper) ->
 running tf st (R.fresh_frame st owner phase) (tf owner).
Proof. intros [upper Hsnapshot]. exists upper. split;[exact Hsnapshot |apply evaluation_initial]. Qed.
Lemma running_restart tf st fr upper :
 Replay.accumulation fr [] -> snapshot tf st (R.frame_owner fr) upper ->
 running tf st fr (tf (R.frame_owner fr)).
Proof.
 intros Hacc Hsnapshot. exists upper. split;[exact Hsnapshot |].
 exists [],[],[]. split;[apply Demand.context_initial |].
 split;[exact Hacc |]. split;[intros t v Hin;contradiction |].
 split;[intros t v Hin;contradiction |].
 split;[intros t Hin;contradiction |intros t vl vu Hin;contradiction].
Qed.
Lemma running_ret tf st fr direct :
 monotone tf -> running tf st fr (R.ConstraintSystem.Ret direct) -> completed tf st fr direct.
Proof.
 intros Hmono [upper [Hsnapshot Heval]].
 destruct (@completed_evaluation_refreshes_snapshot tf st fr direct upper
 (proj1 (Hmono _)) (proj2 (Hmono _)) Hsnapshot Heval) as [reads [effects [spawns [Hs Ha]]]].
 exists {|O.observed_direct:=direct;O.observed_reads:=reads;O.observed_sides:=effects;O.observed_spawns:=spawns|}.
 split;[reflexivity |]. split;assumption.
Qed.
Lemma histories_view tf root before after :
 R.ranking after = R.ranking before -> R.sigma after = R.sigma before ->
 (forall owner result,snapshot tf before owner result -> snapshot tf after owner result) ->
 histories tf root before -> histories tf root after.
Proof.
 intros Hr Hs Hcarry Hhistory owner Hregion [value Hlookup].
 assert (Hregion' : region root before owner).
 { unfold region,R.rank_lt,R.ranking_lt in *. now rewrite Hr in Hregion. }
 assert (Hsolved : Sem.solved before owner) by (exists value;now rewrite Hs in Hlookup).
 destruct (Hhistory owner Hregion' Hsolved) as [result Hsnapshot].
 exists result. apply Hcarry,Hsnapshot.
Qed.
Lemma previous_view before after fr :
 R.lookup_set (R.last_targets after) (R.frame_owner fr) =
 R.lookup_set (R.last_targets before) (R.frame_owner fr) ->
 previous_live before fr -> previous_live after fr.
Proof. unfold previous_live. intros -> Hlive. exact Hlive. Qed.
Lemma region_view root before after owner :
 R.ranking after = R.ranking before -> region root before owner -> region root after owner.
Proof. unfold region,R.rank_lt,R.ranking_lt. now intros ->. Qed.
Lemma stack_view tf root before after base k :
 R.ranking after = R.ranking before -> R.last_targets after = R.last_targets before ->
 stack tf root before base k -> stack tf root after base k.
Proof.
 intros Hr Ht Hstack. induction Hstack;[constructor | |].
 - constructor;[|exact IHHstack]. destruct H as [Ho Hp]. split;[eapply region_view;eassumption |exact Hp].
 - constructor.
   + destruct H as [Ho Hp]. split;[eapply region_view;eassumption |exact Hp].
   + destruct H0 as [Hacc Hprev]. split;[exact Hacc |]. eapply previous_view;[now rewrite Ht |exact Hprev].
   + exact IHHstack.
Qed.
Record state_view before after : Prop := {
 view_ranking : R.ranking after = R.ranking before;
 view_sigma : R.sigma after = R.sigma before;
 view_contributions : R.contributions after = R.contributions before;
 view_targets : R.last_targets after = R.last_targets before;
 view_cells : R.side_cells after = R.side_cells before }.
Lemma view_snapshot tf before after owner result :
 state_view before after -> snapshot tf before owner result -> snapshot tf after owner result.
Proof. intros [Hr Hs Hc Ht Hv]. eapply snapshot_view;eassumption. Qed.
Lemma wave_view tf root base before after ctrl :
 state_view before after -> (forall owner,B.queued after owner -> B.queued before owner) ->
 wave tf root base before ctrl -> wave tf root base after ctrl.
Proof.
 intros Hv Hqueue [Hhistory [Hq Hcontrol]]. destruct Hv as [Hr Hs Hc Ht Hcells].
 assert (Hsnap : forall owner result,snapshot tf before owner result -> snapshot tf after owner result)
 by (intros;eapply snapshot_view;eassumption).
 split;[eapply histories_view;eassumption |]. split.
 - eapply higher_queue_view;eassumption.
 - destruct ctrl;cbn in *;try contradiction.
   + destruct Hcontrol as [Hhigher [Hsolved Hstack]]. split.
     * unfold R.rank_lt,R.ranking_lt in *. now rewrite Hr.
     * split;[destruct Hsolved as [value Hv];exists value;now rewrite Hs |].
       eapply stack_view;eassumption.
   + destruct Hcontrol as [[Ho Hp] [[upper [Hsnapshot Heval]] [Hprev Hstack]]].
     split;[split;[eapply region_view;eassumption |exact Hp] |]. split.
     * exists upper. split;[apply Hsnap,Hsnapshot |].
       eapply evaluation_carries;[ |apply Replay.T.sigma_extends_same;exact Hs |exact Heval].
       intro target. unfold R.sigma_value. rewrite Hs. apply DL.leq_refl.
     * split;[eapply previous_view;[now rewrite Ht |exact Hprev] |eapply stack_view;eassumption].
   + destruct Hcontrol as [[Ho Hp] [[result [Hd [Hsnapshot Hacc]]] [Hpending Hstack]]].
     split;[split;[eapply region_view;eassumption |exact Hp] |]. split.
     * exists result. split;[exact Hd |]. split;[apply Hsnap,Hsnapshot |exact Hacc].
     * split;[unfold pending_live;now rewrite Ht |eapply stack_view;eassumption].
   + destruct Hcontrol as [[Ho Hp] [[result [Hd [Hsnapshot Hacc]]] Hstack]].
     split;[split;[eapply region_view;eassumption |exact Hp] |]. split.
     * exists result. split;[exact Hd |]. split;[apply Hsnap,Hsnapshot |exact Hacc].
     * eapply stack_view;eassumption.
   + destruct Hcontrol as [[Ho Hp] Hstack].
     split;[split;[eapply region_view;eassumption |exact Hp] |eapply stack_view;eassumption].
   + eapply stack_view;eassumption.
Qed.


Lemma get_state_view st fr target after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) -> Sem.solved st target ->
 state_view st after /\ R.queue after = R.queue st /\
 R.frame_owner next_fr = R.frame_owner fr /\ R.frame_phase next_fr = R.frame_phase fr /\
 R.frame_previous_targets next_fr = R.frame_previous_targets fr.
Proof.
 intros Hget [stored Hstored]. unfold R.complete_get in Hget.
 destruct (R.rank_lt st (R.frame_owner fr) target);
 inversion Hget;subst;unfold R.materialize;cbn;rewrite Hstored;
 repeat split;reflexivity.
Qed.
Lemma wave_ret tf root base st fr direct k :
 monotone tf -> wave tf root base st (R.RunRhs fr (R.ConstraintSystem.Ret direct) k) ->
 wave tf root base st (R.RunDead fr direct
 (if Features.eliminate_dead_sides then S.elements (R.frame_previous_targets fr) else []) k).
Proof.
 intros Hmono [Hhistory [Hqueue [Heligible [Hrunning [Hprev Hstack]]]]].
 split;[exact Hhistory |]. split;[exact Hqueue |].
 split;[exact Heligible |]. split;[apply running_ret;assumption |].
 split;[|exact Hstack]. intros target Hin.
 destruct Features.eliminate_dead_sides;[apply Hprev,SL.mem_spec,Hin |contradiction].
Qed.
Lemma wave_get tf root base st fr target next k after next_fr value :
 monotone tf -> wave tf root base st (R.RunRhs fr (R.ConstraintSystem.Get target next) k) ->
 R.complete_get st fr target = (after,next_fr,value) ->
 wave tf root base after (R.RunRhs next_fr (next value) k).
Proof.
 intros Hmono Hwave Hget.
 destruct Hwave as [Hhistory [Hqueue [Heligible [[upper [Hsnapshot Heval]] [Hprev Hstack]]]]].
 assert (Hsolved : Sem.solved st target).
 { eapply snapshot_get_solved;[exact Hsnapshot |].
   eapply evaluation_paths;[apply Hmono |apply Hmono |exact Hsnapshot |exact Heval]. }
 destruct (@get_state_view st fr target after next_fr value Hget Hsolved)
 as [Hv [Hq [Ho [Hp Hprevious]]]].
 assert (Hsame : wave tf root base after (R.RunRhs fr (R.ConstraintSystem.Get target next) k)).
 { eapply wave_view;[exact Hv |unfold B.queued;now rewrite Hq |].
   split;[exact Hhistory |]. split;[exact Hqueue |].
   split;[exact Heligible |]. split;[exists upper;now split |]. split;assumption. }
 destruct Hsame as [Hhistory' [Hqueue' [[Howner Hphase] [_ [Hprev' Hstack']]]]].
 split;[exact Hhistory' |]. split;[exact Hqueue' |]. split.
 - split;[now rewrite Ho |now rewrite Hp].
 - split.
   + exists upper. split;[rewrite Ho;eapply view_snapshot;eassumption |].
     eapply evaluation_get;[exact Hget |exact Hsolved |exact (proj1 (proj2 Hsnapshot)) |exact Heval].
   + split;[unfold previous_live in *;now rewrite Ho,Hprevious |exact Hstack'].
Qed.
Lemma wave_side tf root base st fr target value next k :
 wave tf root base st (R.RunRhs fr (R.ConstraintSystem.Side target value next) k) ->
 wave tf root base st (R.RunRhs (fst (R.record_side_input fr target value)) next k).
Proof.
 intros [Hhistory [Hqueue [[Howner Hphase] [[upper [Hsnapshot Heval]] [Hprev Hstack]]]]].
 split;[exact Hhistory |]. split;[exact Hqueue |]. split;[now split |]. split.
 - exists upper. split;[exact Hsnapshot |apply evaluation_side,Heval].
 - split;[exact Hprev |exact Hstack].
Qed.
Lemma running_side_ranked tf st fr target value next :
 monotone tf -> B.state_data_ranked st ->
 running tf st fr (R.ConstraintSystem.Side target value next) -> B.ranked st target.
Proof.
 intros Hmono Hdata [upper [Hsnapshot Heval]].
 pose proof (@evaluation_paths tf st fr (R.ConstraintSystem.Side target value next) upper
 (proj1 (Hmono _)) (proj2 (Hmono _)) Hsnapshot Heval) as Hpaths.
 destruct (Replay.paths_side_value Hpaths) as [bound [Hin Hle]].
 eapply live_target_ranked;[exact Hdata |].
 destruct Hsnapshot as [_ [_ [_ [_ [_ [_ [Hlive _]]]]]]]. exact (Hlive target bound Hin).
Qed.
Lemma wave_spawn tf root base st fr target next k :
 monotone tf -> wave tf root base st (R.RunRhs fr (R.ConstraintSystem.Spawn target next) k) ->
 Sem.solved st target /\ wave tf root base st (R.RunRhs fr next k).
Proof.
 intros Hmono [Hhistory [Hqueue [Heligible [[upper [Hsnapshot Heval]] [Hprev Hstack]]]]].
 destruct (@bounded_spawn_step tf st fr target next upper
 (proj1 (Hmono _)) (proj2 (Hmono _)) Hsnapshot Heval) as [Hsolved Heval'].
 split;[exact Hsolved |]. split;[exact Hhistory |]. split;[exact Hqueue |].
 split;[exact Heligible |]. split;[exists upper;now split |]. split;assumption.
Qed.
Theorem wave_rhs_step tf roots root base st fr body k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} ->
 monotone tf -> wave tf root base st (R.RunRhs fr body k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} = Some after ->
 R.sigma (R.cfg_state after) = R.sigma st /\ R.ranking (R.cfg_state after) = R.ranking st /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hreach Hmono Hwave Hstep. destruct body;
 cbn -[R.observe R.complete_get R.record_side_input] in Hstep.
 - inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |].
   apply wave_ret;assumption.
 - assert (Htarget : Sem.solved st t).
   { destruct Hwave as [_ [_ [_ [[upper [Hs He]] _]]]].
     eapply snapshot_get_solved;[exact Hs |]. eapply evaluation_paths;
     [apply Hmono |apply Hmono |exact Hs |exact He]. }
   assert (Hobserve : C.P.R.observe st t = st) by (apply observe_ranked;exact (reachable_solved_ranked Hreach Htarget)).
   rewrite Hobserve,(solved_materialized Htarget) in Hstep.
   cbn -[R.complete_get] in Hstep.
   destruct (R.complete_get st fr t) as [[next next_fr] value] eqn:Hget.
   inversion Hstep;subst. cbn.
   destruct (@get_state_view st fr t next next_fr value Hget Htarget) as [Hv _].
   split;[exact (view_sigma Hv) |]. split;[exact (view_ranking Hv) |].
   eapply wave_get;eassumption.
 - assert (Htarget : B.ranked st t).
   { eapply running_side_ranked;[exact Hmono | |exact (proj1 (proj2 (proj2 (proj2 Hwave))))].
     exact (B.configuration_state_data (Replay.reachable_ranked Hreach)). }
   rewrite (observe_ranked Htarget) in Hstep.
   inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |]. apply wave_side,Hwave.
 - destruct (@wave_spawn tf root base st fr t body k Hmono Hwave) as [Htarget Hnext].
   assert (Hobserve : C.P.R.observe st t = st) by (apply observe_ranked;exact (reachable_solved_ranked Hreach Htarget)).
   rewrite Hobserve,(solved_materialized Htarget) in Hstep.
   inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |exact Hnext].
Qed.


Lemma histories_replace tf root before after source :
 R.ranking after = R.ranking before ->
 (forall owner,owner <> source -> Sem.solved after owner -> Sem.solved before owner) ->
 (forall owner result,owner <> source -> snapshot tf before owner result -> snapshot tf after owner result) ->
 (exists result,snapshot tf after source result) ->
 histories tf root before -> histories tf root after.
Proof.
 intros Hr Hsolved Hcarry Hsource Hhistory owner Hregion Hafter.
 destruct (V.eq_dec owner source) as [->|Hneq];[exact Hsource |].
 assert (Hregion' : region root before owner).
 { unfold region,R.rank_lt,R.ranking_lt in *. now rewrite Hr in Hregion. }
 destruct (Hhistory owner Hregion' (Hsolved owner Hneq Hafter)) as [result Hsnapshot].
 exists result. apply Hcarry;assumption.
Qed.
Lemma stack_other tf root before after base k source :
 R.ranking after = R.ranking before ->
 (forall owner,R.rank_lt before owner source = true ->
 R.lookup_set (R.last_targets after) owner = R.lookup_set (R.last_targets before) owner) ->
 Replay.T.continuation_below before source k ->
 stack tf root before base k -> stack tf root after base k.
Proof.
 intros Hr Hrows Hbelow Hstack. revert source Hrows Hbelow.
 induction Hstack;intros source Hrows Hbelow;[constructor | |];destruct Hbelow as [Hlt Hbelow].
 - constructor.
   + destruct H as [Ho Hp]. split;[eapply region_view;eassumption |exact Hp].
   + apply IHHstack with (R.frame_owner fr);[|exact Hbelow].
     intros owner Howner. apply Hrows. eapply Replay.T.rank_lt_trans_true;eassumption.
 - constructor.
   + destruct H as [Ho Hp]. split;[eapply region_view;eassumption |exact Hp].
   + destruct H0 as [Hacc Hprevious]. split;[exact Hacc |].
     eapply previous_view;[apply Hrows,Hlt |exact Hprevious].
   + apply IHHstack with (R.frame_owner fr);[|exact Hbelow].
     intros owner Howner. apply Hrows. eapply Replay.T.rank_lt_trans_true;eassumption.
Qed.
Lemma publication_ranking st fr : R.ranking (publication_state st fr) = R.ranking st.
Proof.
 unfold publication_state. cbn. generalize (S.elements (R.frame_current_targets fr)) as targets.
 intro targets. revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end)) as [next changed] eqn:Hw.
 rewrite IH. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;cbn;eapply write_ranking;exact Hw.
Qed.
Lemma publication_row_other st fr owner :
 owner <> R.frame_owner fr ->
 R.lookup_set (R.last_targets (publication_state st fr)) owner =
 R.lookup_set (R.last_targets st) owner.
Proof.
 intro Hneq. unfold publication_state,R.publish_targets,R.lookup_set. cbn.
 rewrite ML.lookup_update_other by exact Hneq.
 generalize (S.elements (R.frame_current_targets fr)) as targets.
 intro targets. revert st. induction targets as [|target rest IH];intro st;
 cbn -[R.write_side_contribution C.finish_write];[reflexivity |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end)) as [next changed] eqn:Hw.
 rewrite IH. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;cbn;
 rewrite (@write_last_targets st fr target _ next _ Hw);reflexivity.

Qed.
Theorem wave_publish tf roots root base st fr direct k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct [] k|} ->
 wave tf root base st (R.RunDead fr direct [] k) ->
 wave tf root base (publication_state st fr) (R.RunCommit fr direct k).
Proof.
 intros Hreach [Hhistory [Hqueue [[Howner Hphase] [[result [Hd [Hsnapshot Hacc]]] [Hpending Hstack]]]]].
 destruct (publication_snapshot Hsnapshot Hacc) as [Hcontrib [Hagg Hsnapshot']].
 split.
 - eapply histories_replace;[apply publication_ranking | | |exists result;exact Hsnapshot' |exact Hhistory].
   + intros owner Hneq [value Hlookup]. exists value. now rewrite publication_sigma in Hlookup.
   + intros owner current Hneq Hs. eapply publication_other_snapshot;[exact Hsnapshot |exact Hacc |exact Hneq |exact Hs].
 - split.
   + exact (proj1 (@actual_publication_higher_queue tf roots root st fr direct k result Hreach Hqueue Hsnapshot Hacc)).
   + split.
     * split;[eapply region_view;[apply publication_ranking |exact Howner] |exact Hphase].
     * split;[exists result;split;[exact Hd |];split;assumption |].
       eapply stack_other;[apply publication_ranking | | |exact Hstack].
       -- intros owner Hlt. apply publication_row_other. eapply B.rank_lt_true_neq_correctness;exact Hlt.
       -- exact (proj1 (N.reachable_history Hreach)).
Qed.
Lemma write_row_view st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 R.last_targets (C.finish_write st next fr target changed) = R.last_targets st.
Proof.
 intro Hw. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;cbn;
 eapply write_last_targets;exact Hw.
Qed.
Lemma finished_write_ranking st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 R.ranking (C.finish_write st next fr target changed) = R.ranking st.
Proof.
 intro Hw. unfold C.finish_write,C.requeue_source. destruct changed,C.cell_changed;cbn;
 eapply write_ranking;exact Hw.
Qed.
Lemma finished_write_sigma st fr target input next changed :
 R.write_side_contribution st fr target input = (next,changed) ->
 R.sigma (C.finish_write st next fr target changed) = R.sigma st.
Proof.
 intro Hw. rewrite Replay.finish_sigma. eapply Replay.T.write_side_contribution_sigma;exact Hw.
Qed.
Theorem wave_dead_write tf roots root base st fr direct target rest k next changed :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} ->
 wave tf root base st (R.RunDead fr direct (target::rest) k) ->
 S.mem target (R.frame_current_targets fr) = false ->
 R.write_side_contribution st fr target D.bottom = (next,changed) ->
 wave tf root base (C.finish_write st next fr target changed) (R.RunDead fr direct rest k) /\
 R.continue_dead (C.requeue_source st next (R.frame_owner fr) target) fr direct target rest k changed =
 {|R.cfg_state:=C.finish_write st next fr target changed;R.cfg_control:=R.RunDead fr direct rest k|}.
Proof.
 intros Hreach [Hhistory [Hqueue [[Howner Hphase] [[result [Hd [Hsnapshot Hacc]]] [Hpending Hstack]]]]] Hmissing Hw.
 destruct (@dead_frame_snapshot tf st fr result target next changed Hsnapshot Hacc (Hpending target (or_introl eq_refl)) Hmissing Hw)
 as [Hcells [Hagg Hsnapshot']].
 assert (Hbottom : higher_unsolved_bottom root st)
 by (eapply dead_higher_unsolved_bottom;eassumption).
 split;[|eapply descending_dead_continuation;eassumption].
 split.
 - eapply histories_replace;[eapply finished_write_ranking;exact Hw | | | |exact Hhistory].
   + intros owner Hneq [value Hlookup]. exists value. now rewrite (finished_write_sigma Hw) in Hlookup.
   + intros owner current Hneq Hs. apply snapshot_finish. eapply other_write_snapshot;eassumption.
   + exists result. apply snapshot_finish,Hsnapshot'.
 - split.
   + eapply finish_higher_queue;[exact Hw | |exact Hqueue |exact Hbottom |exact Hagg].
     apply Demand.materialized_solved. exact (proj1 (Replay.reachable_owners_materialized Hreach)).
   + split.
     * split;[eapply region_view;[eapply finished_write_ranking;exact Hw |exact Howner] |exact Hphase].
     * split.
       -- exists result. split;[exact Hd |]. split;[apply snapshot_finish,Hsnapshot' |exact Hacc].
       -- split.
          ++ intros owner Hin. rewrite (write_row_view Hw). apply Hpending;now right.
          ++ eapply stack_view;[eapply finished_write_ranking;exact Hw |eapply write_row_view;exact Hw |exact Hstack].
Qed.


Theorem wave_dead_step tf roots root base st fr direct pending k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} ->
 wave tf root base st (R.RunDead fr direct pending k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} = Some after ->
 R.sigma (R.cfg_state after) = R.sigma st /\ R.ranking (R.cfg_state after) = R.ranking st /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hreach Hwave Hstep. destruct pending as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   split;[apply publication_sigma |]. split;[apply publication_ranking |].
   eapply wave_publish;eassumption.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets fr)) eqn:Hmem.
   + inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |].
     destruct Hwave as [Hhistory [Hqueue [Heligible [Hdone [Hpending Hstack]]]]].
     split;[exact Hhistory |]. split;[exact Hqueue |]. split;[exact Heligible |].
     split;[exact Hdone |]. split;[intros owner Hin;apply Hpending;now right |exact Hstack].
   + destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
     destruct (@wave_dead_write tf roots root base st fr direct target rest k next changed Hreach Hwave Hmem Hw)
     as [Hnext Hshape]. rewrite Hshape in Hstep. inversion Hstep;subst. cbn.
     split;[eapply finished_write_sigma;exact Hw |].
     split;[eapply finished_write_ranking;exact Hw |exact Hnext].
Qed.
Lemma clear_wave tf root base st ctrl owner :
 wave tf root base st ctrl -> wave tf root base (C.P.clear_owner st owner) ctrl.
Proof.
 intro Hwave. eapply wave_view with (before:=st);[constructor;reflexivity | |exact Hwave].
 intros target Hq. apply (proj1 (C.P.clear_owner_members st owner target)),Hq.
Qed.
Lemma queue_wave tf root base st ctrl queue :
 (forall owner,In owner queue -> B.queued st owner) ->
 wave tf root base st ctrl -> wave tf root base (R.with_queue st queue) ctrl.
Proof.
 intros Hqueue Hwave. eapply wave_view with (before:=st);[constructor;reflexivity |exact Hqueue |exact Hwave].
Qed.
Lemma materialize_solved_state st owner : Sem.solved st owner -> R.materialize st owner = st.
Proof. intros [value Hlookup]. unfold R.materialize. now rewrite Hlookup. Qed.
Theorem wave_start_step tf root base st owner k :
 wave tf root base st (R.StartEpisode owner k) ->
 wave tf root base (R.materialize (C.P.clear_owner st owner) owner)
 (R.RunRhs (R.fresh_frame (R.materialize (C.P.clear_owner st owner) owner) owner (U.initial_phase false owner)) (tf owner) k).
Proof.
 intro Hwave. pose proof (clear_wave owner Hwave) as Hclear.
 destruct Hclear as [Hhistory [Hqueue [Hhigher [Hsolved Hstack]]]].
 rewrite (materialize_solved_state Hsolved).
 split;[exact Hhistory |]. split;[exact Hqueue |]. split.
 - split;[right;exact Hhigher |discriminate].
 - split.
   + apply running_fresh. apply Hhistory;[right;exact Hhigher |exact Hsolved].
   + split;[apply previous_fresh |exact Hstack].
Qed.
Lemma wave_retry tf root base st fr direct k :
 Sem.solved st (R.frame_owner fr) ->
 wave tf root base st (R.RunCommit fr direct k) ->
 wave tf root base (R.cfg_state (C.P.retry_current tf st fr k))
 (R.cfg_control (C.P.retry_current tf st fr k)).
Proof.
 intros Hsolved Hwave.
 destruct (clear_wave (R.frame_owner fr) Hwave) as [Hhistory [Hqueue [Heligible [Hdone Hstack]]]].
 split;[exact Hhistory |]. split;[exact Hqueue |]. split;[exact Heligible |]. split.
 - apply running_fresh. apply Hhistory;[exact (proj1 Heligible) |exact Hsolved].
 - split;[apply previous_fresh |exact Hstack].
Qed.
Lemma pop_members st target rest :
 R.queue_pop (R.queue st) = Some (target,rest) ->
 B.queued st target /\ (forall owner,In owner rest -> B.queued st owner).
Proof.
 unfold R.queue_pop,B.queued. destruct (R.queue st);[discriminate |].
 intro Hpop. inversion Hpop;subst. split;[now left |intros owner Hin;now right].
Qed.
Lemma higher_from_region root st source target :
 region root st source -> R.rank_lt st source target = true -> R.rank_lt st root target = true.
Proof. intros [->|Hsource] Htarget;[exact Htarget |eapply Replay.T.rank_lt_trans_true;eassumption]. Qed.
Lemma wave_suspend tf root base st fr direct k target rest :
 C.P.pending_above st (R.frame_owner fr) = Some (target,rest) ->
 wave tf root base st (R.RunCommit fr direct k) ->
 wave tf root base (R.cfg_state (C.P.suspend_commit tf st fr k target rest))
 (R.cfg_control (C.P.suspend_commit tf st fr k target rest)).
Proof.
 intros Hpending Hwave.
 destruct (@C.P.pending_above_spec st (R.frame_owner fr) target rest Hpending) as [Hcontrolled [Hpop Hlt]].
 destruct (@pop_members st target rest Hpop) as [Htarget Hrest].
 destruct Hwave as [Hhistory [Hqueue [Heligible [Hdone Hstack]]]].
 assert (Hhigher : R.rank_lt st root target = true)
 by (eapply higher_from_region;[exact (proj1 Heligible) |exact Hlt]).
 assert (Hsolved : Sem.solved st target) by (apply Hqueue;assumption).
 assert (Hqueued : wave tf root base (R.with_queue st rest) (R.RunCommit fr direct k)).
 { apply queue_wave;[exact Hrest |].
   split;[exact Hhistory |]. split;[exact Hqueue |]. split;[exact Heligible |]. split;assumption. }
 destruct Hqueued as [Hhistory' [Hqueue' [Heligible' [_ Hstack']]]].
 split;[exact Hhistory' |]. split;[exact Hqueue' |]. split;[exact Hhigher |].
 split;[exact Hsolved |]. apply (@StackRestart tf root (R.with_queue st rest) base (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) k);
 [exact Heligible' | |exact Hstack'].
 split;[apply Replay.accumulation_fresh |intros owner Hin;exact Hin].
Qed.
Lemma ordinary_requeue_ranking before after source :
 R.ranking (R.requeue_changed_controlled_owner before after source) = R.ranking after.
Proof. unfold R.requeue_changed_controlled_owner. destruct (_ && _)%bool;reflexivity. Qed.
Theorem wave_commit_value tf roots root base st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 wave tf root base st (R.RunCommit fr direct k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 values_descend st after /\ R.ranking after = R.ranking st /\
 wave tf root base after (R.RunDrain next_fr next_k).
Proof.
 intros Hreach [Hhistory [Hqueue [[Howner Hphase] [[result [Hd [Hsnapshot Hacc]]] Hstack]]]] Hstep.
 destruct (@commit_step_shape tf st fr direct k after next_fr next_k Hstep) as [next [Hset [Hafter ->]]].
 assert (Hset' : R.set_value st fr (O.observed_direct result) = (next,next_fr)) by now rewrite Hd.
 destruct (@commit_snapshot tf st fr result next next_fr Hset' Hphase Hsnapshot) as [Hdown [Hphase' Hsnapshot']].
 assert (Hr : R.ranking after = R.ranking st)
 by (rewrite Hafter,ordinary_requeue_ranking;exact (@set_ranking st fr direct next next_fr Hset)).
 split;[rewrite Hafter;exact Hdown |]. split;[exact Hr |].
 split.
 - eapply histories_replace with (source:=R.frame_owner fr);[exact Hr | | | |exact Hhistory].
   + intros owner Hneq Hsolved. rewrite Hafter in Hsolved.
     change (Sem.solved next owner) in Hsolved.
     destruct (@B.set_value_solved_origin st fr direct next next_fr owner Hset Hsolved) as [Hs|Heq];[exact Hs |contradiction].
   + intros owner current Hneq Hs. rewrite Hafter. apply ordinary_requeue_snapshot.
     eapply other_commit_snapshot;eassumption.
   + exists result. rewrite Hafter. apply ordinary_requeue_snapshot,Hsnapshot'.
 - split;[eapply actual_commit_higher_queue;eassumption |]. split.
   + split;[rewrite (@B.set_value_frame_owner st fr direct next next_fr Hset);eapply region_view;eassumption |exact Hphase'].
   + eapply stack_view;[exact Hr | |exact Hstack].
     rewrite Hafter. change (R.last_targets next = R.last_targets st).
     exact (proj1 (@set_value_side_view st fr direct next next_fr Hset)).
Qed.
Theorem wave_commit_step tf roots root base st fr direct k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 wave tf root base st (R.RunCommit fr direct k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} = Some after ->
 values_descend st (R.cfg_state after) /\ R.ranking (R.cfg_state after) = R.ranking st /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hreach Hwave Hstep.
 pose proof Hstep as Hactual.
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current] in Hstep.
 destruct (C.P.pending_above st (R.frame_owner fr)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. split;[intros owner;apply DL.leq_refl |].
   split;[reflexivity |eapply wave_suspend;eassumption].
 - destruct (R.queue_contains (R.frame_owner fr) (R.queue st)).
   + inversion Hstep;subst. split;[intros owner;apply DL.leq_refl |].
     split;[reflexivity |]. eapply wave_retry;[eapply Replay.reachable_commit_owner_solved;exact Hreach |exact Hwave].
   + cbn -[C.P.pending_above R.set_value R.requeue_changed_controlled_owner] in Hstep.
     rewrite Hp in Hstep.
     destruct (R.set_value st fr direct) as [next next_fr] eqn:Hset.
     inversion Hstep;subst. eapply wave_commit_value;eassumption.
Qed.
Lemma reset_ranking st source : R.ranking (R.reset_registered_cells st source) = R.ranking st.
Proof. unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity. Qed.
Lemma reset_sigma st source : R.sigma (R.reset_registered_cells st source) = R.sigma st.
Proof. unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity. Qed.
Lemma reset_targets st source : R.last_targets (R.reset_registered_cells st source) = R.last_targets st.
Proof. unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity. Qed.
Lemma reset_queue st source : R.queue (R.reset_registered_cells st source) = R.queue st.
Proof. unfold R.reset_registered_cells. destruct Features.restart_side_phases;reflexivity. Qed.
Lemma wave_drain_finish tf root base st fr k :
 wave tf root base st (R.RunDrain fr k) ->
 wave tf root base (R.reset_registered_cells st (R.frame_owner fr)) (R.Return k).
Proof.
 intros [Hhistory [Hqueue [Heligible Hstack]]]. split.
 - eapply histories_view;[apply reset_ranking |apply reset_sigma | |exact Hhistory].
   intros owner result Hsnapshot. apply reset_snapshot,Hsnapshot.
 - split.
   + eapply higher_queue_view;[apply reset_ranking |apply reset_sigma | |exact Hqueue].
     unfold B.queued. now rewrite reset_queue.
   + eapply stack_view;[apply reset_ranking |apply reset_targets |exact Hstack].
Qed.
Lemma wave_drain_self tf root base st fr k rest :
 Sem.solved st (R.frame_owner fr) -> R.queue_pop (R.queue st) = Some (R.frame_owner fr,rest) ->
 wave tf root base st (R.RunDrain fr k) ->
 wave tf root base (R.with_queue st rest)
 (R.RunRhs (R.fresh_frame (R.with_queue st rest) (R.frame_owner fr) (R.frame_phase fr)) (tf (R.frame_owner fr)) k).
Proof.
 intros Hsolved Hpop Hwave.
 pose proof (queue_wave rest (proj2 (@pop_members st (R.frame_owner fr) rest Hpop)) Hwave) as Hnext.
 destruct Hnext as [Hhistory [Hqueue [Heligible Hstack]]].
 split;[exact Hhistory |]. split;[exact Hqueue |]. split;[exact Heligible |]. split.
 - apply running_fresh. apply Hhistory;[exact (proj1 Heligible) |exact Hsolved].
 - split;[apply previous_fresh |exact Hstack].
Qed.
Lemma wave_drain_above tf root base st fr k target rest :
 R.queue_pop (R.queue st) = Some (target,rest) -> R.rank_lt st (R.frame_owner fr) target = true ->
 wave tf root base st (R.RunDrain fr k) ->
 wave tf root base (R.with_queue st rest) (R.StartEpisode target (R.KDrain fr k)).
Proof.
 intros Hpop Hlt Hwave.
 destruct Hwave as [Hhistory [Hqueue [Heligible Hstack]]].
 assert (Hhigher : R.rank_lt st root target = true)
 by (eapply higher_from_region;[exact (proj1 Heligible) |exact Hlt]).
 assert (Hsolved : Sem.solved st target)
 by (apply Hqueue;[exact Hhigher |exact (proj1 (@pop_members st target rest Hpop))]).
 assert (Hnext : wave tf root base (R.with_queue st rest) (R.RunDrain fr k)).
 { apply queue_wave;[exact (proj2 (@pop_members st target rest Hpop)) |].
   split;[exact Hhistory |]. split;[exact Hqueue |]. split;assumption. }
 destruct Hnext as [Hhistory' [Hqueue' [Heligible' Hstack']]].
 split;[exact Hhistory' |]. split;[exact Hqueue' |].
 split;[exact Hhigher |]. split;[exact Hsolved |]. constructor;assumption.
Qed.
Theorem wave_drain_step tf roots root base st fr k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} ->
 wave tf root base st (R.RunDrain fr k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} = Some after ->
 R.sigma (R.cfg_state after) = R.sigma st /\ R.ranking (R.cfg_state after) = R.ranking st /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hreach Hwave Hstep.
 assert (Hsolved : Sem.solved st (R.frame_owner fr)).
 { apply Demand.materialized_solved. exact (proj1 (Replay.reachable_owners_materialized Hreach)). }
 change (R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} = Some after) in Hstep.
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame] in Hstep.
 unfold R.queue_peek,R.queue_pop in Hstep. destruct (R.queue st) as [|target rest] eqn:Hqueue.
 - inversion Hstep;subst. split;[apply reset_sigma |]. split;[apply reset_ranking |].
   apply wave_drain_finish,Hwave.
 - destruct (V.eq_dec target (R.frame_owner fr)) as [->|Hneq].
   + inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |].
     apply wave_drain_self;[exact Hsolved |unfold R.queue_pop;rewrite Hqueue;reflexivity |exact Hwave].
   + destruct (R.rank_lt st (R.frame_owner fr) target) eqn:Hlt.
     * inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |].
       apply wave_drain_above;[unfold R.queue_pop;rewrite Hqueue;reflexivity |exact Hlt |exact Hwave].
     * inversion Hstep;subst. split;[apply reset_sigma |]. split;[apply reset_ranking |].
       apply wave_drain_finish,Hwave.
Qed.
Lemma return_restart tf root base st fr k :
 histories tf root st -> higher_queue_solved root st ->
 eligible root st fr -> restart_frame st fr -> stack tf root st base k ->
 Sem.solved st (R.frame_owner fr) ->
 wave tf root base (C.P.clear_owner st (R.frame_owner fr)) (R.RunRhs fr (tf (R.frame_owner fr)) k).
Proof.
 intros Hhistory Hqueue Heligible [Hacc Hprevious] Hstack Hsolved.
 apply clear_wave. split;[exact Hhistory |]. split;[exact Hqueue |]. split;[exact Heligible |]. split.
 - destruct (Hhistory (R.frame_owner fr) (proj1 Heligible) Hsolved) as [upper Hsnapshot].
   eapply running_restart;eassumption.
 - split;assumption.
Qed.
Lemma wave_resume_suspend tf root base st fr k target rest :
 histories tf root st -> higher_queue_solved root st ->
 eligible root st fr -> stack tf root st base k ->
 C.P.pending_above st (R.frame_owner fr)=Some (target,rest) ->
 wave tf root base (R.cfg_state (C.P.suspend_commit tf st fr k target rest))
 (R.cfg_control (C.P.suspend_commit tf st fr k target rest)).
Proof.
 intros Hhistory Hqueue Heligible Hstack Hp.
 destruct (@C.P.pending_above_spec st (R.frame_owner fr) target rest Hp) as [_ [Hpop Hlt]].
 destruct (@pop_members st target rest Hpop) as [Htarget Hrest].
 assert (Hhigher : R.rank_lt st root target=true)
 by (eapply higher_from_region;[exact (proj1 Heligible) |exact Hlt]).
 assert (Hsolved : Sem.solved st target) by (apply Hqueue;assumption).
 assert (Hqueued : wave tf root base (R.with_queue st rest) (R.RunDrain fr k)).
 { apply queue_wave;[exact Hrest |].
   split;[exact Hhistory |]. split;[exact Hqueue |]. split;assumption. }
 destruct Hqueued as [Hhistory' [Hqueue' [Heligible' Hstack']]].
 split;[exact Hhistory' |]. split;[exact Hqueue' |]. split;[exact Hhigher |].
 split;[exact Hsolved |].
 apply (@StackRestart tf root (R.with_queue st rest) base
 (R.fresh_frame st (R.frame_owner fr) (R.frame_phase fr)) k);
 [exact Heligible' | |exact Hstack'].
 split;[apply Replay.accumulation_fresh |intros owner Hin;exact Hin].
Qed.
Theorem wave_return_step tf roots root base st k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.Return k|} ->
 k <> base -> wave tf root base st (R.Return k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|} = Some after ->
 R.sigma (R.cfg_state after) = R.sigma st /\ R.ranking (R.cfg_state after) = R.ranking st /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 intros Hreach Hneq [Hhistory [Hqueue Hstack]] Hstep.
 destruct Hstack as [|fr rest Heligible Hstack|fr rest Heligible Hrestart Hstack];[contradiction | |].
 - cbn in Hstep. inversion Hstep;subst. split;[reflexivity |]. split;[reflexivity |].
   split;[exact Hhistory |]. split;[exact Hqueue |]. split;assumption.
 - destruct (C.P.pending_above st (R.frame_owner fr)) as [[target restq]|] eqn:Hp.
   + rewrite (@N.resume_higher tf st fr (tf (R.frame_owner fr)) rest target restq Hp) in Hstep. inversion Hstep;subst.
     split;[reflexivity |]. split;[reflexivity |].
     eapply wave_resume_suspend;eassumption.
   + rewrite (@N.resume_ready tf st fr (tf (R.frame_owner fr)) rest Hp) in Hstep.
     cbn -[C.P.clear_owner] in Hstep. inversion Hstep;subst.
     split;[reflexivity |]. split;[reflexivity |].
     eapply return_restart;[exact Hhistory |exact Hqueue |exact Heligible |exact Hrestart |exact Hstack |].
     apply Demand.materialized_solved. exact (proj1 (Replay.reachable_owners_materialized Hreach)).
Qed.
Theorem wave_step tf roots root base before after :
 N.steps tf (R.initial_config roots) before ->
 monotone tf -> wave tf root base (R.cfg_state before) (R.cfg_control before) ->
 R.cfg_control before <> R.Return base -> N.next_config tf before = Some after ->
 values_descend (R.cfg_state before) (R.cfg_state after) /\
 R.ranking (R.cfg_state after) = R.ranking (R.cfg_state before) /\
 wave tf root base (R.cfg_state after) (R.cfg_control after).
Proof.
 destruct before as [st ctrl]. intros Hreach Hmono Hwave Hnotbase Hstep.
 destruct ctrl;try solve [destruct Hwave as [_ [_ Hfalse]];contradiction].
 - change (Some {|R.cfg_state:=R.materialize (C.P.clear_owner st t) t;
   R.cfg_control:=R.RunRhs (R.fresh_frame (R.materialize (C.P.clear_owner st t) t) t (U.initial_phase false t)) (tf t) c|} = Some after) in Hstep.
   inversion Hstep;subst. cbn. split.
   + assert (Hs : Sem.solved (C.P.clear_owner st t) t) by exact (proj1 (proj2 (proj2 (proj2 Hwave)))).
     rewrite (materialize_solved_state Hs). intro owner. apply DL.leq_refl.
   + split;[unfold R.materialize;destruct M.lookup;reflexivity |apply wave_start_step,Hwave].
 - destruct (@wave_rhs_step tf roots root base st f r c after Hreach Hmono Hwave Hstep) as [Hs [Hr Hw]].
   split;[intro owner;unfold R.sigma_value;rewrite Hs;apply DL.leq_refl |now split].
 - destruct (@wave_dead_step tf roots root base st f t l c after Hreach Hwave Hstep) as [Hs [Hr Hw]].
   split;[intro owner;unfold R.sigma_value;rewrite Hs;apply DL.leq_refl |now split].
 - eapply wave_commit_step;eassumption.
 - destruct (@wave_drain_step tf roots root base st f c after Hreach Hwave Hstep) as [Hs [Hr Hw]].
   split;[intro owner;unfold R.sigma_value;rewrite Hs;apply DL.leq_refl |now split].
 - assert (Hneq : c <> base) by (intro Heq;apply Hnotbase;cbn;now rewrite Heq).
   destruct (@wave_return_step tf roots root base st c after Hreach Hneq Hwave Hstep) as [Hs [Hr Hw]].
   split;[intro owner;unfold R.sigma_value;rewrite Hs;apply DL.leq_refl |now split].
Qed.


Fixpoint continuation_phases (P : U.phase -> Prop) k :=
 match k with
 | R.KLoop | R.KSeedLoop _ => True
 | R.KAfterGet fr _ _ rest | R.KAfterSide fr _ rest | R.KAfterSpawn fr _ rest
 | R.KDead fr _ _ rest | R.KDrain fr rest => P (R.frame_phase fr) /\ continuation_phases P rest
 end.
Definition control_phases (P : U.phase -> Prop) ctrl :=
 match ctrl with
 | R.RunLoop | R.RunSeeds _ | R.RunSeedLoop _ => True
 | R.StartEpisode _ k | R.Return k => continuation_phases P k
 | R.RunRhs fr _ k | R.RunDead fr _ _ k | R.RunCommit fr _ k | R.RunDrain fr k =>
 P (R.frame_phase fr) /\ continuation_phases P k
 end.
Definition commit_phase (P : U.phase -> Prop) before after :=
 match R.cfg_control before,R.cfg_control after with
 | R.RunCommit _ _ _,R.RunDrain fr _ => P (R.frame_phase fr)
 | _,_ => True
 end.
Lemma get_phase st fr target after next_fr value :
 R.complete_get st fr target = (after,next_fr,value) -> R.frame_phase next_fr = R.frame_phase fr.
Proof. unfold R.complete_get. intro Hget. inversion Hget;reflexivity. Qed.
Lemma base_rhs_phases P tf st fr body k after :
 control_phases P (R.RunRhs fr body k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr body k|} = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 intros [Hp Hk] Hstep. destruct body;cbn -[R.observe R.complete_get R.record_side_input
 R.write_side_contribution R.continue_side] in Hstep.
 - inversion Hstep;subst. now split.
 - destruct (_ && _)%bool.
   + inversion Hstep;subst. now split.
   + destruct (R.complete_get (if R.is_materialized (R.observe st t) t then R.observe st t else R.enqueue (R.observe st t) t) fr t)
     as [[next next_fr] value] eqn:Hg.
     inversion Hstep;subst. split;[now rewrite (get_phase Hg) |exact Hk].
 - destruct (R.record_side_input fr t t0) as [next_fr input] eqn:Hrecord.
   destruct (R.write_side_contribution (R.observe st t) next_fr t input) as [next changed] eqn:Hw.
   inversion Hstep;subst. unfold R.record_side_input in Hrecord. inversion Hrecord;subst.
   unfold R.continue_side. destruct changed;[destruct (_ && _)%bool |];now split.
 - destruct (R.is_materialized (R.observe st t) t);[|destruct (R.rank_lt (R.observe st t) (R.frame_owner fr) t)];
   inversion Hstep;subst;now split.
Qed.
Lemma base_dead_phases P tf st fr direct pending k after :
 control_phases P (R.RunDead fr direct pending k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct pending k|} = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 intros [Hp Hk] Hstep. destruct pending as [|target rest];
 cbn -[R.write_side_contribution R.continue_dead] in Hstep.
 - inversion Hstep;subst. now split.
 - destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;now split |].
   destruct (R.write_side_contribution st fr target D.bottom) as [next changed].
   inversion Hstep;subst. unfold R.continue_dead.
   destruct changed;[destruct (_ && _)%bool |];now split.
Qed.
Lemma base_drain_phases P tf st fr k after :
 control_phases P (R.RunDrain fr k) ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|} = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 intros [Hp Hk] Hstep.
 cbn -[R.queue_peek R.queue_pop R.reset_registered_cells R.fresh_frame] in Hstep.
 destruct (R.queue_peek (R.queue st)) as [target|];[|inversion Hstep;subst;exact Hk].
 destruct (V.eq_dec target (R.frame_owner fr)).
 - destruct (R.queue_pop (R.queue st)) as [[popped rest]|];[|discriminate].
   inversion Hstep;subst. now split.
 - destruct (R.rank_lt st (R.frame_owner fr) target).
   + destruct (R.queue_pop (R.queue st)) as [[popped rest]|];[|discriminate].
     inversion Hstep;subst. now split.
   + inversion Hstep;subst. exact Hk.
Qed.
Lemma base_return_phases P tf st k after :
 continuation_phases P k ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|} = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 intros Hk Hstep. destruct k;cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;exact Hk].
Qed.
Lemma base_phases P tf before after :
 P U.BoxW -> control_phases P (R.cfg_control before) ->
 commit_phase P before after -> R.next_config tf before = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 destruct before as [st ctrl]. intros Hinitial Hp Hcommit Hstep. destruct ctrl.
 - cbn -[R.queue_pop] in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];[|discriminate].
   inversion Hstep;subst. exact I.
 - destruct l;cbn -[R.observe] in Hstep;[inversion Hstep;subst;exact I |].
   destruct (R.is_materialized (R.observe st t) t);inversion Hstep;subst;exact I.
 - cbn -[R.queue_pop] in Hstep. destruct (R.queue_pop (R.queue st)) as [[owner rest]|];
   inversion Hstep;subst;exact I.
 - cbn in Hstep. inversion Hstep;subst. now split.
 - eapply base_rhs_phases;eassumption.
 - eapply base_dead_phases;eassumption.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr]. inversion Hstep;subst.
   split;[exact Hcommit |exact (proj2 Hp)].
 - eapply base_drain_phases;eassumption.
 - exact (@base_return_phases P tf st c after Hp Hstep).
Qed.
Lemma precommit_phases P tf before after :
 P U.BoxW -> control_phases P (R.cfg_control before) ->
 commit_phase P before after -> C.P.next_config tf before = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 destruct before as [st ctrl]. intros Hinitial Hp Hcommit Hstep. destruct ctrl;
 cbn -[R.next_config C.P.pending_above C.P.suspend_commit] in Hstep;
 try solve [eapply base_phases;eassumption].
 destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
 - inversion Hstep;subst. exact Hp.
 - eapply base_phases;eassumption.
Qed.
Lemma batched_phases P tf before after :
 P U.BoxW -> control_phases P (R.cfg_control before) ->
 commit_phase P before after -> C.P.next_batched tf before = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 destruct before as [st ctrl]. intros Hinitial Hp Hcommit Hstep. destruct ctrl;
 cbn -[C.P.next_config R.observe R.record_side_input C.P.publish_accumulated R.publish_targets] in Hstep;
 try solve [eapply precommit_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep]].
 - destruct r;try solve [eapply precommit_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep]].
   inversion Hstep;subst. exact Hp.
 - destruct l;[|eapply precommit_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep]].
   inversion Hstep;subst. exact Hp.
Qed.
Lemma fresh_phases P tf before after :
 P U.BoxW -> control_phases P (R.cfg_control before) ->
 commit_phase P before after -> C.P.next_fresh tf before = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 destruct before as [st ctrl]. intros Hinitial Hp Hcommit Hstep. destruct ctrl;
 cbn -[C.P.next_batched C.P.pending_above C.P.suspend_commit C.P.retry_current C.P.clear_owner] in Hstep;
 try solve [eapply batched_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep]].
 - eapply batched_phases;[ | | |exact Hstep];[exact Hinitial |exact Hp |exact I].
 - destruct (C.P.pending_above st (R.frame_owner f)) as [[target rest]|].
   + inversion Hstep;subst. exact Hp.
   + destruct (R.queue_contains (R.frame_owner f) (R.queue st)).
     * inversion Hstep;subst. exact Hp.
     * eapply batched_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep].
 - destruct c;try solve [eapply batched_phases;[ | | |exact Hstep];[exact Hinitial |exact Hp |exact I]].
Qed.
Lemma next_phases P tf before after :
 P U.BoxW -> control_phases P (R.cfg_control before) ->
 commit_phase P before after -> N.next_config tf before = Some after ->
 control_phases P (R.cfg_control after).
Proof.
 intros Hinitial Hp Hcommit Hstep. destruct (@Replay.Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp0 ->]]]]]]]]].
 2: { exact Hp. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;
 try solve [eapply fresh_phases;[exact Hinitial |exact Hp |exact Hcommit |exact Hstep]].
 destruct l as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst. exact Hp.
 - cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
   destruct (S.mem target (R.frame_current_targets f));[inversion Hstep;subst;exact Hp |].
   destruct (R.write_side_contribution st f target D.bottom) as [next changed].
   inversion Hstep;subst. unfold R.continue_dead.
   destruct changed;[destruct (_ && _)%bool |];exact Hp.
Qed.


Lemma boxw_set_phase st fr direct next next_fr :
 R.set_value st fr direct = (next,next_fr) -> R.frame_phase fr = U.BoxW ->
 R.frame_phase next_fr = U.BoxW \/ R.frame_phase next_fr = U.BoxN.
Proof.
 intros Hset Hphase. unfold R.set_value in Hset.
 set (candidate:=D.join direct (R.aggregate st (R.frame_owner fr))) in *.
 set (old:=R.sigma_value st (R.frame_owner fr)) in *.
 destruct (R.equivalent candidate old).
 - inversion Hset;subst. now left.
 - destruct (S.mem (R.frame_owner fr) (R.controlled st)).
   + rewrite Hphase in Hset. cbn -[D.leq R.sigma_value] in Hset.
     destruct (D.leq candidate old);
     cbn -[R.equivalent WN.widen WN.narrow] in Hset;
     destruct R.equivalent;inversion Hset;subst;[now right |now right |now left |now left].
   + cbn in Hset. destruct (R.equivalent candidate old);inversion Hset;subst;left;exact Hphase.
Qed.
Theorem boxn_entry_wave tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 R.frame_phase fr = U.BoxW -> R.frame_phase next_fr = U.BoxN -> monotone tf ->
 wave tf (R.frame_owner fr) next_k after (R.RunDrain next_fr next_k).
Proof.
 intros Hreach Hstep Hphase Hnext Hmono.
 destruct (@boxn_entry_state tf roots st fr direct k after next_fr next_k Hreach Hstep Hphase Hnext Hmono)
 as [Hdown [Hsolved [Hsnapshot [Hhigher Hqueue]]]].
 destruct (@commit_step_shape tf st fr direct k after next_fr next_k Hstep) as [next [Hset _]].
 split.
 - intros owner [->|Hgt] Hs;[exact Hsnapshot |apply Hhigher;assumption].
 - split;[exact Hqueue |]. split.
   + split;[left;apply (@B.set_value_frame_owner st fr direct next next_fr Hset) |rewrite Hnext;discriminate].
   + constructor.
Qed.
Definition invariant tf c :=
 control_phases (fun phase=>phase=U.BoxW) (R.cfg_control c) \/
 exists root base,continuation_phases (fun phase=>phase=U.BoxW) base /\
 wave tf root base (R.cfg_state c) (R.cfg_control c).
Lemma boxw_commit_invariant tf roots st fr direct k after :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 monotone tf -> control_phases (fun phase=>phase=U.BoxW) (R.RunCommit fr direct k) ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} = Some after ->
 invariant tf after.
Proof.
 intros Hreach Hmono Hphases Hstep. destruct after as [after ctrl]. destruct ctrl;
 try solve [left;eapply next_phases;[ | | |exact Hstep];[exact eq_refl |exact Hphases |exact I]].
 destruct Hphases as [Hphase Hk].
 destruct (@commit_step_shape tf st fr direct k after f c Hstep) as [next [Hset [Hafter Hrest]]].
 destruct (@boxw_set_phase st fr direct next f Hset Hphase) as [Hw|Hn].
 - left. cbn. split;[exact Hw |now rewrite Hrest].
 - right. exists (R.frame_owner fr),c. split;[now rewrite Hrest |].
   eapply boxn_entry_wave;eassumption.
Qed.
Lemma boxw_next_invariant tf roots before after :
 N.steps tf (R.initial_config roots) before -> monotone tf ->
 control_phases (fun phase=>phase=U.BoxW) (R.cfg_control before) ->
 N.next_config tf before = Some after -> invariant tf after.
Proof.
 destruct before as [st ctrl]. intros Hreach Hmono Hphases Hstep. destruct ctrl;
 try solve [left;eapply next_phases;[ | | |exact Hstep];[exact eq_refl |exact Hphases |exact I]].
 eapply boxw_commit_invariant;eassumption.
Qed.

Lemma continuation_boxw_dec k :
 {continuation_phases (fun phase=>phase=U.BoxW) k} +
 {~ continuation_phases (fun phase=>phase=U.BoxW) k}.
Proof.
 induction k;cbn;try solve [left;exact I].
 all: destruct (R.frame_phase f);destruct IHk as [Hyes|Hno];
 try solve [left;now split |right;intros [Hp Hk];discriminate |right;intros [_ Hk];contradiction].
Qed.
Lemma control_boxw_dec ctrl :
 {control_phases (fun phase=>phase=U.BoxW) ctrl} +
 {~ control_phases (fun phase=>phase=U.BoxW) ctrl}.
Proof.
 destruct ctrl;cbn;try solve [left;exact I |apply continuation_boxw_dec].
 all: destruct (R.frame_phase f);destruct (continuation_boxw_dec c) as [Hyes|Hno];
 try solve [left;now split |right;intros [Hp Hk];discriminate |right;intros [_ Hk];contradiction].
Qed.
Theorem invariant_step tf roots before after :
 N.steps tf (R.initial_config roots) before -> monotone tf -> invariant tf before ->
 N.next_config tf before = Some after -> invariant tf after.
Proof.
 intros Hreach Hmono [Hboxw|[root [base [Hbase Hwave]]]] Hstep.
 - eapply boxw_next_invariant;eassumption.
 - destruct (control_boxw_dec (R.cfg_control before)) as [Hboxw|Hnot].
   + eapply boxw_next_invariant;eassumption.
   + right. exists root,base. split;[exact Hbase |].
     assert (Hneq : R.cfg_control before <> R.Return base).
     { intro Heq. apply Hnot. rewrite Heq. exact Hbase. }
     exact (proj2 (proj2 (@wave_step tf roots root base before after Hreach Hmono Hwave Hneq Hstep))).
Qed.


Lemma steps_invariant tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 monotone tf -> invariant tf first -> invariant tf last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hmono Hinv;[exact Hinv |].
 apply IHHsteps.
 - eapply Replay.steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - exact Hmono.
 - eapply invariant_step;eassumption.
Qed.
Theorem reachable_invariant tf roots c :
 N.steps tf (R.initial_config roots) c -> monotone tf -> invariant tf c.
Proof.
 intros Hreach Hmono. eapply steps_invariant;[exact Hreach |constructor |exact Hmono |].
 left. exact I.
Qed.
Lemma continuation_phases_map P Q k :
 (forall phase,P phase -> Q phase) -> continuation_phases P k -> continuation_phases Q k.
Proof.
 intros Hmap. induction k;cbn;intro Hphases;try exact I.
 all: destruct Hphases as [Hp Hk];split;[apply Hmap,Hp |apply IHk,Hk].
Qed.
Lemma control_phases_map P Q ctrl :
 (forall phase,P phase -> Q phase) -> control_phases P ctrl -> control_phases Q ctrl.
Proof.
 intros Hmap Hp. destruct ctrl;cbn in *;try exact I;
 try solve [eapply continuation_phases_map;eassumption].
 all: destruct Hp as [Hphase Hk];split;[apply Hmap,Hphase |eapply continuation_phases_map;eassumption].
Qed.
Lemma stack_no_fallback tf root st base k :
 continuation_phases (fun phase=>phase<>U.Widen) base ->
 stack tf root st base k -> continuation_phases (fun phase=>phase<>U.Widen) k.
Proof.
 intros Hbase Hstack. induction Hstack;[exact Hbase | |].
 all: split;[exact (proj2 H) |exact IHHstack].
Qed.
Lemma wave_no_fallback tf root base st ctrl :
 continuation_phases (fun phase=>phase=U.BoxW) base -> wave tf root base st ctrl ->
 control_phases (fun phase=>phase<>U.Widen) ctrl.
Proof.
 intros Hbase [_ [_ Hcontrol]].
 assert (Hbase' : continuation_phases (fun phase=>phase<>U.Widen) base).
 { eapply continuation_phases_map;[ |exact Hbase]. intros phase ->. discriminate. }
 destruct ctrl;cbn in *;try contradiction.
 - destruct Hcontrol as [_ [_ Hstack]]. eapply stack_no_fallback;eassumption.
 - destruct Hcontrol as [Heligible [_ [_ Hstack]]]. split;[exact (proj2 Heligible) |eapply stack_no_fallback;eassumption].
 - destruct Hcontrol as [Heligible [_ [_ Hstack]]]. split;[exact (proj2 Heligible) |eapply stack_no_fallback;eassumption].
 - destruct Hcontrol as [Heligible [_ Hstack]]. split;[exact (proj2 Heligible) |eapply stack_no_fallback;eassumption].
 - destruct Hcontrol as [Heligible Hstack]. split;[exact (proj2 Heligible) |eapply stack_no_fallback;eassumption].
 - eapply stack_no_fallback;eassumption.
Qed.
Theorem reachable_no_fallback tf roots c :
 N.steps tf (R.initial_config roots) c -> monotone tf ->
 control_phases (fun phase=>phase<>U.Widen) (R.cfg_control c).
Proof.
 intros Hreach Hmono.
 destruct (reachable_invariant Hreach Hmono) as [Hboxw|[root [base [Hbase Hwave]]]].
 - eapply control_phases_map;[ |exact Hboxw]. intros phase ->. discriminate.
 - eapply wave_no_fallback;eassumption.
Qed.
Theorem reachable_narrowing_input_bounded tf roots st fr direct k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 monotone tf -> R.frame_phase fr = U.BoxN ->
 D.leq (D.join direct (R.aggregate st (R.frame_owner fr))) (R.sigma_value st (R.frame_owner fr)) = true.
Proof.
 intros Hreach Hmono Hphase.
 destruct (reachable_invariant Hreach Hmono) as [[Hboxw _]|[root [base [Hbase [_ [_ [_ [[result [Hd [Hsnapshot Hacc]]] Hstack]]]]]]]].
 - rewrite Hphase in Hboxw. discriminate.
 - rewrite <- Hd. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsnapshot))))).
Qed.
Corollary reachable_commit_admissible tf roots st fr direct k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 monotone tf ->
 U.admissible_input (R.frame_phase fr) (R.sigma_value st (R.frame_owner fr))
 (D.join direct (R.aggregate st (R.frame_owner fr))).
Proof.
 intros Hreach Hmono.
 pose proof (proj1 (reachable_no_fallback Hreach Hmono)) as Hsafe.
 destruct (R.frame_phase fr) eqn:Hphase.
 - intro H;discriminate.
 - intro H. eapply reachable_narrowing_input_bounded;eassumption.
 - contradiction.
Qed.
End Episode.

(** Keep final-summary proofs in the same collection instance. Reapplying the
    descent functor here needlessly expands the complete replay proof graph. *)
Module E := Episode.
Module P := C.P.
Module F.
Module Total := B.
Import Total.
Definition narrowing_input
    (st : R.state) (owner : V.t) (direct : D.t) : D.t :=
    D.join direct (R.aggregate st owner).

  Definition narrowing_fixed_at
    (st : R.state) (owner : V.t) (direct : D.t) : Prop :=
    UL.equivalent
      (WN.narrow (R.sigma_value st owner)
        (narrowing_input st owner direct))
      (R.sigma_value st owner).

  Definition fixed_summary
    (tf : R.ConstraintSystem.system) (st : R.state) (owner : V.t) : Prop :=
    Sem.solved st owner /\
    exists direct reads effects,
      Total.rhs_trace (tf owner) direct reads effects /\
      Total.guarded_reads st owner reads /\
      Total.recorded_effects st owner effects /\
      D.leq (narrowing_input st owner direct)
        (R.sigma_value st owner) = true /\
      narrowing_fixed_at st owner direct.

  Definition unknown_narrowing_fixed_point
    (tf : R.ConstraintSystem.system) (st : R.state) (owner : V.t) : Prop :=
    forall direct reads effects,
      Sem.rhs_eval st (tf owner) direct reads effects ->
      narrowing_fixed_at st owner direct.

  Definition fixed_active := Total.control_active.

  Definition control_update_safe (control : R.control) : Prop :=
    match control with
    | R.RunCommit fr _ _ => U.avoids_fallback (R.frame_phase fr)
    | _ => True
    end.

  Lemma fixed_summary_is_summary_valid :
    forall tf st owner,
      fixed_summary tf st owner ->
      Total.summary_valid tf st owner.
  Proof.
    intros tf st owner
      [Hsolved [direct [reads [effects
        [Htrace [Hreads [Heffects [Hinput Hfixed]]]]]]]].
    split; [exact Hsolved |].
    exists direct, reads, effects.
    split; [exact Htrace |].
    split; [exact Hreads |].
    split; [exact Heffects |].
    eapply DL.leq_trans.
    - apply DL.join_upper_left.
    - exact Hinput.
  Qed.

  Lemma quiescent_fixed_summary :
    forall tf st owner,
      Sem.quiescent st ->
      fixed_summary tf st owner ->
      unknown_narrowing_fixed_point tf st owner.
  Proof.
    intros tf st owner Hquiet
      [Hsolved [direct [reads [effects
        [Htrace [Hreads [Heffects [Hinput Hfixed]]]]]]]]
      direct' reads' effects' Heval.
    pose proof (Total.rhs_trace_replay Htrace
      (@Total.guarded_reads_agree st owner reads Hquiet Hreads)) as Hreplay.
    destruct (Total.rhs_eval_deterministic Hreplay Heval)
      as [-> [-> ->]].
    exact Hfixed.
  Qed.

  Lemma equivalent_bool_true :
    forall left right,
      R.equivalent left right = true ->
      UL.equivalent left right.
  Proof.
    intros left right Heq.
    unfold R.equivalent in Heq.
    now apply Bool.andb_true_iff in Heq.
  Qed.

  Lemma narrow_equivalent_input :
    forall old input,
      UL.equivalent input old ->
      UL.equivalent (WN.narrow old input) old.
  Proof.
    intros old input [Hinput_old Hold_input].
    split.
    - now apply WNL.narrow_upper.
    - eapply DL.leq_trans.
      + exact Hold_input.
      + now apply WNL.narrow_lower.
  Qed.

  Lemma domain_equivalent_refl :
    forall value, UL.equivalent value value.
  Proof. intro value. split; apply DL.leq_refl. Qed.

  Lemma domain_equivalent_sym :
    forall left right,
      UL.equivalent left right ->
      UL.equivalent right left.
  Proof. intros left right [Hlr Hrl]. now split. Qed.

  Lemma domain_equivalent_trans :
    forall first middle last,
      UL.equivalent first middle ->
      UL.equivalent middle last ->
      UL.equivalent first last.
  Proof.
    intros first middle last [Hfm Hmf] [Hml Hlm]. split;
      eapply DL.leq_trans; eassumption.
  Qed.

  Lemma join_right_extensional :
    forall direct left right,
      UL.equivalent left right ->
      UL.equivalent (D.join direct left) (D.join direct right).
  Proof.
    intros direct left right [Hlr Hrl]. split.
    - apply DL.join_least.
      + apply DL.join_upper_left.
      + eapply DL.leq_trans; [exact Hlr |apply DL.join_upper_right].
    - apply DL.join_least.
      + apply DL.join_upper_left.
      + eapply DL.leq_trans; [exact Hrl |apply DL.join_upper_right].
  Qed.

  Lemma narrow_extensional :
    forall (owner : V.t) old input input',
      UL.equivalent input input' ->
      D.leq input old = true ->
      D.leq input' old = true ->
      UL.equivalent
        (WN.narrow old input) (WN.narrow old input').
  Proof.
    intros owner old input input' Hinputs Hle Hle'.
    pose proof (@UL.update_extensional false owner U.BoxN
      old old input input'
      (domain_equivalent_refl old) Hinputs) as Hupdate.
    unfold U.update in Hupdate.
    now rewrite Hle, Hle' in Hupdate.
  Qed.

  Lemma safe_update_stutter_is_narrow_stutter :
    forall owner phase old input,
      U.avoids_fallback phase ->
      UL.equivalent
        (snd (U.update false owner phase old input)) old ->
      UL.equivalent (WN.narrow old input) old.
  Proof.
    intros owner phase old input Hsafe Hstutter.
    destruct phase.
    - unfold U.update in Hstutter.
      destruct (D.leq input old) eqn:Hle.
      + exact Hstutter.
      + exfalso.
        destruct Hstutter as [Hresult_old _].
        cbn in Hresult_old.
        pose proof (WNL.widen_upper_input old input) as Hinput_result.
        rewrite <- Bool.not_true_iff_false in Hle.
        apply Hle.
        eapply DL.leq_trans; eassumption.
    - unfold U.update in Hstutter.
      destruct (D.leq input old) eqn:Hle.
      + exact Hstutter.
      + exfalso.
        destruct Hstutter as [Hresult_old _].
        cbn in Hresult_old.
        pose proof (WNL.widen_upper_input old input) as Hinput_result.
        rewrite <- Bool.not_true_iff_false in Hle.
        apply Hle.
        eapply DL.leq_trans; eassumption.
    - exfalso. apply Hsafe. reflexivity.
  Qed.


  Lemma set_value_narrow_fixed_or_queued :
    forall st fr direct st' fr',
      U.avoids_fallback (R.frame_phase fr) ->
      R.set_value st fr direct = (st', fr') ->
      Total.queued
        (R.requeue_changed_controlled_owner st st' (R.frame_owner fr))
        (R.frame_owner fr) \/
      narrowing_fixed_at st' (R.frame_owner fr) direct.
  Proof.
    intros st fr direct st' fr' Hsafe Hset.
    unfold R.set_value in Hset.
    set (owner := R.frame_owner fr) in *.
    set (candidate := D.join direct (R.aggregate st owner)) in *.
    set (old := R.sigma_value st owner) in *.
    destruct (R.equivalent candidate old) eqn:Hcandidate.
    - inversion Hset; subst. right.
      unfold narrowing_fixed_at, narrowing_input. fold owner candidate old.
      now apply narrow_equivalent_input, equivalent_bool_true.
    - destruct (S.mem owner (R.controlled st)) eqn:Hcontrolled.
      + destruct (U.update false owner (R.frame_phase fr) old candidate)
          as [next_phase value] eqn:Hupdate.
        cbn in Hset. destruct (R.equivalent value old) eqn:Hvalue.
        * inversion Hset; subst. right.
          unfold narrowing_fixed_at, narrowing_input. fold owner candidate old.
          eapply safe_update_stutter_is_narrow_stutter; [exact Hsafe |].
          rewrite Hupdate. cbn. now apply equivalent_bool_true.
        * inversion Hset; subst. left. apply Total.requeue_enabled.
          -- exact Hcontrolled.
          -- unfold R.sigma_value. cbn. rewrite ML.lookup_update_same.
             exact Hvalue.
      + cbn in Hset. rewrite Hcandidate in Hset.
        inversion Hset; subst. right.
        unfold narrowing_fixed_at, narrowing_input, R.aggregate; cbn.
        fold candidate. unfold R.sigma_value. cbn.
        rewrite ML.lookup_update_same.
        apply narrow_equivalent_input. split; apply DL.leq_refl.
  Qed.

  Lemma completed_witness_set_value_fixed_or_queued :
    forall tf st fr direct st' fr',
      U.avoids_fallback (R.frame_phase fr) ->
      Total.completed_witness tf st fr direct ->
      R.set_value st fr direct = (st', fr') ->
      Total.queued
        (R.requeue_changed_controlled_owner st st' (R.frame_owner fr))
        (R.frame_owner fr) \/
      fixed_summary tf st' (R.frame_owner fr).
  Proof.
    intros tf st fr direct st' fr' Hsafe
      [Hsolved [reads [effects
        [Htrace [Hreads [Heffects Hframe]]]]]] Hset.
    destruct (@set_value_narrow_fixed_or_queued
      st fr direct st' fr' Hsafe Hset)
      as [Hqueued | Hfixed]; [now left |right].
    split.
    - eapply Total.set_value_solved; eauto.
    - exists direct, reads, effects.
      split; [exact Htrace |].
      split.
      + eapply Total.guarded_reads_set_value; eauto.
      + split.
        * eapply Total.recorded_effects_set_value; eauto.
        * split.
          -- unfold narrowing_input.
             unfold R.aggregate.
             rewrite (@Total.set_value_contributions
               st fr direct st' fr' Hset).
             exact (@Total.set_value_candidate_sound
               st fr direct st' fr' Hset).
          -- exact Hfixed.
  Qed.

  Lemma fixed_summary_transport :
    forall tf before after owner,
      (Sem.solved before owner -> Sem.solved after owner) ->
      (forall reads,
        Total.guarded_reads before owner reads ->
        Total.guarded_reads after owner reads) ->
      R.sigma_value after owner = R.sigma_value before owner ->
      R.contributions after = R.contributions before ->
      fixed_summary tf before owner ->
      fixed_summary tf after owner.
  Proof.
    intros tf before after owner Hsolved_preserved Hreads_preserved
      Hsigma Hcontributions
      [Hsolved [direct [reads [effects
        [Htrace [Hreads [Heffects [Hinput Hfixed]]]]]]]].
    split; [now apply Hsolved_preserved |].
    exists direct, reads, effects.
    split; [exact Htrace |].
    split; [now apply Hreads_preserved |].
    split.
    - unfold Total.recorded_effects in *.
      now rewrite Hcontributions.
    - split.
      + unfold narrowing_input, R.aggregate in *.
        now rewrite Hcontributions, Hsigma.
      + unfold narrowing_fixed_at, narrowing_input, R.aggregate in *.
        now rewrite Hcontributions, Hsigma.
  Qed.

  Lemma fixed_summary_same_solver_view :
    forall tf before after owner,
      Total.same_solver_view before after ->
      fixed_summary tf before owner ->
      fixed_summary tf after owner.
  Proof.
    intros tf before after owner
      [[Hsigma_map [Hreaders Hqueue]] Hcontributions] Hsummary.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - intros [value Hlookup]. exists value.
      now rewrite Hsigma_map.
    - intros reads Hreads.
      exact (@Total.guarded_reads_same_view
        before after owner reads
        (conj Hsigma_map (conj Hreaders Hqueue)) Hreads).
    - unfold R.sigma_value. now rewrite Hsigma_map.
    - exact Hcontributions.
  Qed.

  Lemma fixed_summary_observe :
    forall tf st observed owner,
      fixed_summary tf st owner ->
      fixed_summary tf (R.observe st observed) owner.
  Proof.
    intros. eapply fixed_summary_same_solver_view;
      [apply Total.observe_same_solver_view |exact H].
  Qed.

  Lemma fixed_summary_enqueue :
    forall tf st inserted owner,
      fixed_summary tf st owner ->
      fixed_summary tf (R.enqueue st inserted) owner.
  Proof.
    intros tf st inserted owner Hsummary.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - exact (fun Hsolved => Hsolved).
    - intros reads Hreads. now apply Total.guarded_reads_enqueue.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fixed_summary_set_value_other :
    forall tf st fr direct st' fr' owner,
      R.set_value st fr direct = (st', fr') ->
      owner <> R.frame_owner fr ->
      fixed_summary tf st owner ->
      fixed_summary tf st' owner.
  Proof.
    intros tf st fr direct st' fr' owner Hset Hneq Hsummary.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - intros. eapply Total.set_value_solved; eauto.
    - intros. eapply Total.guarded_reads_set_value; eauto.
    - eapply Total.set_value_sigma_value_other_correctness; eauto.
    - eapply Total.set_value_contributions; eauto.
  Qed.

  Lemma fixed_summary_materialize :
    forall tf st inserted owner,
      fixed_summary tf st owner ->
      fixed_summary tf (R.materialize st inserted) owner.
  Proof.
    intros tf st inserted owner Hsummary.
    pose proof (proj1 Hsummary) as Hsolved.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - intros. now apply Total.materialize_preserves_solved.
    - intros reads Hreads. now apply Total.guarded_reads_materialize.
    - now apply Total.materialize_sigma_value_solved.
    - unfold R.materialize.
      destruct (M.lookup (R.sigma st) inserted); reflexivity.
  Qed.

  Lemma fixed_summary_add_reader :
    forall tf st target added owner,
      fixed_summary tf st owner ->
      fixed_summary tf (Total.add_reader st target added) owner.
  Proof.
    intros tf st target added owner Hsummary.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - exact (fun Hsolved => Hsolved).
    - intros reads Hreads. now apply Total.guarded_reads_add_reader.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fixed_summary_pop_other :
    forall tf st popped rest owner,
      R.queue_pop (R.queue st) = Some (popped, rest) ->
      owner <> popped ->
      fixed_summary tf st owner ->
      fixed_summary tf (R.with_queue st rest) owner.
  Proof.
    intros tf st popped rest owner Hpop Hneq Hsummary.
    eapply fixed_summary_transport; [| | | |exact Hsummary].
    - exact (fun Hsolved => Hsolved).
    - intros reads Hreads.
      eapply Total.guarded_reads_pop_other; eauto.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fixed_summary_complete_get :
    forall tf st fr target st' fr' value owner,
      R.complete_get st fr target = (st', fr', value) ->
      fixed_summary tf st owner ->
      fixed_summary tf st' owner.
  Proof.
    intros tf st fr target st' fr' value owner Hget Hsummary.
    unfold R.complete_get in Hget.
    set (base := if R.rank_lt st (R.frame_owner fr) target
      then st else R.promote_controlled st target) in *.
    set (read_state := Total.add_reader base target (R.frame_owner fr)) in *.
    fold Total.add_reader in Hget. inversion Hget; subst.
    apply fixed_summary_materialize. subst read_state.
    apply fixed_summary_add_reader. subst base.
    destruct (R.rank_lt st (R.frame_owner fr) target).
    - exact Hsummary.
    - eapply fixed_summary_same_solver_view;
        [apply Total.promote_controlled_same_solver_view |exact Hsummary].
  Qed.

  Lemma fixed_summary_requeue tf before st inserted owner :
    fixed_summary tf st owner ->
    fixed_summary tf
      (R.requeue_changed_controlled_owner before st inserted) owner.
  Proof.
    intro H. apply (Total.requeue_preserves (fun st => fixed_summary tf st owner));
      auto using fixed_summary_enqueue.
  Qed.

  Lemma committed_fixed_or_queued tf st fr direct st' fr' :
    U.avoids_fallback (R.frame_phase fr) ->
    Total.completed_witness tf st fr direct ->
    R.set_value st fr direct = (st', fr') ->
    Total.queued (R.requeue_changed_controlled_owner st st' (R.frame_owner fr))
      (R.frame_owner fr) \/
    fixed_summary tf (R.requeue_changed_controlled_owner st st' (R.frame_owner fr))
      (R.frame_owner fr).
  Proof.
    intros Hsafe Hhistory Hset.
    destruct (@completed_witness_set_value_fixed_or_queued
      tf st fr direct st' fr' Hsafe Hhistory Hset) as [Hqueued |Hfixed].
    - now left.
    - right. now apply fixed_summary_requeue.
  Qed.
End F.
Definition summary := F.fixed_summary.
Definition guarded tf st ctrl owner :=
 B.queued st owner \/ B.control_active owner ctrl \/ summary tf st owner.
Lemma summary_aggregate_view tf before after owner :
 R.sigma after = R.sigma before ->
 (forall reads,B.guarded_reads before owner reads -> B.guarded_reads after owner reads) ->
 (forall effects,B.recorded_effects before owner effects -> B.recorded_effects after owner effects) ->
 UL.equivalent (R.aggregate after owner) (R.aggregate before owner) ->
 summary tf before owner -> summary tf after owner.
Proof.
 intros Hsigma Hreads Heffects Hagg
 [Hsolved [direct [reads [effects [Htrace [Hguard [Heffect [Hbound Hfixed]]]]]]]].
 pose proof (F.join_right_extensional direct Hagg) as Hinputs.
 assert (Hbound' : D.leq (D.join direct (R.aggregate after owner)) (R.sigma_value before owner) = true).
 { eapply DL.leq_trans;[exact (proj1 Hinputs) |exact Hbound]. }
 split;[destruct Hsolved as [value Hv];exists value;now rewrite Hsigma |].
 exists direct,reads,effects. split;[exact Htrace |]. split;[apply Hreads,Hguard |].
 split;[apply Heffects,Heffect |]. split.
 - unfold F.narrowing_input,R.sigma_value in *. now rewrite Hsigma.
 - unfold F.narrowing_fixed_at,F.narrowing_input,R.sigma_value in *. rewrite Hsigma.
   eapply F.domain_equivalent_trans;[|exact Hfixed].
   apply (F.narrow_extensional owner);assumption.
Qed.
Lemma write_aggregate_equivalent st fr target input next changed owner :
 R.write_side_contribution st fr target input = (next,changed) ->
 (owner <> target \/ changed = false) ->
 UL.equivalent (R.aggregate next owner) (R.aggregate st owner).
Proof.
 intros Hw [Hneq|Hfalse].
 - unfold R.aggregate. rewrite (@B.write_side_contribution_other st fr target input next changed owner Hw Hneq).
   split;apply DL.leq_refl.
 - destruct (V.eq_dec owner target) as [->|Hneq].
   + subst changed. pose proof (@E.write_changed_flag st fr target input next false Hw) as Hflag.
     destruct (R.equivalent (R.aggregate next target) (R.aggregate st target)) eqn:Heq;
     [apply F.equivalent_bool_true,Heq |discriminate].
   + unfold R.aggregate. rewrite (@B.write_side_contribution_other st fr target input next changed owner Hw Hneq).
     split;apply DL.leq_refl.
Qed.
Lemma summary_write tf st fr target input next changed owner :
 R.write_side_contribution st fr target input = (next,changed) ->
 owner <> R.frame_owner fr -> (owner <> target \/ changed = false) ->
 summary tf st owner -> summary tf next owner.
Proof.
 intros Hw Hsource Htarget Hsummary.
 eapply summary_aggregate_view;[ | | | |exact Hsummary].
 - exact (proj1 (B.write_side_contribution_same_read_view Hw)).
 - intros reads Hreads. eapply B.guarded_reads_same_view;
   [eapply B.write_side_contribution_same_read_view;exact Hw |exact Hreads].
 - intros effects Heffects. eapply B.recorded_effects_write_other_source;eassumption.
 - eapply write_aggregate_equivalent;eassumption.
Qed.
Lemma summary_requeue tf before after source target owner :
 summary tf after owner -> summary tf (C.requeue_source before after source target) owner.
Proof.
 intro Hsummary. unfold C.requeue_source. destruct C.cell_changed;
 [apply F.fixed_summary_enqueue,Hsummary |exact Hsummary].
Qed.
Lemma summary_finish tf before after fr target changed owner :
 summary tf after owner -> summary tf (C.finish_write before after fr target changed) owner.
Proof.
 intro Hsummary. unfold C.finish_write. destruct changed.
 - apply F.fixed_summary_enqueue,summary_requeue,Hsummary.
 - apply summary_requeue,Hsummary.
Qed.
Lemma finish_fixed_or_queued tf st fr target input next changed owner :
 R.write_side_contribution st fr target input = (next,changed) ->
 owner <> R.frame_owner fr -> summary tf st owner ->
 B.queued (C.finish_write st next fr target changed) owner \/
 summary tf (C.finish_write st next fr target changed) owner.
Proof.
 intros Hw Hneq Hsummary.
 destruct (V.eq_dec owner target) as [->|Hother].
 - destruct changed.
   + left. unfold C.finish_write,B.queued,R.enqueue. cbn. apply B.queue_insert_members. now left.
   + right. apply summary_finish. eapply summary_write;[exact Hw |exact Hneq |now right |exact Hsummary].
 - right. apply summary_finish. eapply summary_write;[exact Hw |exact Hneq |now left |exact Hsummary].
Qed.
Lemma publish_fixed_or_queued tf targets st fr owner :
 owner <> R.frame_owner fr -> summary tf st owner ->
 B.queued (C.publish targets st fr) owner \/ summary tf (C.publish targets st fr) owner.
Proof.
 intro Hneq. revert st. induction targets as [|target rest IH];intros st Hsummary;
 cbn -[R.write_side_contribution C.finish_write];[now right |].
 destruct (R.write_side_contribution st fr target
 (match M.lookup (R.frame_local_side fr) target with Some value=>value |None=>D.bottom end)) as [next changed] eqn:Hw.
 destruct (@finish_fixed_or_queued tf st fr target _ next changed owner Hw Hneq Hsummary) as [Hq|Hs].
 - left. apply C.publish_keeps_queued,Hq.
 - apply IH,Hs.
Qed.
Lemma clear_summary_other tf st cleared owner :
 owner <> cleared -> summary tf st owner -> summary tf (P.clear_owner st cleared) owner.
Proof.
 intros Hneq [Hsolved [direct [reads [effects [Htrace [Hreads [Heffects Hrest]]]]]]].
 split;[exact Hsolved |]. exists direct,reads,effects.
 split;[exact Htrace |]. split;[eapply P.clear_other_guarded_reads;eassumption |].
 split;[exact Heffects |exact Hrest].
Qed.
Lemma actual_commit_fixed_or_queued tf roots st fr direct k after next_fr next_k :
 N.steps tf (R.initial_config roots) {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} ->
 E.monotone tf ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunCommit fr direct k|} =
 Some {|R.cfg_state:=after;R.cfg_control:=R.RunDrain next_fr next_k|} ->
 B.queued after (R.frame_owner fr) \/ summary tf after (R.frame_owner fr).
Proof.
 intros Hreach Hmono Hstep.
 destruct (@E.commit_step_shape tf st fr direct k after next_fr next_k Hstep) as [next [Hset [-> Hk]]].
 eapply F.committed_fixed_or_queued;[ | |exact Hset].
 - exact (proj1 (E.reachable_no_fallback Hreach Hmono)).
 - eapply Replay.reachable_commit_witness;exact Hreach.
Qed.
Lemma summary_pop tf st popped rest next owner :
 R.queue_pop (R.queue st) = Some (popped,rest) ->
 B.control_active popped next -> summary tf st owner ->
 guarded tf (R.with_queue st rest) next owner.
Proof.
 intros Hpop Hactive Hsummary. destruct (V.eq_dec owner popped) as [->|Hneq].
 - right;left;exact Hactive.
 - right;right. eapply F.fixed_summary_pop_other; eassumption.
Qed.
Lemma summary_clear tf st cleared next owner :
 B.control_active cleared next -> summary tf st owner ->
 guarded tf (P.clear_owner st cleared) next owner.
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
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Get target next) k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : summary tf (R.observe st target) owner)
 by (apply F.fixed_summary_observe,Hsummary).
 cbn -[R.observe R.complete_get R.enqueue] in Hstep.
 destruct (negb (R.is_materialized (R.observe st target) target) &&
 R.rank_lt (R.observe st target) (R.frame_owner fr) target)%bool.
 - inversion Hstep;subst. right;right;exact Hobs.
 - set (current := if R.is_materialized (R.observe st target) target
   then R.observe st target else R.enqueue (R.observe st target) target) in *.
   destruct (R.complete_get current fr target) as [[after_st after_fr] value] eqn:Hg.
   inversion Hstep;subst. right;right.
   eapply F.fixed_summary_complete_get; [exact Hg |].
   subst current. destruct (R.is_materialized (R.observe st target) target);
   [exact Hobs |apply F.fixed_summary_enqueue,Hobs].
Qed.
Lemma summary_spawn tf st fr target next k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunRhs fr (R.ConstraintSystem.Spawn target next) k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 assert (Hobs : summary tf (R.observe st target) owner)
 by (apply F.fixed_summary_observe,Hsummary).
 cbn -[R.observe R.materialize R.enqueue] in Hstep.
 destruct (R.is_materialized (R.observe st target) target).
 - inversion Hstep;subst. right;right;exact Hobs.
 - destruct (R.rank_lt (R.observe st target) (R.frame_owner fr) target);
   inversion Hstep;subst;right;right;[exact Hobs |].
   apply F.fixed_summary_materialize,F.fixed_summary_enqueue,Hobs.
Qed.
Lemma summary_drain tf st fr k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDrain fr k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct (R.queue st) as [|target rest] eqn:Hq;
 cbn -[R.reset_registered_cells R.fresh_frame] in Hstep; rewrite Hq in Hstep; cbn in Hstep.
 - inversion Hstep;subst. right;right.
   eapply F.fixed_summary_same_solver_view; [apply B.reset_registered_cells_same_solver_view |exact Hsummary].
 - destruct (V.eq_dec target (R.frame_owner fr)) as [Heq|Hneq].
   + inversion Hstep;subst. eapply summary_pop;
     [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
   + destruct (R.rank_lt st (R.frame_owner fr) target).
     * inversion Hstep;subst. eapply summary_pop;
       [unfold R.queue_pop;rewrite Hq;reflexivity |now left |exact Hsummary].
     * inversion Hstep;subst. right;right.
       eapply F.fixed_summary_same_solver_view; [apply B.reset_registered_cells_same_solver_view |exact Hsummary].
Qed.
Lemma summary_return tf st k owner after :
 summary tf st owner ->
 R.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.Return k|}
 = Some after -> guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep. destruct k; cbn -[R.complete_get] in Hstep;
 try solve [inversion Hstep;subst;right;right;exact Hsummary].
 destruct (R.complete_get st f t) as [[after_st after_fr] value] eqn:Hg.
 inversion Hstep;subst. right;right. eapply F.fixed_summary_complete_get; eassumption.
Qed.

Lemma summary_base tf before after owner :
 Replay.not_side (R.cfg_control before) -> Replay.nonpublication (R.cfg_control before) ->
 Replay.commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 F.control_update_safe (R.cfg_control before) -> summary tf (R.cfg_state before) owner ->
 R.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hcompleted Hsafe Hsummary Hstep.
 destruct control.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp; [|discriminate].
   inversion Hstep;subst. eapply summary_pop; [exact Hp |now left |exact Hsummary].
 - destruct l; cbn -[R.observe] in Hstep.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + destruct (R.is_materialized (R.observe st t) t);
     inversion Hstep;subst;right;right;apply F.fixed_summary_observe,Hsummary.
 - cbn in Hstep. destruct (R.queue_pop (R.queue st)) as [[popped rest]|] eqn:Hp.
   + inversion Hstep;subst. eapply summary_pop; [exact Hp |now left |exact Hsummary].
   + inversion Hstep;subst. right;right;exact Hsummary.
 - inversion Hstep;subst. right;right;apply F.fixed_summary_materialize,Hsummary.
 - destruct r.
   + inversion Hstep;subst. right;right;exact Hsummary.
   + eapply summary_get; eassumption.
   + contradiction.
   + eapply summary_spawn; eassumption.
 - contradiction.
 - cbn -[R.set_value R.requeue_changed_controlled_owner] in Hstep.
   destruct (R.set_value st f t) as [next next_fr] eqn:Hs.
   inversion Hstep;subst.
   destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq].
   + destruct (@F.committed_fixed_or_queued tf st f t next next_fr Hsafe Hcompleted Hs) as [Hq|Hfixed];
     [now left |now right;right].
   + right;right. apply F.fixed_summary_requeue. eapply F.fixed_summary_set_value_other;eassumption.
 - eapply summary_drain; eassumption.
 - eapply summary_return; eassumption.
Qed.

Lemma summary_precommit tf before after owner :
 Replay.not_side (R.cfg_control before) -> Replay.nonpublication (R.cfg_control before) ->
 Replay.commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 F.control_update_safe (R.cfg_control before) -> summary tf (R.cfg_state before) owner ->
 P.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hside Hdead Hcompleted Hsafe Hsummary Hstep.
 destruct control; cbn -[R.next_config P.pending_above P.suspend_commit] in Hstep;
 try solve [eapply summary_base; eauto].
 destruct (P.pending_above st (R.frame_owner f)) as [[target rest]|] eqn:Hp.
 - inversion Hstep;subst. eapply summary_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner f) target rest Hp)))
   |now left |exact Hsummary].
 - eapply summary_base; eauto.
Qed.
Lemma summary_batched tf before after owner :
 Replay.nonpublication (R.cfg_control before) ->
 Replay.commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 F.control_update_safe (R.cfg_control before) -> summary tf (R.cfg_state before) owner ->
 P.next_batched tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hcompleted Hsafe Hsummary Hstep.
 destruct control; cbn -[P.next_config R.observe R.record_side_input] in Hstep;
 try solve [eapply summary_precommit; [ | | | |exact Hsummary |exact Hstep]; [exact I |exact Hdead |exact Hcompleted |exact Hsafe]].
 - destruct r;
   try solve [eapply summary_precommit; [ | | | |exact Hsummary |exact Hstep]; [exact I |exact Hdead |exact Hcompleted |exact Hsafe]].
   inversion Hstep;subst. right;right. apply F.fixed_summary_observe,Hsummary.
 - contradiction.
Qed.
Lemma summary_fresh tf before after owner :
 Replay.nonpublication (R.cfg_control before) ->
 Replay.commit_completed tf (R.cfg_state before) (R.cfg_control before) ->
 F.control_update_safe (R.cfg_control before) -> summary tf (R.cfg_state before) owner ->
 P.next_fresh tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 destruct before as [st control]. intros Hdead Hcompleted Hsafe Hsummary Hstep.
 destruct control;
 cbn -[P.next_batched P.pending_above P.suspend_commit P.retry_current] in Hstep;
 try solve [eapply summary_batched; eauto].
 - inversion Hstep;subst. destruct (V.eq_dec owner t) as [->|Hneq].
   + right;left;now left.
   + right;right. apply F.fixed_summary_materialize,clear_summary_other; assumption.
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


Lemma dead_pending_summary tf st fr direct target rest k owner after :
 summary tf st owner ->
 N.next_config tf {|R.cfg_state:=st;R.cfg_control:=R.RunDead fr direct (target::rest) k|} = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hsummary Hstep.
 cbn -[R.write_side_contribution C.requeue_source R.continue_dead] in Hstep.
 destruct (S.mem target (R.frame_current_targets fr));[inversion Hstep;subst;now right;right |].
 destruct (R.write_side_contribution st fr target D.bottom) as [next changed] eqn:Hw.
 inversion Hstep;subst. destruct (V.eq_dec owner (R.frame_owner fr)) as [->|Hsource].
 - unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];right;left;cbn;auto.
 - destruct (V.eq_dec owner target) as [->|Htarget].
   + destruct changed.
     * unfold R.continue_dead. destruct (_ && _)%bool.
       -- right;left;now left.
       -- left. unfold B.queued,R.enqueue. cbn. apply B.queue_insert_members;now left.
     * right;right. apply summary_requeue. eapply summary_write;[exact Hw |exact Hsource |now right |exact Hsummary].
   + assert (Hs : summary tf (C.requeue_source st next (R.frame_owner fr) target) owner).
     { apply summary_requeue. eapply summary_write;[exact Hw |exact Hsource |now left |exact Hsummary]. }
     unfold R.continue_dead. destruct changed;[destruct (_ && _)%bool |];
     right;right;cbn;try exact Hs.
   apply F.fixed_summary_enqueue,Hs.
Qed.
Theorem next_preserves_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before -> E.monotone tf ->
 summary tf (R.cfg_state before) owner -> N.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach Hmono Hsummary Hstep.
 assert (Hcompleted : Replay.commit_completed tf (R.cfg_state before) (R.cfg_control before)).
 { destruct before as [st ctrl]. destruct ctrl;try exact I.
   eapply Replay.reachable_commit_witness;exact Hreach. }
 assert (Hsafe : F.control_update_safe (R.cfg_control before)).
 { pose proof (E.reachable_no_fallback Hreach Hmono) as Hphases.
   destruct before as [st ctrl]. destruct ctrl;try exact I. exact (proj1 Hphases). }
 destruct (@Replay.Front.step_cases tf before after Hstep)
 as [Hb0|[st [fr [body [k [target [rest [-> [Hp ->]]]]]]]]].
 2: { eapply summary_pop;
   [exact (proj1 (proj2 (@P.pending_above_spec st (R.frame_owner fr) target rest Hp)))
   |now left |exact Hsummary]. }
 clear Hstep. rename Hb0 into Hstep.
 destruct before as [st ctrl]. destruct ctrl;
 try solve [eapply summary_fresh;[ |exact Hcompleted |exact Hsafe |exact Hsummary |exact Hstep];exact I].
 destruct l as [|target rest].
 - cbn -[C.publish R.publish_targets] in Hstep. inversion Hstep;subst.
   destruct (V.eq_dec owner (R.frame_owner f)) as [->|Hneq];[right;left;now left |].
   destruct (@publish_fixed_or_queued tf (S.elements (R.frame_current_targets f)) st f owner Hneq Hsummary) as [Hq|Hs].
   + left;exact Hq.
   + right;right. eapply F.fixed_summary_same_solver_view;[apply B.publish_targets_same_solver_view |exact Hs].
 - exact (@dead_pending_summary tf st f t target rest c owner after Hsummary Hstep).
Qed.
Lemma discharge_fixed tf roots before after owner :
 N.steps tf (R.initial_config roots) before -> E.monotone tf ->
 B.commit_discharge before after owner ->
 B.queued (R.cfg_state after) owner \/ summary tf (R.cfg_state after) owner.
Proof.
 intros Hreach Hmono [st [fr [direct [k [next [next_fr [-> [Hset [-> ->]]]]]]]]].
 eapply F.committed_fixed_or_queued;[ | |exact Hset].
 - exact (proj1 (E.reachable_no_fallback Hreach Hmono)).
 - eapply Replay.reachable_commit_witness;exact Hreach.
Qed.
Theorem next_guarded_summary tf roots before after owner :
 N.steps tf (R.initial_config roots) before -> E.monotone tf ->
 guarded tf (R.cfg_state before) (R.cfg_control before) owner ->
 N.next_config tf before = Some after ->
 guarded tf (R.cfg_state after) (R.cfg_control after) owner.
Proof.
 intros Hreach Hmono [Hq|[Ha|Hs]] Hstep.
 - destruct (@Replay.next_schedule tf before after Hstep owner (or_introl Hq))
   as [[Hq'|Ha']|Hd];[now left |now right;left |].
   destruct (@discharge_fixed tf roots before after owner Hreach Hmono Hd) as [Hq'|Hs'];
   [now left |now right;right].
 - destruct (@Replay.next_schedule tf before after Hstep owner (or_intror Ha))
   as [[Hq'|Ha']|Hd];[now left |now right;left |].
   destruct (@discharge_fixed tf roots before after owner Hreach Hmono Hd) as [Hq'|Hs'];
   [now left |now right;right].
 - eapply next_preserves_summary;eassumption.
Qed.
Definition summaries_guarded tf c := forall owner,Sem.solved (R.cfg_state c) owner ->
 guarded tf (R.cfg_state c) (R.cfg_control c) owner.
Theorem next_summaries tf roots before after :
 N.steps tf (R.initial_config roots) before -> E.monotone tf -> summaries_guarded tf before ->
 N.next_config tf before = Some after -> summaries_guarded tf after.
Proof.
 intros Hreach Hmono Hsummaries Hstep owner Hsolved.
 destruct (@Replay.next_solved_origin tf roots before after Hreach Hstep owner Hsolved)
 as [Hbefore|[Hq|Ha]];[|now left |now right;left].
 eapply next_guarded_summary;[exact Hreach |exact Hmono |apply Hsummaries,Hbefore |exact Hstep].
Qed.
Lemma steps_summaries tf roots first last :
 N.steps tf first last -> N.steps tf (R.initial_config roots) first ->
 E.monotone tf -> summaries_guarded tf first -> summaries_guarded tf last.
Proof.
 intro Hsteps. induction Hsteps;intros Hreach Hmono Hsummaries;[exact Hsummaries |].
 apply IHHsteps.
 - eapply Replay.steps_append;[exact Hreach |]. econstructor;[exact H |constructor].
 - exact Hmono.
 - eapply next_summaries;eassumption.
Qed.
Theorem reachable_summaries tf roots c :
 N.steps tf (R.initial_config roots) c -> E.monotone tf -> summaries_guarded tf c.
Proof.
 intros Hreach Hmono. eapply steps_summaries;[exact Hreach |constructor |exact Hmono |].
 intros owner [value Hlookup]. cbn in Hlookup. rewrite ML.lookup_empty in Hlookup. discriminate.
Qed.


Theorem terminal_summary tf roots final owner :
 N.steps tf (R.initial_config roots) (Sem.terminal_config final) ->
 E.monotone tf -> Sem.quiescent final -> Sem.solved final owner -> summary tf final owner.
Proof.
 intros Hreach Hmono Hquiet Hsolved.
 destruct (@reachable_summaries tf roots (Sem.terminal_config final) Hreach Hmono owner Hsolved)
 as [Hq|[Ha|Hs]];[|contradiction |exact Hs].
 exfalso. exact (@B.quiescent_not_queued final owner Hquiet Hq).
Qed.
Theorem successful_run_fixedpoint fuel tf roots final :
 N.solve_fuel fuel tf roots = Some final -> E.monotone tf ->
 forall owner,Sem.solved final owner ->
 (exists direct reads effects,Sem.rhs_eval final (tf owner) direct reads effects) /\
 (forall direct reads effects,Sem.rhs_eval final (tf owner) direct reads effects ->
 UL.equivalent (WN.narrow (R.sigma_value final owner)
 (D.join direct (R.aggregate final owner))) (R.sigma_value final owner)).
Proof.
 intros Hsolve Hmono owner Hsolved.
 split;[exact (proj1 (@Replay.successful_run_replay_post_solution fuel tf roots final Hsolve owner Hsolved)) |].
 unfold N.solve_fuel in Hsolve.
 destruct (@B.terminal_state_shape (N.run_fuel fuel tf (R.initial_config roots)) final Hsolve) as [Hshape Hquiet].
 apply F.quiescent_fixed_summary;[exact Hquiet |].
 eapply terminal_summary;[ |exact Hmono |exact Hquiet |exact Hsolved].
 rewrite <- Hshape. apply Replay.fuel_steps.
Qed.
Theorem successful_run_correct_and_fixed fuel tf roots final :
 E.monotone tf -> N.solve_fuel fuel tf roots = Some final ->
 Sem.correct_final_state tf roots final /\
 (forall owner,Sem.solved final owner ->
 exists direct reads effects,Sem.rhs_eval final (tf owner) direct reads effects /\
 UL.equivalent (WN.narrow (R.sigma_value final owner)
 (D.join direct (R.aggregate final owner))) (R.sigma_value final owner)).
Proof.
 intros Hmono Hsolve. split;[eapply Replay.successful_run_correct;exact Hsolve |].
 intros owner Hsolved.
 destruct (@successful_run_fixedpoint fuel tf roots final Hsolve Hmono owner Hsolved)
 as [[direct [reads [effects Heval]]] Hfixed].
 exists direct,reads,effects. split;[exact Heval |eapply Hfixed;exact Heval].
Qed.
(** Infer the finite-support witness from the termination theorem, preserving
    its inductive type through the shared module aliases. *)
Definition sufficient_fuel := Replay.Termination.sufficient_fuel.
Definition total_correct :=
 fun tf roots finite =>
 match @sufficient_fuel tf roots finite return
   (exists fuel final, N.solve_fuel fuel tf roots = Some final /\
      Sem.correct_final_state tf roots final)
 with
 | ex_intro _ fuel (ex_intro _ final Hsolve) =>
   ex_intro _ fuel (ex_intro _ final
     (conj Hsolve (@Replay.successful_run_correct fuel tf roots final Hsolve)))
 end.
(** Public statement vocabulary lives with the implementation so that the
    facade can alias this functor without copying its nested proof modules. *)
Module N := Replay.Front.N.
Definition solved (final : R.state) (owner : V.t) : Prop :=
  exists value, M.lookup (R.sigma final) owner = Some value.

Definition replay (final : R.state) :=
  Sem.rhs_eval_with (fun target => M.lookup (R.sigma final) target).

Definition owner_post_solution (tf : R.ConstraintSystem.system)
  (final : R.state) (owner : V.t) : Prop :=
  forall direct reads effects, replay final (tf owner) direct reads effects ->
    D.leq direct (R.sigma_value final owner) = true /\
    (forall target value, In (target,value) effects ->
      D.leq value (R.sigma_value final target) = true).

Definition correct_final_state (tf : R.ConstraintSystem.system)
  (roots : list V.t) (final : R.state) : Prop :=
  forall owner, In owner roots ->
    solved final owner /\ owner_post_solution tf final owner.

Definition monotonic_system (tf : R.ConstraintSystem.system) : Prop :=
  forall owner, Sem.rhs_dependencies_monotone (tf owner) /\
                Sem.rhs_effects_monotone (tf owner).

Definition narrowing_fixed (tf : R.ConstraintSystem.system) (final : R.state) : Prop :=
  forall owner, solved final owner ->
    (exists direct reads effects, replay final (tf owner) direct reads effects) /\
    (forall direct reads effects, replay final (tf owner) direct reads effects ->
      UL.equivalent
        (WN.narrow (R.sigma_value final owner)
          (D.join direct (R.aggregate final owner)))
        (R.sigma_value final owner)).

Theorem total_correct_and_fixed : forall tf roots,
  Sem.finite_system tf roots -> monotonic_system tf ->
  exists fuel final, N.solve_fuel fuel tf roots = Some final /\
    correct_final_state tf roots final /\ narrowing_fixed tf final.
Proof.
 intros tf roots finite Hmono.
 destruct (@sufficient_fuel tf roots finite) as [fuel [final Hsolve]].
 exists fuel, final. split; [exact Hsolve |]. split.
 - exact (@Replay.successful_run_correct fuel tf roots final Hsolve).
 - exact (@successful_run_fixedpoint fuel tf roots final Hsolve Hmono).
Qed.
End WithCollections.
End WithLaws.
End Make.
